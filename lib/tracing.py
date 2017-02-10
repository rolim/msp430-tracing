import networkx as nx
from add_gpio_fun import *
from math import ceil

def hexlist(l):
    if not isinstance(l, list) and not isinstance(l, tuple) and not isinstance(l, set):
        return '%x' %l
    return [hexlist(x) for x in l]

class Marker(object):
    def __init__(self, address, sourceAddress, targetAddress, id, targetAtInstrumentation, saveSr = False, needJmp = None):
        """Marker to be used for instrumentation
        
        Arguments:
        address -- Where to put the instrumentation code
        sourceAddress -- address of the source basic block
        targetAddress -- address of the target basic block (can be different to the address)
        id -- marker value to emit
        needJmp -- Address of jump instruction: add an additional jump at instrumentation addr to guide preceeding fall through edges to the real block entry, adapt jump instruction to jump to second instrumentation instruction
        targetAtInstrumentation -- True: Branches should target the instrumentation code, False: Branches should target the code after the instrumentation
        """
        self.address = address
        self.targetAddress = targetAddress
        self.sourceAddress = sourceAddress
        self.id = id
        self.needJmp = needJmp
        self.saveSr = saveSr
        self.targetAtInstrumentation = targetAtInstrumentation
        self.targetCfg = None
        self.cycles = None
        self.latentCycles = 0 # cycles that are to be added to the following basic block
        self.isTimedMarker = True
        
    def __repr__(self):
        if self.sourceAddress:
            return '<%d@%x> %x -> %x' % (self.id, self.address, self.sourceAddress, self.targetAddress)
        else:
            return '<%d@%x>  x -> %x' % (self.id, self.address, self.targetAddress)
            
    def isRet(self):
        return isinstance(self, RetMarker)
        
class IrqMarker(Marker):
    pass
    
class RetMarker(Marker):
    pass

class IndirectCallMarker(Marker):
    pass


class BasicBlock(object):

    def __init__(self, start, end, endsize):
        self.successors = []
        self.start = start
        self.end = end
        self.endsize = endsize
        self.isCall = False
        self.isIndirectCall = False
        self.callTarget = None
        self.cycles = 0        
        
    def setSuccessors(self, suc):
        self.successors = suc
        
    def isPredicate(self):
        return len(self.successors)>1
        
    def __repr__(self):
        return 'BB %x-%x > %s' % (self.start, self.end, ['%x' %x for x in self.successors])
        
class LoopBlock(BasicBlock):

    def __init__(self, start, end, endsize):
        super(LoopBlock, self).__init__(start, end, endsize)
        self.header_bb = None # list: basic blocks in header, used in lookup table
        self.loop_bb   = None # list: basic blocks in loop, used in lookup table
        
    def getHeaderAddrAndCycles(self):
        return list([(bb.start, bb.cycles) for bb in self.header_bb])
    
    def getLoopAddrAndCycles(self):
        return list([(bb.start, bb.cycles) for bb in self.loop_bb])
    
    def __repr__(self):
        return 'LB %x-%x > %s cycles (%d,%d)' % (self.start, self.end, hexlist(self.successors), self.cycles, self.loopcycles)

class MarkerBlock(BasicBlock):
    """
    Used to represent a marker that should be handled as if it was normal code. As such, only the number of cycles is important.
    """
    def __init__(self, cycles, successor):
        super(MarkerBlock, self).__init__(0,0,0)
        self.successors.append(successor)
        self.cycles = cycles   
        
    def __repr__(self):
        return 'MB %x-%x > %s' % (self.start, self.end, ['%x' %x for x in self.successors])
     
     
class ControlFlowGraph(object):    

    def __init__(self, entry, bbs, name): 
        self.entry = entry
        self.exit = None
        self.bbs = {}
        self.tree = None
        self.edges = None
        self.blocking = None        
        self.graphedges(bbs)
        self.weightingHeuristic()
        self.hasMarkers = len([x for x in list(self.bbs.values()) if x.isPredicate()]) > 0        
        self.name = name
        self.coloring = None
        self.loopbounds = {} # dict: {(list of loop nodes): upper bound, None if unbounded}
        
    def graphedges(self, bbs):
        """
        traverses graph given by bss, starting from self.entry
        creates data structures
            self.edges -- edges of the graph
            self.diedges -- dictionary source -> destinations
            self.diedges_rev -- dictionary destination -> sources
        """
        print('<graphedges>')
        tovisit = [self.entry]
        visited = []
        self.edges = []
        self.diedges = {}
        self.diedges_rev = {}
        while len(tovisit) > 0:
            visited.append(tovisit[0])
            self.bbs[tovisit[0]] = bbs[tovisit[0]]
            self.bbs[tovisit[0]].incfg = self.entry
            self.diedges[tovisit[0]] = bbs[tovisit[0]].successors
            for suc in bbs[tovisit[0]].successors:
                if not suc in self.diedges_rev:
                    self.diedges_rev[suc] = []
                self.diedges_rev[suc].append(tovisit[0])
                self.edges.append((tovisit[0], suc))
                if not suc in visited and not suc in tovisit:
                    tovisit.append(suc)
            del(tovisit[0])
        cfg_exit = [x for x in list(self.diedges.keys()) if x % 2 == 1]
        if len(cfg_exit) > 0:
            self.exit=cfg_exit[0]
    
    def addVertex(self, bb):
        assert(bb.start not in self.bbs)
        self.bbs[bb.start] = bb
        self.diedges[bb.start] = bb.successors
    
    def removeEdge(self, e):
        assert(e in self.edges)
        self.edges.remove(e)
        self.diedges[e[0]].remove(e[1]) # diedges is reference to self.bbs[e[0]].successors
        self.diedges_rev[e[1]].remove(e[0])
        weight = self.edgeweights[e]
        del(self.edgeweights[e])
        if e in self.tree:
            self.tree.remove(e)
            return weight, True
        return weight, False
    
    def addEdge(self, e, weight, inTree):
        assert(e not in self.edges)
        self.edges.append(e)
        if not e[1] in self.diedges_rev:
            self.diedges_rev[e[1]] = []
        self.diedges[e[0]].append(e[1])
        self.diedges_rev[e[1]].append(e[0])
        self.edgeweights[e] = weight
        if inTree:
            self.tree.append(e)
    
    def weightingHeuristic(self, nloop = 10):
        """
        Assume only single entry loops!
        """
        print("<weightingHeuristic %x>" % self.entry)
        self.edgeweights = {}
        G=nx.DiGraph(self.edges)
        G.add_edge(-1, self.entry, weight=1)
        visited = set([-1])
        allexitedges = set()
        
        naturalloop = {}
        exitedges = {}
        backedges = {}

        for s,t in nx.dfs_edges(G, -1):
            #print(t)
            backedges[t] = set(G.predecessors(t)).difference(visited)
            backedges[t] = [b for b in backedges[t] if nx.has_path(G,t,b)]
            if len(backedges[t]) > 0:
                backedges[t] = [(bs,t) for bs in backedges[t]]
                #print('backedges: %s' % str(backedges[t]))
                #print(list(G.in_edges([t])))
                #print('non-backedges into %d: %s' % (t,str(set(G.in_edges([t])).difference(set(backedges[t])))))
                #G_=nx.DiGraph(list(set(G.edges()).difference(set(G.in_edges([t])).difference(set(backedges[t])))))
                naturalloop[t] = [n for n in G.nodes() if nx.has_path(G, n, t) and nx.has_path(G, t, n)]
                #print('natural loop: %s'% str(list(naturalloop[t])))
                exitedges[t] = [e for e in G.edges() if e[0] in naturalloop[t] and not e[1] in naturalloop[t]]
                allexitedges.update(exitedges[t])
                #print('exit edges: %s'% str(list(exitedges[t])))
            visited.update([t])
                
        # assign weights in topological order
        #print('assign weights in topological order')
        G_ = G.copy()
        for s,t in [e for es in backedges.values() for e in es]:
            G_.remove_edge(s,t)
        for t in nx.topological_sort(G_):
            if t == -1:
                continue
            #print(t)
            if t in naturalloop:
                # in-weights
                inweight = sum([G[parent][child]['weight'] for parent,child in G.in_edges([t]) if parent not in naturalloop[t]])
                # exit-weights
                for es,et in exitedges[t]:
                    G[es][et]['weight'] = inweight / len(exitedges[t])
                inweight = inweight * LOOP_MULTIPLIER
            else:
                # in-weights
                inweight = sum([G[parent][child]['weight'] for parent,child in G.in_edges([t])])
            
            outedges = G.out_edges(t)   
            outedges_exits = [e for e in allexitedges if e[0] == t]
            #print('outedges %s, outedges_exits %s' % (str(outedges),str(outedges_exits)))
            try:
                weights_exits = sum([G[es][et]['weight'] for es,et in outedges_exits])
            except KeyError:
                for s,t in outedges_exits:
                    if 'weight' in G[s][t]:
                        print('(%d,%d,%0.2f)' % (s,t,G[s][t]['weight']))
                    else:
                        print('(%d,%d,--)' % (s,t))
                raise
                    
            #print('inweights %f, outedges %s, weights_exits, %s' % (inweight, outedges, weights_exits))
            for parent, child in set(outedges).difference(set(outedges_exits)):
                G[parent][child]['weight'] = (inweight - weights_exits) / (len(outedges) - len(outedges_exits))
                
        for e in G.edges():
            if e[0] >= 0:
                self.edgeweights[e] = G[e[0]][e[1]]['weight']
                #print('weights: %x->%x %0.3f' % (e[0],e[1],self.edgeweights[e]))
            
    def addBlockingMarkersAtPredicates(self, callswithmarkers):
        """
        this method creates the blocking edge set by selecting edges that lead from immediate predicates of the (call) basic block
        exit edges are also included into the blocking set to satisfy the blocking property (see Ball Laurs paper)
        """
        self.blocking = []
        self.blockingTarget = {}
        calls = [x for x in list(self.bbs.values()) if x.isCall and (x.callTarget in callswithmarkers or x.isIndirectCall)]
        for c in calls:
            #print 'call %x' % c
            tovisit = [c.start]
            visited = []
            while len(tovisit) > 0:
                visited.append(tovisit[0])
                pre = [p[0] for p in [x for x in self.edges if x[1]==tovisit[0]]]
                for p in pre:
                    if self.bbs[p].isPredicate():
                        #print 'blocking (%x,%x)' % (p,tovisit[0])
                        self.blocking.append((p,tovisit[0]))
                        self.blockingTarget[(p,tovisit[0])] = c.callTarget
                    elif not p in visited and not p in tovisit:
                        tovisit.append(p)
                del(tovisit[0])
        #self.tree = list(set(self.edges).difference(set(self.blocking)))
        if self.exit:
            for n in self.diedges_rev[self.exit]:
                self.blocking.append((n,self.exit))
        self.blocking = list(set(self.blocking))
        #print self.blocking
        
    def addBlockingMarkersLPM(self, lpm):
        # test edges and if they are member of cfg, append edge to blocking set
        l = [l for l in lpm if l[1] in self.bbs.keys()]
        # add edge l[0]-l[1]
        if len(l)>0:
            print('lpm %s' % hexlist(l))

            lpmsourcebb = [bb.start for bb in self.bbs.values() if bb.end in [s[0] for s in l] and not bb.isCall]
            lpmtargetbb = [s[1] for s in l]
            self.blocking.extend(zip(lpmsourcebb, lpmtargetbb))
            
            # add all incoming edges to l[0]
            for s in lpmsourcebb:
                for ie in self.diedges_rev[s]:
                    if self.bbs[ie].isCall:
                        print('lpm not adding incoming because of call %x->%x' % (ie,s))
                    else:
                        self.blocking.append((ie, s))
                        print('lpm add incoming %x->%x' % (ie,s))
        
    def spanningtrees(self):
        print('<spanningtrees>')
        # implementation using networkx --
        G = nx.MultiGraph() # use MultiGraph to allow parallel edges
        for s,t in self.edges:
            if not (s,t) in self.blocking:
                G.add_edge(s,t,weight = -self.edgeweights[(s,t)], edge = (s,t))
        self.tree = [data['edge'] for s,t,data in nx.minimum_spanning_edges(G, data=True)]
        print('tree edges: %s'  % (['%x->%x' %(x[0],x[1]) for x in self.tree]))
        
    def simplecycles(self):
        """
        finds all simple cycles in the graph and converts nonoverlapping cycles into *nodes
        overlapping cycles are broken using existing markers
        """
        print('<simplecycles>')
        # save original structure
        self.o_bbs = copy.deepcopy(self.bbs)
        self.o_diedges = copy.deepcopy(self.diedges)
        self.o_diedges_rev = copy.deepcopy(self.diedges_rev)
        self.o_edges = copy.deepcopy(self.edges)
        # https://networkx.readthedocs.org/en/stable/reference/generated/networkx.algorithms.cycles.simple_cycles.html
        # NOTE: prior to 1.8.1, simple_cycles returns repeated last node twice
        #  see http://networkx.github.io/documentation/networkx-1.8.1/reference/api_1.8.html
        G = nx.DiGraph(list(set(self.edges).difference(set(self.blocking))))
        cycles = list(nx.simple_cycles(G))
        if nx.__version__.startswith('1.8.1') or float(nx.__version__[:3]) > 1.8:
            for c in cycles:
                c.append(c[0])
        # overlapping cycles
        overlapcycles = set()
        for v in list(self.bbs.keys()):
            ov = [c for c in cycles if v in c] # for every node, create a list of cycles
            if len(ov) > 1:
                overlapcycles.update([tuple(x) for x in ov])
        nono_cycles = list(set([tuple(x) for x in cycles]).difference(overlapcycles))
        print('cycles: %d, overlap: %d, non-overlap: %s' % (len(cycles), len(overlapcycles), hexlist(nono_cycles)))
        
        
        # convert non-overlapping cycles to *-nodes
        # need to have exactly one entry point and one or more exit points
        # TODO: handle more than one exit nodes in *-node
        for c in nono_cycles:
            entry = []
            exit = []
            for n in c[:-1]: # iterate through all nodes in cycle (last element is equal to the first)
                e = self.diedges_rev[n] # edges towards this node
                if len([x for x in e if x not in c]) > 0:
                    entry.append(n)
                elif n == self.entry:
                    entry.append(n)
                e = self.diedges[n]
                if len([x for x in e if x not in c]) > 0:
                    exit.append(n)
            print('entry: %s, exit: %s' % (hexlist(entry),hexlist(exit)))
            if len(exit)>1:
                print('TODO: handle more than one exit nodes in *-node, skipping')
                continue
            # *-node: entry to exit + exit to exit loops
            lb = LoopBlock(entry[0], self.bbs[exit[0]].end, self.bbs[exit[0]].endsize)
            lb.setSuccessors([x for x in self.diedges[exit[0]] if x not in c])
            n = c.index(entry[0])
            lb.cycles = self.bbs[c[n]].cycles # cycles of header
            while c[n] != exit[0]:
                n = (n + 1) % (len(c)-1)
                lb.cycles += self.bbs[c[n]].cycles
            # loop
            lb.loopcycles = sum([self.bbs[n].cycles for n in c[:-1]])
            lb.loop = c[:-1]
            for n in c[:-1]:
                del(self.bbs[n])
            self.bbs[entry[0]] = lb
        bbs = self.bbs
        self.bbs = {}
        #print bbs
        self.graphedges(bbs)
        
        # find one non-tree edge in every overlapping cycle and add it to the blocking set
        # TODO: find a minimal cost solution
        self.blockcycles = []
        e_tree = set(self.edges).difference(set(self.tree))
        e_blocking = set(self.blocking)
        for c in overlapcycles:
            G = nx.DiGraph()
            G.add_path(c)
            i = set(self.blockcycles).intersection(set(G.edges()))
            if len(i) > 0:
                continue
            i = e_blocking.intersection(set(G.edges()))
            if len(i) > 0:
                continue
            i = list(e_tree.intersection(set(G.edges())))
            if len(i) > 0:
                self.blockcycles.append(tuple(i[0]))
        self.blockcycles = list(set(self.blockcycles))
        #print self.blockcycles
        
        # break connections between * nodes
        # if there is a path from *1 to *2, add entry edge to *2 to blocking set
        G = nx.DiGraph(list(set(self.edges).difference(set(self.blocking).union(set(self.blockcycles)))))
        self.blockstar = []
        starnodes = [k for k,v in self.bbs.items() if isinstance(v, LoopBlock)]
        for i in starnodes:
            for j in starnodes:
                if i==j:
                    continue
                remove = []
                for p in nx.all_simple_paths(G, i, j): # there might be more than one egde pointing to the entry of a loop
                    if not tuple(p[-2:]) in remove:
                        print('remove path from %x to %x: %s' % (i,j, hexlist(p)))                    
                        remove.append(tuple(p[-2:]))
                print('%s' % str(remove))
                self.blockstar.extend(remove) 
                for s,t in remove:
                    G.remove_edge(s,t)
        #print self.blockstar
        
    def timegraph(self):
        print('<timegraph>')
        # 5.
        # for every root node
        # extract all simple paths to all other nodes, annotate with cycle count (offsets and loops), connect nodes with equal cycle count        
        G = nx.DiGraph(list(set(self.edges).difference(set(self.blocking).union(set(self.blockcycles)).union(set(self.blockstar)))))
        G.add_nodes_from(list(self.bbs.keys()))
        bG = nx.DiGraph(list(set(self.blocking).union(set(self.blockcycles)).union(set(self.blockstar)))) # graph made from blocking edges
        rG = G.reverse()
        rootnodes = [r for r in rG.nodes() if len(rG.edges(r))==0]
        sinknodes = [r for r in bG.nodes() if len(bG.edges(r))>0]
        print('root nodes: %s ' % hexlist(rootnodes))
        print('sink nodes: %s' % hexlist(sinknodes))
        self.tg_break = []
        for source in rootnodes:
            tg = nx.DiGraph()
            for target in list(sinknodes):
                #print 's: %x t: %x' % (source, target)
                # consider all paths between the source node and the sink node
                sp = list(nx.all_simple_paths(G, source, target))
                if len(sp) == 0:
                    continue
                c = [accumulateCycles([self.bbs[i] for i in x]) for x in sp]                
                pc = list(map(lambda x,y: list(zip(x,y)), sp, c)) # list of path nodes and accumulated cycles               
                combinelist = self.combineCycleNodes([item for sublist in pc for item in sublist])
                print('%x -> %x: %s' % (source, target, str(pc)))
                for x in pc:
                    tg.add_path([combinelist[y] for y in x])
                #map(lambda x: tg.add_path(map(lambda y: combinelist[y], x)),pc)
            print('time graph from %x: %d nodes, %d edges, %d markers' % (source, len(tg.nodes()), len(tg.edges()), max(0,len(tg.edges()) - (len(tg.nodes())-1))))
        #   6. break time graph using edges in non-tree set
            # weight edges in non-tree set higher than others to produce spanning tree containing edges from original tree ..
            revtree = [(x[1],x[0]) for x in self.tree]
            for e in tg.edges():
                if (e[0][0], e[1][0]) in self.tree or (e[0][0], e[1][0]) in revtree:
                    tg[e[0]][e[1]]['weight'] = 0.5
            tgG = nx.minimum_spanning_tree(nx.Graph(tg.edges(data=True)))
            tg_tree = tgG.edges()
            tg_revtree = [(x[1],x[0]) for x in tg_tree]
            tg_break = list(set(tg.edges()).difference(set(tg_tree).union(set(tg_revtree))))
            tg_break = list(set([(x[0][0], x[1][0]) for x in tg_break]))
            #print list(nx.minimum_spanning_edges(nx.Graph(tg.edges(data=True))))
            #print 'time graph: %s' % hexlist(tg.edges())
            #print 'time graph tree: %s' % hexlist(tg_tree)
            print('time graph breakers: %s' % hexlist(tg_break))
            self.tg_break = list(set(self.tg_break).union(set(tg_break)))
        
        
    def combineCycleNodes(self, cyclenodes):
        print('<combineCycleNodes>')
        cyclenodes = list(set(cyclenodes))
        # return a dict with nodes as keys pointing to combined nodes
        combinelist = {}
        # for every bb, find cycle counts that are ambiguous
        addrs = list(set([x[0] for x in cyclenodes]))
        for a in addrs:
            s = [n[1] for n in cyclenodes if n[0]==a]
            if sum([x[1] for x in s]) == 0:
                continue # no loop cycles
            nodeclusters = {}
            clusterheads = []
            numclusters = 0
            #print 'loop cycles for node %x' % a
            #print list(s)
            # compare all to all
            for i in range(len(s)):
                for j in range(i+1,len(s)):
                    # c_i - c_j = 0 ?
                    # possible combinations loop in i, loop in j, loop in i and j
                    # no loops
                    if s[i][1] == 0 and s[j][1] == 0:
                        continue
                    # only one loop
                    if s[i][1] == 0:
                        if s[i][0] < s[j][0]: # loop offset is larger, can never be equal
                            continue
                    elif s[j][1] == 0:
                        if s[j][0] < s[i][0]: # loop offset is larger, can never be equal
                            continue
                    # two loops or one loop with smaller offset
                    if (s[j][0] - s[i][0]) % fractions.gcd(s[i][1],s[j][1]) == 0: # difference is multiple of gcd                    
                        # print 'ambiguous cycle count: %d %d = %d %d' % (s[i][0],s[i][1],s[j][0],s[j][1])
                        if not s[i] in nodeclusters:
                            nodeclusters[s[i]] = numclusters
                            clusterheads.append((a,s[i]))
                            numclusters = numclusters + 1
                            combinelist[(a,s[i])] = (a,s[i])
                        nodeclusters[s[j]] = nodeclusters[s[i]]
                        combinelist[(a,s[j])] = clusterheads[nodeclusters[s[i]]]
        for c in cyclenodes:
            if c not in combinelist:
                combinelist[c] = c
        #print 'reduce %d nodes to %d nodes' % (len(cyclenodes), len(set(combinelist.values())))
        return combinelist
        
    def updateMarkerEdges(self):
        """
        put all blocking edges to the marker set (used for trace reconstruction)
        """
        self.markeredges = set(self.blocking).union(set(self.blockcycles)).union(set(self.tg_break)).union(set(self.blockstar))
            
    def getMarkers(self, startmakerid, edges = None):
        """
        Returns (next free marker ID, [markers])
        """
        coloring = None
        m = startmakerid
        markers = []
        self.updateMarkerEdges()
        if edges is None:
            edges = self.markeredges
            if self.coloring and not USE_UNIQUE_MARKERS and not USE_CFG_UNIQUE_MARKERS:
                coloring = self.coloring
        #if len(filter(lambda x: x[1] % 2 == 1, self.markeredges)) > 0:
        #returnm = 1
        #else:
            #returnm = 0       
        for source, target in edges:
            if coloring:
                m = coloring[(source, target)] + 1
            print('marker %x -> %x, id=%d' % (source,target,m))
            # needed information:
            #  type of edge: fall through, conditional jump, unconditional jump
            # ret or reti
            if target % 2 == 1:
                print('  function return')
                markers.append(RetMarker(self.o_bbs[source].end, source, target, m, True, True))
            # single entry: at beginning
            elif len(self.o_diedges_rev[target]) == 1:
                print('  single entry target')
                markers.append(Marker(target, source, target, m, True, True))                           # store SR
            # unconditional jump (or call): before jump
            elif len(self.o_diedges[source]) == 1:
                if (target - self.o_bbs[source].end) == self.o_bbs[source].endsize * 2:
                    print('  unconditional fall through') # happens if another jump has this bb as target, same as fall through
                    markers.append(Marker(target, source, target, m, False, True))                      # store SR
                else:
                    print('  unconditional jump')
                    markers.append(Marker(self.o_bbs[source].end, source, target, m, True, True))       # store SR
            # fall through: after jc
            elif (target - self.o_bbs[source].end) == self.o_bbs[source].endsize * 2:
                print('  fall through')
                markers.append(Marker(target, source, target, m, False, True))
            # multiple entry: at beginning with jump
            elif len(self.o_diedges_rev[target]) > 1:
                print('  multiple entry target')
                markers.append(Marker(target, source, target, m, True, True, self.o_bbs[source].end))   # store SR
            else:
                print('  can\'t put marker')
                assert(False)
            try:
                markers[-1].targetCfg = self.blockingTarget[(source, target)]
            except KeyError:
                pass
            markers[-1].saveSr = False
            m = m + 1
        # sort markers, have ret markers first, then all other egdes. This ensures that ret markers are appended last, after multiple markers to multiple entry blocks. Otherwise they migh be skipped (due to the jump before the multiple entry marker).
        markers = sorted(markers, key=operator.methodcaller('isRet'), reverse=True)

        return m,markers
    
    def setReduceParameters(self, CPU_SPEED_ERROR, ALLOW_LOOPS_IN_TIMED, boundsdb = None):
        self.CPU_SPEED_ERROR = CPU_SPEED_ERROR
        self.ALLOW_LOOPS_IN_TIMED = ALLOW_LOOPS_IN_TIMED
        self.boundsdb = boundsdb
    
    # destructive / reductive approach
    def reduceMarkers(self, isFirst, markers = None):
        """
        If the markers (list of Marker objects) argument is given, cycle counts from markers are added to the cfg in the cycle analysis. This is used for the none_and_reduction method
        """
        if isFirst:
            # save original structure
            self.o_bbs = copy.deepcopy(self.bbs)
            self.o_diedges = copy.deepcopy(self.diedges)
            self.o_diedges_rev = copy.deepcopy(self.diedges_rev)
            self.o_edges = copy.deepcopy(self.edges)
            blockingmarkers = self.blocking
            markers = {}
        else:
            if markers is None:
                # just extend existing marker set, in case there are new ambigeous paths due to changes in program code
                markers = {}
                blockingmarkers = []
                blockingmarkers.extend(self.tg_break) # keep markers from last pass
                blockingmarkers.extend(self.blocking)
            else:
                # do analysis by keeping marker code in the program (treat it as normal program instructions when marker is removed)
                blockingmarkers = self.blocking
                markers = {(m.sourceAddress,m.targetAddress): m.cycles + m.latentCycles for m in markers}
        # all edges with markers we could potentially leave out
        testmarkers = list(set(self.edges).difference(set(self.tree)).difference(set(blockingmarkers)))
        # order markers by weight, heaviest first
        testmarkers = [tm[0] for tm in sorted([(m, self.edgeweights[m]) for m in testmarkers], key=operator.itemgetter(1), reverse=True)]
        # for each marker, try to remove
        removemarkers = [] # here we store the markers we successfully removed
        cycleedges = {} # dict: {edge -> number of added cycles due to marker}
        for i in range(len(testmarkers)):
            testset = list(set(testmarkers).difference(set([testmarkers[i]])).difference(set(removemarkers)).union(set(blockingmarkers)))
            print("Try to leave out %s" % hexlist(testmarkers[i]))
            if testmarkers[i] in markers:
                cycleedges[testmarkers[i]] = markers[testmarkers[i]]
            if self.checkFeasibility(list(set(testset).union(set(blockingmarkers))), testmarkers[i], cycleedges):
                print("remove marker %s from marker set" % hexlist(testmarkers[i]))
                removemarkers.append(testmarkers[i])
            else: # if not feasible, do not remove this marker
                try:
                    del(cycleedges[testmarkers[i]])
                except KeyError:
                    pass
        self.tg_break = list(set(testmarkers).difference(set(removemarkers)).difference(set(blockingmarkers)))
        if not isFirst:
            self.tg_break = list(set(self.tg_break).union(set(blockingmarkers).difference(set(self.blocking))))
        self.blockcycles = [] # no blocking markers between cycles
        self.blockstar = [] # no blocking markers between star nodes
        print("remainung non-blocking markers: %s, total weight %f" % (hexlist(sorted(self.tg_break)), sum([self.edgeweights[i] for i in self.tg_break])))
        print("%x:<%s> originally %d markers (weight %f), reduced to %d markers (weight %f), blocking %d" % (self.entry, self.name, len(blockingmarkers) + len(testmarkers), sum([self.edgeweights[i] for i in list(set(blockingmarkers).union(set(testmarkers)))]), len(blockingmarkers) + len(testmarkers)-len(removemarkers), sum([self.edgeweights[i] for i in list(set(blockingmarkers).union(set(testmarkers).difference(set(removemarkers))))]), len(blockingmarkers)))
        
    def checkFeasibility(self, testmarkers, removed_edge, cycleedges):
        #print("%d test markers" % len(testmarkers))
        # for every entry node, check for ambigeous paths:
        # local data structures
        G = nx.DiGraph(list(set(self.edges).difference(set(testmarkers))))
        G.add_nodes_from(list(self.bbs.keys()))
        rG = G.reverse()
        #bG = nx.DiGraph(testmarkers) # graph made from marker edges
        #rbG = bG.reverse()
        #sourcenodes = [v for v in rbG.nodes() if len(rbG.edges(v))>0]
        #sinknodes = [v for v in bG.nodes() if len(bG.edges(v))>0]
        sourcenodes = set([e[1] for e in testmarkers])
        sourcenodes.update([self.entry])
        sinknodes = set([e[0] for e in testmarkers])
        if self.exit:
            sinknodes.update([self.exit])
        #print('source nodes: %s ' % hexlist(sourcenodes))
        #print('sink nodes:   %s' % hexlist(sinknodes))
        #print('Graph to check: %s' % hexlist(G.edges()))
        # keep only sink nodes that have paths from removed edge
        #print("total:     %d source nodes, %d sink nodes" % (len(sourcenodes), len(sinknodes)))
        reachable_successor_nodes = set(nx.dfs_predecessors(G, removed_edge[1]).keys()).union(set((removed_edge[1],)))
        reachable_predecessor_nodes = set(nx.dfs_predecessors(rG, removed_edge[0]).keys()).union(set((removed_edge[0],)))       
        #v = reachable_successor_nodes.union(reachable_predecessor_nodes)
        sourcenodes = list(set(sourcenodes).intersection(reachable_predecessor_nodes))
        sinknodes = list(set(sinknodes).intersection(reachable_successor_nodes))
        G.add_edges_from([(0,s) for s in sourcenodes])
        reachable_nodes =  set(nx.dfs_predecessors(G, 0).keys())
        G.remove_node(0)
        #print("reachable: %d source nodes, %d sink nodes" % (len(sourcenodes), len(sinknodes)))
        for rm in tuple(set(G.nodes()).difference(reachable_nodes)):
            G.remove_node(rm)
        rG = G.reverse()
        #print('Graph to check: %s' % hexlist(G.edges()))

        # 1. Number of cycles (use nx simplecycles)
        cycles = list(nx.simple_cycles(G))
        if self.ALLOW_LOOPS_IN_TIMED == False and len(cycles) > 0:
            return False
        #print('cycles: %s' % str(cycles))
        # if overlapping cycles, return False
        for c in cycles:
            rest = cycles
            rest = [y for x in rest if x != c for y in x]
            if len(set(c).intersection(set(rest))) > 0:
                print("%s not feasible: overlapping cycles: %s %s" % (hexlist(removed_edge),c, rest))
                return False
        # for every source / sink combination
        G.add_edges_from([(k,0) for k in sinknodes])
        
        for s in sourcenodes:
            sreachable = set(nx.dfs_predecessors(G, s).keys()).union(set([s]))
            #spaths = list(nx.all_simple_paths(G, s, 0))
            #print("%d source nodes, %d sink nodes, paths from %x: %s" % (len(sourcenodes), len(sinknodes), s, hexlist(spaths)))
            for k in sinknodes:
                kreachable = set(nx.dfs_predecessors(rG, k).keys()).union(set([k]))
                v = kreachable.intersection(sreachable)
                if len(v) == 0:
                    continue
                #paths = [p[:-1] for p in spaths if p[-2] == k]
                #if len(paths) == 0:
                    #continue
                #v = set([v for p in paths for v in p])
                #v = list((set(nx.descendants(G,s)).union(set([s]))).intersection(set(nx.descendants(rG,k)).union(set([k]))))
                #print("paths from %x to %x: %s" % (s,k,hexlist(paths)))
                sbbs = {addr: self.bbs[addr] for addr in v}
                sG = G.subgraph(v)
                print("subgraph for %x->%x: %s" % (s,k,hexlist(sG.edges())))
                # 2. convert cycles to *nodes
                for c in cycles:
                    if set(c).issubset(set(v)):
                        print ("cycle: %s" % hexlist(c))
                        # find entry and exit to cycle
                        c_entry = [e[0] for e in sG.reverse().edges(c) if e[1] not in c]
                        c_exit = [e[0] for e in sG.edges(c) if e[1] not in c]
                        if s in c and not s in c_entry:
                            c_entry.append(s)
                        if k in c and not k in c_exit:
                            c_exit.append(k)
                        c_entry = list(set(c_entry)) # there might be more than one edge leading to the same entry node
                        c_exit = list(set(c_exit))
                        #print ("exits: %s" % hexlist(c_exit))
                        #print ("entries: %s" % hexlist(c_entry))
                        if len(c_exit) > 1 or len(c_entry) > 1:
                            print("%s not feasible: cycle with more than 1 exit or entry nodes (%x, %x), %s, %s, %s\n%s" %(hexlist(removed_edge),s,k,hexlist(c_entry), hexlist(c_exit), hexlist(c), hexlist(sG.edges())))
                            return False
                        # *-node: entry to exit + exit to exit loops
                        lb = LoopBlock(c_entry[0], self.bbs[c_exit[0]].end, self.bbs[c_exit[0]].endsize)
                        lb.loopexit = c_exit[0]
                        lb.setSuccessors([e[1] for e in sG.edges(c_exit[0]) if e[1] != 0 and e[1] not in c])
                        n = c.index(c_entry[0])
                        lb.cycles = self.bbs[c[n]].cycles # cycles of header
                        while c[n] != c_exit[0]:
                            n_s = n
                            n = (n + 1) % (len(c))
                            if (c[n_s],c[n]) in cycleedges:
                                lb.cycles += cycleedges[(c[n_s],c[n])]
                                print("markercycles in header %x->%x %s" % (c[n_s],c[n],cycleedges[(c[n_s],c[n])]))
                            lb.cycles += self.bbs[c[n]].cycles
                        # loop
                        lb.loopcycles = sum([self.bbs[n].cycles for n in c])
                        for n in range(len(c)):
                            n_t = (n + 1) % (len(c))
                            if (c[n],c[n_t]) in cycleedges:
                                lb.loopcycles += cycleedges[(c[n],c[n_t])]
                                print("markercycles in loop %x->%x %s" % (c[n],c[n_t],cycleedges[(c[n],c[n_t])]))
                        lb.loop = c
                        if k in c:
                            k = c_entry[0]
                        for n in c:
                            if n != c_entry[0]:
                                del(sbbs[n])
                                sG.remove_node(n)
                        for n in lb.successors:
                            sG.add_edge(c_entry[0], n)
                        if len(c) == 1:
                            sG.remove_edge(c[0], c[0])
                        sbbs[c_entry[0]] = lb
                # iterate through paths from s(ource) to (sin)k
                #print("subgraph without cycles: %s" % hexlist(sG.edges()))
                if s == k:
                    paths = [[s]]
                else:
                    paths = list(nx.all_simple_paths(sG, s, k))
                ex_time = [] # list of possible execution times: [(const amount, [(loop_1, upperbound_1), ..., (loop_n, upperbound_n)])]
                assert(len(paths)>0)
                # 3. Annotate nodes with accumulated cycles
                for p in paths:
                    ex_t_p = accumulateCycles([sbbs[v] for v in p])
                    looptuples = []
                    loops = []
                    mloopbounds = {}
                    for lb in [sbbs[v] for v in p if isinstance(sbbs[v], LoopBlock)]:
                        self.loopbounds[tuple(lb.loop)] = None
                        mloopbounds[tuple(lb.loop)] = None
                        loops.append(lb)
                    if self.boundsdb is not None:
                        mloopbounds = self.boundsdb.getBounds(mloopbounds)
                        for lb in loops:
                            looptuples.append((lb.loopcycles, mloopbounds[tuple(lb.loop)]))
                    else:
                        for lb in loops:
                            looptuples.append((lb.loopcycles, None))
                    #print("path %s, times %s" % (hexlist(p), str(ex_t_p)))
                    # if more than 1 cycle on a path (path from one cycle to another / shared vertices in cycles), return False
                    #print("ex_t_p: %s" % str(ex_t_p))
                    if not self.ALLOW_LOOPS_IN_TIMED and (len(set([0]).union(set([x[1] for x in ex_t_p]))) > 2): 
                        print("%s not feasible: more than one simple cycle in path: %s" %(hexlist(removed_edge),hexlist(p)))
                        return False
                    if self.ALLOW_LOOPS_IN_TIMED and any([v==None for v in mloopbounds.values()]):
                        print("%s not feasible: no upper bound found: %s" %(hexlist(removed_edge),hexlist(p)))
                        return False
                    # add cycles from markers
                    addedcycles = 0
                    lastv = -9999999
                    for v in p:
                        if (lastv, v) in cycleedges:
                            addedcycles+=cycleedges[(lastv, v)]
                            print("markercycles in path %x->%x %s" % (lastv,v,cycleedges[(lastv,v)]))
                        if isinstance(sbbs[v], LoopBlock):
                           lastv = sbbs[v].loopexit
                        else:
                           lastv = v
                    ex_time.append((ex_t_p[-1][0]+addedcycles, looptuples))
                # 4  If ranges / cylces intersect, return False
                print('ex_time: %s' % str(ex_time))
                if len(ex_time) > 1:
                    if self.ALLOW_LOOPS_IN_TIMED:
                        if self.hasAmbiguousPathsTolerances(ex_time):
                            print("%s not feasible: ambiguous paths." % hexlist(removed_edge))
                            return False
                    elif self.hasAmbiguousPaths(ex_time):
                        print("%s not feasible: ambiguous paths." % hexlist(removed_edge))
                        return False
        return True
        
    def hasAmbiguousPaths(self, pathcycles):
        """
        this method checks for possible collisions or overlaps in number of cycles
        pathcycles is a list of tuples containing the number of static execution cycles and the number of cycles in a loop
        returns True if there is an overlap, False otherwise.
        """
        # compare all to all
        for i in range(len(pathcycles)):
            for j in range(i+1,len(pathcycles)):
                # c_i - c_j = 0 ?
                # possible combinations loop in i, loop in j, loop in i and j
                # no loops
                if len(pathcycles[i][1]) == 0 and len(pathcycles[j][1]) == 0:
                    # only check CPU_SPEED_ERROR for paths without cycles
                    if pathcycles[i][0] == pathcycles[j][0]:
                        #print('ambiguous cycle count: %d %d = %d %d' % (pathcycles[i][0],pathcycles[i][1],pathcycles[j][0],pathcycles[j][1]))
                        return True
                    if self.CPU_SPEED_ERROR > 0:
                        upper = max(pathcycles[i][0], pathcycles[j][0])
                        lower = min(pathcycles[i][0], pathcycles[j][0])
                        if upper * (1 - self.CPU_SPEED_ERROR) <= lower * (1 + self.CPU_SPEED_ERROR):
                            #print('ambiguous cycle count: %d %d = %d %d, upper %0.2f, lower %0.2f' % (pathcycles[i][0],pathcycles[i][1],pathcycles[j][0],pathcycles[j][1], upper * (1 - self.CPU_SPEED_ERROR), lower * (1 + self.CPU_SPEED_ERROR)))
                            return True
                    continue
                # only one loop
                if len(pathcycles[i][1]) == 0:
                    if pathcycles[i][0] < pathcycles[j][0]: # loop offset is larger, can never be equal
                        continue
                elif len(pathcycles[j][1]) == 0:
                    if pathcycles[j][0] < pathcycles[i][0]: # loop offset is larger, can never be equal
                        continue
                # two loops or one loop with smaller offset
                if (pathcycles[j][0] - pathcycles[i][0]) % fractions.gcd(pathcycles[i][1][0],pathcycles[j][1][0]) == 0: # difference is multiple of gcd                    
                    #print('ambiguous cycle count: %d %d = %d %d' % (pathcycles[i][0],pathcycles[i][1],pathcycles[j][0],pathcycles[j][1]))
                    return True
        return False
        
    def hasAmbiguousPathsTolerances(self, pathcycles):
        """
        this method checks for possible collisions or overlaps in number of cycles
        pathcycles is a list of tuples containing the number of static execution cycles and the number of cycles in a loop
        returns True if there is an overlap, False otherwise.
        """
        # compare all to all
        seqs = {}
        hasloops = False
        for i in range(len(pathcycles)):
            for j in range(i+1,len(pathcycles)):
                
                try:
                    seq_a = copy.copy(seqs[i])
                except KeyError:
                    seqs[i] = self.sequenceGenerator(pathcycles[i][0], pathcycles[i][1])
                    if len(set(seqs[i])) != len(seqs[i]): # duplicates
                        seqs[i] = None
                    elif len(seqs[i])>1:
                        for ii in range(len(seqs[i])-1):
                            if seqs[i][ii+1] * (1 - self.CPU_SPEED_ERROR) <= seqs[i][ii] * (1 + self.CPU_SPEED_ERROR): # overlapping itself
                                seqs[i] = None
                                break
                    seq_a = copy.copy(seqs[i])
                    
                try:
                    seq_b = copy.copy(seqs[j])
                except KeyError:
                    seqs[j] = self.sequenceGenerator(pathcycles[j][0], pathcycles[j][1])
                    if len(set(seqs[j])) != len(seqs[j]): # duplicates
                        seqs[j] = None
                    elif len(seqs[j])>1:
                        for ii in range(len(seqs[j])-1):
                            if seqs[j][ii+1] * (1 - self.CPU_SPEED_ERROR) <= seqs[j][ii] * (1 + self.CPU_SPEED_ERROR): # overlapping itself
                                seqs[j] = None
                                break
                    seq_b = copy.copy(seqs[j])
                    
                if seq_a is None or seq_b is None:
                    #print('one path overlapps with itself.')
                    return True
                    
                path_a = seq_a.pop(0)
                path_b = seq_b.pop(0)
                    
                # increase lower path as long as not above upper part
                if path_a > path_b:
                    while len(seq_b) > 0 and path_a > seq_b[0]:
                        path_b = seq_b.pop(0)
                else:
                    while len(seq_a) > 0 and path_b > seq_a[0]:
                        path_a = seq_a.pop(0)
                    
                while True:
                    # check overlap of path a and path b
                    if path_a > path_b:
                        upper = path_a
                        lower = path_b
                    else:
                        upper = path_b
                        lower = path_a
                        
                    print('check %d %d' %  (path_a, path_b))
                    if upper * (1 - self.CPU_SPEED_ERROR) <= lower * (1 + self.CPU_SPEED_ERROR):
                            #print('ambiguous cycle count: %d = %d, upper %0.2f, lower %0.2f' % (path_a, path_b, upper * (1 - self.CPU_SPEED_ERROR), lower * (1 + self.CPU_SPEED_ERROR)))
                            return True
                    # increase lower one until it is ahead of higher one
                    if path_a > path_b:
                        while path_a > path_b:
                            if len(seq_b)==0:
                                path_b = None
                                break # no more times to compare
                            path_b = seq_b.pop(0)
                    else:
                        while path_a < path_b:
                            if len(seq_a)==0:
                                path_a = None
                                break # no more times to compare
                            path_a = seq_a.pop(0)
                    if path_a is None or path_b is None:
                        break
                    hasloops = True
        if hasloops:
            print('feasible paths with loops.')
            pass
        return False
        
    def sequenceGenerator(self, c, n):
        # n should be a list of tuples (cycle count, upper bound)        
        if len(n)==0:
            return [c]
        k = list([0 for j in n])
        i = 0
        l = [c] # list of generated numbers
        while True:
            if k[i] < n[i][1]:
                k[i] = k[i] + 1
                #print(k)
                l.append(c + sum([a*b for a,b in zip([nn[0] for nn in n],k)]))
            else:
                while k[i] == n[i][1]:
                    k[i] = 0
                    i = i + 1
                    if i == len(n):
                        return sorted(l)
                for j in range(i):
                    k[j] = 0
                k[i] = k[i] + 1
                i = 0
        
    def createLookupTable(self, markers, cycleedges):
        """
        builds a lookup table with the form:
        dict {(start node, marker id) -> [possible paths]}
        """
        print("<create lookup table %x>" % self.entry)
        self.pathLookup = {}
        """
        Lookup is done during replay: From current state (source bbaddr) to marker m, return possible paths and destionation bbaddr.
        pathLookup: { (source bbaddr, marker id) : (destionation bbaddr, [[path 1],[path 2],..,[path n]], Marker object corresponding to id) }
        path n is a list of BasicBlock objects
        """
        # create helper dict edge -> marker
        edgetomarker = {(m.sourceAddress,m.targetAddress): m for m in markers}
        assert(len(markers)==len(edgetomarker.keys()))
        # create graph
        G = nx.DiGraph(list(set(self.edges).difference(set(self.markeredges))))
        G.add_nodes_from(list(self.bbs.keys()))
        sourcenodes = set([e[1] for e in self.markeredges])
        sourcenodes.update([self.entry])
        sinknodes = set([e[0] for e in self.markeredges])
        if self.exit:
            sinknodes.update([self.exit])
        rG= G.reverse()
        
        # global stuff, valid for the entire graph
        cycles = list(nx.simple_cycles(G))
        # for every source / sink combination
        G.add_edges_from([(k,0) for k in sinknodes])
        for s in sourcenodes:
            sreachable = set(nx.dfs_predecessors(G, s).keys()).union(set([s]))
            #spaths = list(nx.all_simple_paths(G, s, 0))
            #print("%d source nodes, %d sink nodes, paths from %x: %s" % (len(sourcenodes), len(sinknodes), s, hexlist(spaths)))
            for k in sinknodes:
                kreachable = set(nx.dfs_predecessors(rG, k).keys()).union(set([k]))
                v = kreachable.intersection(sreachable)
                if len(v) == 0:
                    continue
                #print("remaining paths: %s" % hexlist(paths))
                sbbs = {addr: self.bbs[addr] for addr in v}
                sG = G.subgraph(v)
                endnode = k
                # 2. convert cycles to *nodes
                for c in cycles:
                    if set(c).issubset(set(v)):
                        #print ("cycle: %s" % hexlist(c))
                        # find entry and exit to cycle
                        c_entry = [e[0] for e in sG.reverse().edges(c) if e[1] not in c]
                        c_exit = [e[0] for e in sG.edges(c) if e[1] not in c]
                        if s in c and not s in c_entry:
                            c_entry.append(s)
                        if k in c and not k in c_exit:
                            c_exit.append(k)
                        #print ("exits: %s" % hexlist(c_exit))
                        #print ("entries: %s" % hexlist(c_entry))
                        assert(not len(c_exit) > 1 or len(c_entry) > 1) # should be constructed like this
                        # *-node: entry to exit + exit to exit loops
                        lb = LoopBlock(c_entry[0], self.bbs[c_exit[0]].end, self.bbs[c_exit[0]].endsize)
                        lb.loopexit = c_exit[0]
                        lb.setSuccessors([e[1] for e in G.edges(c_exit[0]) if e[1] != 0 and e[1] not in c])
                        n = c.index(c_entry[0])
                        lb.cycles = self.bbs[c[n]].cycles # cycles of header
                        lb.header_bb = [self.bbs[c[n]]]
                        while c[n] != c_exit[0]:
                            n_s = n
                            n = (n + 1) % (len(c))
                            if (c[n_s],c[n]) in cycleedges:
                                lb.cycles += cycleedges[(c[n_s],c[n])]
                                print("markercycles in header %x->%x %s" % (c[n_s],c[n],cycleedges[(c[n_s],c[n])]))
                                mb = MarkerBlock(cycleedges[(c[n_s],c[n])], c[n])
                                lb.header_bb.append(mb)
                            lb.header_bb.append(self.bbs[c[n]])
                            lb.cycles += self.bbs[c[n]].cycles
                        # loop
                        lb.loopcycles = sum([self.bbs[n].cycles for n in c])
                        exitoffset = c.index(c_exit[0])
                        lb.loop_bb = []
                        for n in range(len(c)):
                            n_s = (exitoffset + n) % (len(c))
                            n_t = (exitoffset + 1 + n) % (len(c))
                            if (c[n_s],c[n_t]) in cycleedges:
                                lb.loopcycles += cycleedges[(c[n_s],c[n_t])]
                                print("markercycles in loop %x->%x %s" % (c[n_s],c[n_t],cycleedges[(c[n_s],c[n_t])]))
                                mb = MarkerBlock(cycleedges[(c[n_s],c[n_t])], c[n_t])
                                lb.loop_bb.append(mb)
                            lb.loop_bb.append(self.bbs[c[n_t]])
                        print('loop: header %s, loop %s' % (str(lb.header_bb), str(lb.loop_bb)))
                        if k in c:
                            endnode = c_entry[0]
                        for n in c:
                            if n != c_entry[0]:
                                del(sbbs[n])
                                sG.remove_node(n)
                        for n in lb.successors:
                            sG.add_edge(c_entry[0], n)
                        if len(c) == 1:
                            sG.remove_edge(c[0], c[0])
                        sbbs[c_entry[0]] = lb
                        #print("loop block %s" % str(lb))
                # iterate through paths from s(ource) to (sin)k
                #print("subgraph without cycles: %s" % hexlist(sG.edges()))
                if s == endnode:
                    paths = [[s]]
                else:
                    paths = list(nx.all_simple_paths(sG, s, endnode))
                #print("paths: %x->%x %s" % (s, k, str([hexlist(p) for p in paths])))
                lut = [] # list of lists of basic blocks
                #print("%x -> %x" % (s,k))
                for p in paths:
                    bblist = []
                    lastv = -9999999
                    for v in p:
                        if (lastv, v) in cycleedges:
                            mb = MarkerBlock(cycleedges[(lastv, v)], v)
                            print("markercycles in path %x->%x %s" % (lastv,v,cycleedges[(lastv,v)]))
                            bblist.append(mb)
                        if isinstance(sbbs[v], LoopBlock):
                           lastv = sbbs[v].loopexit
                        else:
                           lastv = v
                        bblist.append(copy.copy(sbbs[v]))
                    #print("path %s, %s" % (hexlist(p),totalCycles(bblist)))
                    lut.append(bblist)
                # for all destination markers
                assert(len(paths)>0)
                try:
                    for destinationmarkeredge in [e for e in self.markeredges if e[0]==k]:                        
                        self.pathLookup[(s,edgetomarker[destinationmarkeredge].id)] = (destinationmarkeredge[1], lut, edgetomarker[destinationmarkeredge])
                        print("lookup table: %x to marker %d: %s, cycles %s" % (s,edgetomarker[destinationmarkeredge].id,str([[bb.start for bb in bbs] for bbs in lut]), str([[bb.cycles for bb in bbs] for bbs in lut])))
                except:
                    print(edgetomarker)
                    raise
        #print(self.pathLookup)
        return True
        
    def markerColoring(self):
        self.updateMarkerEdges()
        G = nx.DiGraph(list(set(self.edges).difference(set(self.markeredges))))
        G.add_nodes_from(list(self.bbs.keys()))
        sourcenodes = set([e[1] for e in self.markeredges])
        sourcenodes.update([self.entry])
        sinknodes = set([e[0] for e in self.markeredges])
        if self.exit:
            sinknodes.update([self.exit])
        cG = nx.Graph() # coloring graph
        cG.add_nodes_from(self.markeredges) # in this graph, vertices correspond to markers in the CFG
        for s in sourcenodes:
            reachable_sink_nodes = (set(nx.dfs_predecessors(G, s).keys()).union(set([s]))).intersection(sinknodes)
            reachable_markers = [e for e in self.markeredges if e[0] in reachable_sink_nodes]
            print("coloring %x -> %s, %s" % (s, hexlist(reachable_sink_nodes),hexlist(reachable_markers)))
            for a in range(len(reachable_markers)):
                for b in range(a + 1,len(reachable_markers)):
                    cG.add_edge(reachable_markers[a],reachable_markers[b])
        # remove exit nodes, since we assign this node a unique id
        #if self.exit:
            #for ee in [e for e in cG.nodes() if e[1]==self.exit]:
                #cG.remove_node(ee)
                
        print("coloring graph: %s" %hexlist(cG.edges()))
        if len(cG.nodes())>0:
            print("max degree %s" % hexlist(max(cG.degree(cG.nodes()).items(), key=operator.itemgetter(1))))
        self.coloring = nx.coloring.greedy_color(cG, strategy=nx.coloring.strategy_smallest_last)
        #for ee in self.markeredges:
            #if ee[1]==self.exit:
                #self.coloring[ee]=-1
        # further optimizations:
        # - code size: assign often used colors more efficient instrumentation code, i.e. with ids that can be generated using the constant generator       
        # - execution time: assign edges with larger weights more efficient ids
        cost = {}
        for e in self.markeredges:
            #cost[self.coloring[e]] = cost.setdefault(self.coloring[e], 0) + self.edgeweights[e]
            cost[self.coloring[e]] = cost.setdefault(self.coloring[e], 0) + 1
        # cheap ids are [1,2,4]-1, assign ids starting from most costly markers: 0, 1, 3, 2, 4, ... n
        newcoloring = {}
        idorder = (0,1,3,2)
        idx = 0
        for oldid, c in sorted([(k,v) for k,v in cost.items()], key=operator.itemgetter(1), reverse=True):
            if oldid == -1:
                newdid = -1
            else:
                if len(idorder) > idx:
                    newdid = idorder[idx]
                else:
                    newdid = idx
                idx = idx + 1
            for e,id in self.coloring.items():
                if id == oldid:
                    newcoloring[e] = newdid
        #print("old coloring: %s" % str(self.coloring))
        #print("new coloring: %s" % str(newcoloring))
        self.coloring = newcoloring
            
        print("%x %s costs: %s" % (self.entry, self.name, str(cost)))
        print("coloring: %d colors" % len(set([c for c in self.coloring.values()])))
        #print("coloring: %d colors: %s"% (len(set([c for c in self.coloring.values()])),str(self.coloring)))
        
class GPIOEncoding(object):

    """
    Uses numbits bits to encode values from 1 to maxid
    Special ID for IRQ: 2^(numbits)-1    
    """
    def __init__(self, maxid, numbits):
        self.maxid = maxid
        self.numbits = numbits
        # heuristic to calculate the number short ids
        self.numperins = pow(2,numbits) - 2
        self.multrange = 2
        while (self.multrange) * (self.multrange + 1) * (self.numperins - self.multrange) < maxid:
            self.multrange = self.multrange + 1
            if self.multrange > self.numperins / 2:
                break
        print("GPIOEncoding: maxid %d, max calc %d, mulrange %d" % (maxid, (self.multrange) * (self.multrange + 1) * (self.numperins - self.multrange), self.multrange))
        self.longrangestart = self.numperins - self.multrange + 1
        #self.test()
    
    def encode(self, val):
        orig = val
        val = val - 1
        f = self.numperins - self.multrange
        r = [(val) % f]
        base = f
        #print("%d: val %d base %d, r %s" % (orig, val, base, str(r)))
        while val > base - 1:
            val = int((val - r[0]) / base)
            base = self.multrange
            if val < base + 1:
                r.insert(0, val % (base + 1) - 1)
                #print("%d: val %d base %d, r %s" % (orig, val, base, str(r)))
                break
            else:
                val = val - 1 # since this value is already encoded with less symbols
                r.insert(0, val % base)
                #print("%d: val %d base %d, r %s" % (orig, val, base, str(r)))
        
        r[-1] = r[-1]+1
        for i in range(len(r)-1):
            r[i]=r[i]+f+1
        #print(r)
        return r
    
    def decode(self, val):
        f = self.numperins - self.multrange
        val=list(tuple(val))
        val[-1] = val[-1]-1
        for i in range(len(val)-1):
            val[i]=val[i] - f - 1
        #print(val)
        r = val[-1]
        
        base = f
        #print("base %d, r %s" % (base, r))
        for i in range(len(val)-2,-1,-1):
            if i == 0:
                r = r + (val[i]+1) * base
            else:
                r = r + (val[i]+1) * base
            #print("base %d, r %s" % (base, r))
            base = base * self.multrange
        return r + 1
        
    def test(self):
        for z in range(1,40001):
        #for z in (1,25,26,51,52,129,130,155, 234):
            r = self.encode(z)
            d = self.decode(r)
            #print("%d, encoded: %s, decoded: %s" % (z, str(r), d))
            assert(d == z)
            
class TraceBounds(object):

    CHUNKSIZE = 1024
    MARGIN = 0.2

    def __init__(self, binarytracefile):
        self.binarytracefile = binarytracefile
        self.cache = {}
        
    def getBounds(self, loopdict):
        loopbounds = loopdict
        if all([k in self.cache for k in loopdict.keys()]):
            return dict({k: v for k,v in self.cache.items() if k in loopdict.keys()})
        
        totalex = {k:0 for k,v in loopdict.items()}
        patterns = {k:struct.pack('%dH' % len(k), *k) for k,v in loopdict.items()}
        finds = {k:None for k,v in loopdict.items()}

        chunk=[]
        with open(self.binarytracefile, 'rb') as tracefile:
            while True:
                chunk.append(tracefile.read(self.CHUNKSIZE*2))
                if len(chunk[-1])==0:
                    break
                if len(chunk)<=1:
                    continue
                test = b''.join(chunk[-2:-1])
                #print('test patterns')
                for path,p in patterns.items():
                    #print(path)
                    if finds[path] is None:
                        pos = 0
                    else:
                        #print('continuation')
                        pos = finds[path][0] - self.CHUNKSIZE * 2
                    while pos < self.CHUNKSIZE * 2:
                        try:
                            f = test.index(p, pos)
                            
                            #print('%s %d %d %d %d' % (str(path),f,pos,len(path)*2, pos + len(path)*2))
                            if finds[path] is None:
                                finds[path] = [f+len(path)*2,1]
                            elif f >= pos + len(path)*2:
                                #print("found %d occurrences of %s" % (finds[path][1], str(path)))
                                if loopbounds[path] is None or loopbounds[path] < finds[path][1]:
                                    loopbounds[path] = finds[path][1]
                                totalex[path] = totalex[path] + finds[path][1]
                                finds[path] = [f+len(path)*2,1]
                            else:
                                finds[path] = [f+len(path)*2,finds[path][1]+1]
                            pos = f+len(path)*2
                        except ValueError:
                            if not finds[path] is None:
                                #print("found %d occurrences of %s" % (finds[path][1], str(path)))
                                if loopbounds[path] is None or loopbounds[path] < finds[path][1]:
                                    loopbounds[path] = finds[path][1]
                                totalex[path] = totalex[path] + finds[path][1]
                                finds[path] = None
                            pos = self.CHUNKSIZE * 2
                oldjunk = chunk
                #print(a)
        for k in loopbounds.keys():
            if loopbounds[k] is not None:
                loopbounds[k] = ceil(loopbounds[k] * (1+self.MARGIN))
            self.cache[k] = loopbounds[k]
        return loopbounds
    
    