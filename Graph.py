import networkx
from networkx import NetworkXNoPath
import random
from Objects import *
import itertools

import pickle

def GenerateSetting(n, m, e, weight=False, save=False, load=False, filename=None):
    '''
    :param n: the number of vertices
    :param m: the number of messages
    :param e: the number of edges in the graph.
    '''

    if load:
        file = open(filename, 'r')
        (G, M) =  pickle.load(file)

        file.close()
    else:
        G = networkx.dense_gnm_random_graph(n, e)
        M = []

    V = dict([(i,Vertex(i)) for i in range(n)])
    E = []
    for e in G.edges_iter():
        E.append(Edge(V[e[0]], V[e[1]]))
        E.append(Edge(V[e[1]], V[e[0]]))
        if weight:
            G[e[0]][e[1]]['weight'] = 0


    g = Graph(V.values(), E)
    if load:
        M = [Message(V[s], V[t], name) for (s,t,name) in M]



    FCv = {} # m -> the vertices in FC[m]
    FCe = {} # m --> the edges in FV
    SCv = {} # m -> the vertices in SC[m]
    SCe = {} # m --> the edges in SC
    UFSv = {} # the union of vertices in FCv and SCv



    for i in range(m):
        if load:
            s = M[i].s.name
            t = M[i].t.name
            m = M[i]
        else:
            s = random.randint(0, n-1)
            t = s
            while t == s:
                t = random.randint(0,n-1)



            m = Message(V[s], V[t], i)
            M.append(m)

        #first path is the shortest path from s to t
        prev = V[s]
        FCv[m] = [prev]
        FCe[m] = []
        if not weight:
            p = networkx.shortest_path(G, source=s, target=t)
        else:
            p = networkx.shortest_path(G, source=s, target=t, weight='weight')

        for v in p[1:]:
            nextV = V[v]
            FCv[m].append(nextV)
            e = g(prev, nextV)
            assert e != None
            FCe[m].append(e)
            prev.setNextF(m, nextV)
            if weight:
                G[prev.name][nextV.name]['weight'] += 1
            prev = nextV


        #second path:
        #the second path does not use first-path edges

        #remember the edge weights
        if weight:
            weightDict = {}
            for e in FCe[m]:
                weightDict[e] = G[e.s.name][e.t.name]['weight']

        G.remove_edges_from([(e.s.name, e.t.name) for e in FCe[m]])



        #Algorithm for second-path:
        #iterate the first path in reversed order. For each vertex, find the shortest path to t that does not use the first-choice edges.
        #Add these vertices one after the other until you hit a vertex that is already in the second choice path.
        SCv[m] = []
        SCe[m] = []
        for v in reversed(FCv[m][:-1]):
            prev = v

            #if there is no second path, leave this field empty
            try:
                if not weight:
                    p = networkx.shortest_path(G, source=v.name, target=t)
                else:
                    p = networkx.shortest_path(G, source=v.name, target=t, weight='weight')
            except NetworkXNoPath:
                continue

            for u in p[1:]:
                nextV = V[u]
                prev.setNextS(m, nextV)

                if nextV in SCv[m]:
                    break

                SCv[m].append(nextV)
                SCe[m].append(g(prev, nextV))
                prev = nextV

            if weight:
                for i in range(len(p)-1):
                    G[p[i]][p[i+1]]['weight'] += 1

        G.add_edges_from([(e.s.name, e.t.name) for e in FCe[m]])

        if weight:
            for e in FCe[m]:
                G[e.s.name][e.t.name]['weight'] = weightDict[e]


    for m in M:
        UFSv[m] = set([v for v in itertools.chain(FCv[m], SCv[m])])

    if save:
        file = open(filename, 'w')
        pickle.dump((G, [(m.s.name, m.t.name, m.id) for m in M]), file)
        file.close()


    return (g, M, FCv, FCe, SCv, SCe, UFSv)

if __name__=='__main__':
    print GenerateSetting(10, 5, 20)