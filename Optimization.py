
from z3 import *



stng = None


def AddScheduleConstraints(M, t, s):
    for m in M:
        for e in stng.FCe[m]:
            for i in range(t):
                stng.vars.setSched(e, m, i)

    for m in M:
        stng.vars.setMsgArrive(m)

    # a message is sent on e only if it arrived at e.s at a previous time
    for m in M:
        for e in stng.FCe[m]:
            #find the previous edge on the first path
            for p in stng.FCe[m]:
                if p.t == e.s:
                    break
            else:
                #if no such edge exists, this is the first edge in the path, and it should not have this contraint.
                continue

            for i in range(1,t):
                o = Or([stng.vars.sched(p, m, j) for j in range(i)])
                s.add(Implies(stng.vars.sched(e,m,i), o))

    # a message only exits through its origin
    for m in M:
        s.add(And([Not(stng.vars.sched(e, m, 0)) for e in stng.FCe[m] if e.s != m.s]))


    # two messages can't be sent on the same link at the same time
    for m in M:
        for e in stng.FCe[m]:
            for i in range(t):
                s.add(Implies(stng.vars.sched(e, m, i), Not(Or([stng.vars.sched(e, m2,i) for m2 in M if m2 != m and e in stng.FCe[m2]]))))

    # A message can only exit a vertex once
    for m in M:
        for e in stng.FCe[m]:
            for i in range(t-1):
                o = Or([stng.vars.sched(e, m, j) for j in range(i+1, t)])
                s.add(Implies(stng.vars.sched(e, m, i), Not(o)))



def ExistsSchedGivenConfig(g, st, M, t, l, mdl, i, s=None):
    global stng
    stng = st
    if s:
        return lastPart(s, stng, mdl, M, i)

    s = Solver()
    AddScheduleConstraints(M, t, s)

    for m in M:
        for v in stng.UFSv[m]:
            for j in range(i, t+1):
                stng.vars.setConfig(v,m,j)


    for m in M:
        for v in stng.FCv[m]:
            for j in range(i,t):
                #if a message reaches its destination, it stays there.
                if v == m.t:
                    s.add(Implies(stng.vars.config(m.t, m, j), getUniqueConfigConstr(m.t, m, j+1)))
                    continue

                e = g(v, v.nextF(m))
                if not e:
                    assert(v == m.t)
                    continue

                #if the first-choice edge does not crash use it according to the schedule
                if not is_true(mdl[stng.vars.crash(e, j)]):
                    s.add(Implies(And(stng.vars.config(v,m,j), stng.vars.sched(e,m,j)), getUniqueConfigConstr(v.nextF(m), m, j+1)))
                    s.add(Implies(And(stng.vars.config(v,m,j), Not(stng.vars.sched(e,m,j))), getUniqueConfigConstr(v, m, j+1)))

                else:
                    e = g(v, v.nextS(m))
                    if not e:
                        s.add(Implies(stng.vars.config(v, m, j), getUniqueConfigConstr(v, m, j+1)))
                        continue

                    fr = free(g, mdl, e, m, M, j)
                    if fr is True:
                        s.add(Implies(stng.vars.config(v,m,j), getUniqueConfigConstr(v.nextS(m), m, j+1)))

                    elif fr is False:
                        s.add(Implies(stng.vars.config(v,m,j), getUniqueConfigConstr(v, m, j+1)))

                    else:
                        s.add(Implies(And(Not(fr), stng.vars.config(v,m,j)), getUniqueConfigConstr(v, m, j+1)))
                        s.add(Implies(And(fr, stng.vars.config(v,m,j)), getUniqueConfigConstr(v.nextS(m), m, j+1)))

    for m in M:
        for v in stng.SCv[m]:
            #handled in the above
            if v in stng.FCv[m]: continue

            e = g(v, v.nextS(m))
            if not e: continue

            for j in range(i,t):
                fr = free(g, mdl, e, m, M, j)
                if fr is True:
                    s.add(Implies(stng.vars.config(v,m,j), getUniqueConfigConstr(v.nextS(m), m, j+1)))

                elif fr is False:
                    s.add(Implies(stng.vars.config(v,m,j), getUniqueConfigConstr(v, m, j+1)))

                else:
                    s.add(Implies(And(Not(fr), stng.vars.config(v,m,j)), getUniqueConfigConstr(v, m, j+1)))
                    s.add(Implies(And(fr, stng.vars.config(v,m,j)), getUniqueConfigConstr(v.nextS(m), m, j+1)))

    #at least l messages arrive
    s.add(Sum([If(stng.vars.config(m.t, m, t), 1, 0) for m in M]) >= l)

    return lastPart(s, stng, mdl, M, i)




def lastPart(s, stng, mdl, M, i):
    s.push()

    # messages start at their position in C_i
    for m in M:
        for v in stng.UFSv[m]:
            if is_true(mdl[stng.vars.config(v,m,i)]):
                s.add(getUniqueConfigConstr(v, m, i))


    if s.check() == sat:
        mdl = s.model()
        return mdl,s
    else:
        return False,s



def getUniqueConfigConstr(v,m,i):
    '''
    Returns a constraint that guarantees that m is on v at time i, and not on any other vertex.
    '''
    notThere = And([Not(stng.vars.config(u, m, i)) for u in stng.UFSv[m] if u != v])
    here = stng.vars.config(v, m, i)
    return And(here, notThere)







def free(g, mdl, e, m, M, i):
    #first things first, if e has crashed, it is not free.
    if is_true(mdl[stng.vars.crash(e,i)]):
        return False

    #we are going to return And(l), so all the constraints should be true iff e is free.
    l = []
    for m2 in M:
        if m2 == m:
            continue

        #if e is a first-choice of m2, it is not free if m is scheduled on e
        if e in stng.FCe[m2]:
            l.append(Not(stng.vars.sched(e, m2, i)))


    # if a lower message tries to use e, then it is not free
    l = []
    for m2 in M:
        #we consider only lower messages
        if m < m2 or m2 == m:
            continue

        # we consider only messages that attempt to use e as a second choice
        if (e.s).nextS(m2) != e.t:
            continue

        # the first choice option of m2 at e.s
        e2 = g(e.s, (e.s).nextF(m2))

        #if there is no first choice, or if the first choice crashed, m2 will try to use e if its there.
        if not e2 or is_true(mdl[stng.vars.crash(e2, i)]):
            l.append(Not(stng.vars.config(e.s, m2, i)))

    if not l:
        return True

    return And(l)


def printModel(g, mdl, M, t, i):
    S = GenerateSchedule(mdl, M, t)
    print S
    printCounterexample(g, mdl, t, M, i)




def GenerateSchedule(mdl, M, t):
    from Objects import  Schedule
    S = Schedule()
    for m in M:
        for e in stng.FCe[m]:
            for i in range(t):
                if is_true(mdl[stng.vars.sched(e,m,i)]):
                    S.add(e, i, m)

    return S

def printCounterexample(g, mdl, t, M, j=0):
    for e in g.E:
        for i in range(t):
            if is_true(mdl[stng.vars.crash(e,i)]):
                print 'edge: %s crashed at time %d'%(str(e), i)
                break
    for m in M:
        print 'message:',str(m)
        for i in range(j, t+1):
            for v in stng.UFSv[m]:
                if is_true(mdl[stng.vars.config(v,m,i)]):
                    print v,i
