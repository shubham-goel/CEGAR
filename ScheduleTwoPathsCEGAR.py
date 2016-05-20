import sys
import itertools
import subprocess

sys.path.append("bin")
from z3 import *

from Objects import *


FC = {} #(m,v) --> v
FCv = {} # m -> the vertices in FC[m]
FCe = {} # m --> the edges in FV
SC =  {} #(m,v) --> v
SCv = {} # m -> the vertices in SC[m]
SCe = {} # m --> the edges in SC
UFSv = {} # the union of vertices in FCv and SCv
vars = Vars()
g = None

from Optimization import setLastConfig
from Optimization import addScheduleConstraints
from Optimization import GenerateSchedule
from Optimization import getUniqueConfigConstr
from Optimization import addScheduleSimulationConstraints

def save_to_file(S,filename):
	file = open(filename, 'w')
	pickle.dump(S, file)
	file.close()

def existsSchedule(stng, M, t, s=None):
	if not s:
		s = Solver()

	addScheduleConstraints(stng, M, t, s)

	if s.check() == sat:
		return s.model()


# is there a fault sequence that performs at most k faults and in which less than l messages arrive
def WorstFaultSeq(stng, S, M, t, l, k, immediatefailure=False, returnSolver=False):
	s = Solver()

	# edge e fails at time i
	for e in g.E:
		for i in range(t):
			stng.vars.setCrash(e, i)

			# once an edge crashes, it stays down
			if i > 0:
				s.add(Implies(stng.vars.crash(e, i-1), stng.vars.crash(e, i)))

		#require that if an edge fails, it fails at time 0
		if immediatefailure:
			s.add(Implies(stng.vars.crash(e, t-1), stng.vars.crash(e, 0)))



	# the total number of crashes is at most k
	s.add(Sum([If(stng.vars.crash(e,t-1), 1, 0) for e in g.E]) <= k)



	# configuration variables -- m is on v at time i.
	for m in M:
		for v in stng.UFSv[m]:
			for i in range(t+1):
				stng.vars.setConfig(v,m,i)



	# messages start at their origin
	for m in M:
		s.add(getUniqueConfigConstr(stng, m.s, m, 0))


	for m in M:
		for v in stng.FCv[m]:
			for i in range(t):
				#if a message reaches its destination, it stays there.
				s.add(Implies(stng.vars.config(m.t, m, i), getUniqueConfigConstr(stng, m.t, m, i+1)))

				e = g(v, v.nextF(m))
				if not e:
					assert(v == m.t)
					continue

				if S(e, i) == m:
					# m is on v and edge e has not crashed. Move according to the schedule
					a = And(stng.vars.config(v, m, i), Not(stng.vars.crash(e,i)))
					s.add(Implies(a, getUniqueConfigConstr(stng, e.t, m, i+1)))
				else:
					# m is on v and edge e has not crashed but it is not time to move. Wait.
					a = And(stng.vars.config(v, m, i), Not(stng.vars.crash(e,i)))
					s.add(Implies(a, getUniqueConfigConstr(stng, v, m, i+1)))

				if not v.nextS(m):
					#no fall back edge, do nothing.
					s.add(Implies(And(stng.vars.config(v, m, i), stng.vars.crash(e,i)), getUniqueConfigConstr(stng, v, m, i+1)))
					continue

				#m is on v and e has crashed.
				x = And(stng.vars.config(v,m,i), stng.vars.crash(e, i))

				# the fallback edge is free
				fr = free(stng, g(v, v.nextS(m)), m, M, S, i)
				# if it is not free, stay
				stay = Implies(Not(fr), getUniqueConfigConstr(stng, v, m, i+1))
				#if it is free, use it
				move = Implies(fr, getUniqueConfigConstr(stng, v.nextS(m), m, i+1))
				s.add(Implies(x, stay))
				s.add(Implies(x, move))

	for m in M:
		for v in stng.SCv[m]:
			#handled in the above
			if v in stng.FCv[m]: continue

			if not g(v, v.nextS(m)): continue

			for i in range(t):
				#m is on v
				x = stng.vars.config(v,m,i)

				# the fallback edge is free
				fr = free(stng, g(v, v.nextS(m)), m, M, S, i)

				# if it is not free, stay
				stay = Implies(Not(fr), getUniqueConfigConstr(stng, v, m, i+1))
				#if it is free, use it
				move = Implies(fr, getUniqueConfigConstr(stng, v.nextS(m), m, i+1))
				s.add(Implies(x, stay))
				s.add(Implies(x, move))


	if returnSolver:
		s.push()

	#less than l messages arrive
	s.add(Sum([If(stng.vars.config(m.t, m, t), 1, 0) for m in M]) < l)

	print 'worst faults start check', time.time()
	if s.check() == sat:
		print 'end', time.time()
		mdl = s.model()
	else:
		print 'end', time.time()
		mdl =  False

	if not returnSolver:
		return mdl
	else:
		return mdl, s



def free(stng, e, m, M, S, i):
	'''
	returns False if the edge is not free according to the schedule
	return a constraint if it is
	'''
	for m2 in M:
		if m2 == m:
			continue

		# if there is a message scheduled on e, it is not free
		if S(e, i):
			return False

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
		if e2:
			#if m2 is on e.s and e2 has crashed, m2 will attempt to use e, so it is not free.
			n1 = Not(stng.vars.config(e.s, m2, i))
			n2 = Not(stng.vars.crash(e2, i))
			l.append(Or(n1, n2))
		else:
			assert(e.s == m2.t or e.s not in stng.FCv[m2])
			#Since e.s is a second choice vertex, if m2 is on e.s, m2 will attempt to use e.
			n1 = Not(stng.vars.config(e.s, m2, i))
			l.append(n1)

	#edge e has not crashed
	l.append(Not(stng.vars.crash(e, i)))
	return And(l)



def getPsiv(stng, T, m, v, u, i, M):
	'''
	Assuming m is on v at time i, and the set of edges that fail are T, returns a predicate that ensures that m moves to u.
	'''
	if v == m.t:
		return None

	e = g(v, v.nextF(m))
	# If the edge (v,u) is on the first path, m should be scheduled on it
	if u == v.nextF(m):
		return stng.vars.sched(e, m, i-1)

	# if m is on the first path and the next edge has not crashed, but m does not move, then it should not be scheduled
	elif v in stng.FCv[m] and u == v and e not in T:
		return Not(stng.vars.sched(e, m, i-1))

	elif v in stng.FCv[m] and u == v and e in T:
		return None

	# if m moves to the second choice, that edge should be free
	elif u == v.nextS(m):
		l = []
		for m2 in M:
			if v.nextF(m2) == u:
				l.append(Not(stng.vars.sched(g(v, u), m2, i-1)))

		return And(l) if l else None

	elif u in stng.SCv[m] and u == v:
		return None

	else:
		raise Exception('T: %s,\nmsg: %s, v: %s, u: %s, i: %d'%(' '.join([str(e) for e in T]), m, v, u, i))




def optimizeSched(stng, s, crash_mdl, M, t, optimize=False, lval=None, S=None):
	Psis = []
	prevC = [(m, m.s) for m in M]
	prevT = []
	sOpt = s #a solver that is used in optimize
	mdl = None
	previous_model = mdl # For returning schedule model obtained from penultimate configuration

	if optimize:
		addScheduleSimulationConstraints(stng, sOpt, g, M, t, lval, crash_mdl)

	for i in range(1, t):
		psi = []
		curC = []
		curT = []

		for e in g.E:
			if is_true(crash_mdl[stng.vars.crash(e, i)]):
				curT.append(e)

		for (m,v) in prevC:
			# the message either doesn't move
			if is_true(crash_mdl[stng.vars.config(v, m, i)]):
				curC.append((m, v))
				p = getPsiv(stng, prevT, m, v, v, i, M)

			#or moves to the first choice
			elif v.nextF(m) and is_true(crash_mdl[stng.vars.config(v.nextF(m), m, i)]):
				curC.append((m, v.nextF(m)))
				p = getPsiv(stng, prevT, m, v, v.nextF(m), i, M)


			#or moves to the second choice
			elif v.nextS(m) and is_true(crash_mdl[stng.vars.config(v.nextS(m), m, i)]):
				curC.append((m, v.nextS(m)))
				p = getPsiv(stng, prevT, m, v, v.nextS(m), i, M)

			else:
				raise Exception('time: %d, msg: %s, v: %s'%(i, m, v))


			if p:
				psi.append(p)
		if psi:
			if optimize:
				print 'starting optimization', time.time()
				previous_model = mdl #storing schedule for configuration just before doomed state	
				sOpt.push()
				mdl = setLastConfig(stng, sOpt, crash_mdl, M, i)
				print 'end optimization', time.time()
				if not mdl:
					print 'breaking at', i
					break
				else:
					sOpt.pop() # this will pop the configuration constrains added in setLastConfig. The other constraints don't change.
			Psis.append(And(psi))
		prevC = curC
		prevT = curT

	if Psis:
	#    print '\n\n'.join([str(x) for x in Psis])
		print 'len(Psis) = ', len(Psis)
		s.add(Not(And(Psis)))
		if optimize and (previous_model is not None):
			return previous_model
		else:
			return checkReturnModel(s)

	else:
		# No schedule exists
		return False


def checkReturnModel(s):
	print 'start check()', time.time()
	b = s.check()
	print 'end check()', time.time()

	if b == sat:
		mdl = s.model()
		return mdl
	else:
		return False

def printCounterexample(stng, mdl, t, M):
	for e in g.E:
		for i in range(t):
			if is_true(mdl[stng.vars.crash(e,i)]):
				print 'edge: %s crashed at time %d'%(str(e), i)
				break
	return
	for m in M:
		print 'message:',str(m)
		for i in range(t+1):
			for v in stng.UFSv[m]:
				if is_true(mdl[stng.vars.config(v,m,i)]):
					print v,i


def CEGAR(stng, M, t, k, l, optimize=False, showProgress=False):
	'''
	:param M: The messages to be sent
	:param t: The timeout.
	:param k: At most k faults are allowed.
	:param l: At least l messages should arrive.
	:return: A (k,l)-resistant schedule, if it exists, and otherwise False.
	'''
	j = 1
	counter=1
	s = Solver()
	print 'start existsSchedule', time.time()
	mdl = existsSchedule(stng, M, t, s=s)
	print 'end existsSchedule', time.time()
	if not mdl:
		print 'NO valid resistant schedule EXISTS'
		return False

	I = tuple([(m, m.s) for m in M])
	emptyT = tuple([])

	while True:
		print j,counter
		j += 1
		counter += 1

		if counter > 20:
			return "Timeout"

		#mdl is has the information about the schedule
		S = GenerateSchedule(stng, mdl, M, t)

		#optimization: first try to find a fault seq in which the crashes are at time 0.
		# print 'start WorstFaultSeq with immediate faults', time.time()
		print 'start WorstFaultSeq', time.time()
		crash_mdl = WorstFaultSeq(stng, S, M, t, l, k, immediatefailure=True)
		# print 'end WorstFaultSeq with immediate faults', time.time()
		if not crash_mdl:
			print 'no fault seq with immediate failures!', time.time()
			crash_mdl = WorstFaultSeq(stng, S, M, t, l, k)
			print 'end second WorstFaultSeq', time.time()

		if not crash_mdl:
			print 'FOUND (k-l) resistant schedule', "k=",k,"l=",l
			print S
			save_to_file(S,'schedules/Schedule_k'+str(k)+'_l'+str(l))
			l+=1
			counter=1
			# mdl = s.model()
			continue

		if showProgress:
			printProgress(stng, S, M, t, l, k)


		#print '############'
		#printCounterexample(stng, mdl, t, M)
		#print '$$$$$$$$$$$\n\n'
		new_mdl = optimizeSched(stng, s, crash_mdl, M, t, optimize, l, S=S)
		if  new_mdl is False:
			print 'NO (k-l) resistant schedule EXISTS', "k=",k,"l=",l
			return False
		else:
			mdl = new_mdl
		# else:
		# 	print 'start check()', time.time()
		# 	b = s.check()
		# 	print 'end check()', time.time()

		# 	if b == sat:
		# 		mdl = s.model()
		# 	else:
		# 		print 'NO (k-l) resistant schedule EXISTS', "k=",k,"l=",l
		# 		return False



def printProgress(stng, S, M, t, l, k):
	low = 0
	high = l
	rest = 0

	mid = (high + low)/2
	mdl,s = WorstFaultSeq(stng, S, M, t, mid, k, returnSolver=True)
	while low < high:
		print 'print progress start iteration', time.time()
		if mdl is False:
			low = mid+1
			rest = mid
		else:
			high = mid-1

		mid = (high + low)/2

		s.pop()
		s.push()
		s.add(Sum([If(stng.vars.config(m.t, m, t), 1, 0) for m in M]) < mid)

		if s.check() == sat:
			print mid
			printCounterexample(stng, s.model(), t, M)
			mdl = True
		else:
			rest = mid
			mdl = False
	print 'The schedule is (%d, %d)-resistant'%(rest, k)


def test(stng):
	V = ['s', 'u1', 'u3', 'u4', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h','i']
	V = dict([(n, Vertex(n)) for n in V])
	E = [('s', 'a'), ('s', 'u1'), ('s', 'b'), ('s', 'h'), ('s','f'), ('a', 'u1'), ('a', 'u3'), ('a', 'u4'), ('a', 'i'), ('i', 'u1'), ('a', 'b'), ('b', 'c'), ('c','g'), ('g', 'u4'), ('h', 'c'), ('c', 'd'), ('d', 'u3'), ('d', 'u1'), ('f', 'e'), ('e', 'd')]
	E = [Edge(V[s], V[t]) for (s,t) in E]
	global g
	g = Graph(V.values(), E)

	m1 = Message(V['s'], V['u1'], 1)
	m2 = Message(V['s'], V['u1'], 2)
	m3 = Message(V['s'], V['u3'], 3)
	m4 = Message(V['s'], V['u4'], 4)
	M = [m1, m2, m3, m4]
	dM = dict([(i+1, m) for i,m in enumerate(M)])

	for i,m in enumerate(M):
		V['s'].setNextF(m, V['a'])
		j = i+1 if i != 1 else i
		V['a'].setNextF(m, V['u%d'%j])

	for m in M:
		stng.FCv[m] = [m.s]
		stng.FCe[m] = []
		for v in g.V:
			if v.nextF(m):
				stng.FCv[m].append(v.nextF(m))
				stng.FCe[m].append(g(v, v.nextF(m)))

	d= {}
	d[1] = [('s', 'u1'), ('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'u1')]
	d[2] = [('s', 'f'), ('f', 'e'), ('e', 'd'), ('d', 'u1'),('a', 'i'), ('i', 'u1')]
	d[3] = [('s', 'h'), ('h', 'c'), ('c', 'd'), ('d', 'u3')]
	d[4] = [('s', 'b'), ('b', 'c'), ('c', 'g'), ('g', 'u4')]
	for i in range(1, 5):
		for s,t in d[i]:
			V[s].setNextS(dM[i], V[t])



	for m in M:
		stng.SCv[m] = [m.s]
		stng.SCe[m] = []
		for v in g.V:
			if v.nextS(m):
				stng.SCv[m].append(v.nextS(m))
				stng.SCe[m].append(g(v, v.nextS(m)))



	for m in M:
		stng.UFSv[m] = set([v for v in itertools.chain(stng.FCv[m], stng.SCv[m])])

	#S = CEGAR(stng, M, 5, 2, 3)
	#if S:
	#    print 'done!'
	#    print S
	#else:
	#    print 'no schedule!'
	#return

	S = Schedule()
	S.add(g(V['s'],V['a']), 0, m1)
	S.add(g(V['a'], V['u1']), 1, m1)
	S.add(g(V['s'],V['a']), 1, m2)
	S.add(g(V['a'], V['u1']), 2, m2)
	S.add(g(V['s'],V['a']), 2, m3)
	S.add(g(V['a'], V['u3']), 3, m3)
	S.add(g(V['s'],V['a']), 3, m4)
	S.add(g(V['a'], V['u4']), 4, m4)
	mdl = WorstFaultSeq(stng, S, M, 5, 2, 2)
	if mdl:
		printCounterexample(stng, mdl, 5, M)
		s = Solver()
		existsSchedule(stng, M, 5, s=s)
		s.reset()
		addCounterexample(s, mdl, M, 5)
		print s.assertions()
	else:
		print 'no sequence'
	return


def testOpt(stng):
	V = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']
	V = dict([(n, Vertex(n)) for n in V])
	E = [('a', 'b'), ('a', 'g'), ('g', 'c'), ('h', 'c'), ('a', 'h'), ('b', 'c'), ('b', 'e'), ('b', 'd'), ('e', 'f'), ('f', 'c'), ('d', 'c')]
	E = [Edge(V[s], V[t]) for (s,t) in E]
	global g
	g = Graph(V.values(), E)

	m1 = Message(V['a'], V['c'], 1)
	m2 = Message(V['a'], V['c'], 2)
	M = [m1, m2]
	dM = dict([(i+1, m) for i,m in enumerate(M)])


	V['a'].setNextF(m1, V['b'])
	V['b'].setNextF(m1, V['c'])
	V['a'].setNextF(m2, V['b'])
	V['b'].setNextF(m2, V['c'])

	for m in M:
		stng.FCv[m] = [m.s]
		stng.FCe[m] = []
		for v in g.V:
			if v.nextF(m):
				stng.FCv[m].append(v.nextF(m))
				stng.FCe[m].append(g(v, v.nextF(m)))

	d= {}
	d[1] = [('a', 'g'), ('g', 'c'), ('b', 'd'), ('d', 'c')]
	d[2] = [('a', 'h'), ('h', 'c'), ('b', 'e'), ('e', 'f'), ('f', 'c')]

	for i in range(1, 3):
		for s,t in d[i]:
			V[s].setNextS(dM[i], V[t])



	for m in M:
		stng.SCv[m] = [m.s]
		stng.SCe[m] = []
		for v in g.V:
			if v.nextS(m):
				stng.SCv[m].append(v.nextS(m))
				stng.SCe[m].append(g(v, v.nextS(m)))



	for m in M:
		stng.UFSv[m] = set([v for v in itertools.chain(stng.FCv[m], stng.SCv[m])])

	S = Schedule()
	S.add(g(V['a'],V['b']), 0, m1)
	S.add(g(V['b'], V['c']), 1, m1)
	S.add(g(V['a'],V['b']), 1, m2)
	S.add(g(V['b'], V['c']), 2, m2)
	mdl = WorstFaultSeq(stng, S, M, 4, 2, 1, immediatefailure=True)
	printCounterexample(stng, mdl, 4, M)
	b, sOpt = ExistsSchedGivenConfig(g, M, 4, 2, mdl, 0)
	print 'true' if b else 'false'
	sOpt.pop()
	b, sOpt = ExistsSchedGivenConfig(g, M, 4, 2, mdl, 1, sOpt)
	print b
	print 'done'


import time
from Graph import GenerateSetting
import pickle
def main(n, m, e, t, k, l, filename=None, save=False, load=False, optimize=False, showProgress=False, weight=False):
	print 'start setup', time.time()
	global g #, FCv, FCe, SCv, SCe, UFSv
	#(g, M, FCv, FCe, SCv, SCe, UFSv) = GenerateSetting(20, 20, 40)
	(g, M, FCv, FCe, SCv, SCe, UFSv) = GenerateSetting(n, m, e, save=save, load=load, filename=filename, weight=weight)
	# global stng
	stng = Glbl(vars, FCe, FCv, SCv, SCe, UFSv)



	for m in M:
		print m.id, '%s --> %s'%(m.s, m.t)
		print ', '.join([str(v) for v in stng.FCv[m]])
		print ', '.join(['%s --> %s'%(str(v), str(v.nextS(m))) for v in stng.UFSv[m]])
		print '################'

	lengths = [len(stng.FCe[m]) for m in M]
	print 'max length = ', max(lengths), "min length = ", min(lengths)
	print 'end setup', time.time()


	S = CEGAR(stng, M, t, k, l, optimize=optimize, showProgress=showProgress)
	if S == "Timeout":
		print 'Script Timed out'
		return 1
	else:
		print 'Finished CEGAR!'
		return 0


from optparse import OptionParser

def parse_arguments():
	parser = OptionParser()
	parser.add_option('-t','--timeout', dest="t",
				  help="The timeout, should be an integer")
	# parser.add_option("-l", dest="l",
	# 			  help="The guarantee on the number of messages that should arrive.")
	parser.add_option("-k", dest="k",
				  help="#edges that are allowed to crash.")
	parser.add_option("-n", dest="n",
				  help="#vertices in the network.")
	parser.add_option("-m", dest="m",
				  help="#messages in the network.")
	parser.add_option("-e", dest="e",
				  help="#edges in the network.")

	parser.add_option("-l","--load",
				  action="store_true", dest="load", default=False,
				  help="Load setting from file")
	parser.add_option("-b","--brute",
				  action="store_false", dest="optimize", default=True,
				  help="Dont Optimize")
	parser.add_option("-v","--verbose",
				  action="store_true", dest="showProgress", default=False,
				  help="Dont show progress")
	parser.add_option("--nw","--no-weight",
				  action="store_false", dest="weight", default=True,
				  help="Choose paths without weights")
	parser.add_option("-d","--no-diff",
				  action="store_false", dest="diff", default=True,
				  help="Check if schedules generated are different")
	return parser.parse_args()

def save_parameters(n,m,e,t,k,l,result):
	parameter_file = "parameters.output"
	line = "{}\t{}\t{}\t{}\t{}\t{}\t{}\n".format(n,m,e,t,k,l,result)
	with open(parameter_file, "a") as myfile:
		myfile.write(line)


if __name__ == '__main__':
	(options, args) = parse_arguments()

	save = not options.load
	load = options.load
	optimize = options.optimize
	showProgress = options.showProgress
	weight = options.weight
	diff = options.diff
	n = int(sys.argv[1])
	m = int(sys.argv[2])
	e = int(sys.argv[3])
	t = int(sys.argv[4])
	k = int(sys.argv[5])
	l = int(sys.argv[6])

	# filename='{}-{}-{}-{}-{}-{}.setting'.format(n,m,e,t,k,l)
	filename="settings.curr"

	# Remove old Schedules
	cmd = "rm -r schedules/"
	subprocess.call([cmd],shell=True)
	cmd = "mkdir schedules/"
	subprocess.call([cmd],shell=True)

	# main(n, m, e, t, k, l, filename=None, save=False, load=False, optimize=False, showProgress=False, weight=False):
	# main(int(options.n), int(options.m), int(options.e), int(options.t), int(options.l), int(options.k))
	# main(10, 30, 15, 7, 26, 1, filename, save=True, load=False, optimize=True, showProgress=True, weight=True)
	exit_status = main(n,m,e,t,k,l,filename, save=save, load=load, optimize=optimize, showProgress=showProgress, weight=weight)

	if diff:
		from diff_script import *

		print "##################################"
		print "Checking if Schedules found differ"
		print "##################################"
		k = int(sys.argv[5])
		l = int(sys.argv[6])
		differed_l = diff_script(k,l)
		print "\n\nEnded script!"

		if exit_status>0:
			msg = "Timeout; "
		else:
			msg = ""

		if differed_l == None:
			save_parameters(n,m,e,t,k,l,msg + "No Schedule")
			sys.exit(0)
		elif differed_l == []:
			save_parameters(n,m,e,t,k,l,msg + "Same Schedule")
			sys.exit(0)
		else:
			for i in differed_l:
				save_parameters(n,m,e,t,k,i,msg + "l and (l+1) DIFFER")
			sys.exit(1)
