
from z3 import *

class Vars:
	def __init__(self):
		self.vars = {}

	def setSched(self, e, m, i):
#        assert((e,m,i) not in self.vars)
		self.vars[(e,m,i)] = Bool('%s is scheduled on %s at time %d'%(str(m), str(e), i))

	def sched(self, e, m, i):
		return self.vars[(e,m,i)]

	def setConfig(self, v, m, i):
		self.vars[(v,m,i)] = Bool('%s is on %s at time %d'%(str(m), str(v), i))

	def config(self, v, m, i):
		return self.vars[(v,m,i)]

	def setCrash(self, e, i):
		'''
		e crashes at time i.
		'''
		self.vars[(e, i)] = Bool('%s crashes at time %d'%(str(e), i))

	def crash(self, e, i):
		return self.vars[(e,i)]

	def setMsgArrive(self, m):
		'''
		message m has arrived at its destination.
		'''
#        assert(m not in self.vars)
		self.vars[m] = Bool('%s has arrived'%str(m))

	def msg(self, m):
		return self.vars[m]


class Vertex:
	def __init__(self, name):
		self.name = name
		self.__nextS = {}
		self.__nextF = {}

	def __str__(self):
		return str(self.name)

	def nextS(self,m):
		if m in self.__nextS:
			return self.__nextS[m]
		#if (m,self) in SC:
		#    return SC[(m,self)]

	def setNextS(self, m, u):
		self.__nextS[m] = u

	def nextF(self,m):
		if m in self.__nextF:
		   return self.__nextF[m]
#        if (m,self) in FC:
#            return FC[(m,self)]

	def setNextF(self, m, u):
		self.__nextF[m] = u

	def __hash__(self):
		return hash(self.name)

	def __eq__(self, other):
		if not other:
			return False
		return self.name == other.name


class Edge:
	def __init__(self, s, t):
		self.s = s
		self.t = t

	def __str__(self):
		return '(%s, %s)'%(self.s, self.t)

	def __hash__(self):
		return hash((hash(self.s), hash(self.t)))

	def __eq__(self, other):
		return self.s == other.s and self.t == other.t

class Graph:
	def __init__(self, V, E):
		self.V = V
		self.E = E

	def __call__(self, v, u):
		for e in self.E:
			if e.s == v and e.t == u:
				return e


class Message:
	def __init__(self, s, t, name):
		self.s = s
		self.t = t
		self.name = str(name)
		self.id = name

	def __str__(self):
		return self.name

	def __lt__(self, m):
		return self.id < m.id

	def __le__(self, m):
		return self.id <= m.id

	def __hash__(self):
		return hash(self.id)

	def __eq__(self, other):
		if not other:
			return False
		return self.id == other.id


class Schedule:
	def __init__(self):
		self.d = {}

	def __call__(self, e, i):
		if (e,i) in self.d:
			return self.d[(e,i)]
		else:
			return None
	def add(self, e, i, m):
		self.d[(e,i)] = m

	def __str__(self):
		sorted = list(set([i for (e,i) in self.d.keys()]))
		sorted.sort()
		l = []
		for i in sorted:
			for (e,j) in self.d.keys():
				if j != i:
					continue
				s = 'i: %d, e: %s, m: %s'%(i, str(e),  str(self.d[(e,i)]))
				l.append(s)

		return '\n'.join([str(x) for x in l])


class Glbl:
	def __init__(self, vars, FCe, FCv, SCv, SCe, UFSv):
		self.vars = vars
		self.FCe = FCe
		self.SCe = SCe
		self.SCv = SCv
		self.FCv = FCv
		self.UFSv = UFSv