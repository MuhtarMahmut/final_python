import sys
import traceback

from prolog_structures import Rule, RuleBody, Term, Function, Variable, Atom, Number
from final import Interpreter, Not_unifiable

if __name__ == '__main__':

	interpreter = Interpreter()

	def test_final_1_1 ():
		assert ((interpreter.variables_of_term (Function ("f", [Variable ("X"), Variable ("Y"), Atom ("a")]))) ==
			set([Variable ("X"), Variable ("Y")]))

	def test_final_1_2 ():
		assert ((interpreter.variables_of_term (Function ("p", [Variable ("X"), Variable ("Y"), Atom ("a")]))) ==
			set([Variable ("X"), Variable ("Y")]))

	def test_final_1_3 ():
		r = Rule ((Function ("p", [Variable ("X"), Variable ("Y"), Atom ("a")])), RuleBody([]))
		assert ((interpreter.variables_of_clause (r) ==
			set([Variable ("X"), Variable ("Y")])))

	def test_final_1_4 ():
		h = Function ("p", [Variable ("X"), Variable ("Y"), Atom ("a")])
		b = [Function ("q", [Atom ("a"), Atom ("b"), Atom ("a")])]
		r = Rule (h, RuleBody(b))
		assert  (interpreter.variables_of_clause (r) ==
			set([Variable ("X"), Variable ("Y")]))

	def test_final_2_1 ():
		s = { Variable(("Y")): Number(0), Variable("X"): Variable(("Y")) }
		t = Function ("f", [Variable ("X"), Variable ("Y"), Atom ("a")])
		t_= Function ("f", [Variable ("Y"), Number("0"), Atom ("a")])
		assert (interpreter.substitute_in_term (s, t) == t_)

	def test_final_2_2 ():
		s = { Variable(("Y")): Number(0), Variable("X"): Variable(("Y")) }
		t = Function ("p", [Variable ("X"), Variable ("Y"), Atom ("a")])
		t_ = Function ("p", [Variable ("Y"), Number("0"), Atom ("a")])
		assert (interpreter.substitute_in_term (s, t) == t_)

	def test_final_2_3 ():
		s = { Variable(("Y")): Number(0), Variable("X"): Variable(("Y")) }
		r = Rule ((Function ("p", [Variable ("X"), Variable ("Y"), Atom ("a")])), RuleBody([]))
		r_ = Rule ((Function ("p", [Variable ("Y"), Number("0"), Atom ("a")])), RuleBody([]))
		assert (interpreter.substitute_in_clause (s, r) == r_)

	def test_final_2_4 ():
		s = { Variable(("Y")): Number("0"), Variable("X"): Variable(("Y")) }
		p = Function ("p", [Variable("X"), Variable(("Y")), Atom(("a"))])
		q = Function ("q", [Atom(("a")), Atom(("b")), Atom(("a"))])
		p_ = Function ("p", [Variable(("Y")), Number("0"), Atom(("a"))])
		q_ = Function ("q", [Atom(("a")), Atom(("b")), Atom(("a"))])
		r = Rule (p, RuleBody([q]))
		r_ = Rule (p_, RuleBody([q_]))
		assert (interpreter.substitute_in_clause(s, r) == r_)

	# Test on unification
	def test_final_3_1 ():
		t = Variable ("X")
		t_ = Variable ("Y")
		u = {Variable ("Y"): Variable ("X")}
		u_ = {Variable ("X"): Variable ("Y")}
		assert (interpreter.unify (t, t_) == u or interpreter.unify (t, t_) == u_)

	def test_final_3_2 ():
		t = Variable ("Y")
		t_ = Variable ("X")
		u = {Variable ("X"): Variable ("Y")}
		u_ = {Variable ("Y"): Variable ("X")}
		assert (interpreter.unify (t, t_) == u or interpreter.unify (t, t_) == u_)

	def test_final_3_3 ():
		t = Variable ("Y")
		t_ = Variable ("Y")
		assert (interpreter.unify (t, t_) == {})

	def test_final_3_4 ():
		t = Number("0")
		t_ = Number("0")
		assert (interpreter.unify (t, t_) == {})

	def test_final_3_5 ():
		t = Number ("0")
		t_ = Variable ("Y")
		u = {Variable ("Y"): Number("0")}
		assert (interpreter.unify (t, t_) == u)

	def test_final_3_6 ():
		t = Number("0")
		t_ = Number("1")
		try:
			interpreter.unify (t, t_)
			assert False
		except Not_unifiable:
			assert True

	def test_final_3_7 ():
		t = Function ("f", [Number("0")])
		t_ = Function ("g", [Number("1")])
		try:
			interpreter.unify (t, t_)
			assert False
		except Not_unifiable:
			assert True

	def test_final_3_8 ():
		u = {(Variable ("X")): (Variable ("Y"))}
		u_ = {(Variable ("Y")): (Variable ("X"))}
		t = Function ("f", [Variable ("X")])
		t_ = Function ("f", [Variable ("Y")])
		assert (interpreter.unify (t, t_) == u or interpreter.unify (t, t_) == u_)

	def test_final_3_9 ():
		t1 = Function ("f", [Variable ("X"), Variable ("Y"), Variable ("Y")])
		t2 = Function ("f", [Variable ("Y"), Variable ("Z"), Atom ("a")])
		u = { Variable("X"): Atom("a"), Variable("Y"): Atom("a"), Variable("Z"): Atom("a") }
		assert (interpreter.unify (t1, t2) == u)

	def list2str(l):
		return ('(' + (',' + ' ').join(
			list(map(str, l))) + ')')

	# Test on a simple program
	psimple = [Rule(Function ("f", [Atom("a"), Atom("b")]), RuleBody ([]))]

	def test_final_4_1():
		print ("\n\n################################################################")
		print ("###### Testing the non-deterministic abstract interpreter ######")
		print ("################################################################")
		print (f"Program: {list2str(psimple)}")
		g = [Function ("f", [Atom("a"), Atom("b")])]
		print (f"Goal: {list2str(g)}")
		g_ = interpreter.nondet_query (psimple, g)
		assert (g_ == [Function ("f", [Atom("a"), Atom("b")])])
		print (f"Solution: {list2str(g_)}")

	def test_final_4_2():
		g = [Function ("f", [Variable("X"), Atom("b")])]
		print (f"Goal: {list2str(g)}")
		g_ = interpreter.nondet_query (psimple, g)
		assert (g_ == [Function ("f", [Atom("a"), Atom("b")])]);
		print (f"Solution: {list2str(g_)}")

	def test_final_4_3():
		g = [Function ("f", [Variable ("X"), Variable("Y")])]
		print (f"Goal: {list2str(g)}")
		g_ = interpreter.nondet_query (psimple, g)
		assert (g_ == [Function ("f", [Atom("a"), Atom("b")])])
		print (f"Solution: {list2str(g_)}")


	# Test on the House Stark program
	def ancestor (x, y): return Function ("ancestor", [x, y])
	def father (x, y): return Function ("father", [x, y])
	def father_consts (x, y):  return father (Atom (x), Atom (y))
	f1 = Rule (father_consts ("rickard", "ned"), RuleBody([]))
	f2 = Rule (father_consts ("ned", "robb"), RuleBody([]))
	r1 = Rule (ancestor (Variable ("X"), Variable ("Y")), RuleBody([father (Variable ("X"), Variable ("Y"))]))
	r2 = Rule (ancestor (Variable ("X"), Variable ("Y")), \
					RuleBody([father (Variable ("X"), Variable ("Z")), ancestor (Variable ("Z"), Variable ("Y"))]))
	pstark = [f1,f2,r1,r2]

	def test_final_4_4():
		print (f"\nProgram: {list2str(pstark)}")
		g = [ancestor (Atom("rickard"), Atom("ned"))]
		print (f"Goal: {list2str(g)}")
		g_ = interpreter.nondet_query (pstark, g)
		print (f"Solution: {list2str(g_)}")
		assert (g_ == [ancestor (Atom("rickard"), Atom("ned"))])

	def test_final_4_5():
		g = [ancestor (Atom("rickard"), Atom("robb"))]
		print (f"Goal: {list2str(g)}")
		g_ = interpreter.nondet_query (pstark, g)
		print (f"Solution: {list2str(g_)}")
		assert (g_ == [ancestor (Atom("rickard"), Atom("robb"))])

	def test_final_4_6 ():
		g = [ancestor (Variable("X"), Atom("robb"))]
		print (f"Goal: {list2str(g)}")
		g_ = interpreter.nondet_query (pstark, g)
		print (f"Solution: {list2str(g_)}")
		assert (g_ == [ancestor (Atom("ned"), Atom("robb"))] or
		              g_ == [ancestor (Atom("rickard"), Atom("robb"))])

	# Test on the list append program
	nil = Atom("nil")
	def cons (h, t): return Function ("cons", [h, t])
	def append (x, y, z): return Function ("append", [x, y, z])
	c1 = Rule (append (nil, Variable("Q"), Variable("Q")), RuleBody([]))
	c2 = Rule (append ((cons (Variable("H"), Variable("P"))), Variable("Q"), (cons (Variable("H"), Variable("R")))), \
	                RuleBody([append (Variable("P"), Variable("Q"), Variable("R"))]))
	pappend = [c1, c2]

	def test_final_4_7():
		print (f"\nProgram: {list2str(pappend)}")
		g = [append (Variable("X"), Variable("Y"), \
				(cons (Number("1"), (cons (Number("2"), (cons (Number("3"), nil)))))))]
		print (f"Goal: {list2str(g)}")
		g_ = interpreter.nondet_query (pappend, g)
		print (f"Solution: {list2str(g_)}")
		assert (
		g_ == [append (nil, (cons (Number("1"), (cons (Number("2"), (cons (Number("3"), nil)))))), \
								(cons (Number("1"), (cons (Number("2"), (cons (Number("3"), nil)))))))] or
		g_ == [append ((cons (Number("1"), nil)), (cons (Number("2"), (cons (Number("3"), nil)))), \
								(cons (Number("1"), (cons (Number("2"), (cons (Number("3"), nil)))))))] or
		g_ == [append ((cons (Number("1"), (cons (Number("2"), nil)))), (cons (Number("3"), nil)), \
		 						(cons (Number("1"), (cons (Number("2"), (cons (Number("3"), nil)))))))] or
		g_ == [append ((cons (Number("1"), (cons (Number("2"), (cons (Number("3"), nil)))))), nil, \
								(cons (Number("1"), (cons (Number("2"), (cons (Number("3"), nil)))))))] )


	# Test on the simple program
	def test_challenge_1():
		print ("\n\n###################################################")
		print ("###### Testing the deterministic interpreter ######")
		print ("###################################################")
		print (f"Program: {list2str(psimple)}")
		# Tests query failure
		g = [Function ("f", [Atom ("a"), Atom ("c")])]
		print (f"Goal: {list2str(g)}")
		assert (interpreter.det_query (psimple, g) == [])
		print ("Solution: Empty solution")

	# Test on the Stark House program
	def test_challenge_2():
		print (f"\nProgram:{list2str(pstark)}")
		# Tests backtracking
		g = [ancestor (Atom("rickard"), Atom("robb"))]
		print (f"Goal: {list2str(g)}")
		g_ = interpreter.det_query (pstark, g)
		assert (len(g_) == 1)
		g_ = g_[0]
		print (f"Solution: {list2str(g_)}")
		assert (g_ == g)


	def test_challenge_3():
		# Tests choice points
		g = [ancestor (Variable("X"), Atom("robb"))]
		print (f"Goal: {list2str(g)}")
		g_ = interpreter.det_query (pstark, g)
		assert (len(g_) == 2)
		g1, g2 = g_[0], g_[1]
		print (f"Solution: {list2str(g1)}")
		print (f"Solution: {list2str(g2)}")
		assert (g1 == [ancestor (Atom("ned"), Atom("robb"))])
		assert (g2 == [ancestor (Atom("rickard"), Atom("robb"))])

	# Test on the list append program
	def test_challenge_4():
		print (f"\nProgram: {list2str(pappend)}")
		# Tests choice points
		g = [append (Variable("X"), (Variable("Y")), (cons (Number("1"), (cons (Number("2"), (cons (Number("3"), nil)))))))]
		print (f"Goal: {list2str(g)}")
		g_ = interpreter.det_query (pappend, g)
		assert (len(g_) == 4)
		for sg in g_:
			print (f"Solution: {list2str(sg)}")

	error_count = 0

	try:
		test_final_1_1()
		test_final_1_2()
		test_final_1_3()
		test_final_1_4()
	except AssertionError as err:
		error_count += 1
		_, _, tb = sys.exc_info()
		traceback.print_tb(tb)
	except:
		error_count += 1
		print("Unexpected error:", sys.exc_info()[0])
		_, _, tb = sys.exc_info()
		traceback.print_tb(tb)

	try:
		test_final_2_1()
		test_final_2_2()
		test_final_2_3()
		test_final_2_4()
	except AssertionError as err:
		error_count += 1
		_, _, tb = sys.exc_info()
		traceback.print_tb(tb)
	except:
		error_count += 1
		print("Unexpected error:", sys.exc_info()[0])
		_, _, tb = sys.exc_info()
		traceback.print_tb(tb)

	try:
		test_final_3_1()
		test_final_3_2()
		test_final_3_3()
		test_final_3_4()
		test_final_3_5()
		test_final_3_6()
		test_final_3_7()
		test_final_3_8()
		test_final_3_9()
	except AssertionError as err:
		error_count += 1
		_, _, tb = sys.exc_info()
		traceback.print_tb(tb)
	except:
		error_count += 1
		print("Unexpected error:", sys.exc_info()[0])
		_, _, tb = sys.exc_info()
		traceback.print_tb(tb)

	try:
		test_final_4_1()
		test_final_4_2()
		test_final_4_3()
		test_final_4_4()
		test_final_4_5()
		test_final_4_6()
		test_final_4_7()
	except AssertionError as err:
		error_count += 1
		_, _, tb = sys.exc_info()
		traceback.print_tb(tb)
	except:
		error_count += 1
		print("Unexpected error:", sys.exc_info()[0])
		_, _, tb = sys.exc_info()
		traceback.print_tb(tb)

	try:
		test_challenge_1()
		test_challenge_2()
		test_challenge_3()
		test_challenge_4()
	except AssertionError as err:
		error_count += 1
		_, _, tb = sys.exc_info()
		traceback.print_tb(tb)
	except:
		error_count += 1
		print("Unexpected error:", sys.exc_info()[0])
		_, _, tb = sys.exc_info()
		traceback.print_tb(tb)

	print (f"{error_count} out of 5 programming questions are incorrect.")
