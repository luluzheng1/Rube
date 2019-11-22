(*Yes, we're violating our rules by opening Ast...it's okay... *)
open Ast

type location = int
type ('a, 'b) mutable_alist = ('a * 'b ref) list ref
datatype rubevalue = 
	RNIL
|	RINT of int
|	RSTR of string
|	RLOC of int
type id = string
type name = string
type clsname = string
type object = { class: clsname, fields: (id, rubevalue) mutable_alist }
type locals = (name, rubevalue) mutable_alist
type heap = (location, object) mutable_alist
val empty_A : unit -> locals = fn () => ref []
val empty_H : unit -> heap = fn () => ref []
type config = locals * heap * expr
type result = locals * heap * rubevalue

fun defined_class (p:rube_prog) (c:string):bool = 
	let fun class_exists cls c =
		if (#cls_name cls) = c then
			true
		else
			false
	    fun find_class [] c = false
		  | find_class (x::xs) c = 
			if class_exists x c then
				true
			else
				find_class xs c
	in find_class (#prog_clss p) c
	end

fun lookup_meth (p:rube_prog) (c:string) (m:string):meth option = 
	let fun get_class [] c = NONE (* get class from prog_clss*)
		  | get_class (x::xs) c = 
		  	if (#cls_name x) = c then
		  		SOME x
		  	else
		  		get_class xs c

		fun convert NONE = raise Fail "Undefined program class"
		  | convert (SOME x) = x
		
		fun meth_list NONE m = [] (* get list of methods from a class*)
		  | meth_list (SOME x) m = (#cls_meths x)

		fun super_meth [] m = NONE
		  | super_meth (x::xs) m = 
		  	if (#meth_name x) = m then
		  		SOME x
		  	else
		  		super_meth xs m
		 (* NONE case we need to look in superclass, find desired method in list of methods *)
		fun meth [] m = super_meth (meth_list (get_class (#prog_clss p) (#cls_super (convert (get_class (#prog_clss p) c)))) m) m 
		  | meth (x::xs) m = 
		  	if (#meth_name x) = m then
		  		SOME x
		  	else
		  		meth xs m
	in meth (meth_list (get_class (#prog_clss p) c) m) m
	end

(* Helper functions for run *)
fun lookup k (ref alist) = 
	let fun find_k [] = NONE
		  | find_k ((k', ref v')::rest) = 
		  	if k = k' then
		  		SOME v'
		  	else
		  		find_k rest
	in find_k alist
	end

fun update (env as ref alist) (k, v) = 
	let fun extend_or_update [] = env := (k, ref v) :: !env
		  | extend_or_update ((k', v') :: rest) = 
		  	if k = k' then
		  		v' := v
		  	else
		  		extend_or_update rest
	in extend_or_update alist
	end

val last_loc = ref ~1
fun fresh_location () = 
	let val () = last_loc := !last_loc + 1
	in !last_loc
	end

fun rubeval (e) = 
  (case e
	of (A, H, rv) => rv)

fun extract_option (opt) =
  (case opt
  	of NONE => raise Fail "Could not find object or rubevalue in env"
  	 | (SOME v) => v)

fun read_location (option_location) =
  (case option_location
  	 of NONE => raise Fail "self not bound in A"
	  | (SOME (RLOC n)) => n
	  | (SOME _) => raise Fail "expects self to be RLOC") 

fun eval p (A, H, ENil) = (A, H, RNIL)
  | eval p (A, H, EInt n) = (A, H, RINT n)
  | eval p (A, H, ESelf) = (A, H, extract_option (lookup "self" A))
  | eval p (A, H, EString s) = (A, H, RSTR s)
  | eval p (A, H, ELocRd s) = 
	let val option_var = lookup s A
		val read_var =  
		  (case option_var
			 of NONE => raise Fail "id not bound in A"
			  | (SOME v) => v)
	in (A, H, read_var)
	end

  | eval p (A, H, ELocWr (s, e)) = 
	let val v = eval p (A, H, e)
		val rv = rubeval (v)
		val () = update A (s, rv)
	in (A, H, rv)
	end

  | eval p (A, H, EFldRd s) = 
	let val option_location = lookup "self" A
		val location = read_location (option_location)
		  	  
		val option_object = lookup location H
		val read_object = 
		  (case option_object
		  	 of NONE => raise Fail "object not bound in H"
		  	  | (SOME v) => v)

		val {class = _, fields = fs} = read_object
		val option_field = lookup s fs
		val read_field =	
		  (case option_field
		  	 of NONE => RNIL
		  	  | (SOME rv) => rv)
	in (A, H, read_field)
	end 

  | eval p (A, H, EFldWr (s, e)) = 
  	let val option_location = lookup "self" A
  		val location = read_location (option_location)

  		val option_object = lookup location H
  		val read_object = 
  		  (case option_object
  		  	 of NONE => raise Fail "object not bound in H"
  		  	  | (SOME v) => v)

  		val {class = _, fields = fs} = read_object
  	    val v = eval p (A, H, e)
  		val rv = rubeval (v)
  		val () = update fs (s, rv)
  	in (A, H, rv)
  	end 

  | eval p (A, H, EIf (e1, e2, e3)) =
  	let val guard = eval p (A, H, e1)
  		val rubevalue = rubeval (guard)
  		val evaluate =
  		  (case rubevalue
  		  	 of RNIL => eval p (A, H, e2)
  		  	  | _ => eval p (A, H, e3))
  	in evaluate
  	end

  | eval p (A, H, ESeq (e1, e2)) =
    let val v1 = eval p (A, H, e1)
    	val v2 = eval p (A, H, e2)
    in v2
    end

  | eval p (A, H, ENew s) =
  	let val has_class = 
  		  (case s
  		  	 of "nil" => raise Halt "Cannot instantiate Bot"
  		  	  | _ => (defined_class p s))
  		val location =
  	      (case has_class
  	      	 of true => fresh_location()
  	      	  | false => raise Halt "No such class C")
  	    val new_class = {class = s, fields = ref []}
  	    val () = update H (location, new_class) (*update H with (location, object)*)
  	in (A, H, (RLOC location))
  	end
(* r_loc = rv
   location = temp*)
  | eval p (A, H, EInvoke (e, s, es)) =
    let val rv = rubeval (eval p (A, H, e))
    	val vs = List.map (fn x => eval p (A, H, x)) es
    	val r_vs = List.map (fn x => rubeval (x)) vs
    	
    	val location = 
    	  (case rv
    	  	 of (RLOC n) => n
    	  	  | _ => built_in(rv, s, vs))
    	

    	val option_object = lookup location H (* returns an object *)
    	val object = 
		  (case option_object
		  	 of NONE => raise Fail "object not bound in H"
		  	  | (SOME v) => v)
		val {class = cls, fields = _} = object (* get cls name from object*)
		
		val option_meth = lookup_meth p cls s 
		(* get meth from object*)
		val meth = 
		  (case option_meth
		  	 of NONE => raise Halt "No such method"
		  	  | (SOME v) => v)
		val {meth_name = meth_name, meth_args = arg_list, meth_body = body} = meth
		
		(* get arguments from method*)
		val same_length =
		  (case (length r_vs = length arg_list)
		  	 of true => true
		  	  | false => raise Fail "Wrong number of arguments") 
		(* bind object to self*)
		val A' = empty_A ()
		val () = update A' ("self", r_loc)
		val args = ListPair.zipEq (arg_list, r_vs)
		(*adds arguments to env A *)
		val () = List.app (fn x => update A' x) args 
		val value = 
		  (case (eval p (A', H, body))
		  	 of (_, _, v) => v)
	in (A, H, value)
	end

(* Evaluate built methods*)
fun built_in (receiver, meth, args)
  	(* Special built ins*)
	case (receiver, meth, args)
	  of (RINT n, "+", [RINT m]) => RINT (n+m)
	   | (RINT n, "+", _) => raise Halt "non-Integer passed as argument"
	   | (RSTR s, "+", [RSTR s']) => RSTR (s ^ s')
	   | (RSTR s, "+", _) => raise Halt "non-String passed as argument"
	   | (RINT n, "-", [RINT m]) => RINT (n-m)
	   | (RINT n, "-", _) => raise Halt "non-Integer passed as argument"
	   | (RINT n, "*", [RINT m]) => RINT (n*m)
	   | (RINT n, "*", _) => raise Halt "non-Integer passed as argument"
	   | (RINT n, "/", [RINT m]) => RINT (n/m)
	   | (RINT n, "/", _) => raise Halt "non-Integer passed as argument"
	   | (_, _, _) => RNIL(*continue this *)

(* Evaluate non built in method *)
fun invoke_meth (location, rv, vs)
	

fun run (p:rube_prog):string = 
	let val {prog_clss=cls, prog_main=e} = p
		fun to_s(RNIL: rubevalue):string = "nil"
		  | to_s(RINT n) = Int.toString n
		  | to_s(RSTR s) = s
		  | to_s _ = raise Fail "not implemented"

		val A = empty_A ()
		val H = empty_H ()

		val (A', H', v) = eval p (A, H, e)

 	in to_s v
	end


(*val A1 = ref [("x", ref 0), ("y", ref 1)]

val test_meth1 = {meth_name = "D", meth_args = [], meth_body = (EInt 1)}
val test_class1 = {cls_name = "A", cls_super = "Object", cls_meths = [test_meth1]}
val p1 = {prog_clss= [test_class1], prog_main = ENil}

val () = 
    Unit.checkExpectWith String.toString
    "testing run ENil"
    (fn () => run p1)
    "nil"

val p2 = {prog_clss= [test_class1], prog_main = EInt 1}
val () = 
    Unit.checkExpectWith String.toString
    "testing run EInt"
    (fn () => run p2)
    "1"

val p3 = {prog_clss= [test_class1], prog_main = EString "string"}
val () = 
    Unit.checkExpectWith String.toString
    "testing run EString"
    (fn () => run p3)
    "string"
*)
(* Testing: is defnied class*)
(*val test_meth1 = {meth_name = "D", meth_args = [], meth_body = (EInt 1)}
val test_meth2 = {meth_name = "E", meth_args = [], meth_body = (EInt 1)}
val test_meth3 = {meth_name = "F", meth_args = [], meth_body = (EInt 1)}

val test_class1 = {cls_name = "A", cls_super = "Object", cls_meths = [test_meth1]}
val test_class2 = {cls_name = "B", cls_super = "Object", cls_meths = [test_meth2]}
val test_class3 = {cls_name = "C", cls_super = "Object", cls_meths = [test_meth3]}
val p = {prog_clss= [test_class1, test_class2, test_class3], prog_main = (EInt 1)}

val () =
    Unit.checkAssert "is defined class"
    (fn () => defined_class p "C")
val () =
    Unit.checkAssert "is defined class"
    (fn () => not (defined_class p "D"))
*)

(*Dont pattern match on mutable alists, use lookup and update*)
val () = Unit.report () 