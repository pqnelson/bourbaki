type Var = string;

datatype Prop = P of Var;

datatype 'a Formula = False
                    | True
                    | Atom of 'a
                    | Not of ('a Formula)
                    | And of ('a Formula)*('a Formula)
                    | Or of ('a Formula)*('a Formula)
                    | Implies of ('a Formula)*('a Formula)
                    | Iff of ('a Formula)*('a Formula)
                    | Forall of Var*('a Formula)
                    | Exists of Var*('a Formula);

fun merge member [] ys = ys
  | merge member xs [] = xs
  | merge member (x::tl) ys = if member x ys
                              then merge member tl ys
                              else merge member tl (x::ys);

structure Prop = struct
(* Prop.member : Prop -> Prop list -> bool *)
fun member _ [] = false
  | member (p as (P y)) ((P x)::tl) = (x = y) orelse (member p tl);

(* Prop.vars : Prop Formula -> Prop list *)
fun vars False = []
  | vars True = []
  | vars (Atom p) = [p]
  | vars (Not fm) = vars fm
  | vars (Or (A,B)) = merge member (vars A) (vars B)
  | vars (And (A,B)) = merge member (vars A) (vars B)
  | vars (Implies (A,B)) = merge member (vars A) (vars B)
  | vars (Iff (A,B)) = merge member (vars A) (vars B)
  | vars _ = [];

(* Prop.eval : 'a Formula -> ('a -> bool) -> bool *)
fun eval False v = false
  | eval True v = true
  | eval (Atom p) v = v(p)
  | eval (Not fm) v = not (eval fm v)
  | eval (And (A,B)) v = (eval A v) andalso (eval B v)
  | eval (Or (A,B)) v = (eval A v) orelse (eval B v)
  | eval (Implies (A,B)) v = not(eval A v) orelse (eval B v)
  | eval (Iff (A,B)) v = (eval A v) = (eval B v)
  | eval _ _ = raise Fail "Invalid propositional formula"; 

(* Prop.onallvaluations : ((Prop -> bool) -> bool)
                          -> (Prop -> bool)
                          -> Prop list
                          -> bool *)
fun onallvaluations subfn v ([] : Prop list) = subfn v
  | onallvaluations subfn v (((p as (P x))::ps) : Prop list) =
    let fun v' t ((q as (P y)) : Prop) = if (x = y) then t else v(q)
    in (onallvaluations subfn (v' false) ps) andalso
       (onallvaluations subfn (v' true) ps)
    end;

(* tautology : Prop Formula -> bool *)
fun tautology fm = onallvaluations (eval fm) (fn _ => false) (vars fm);
end;

(* Bourbaki's axioms *)
local
    val A = Atom (P "A")
    val B = Atom (P "B")
    val C = Atom (P "C")
in
    val s1 = Implies (Or(A,A), A);
    val s2 = Implies (A, Or(A,B));
    val s3 = Implies (Or(A,B), Or(B,A));
    val s4 = Implies (Implies(A,B),
                      Implies(Or(C,A),
                              Or(C,B)));
    val bourbaki_axioms_are_tautologies = Prop.tautology s1 andalso
                                          Prop.tautology s2 andalso
                                          Prop.tautology s3 andalso
                                          Prop.tautology s4;
end;
