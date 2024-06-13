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

(* Merge two lists together without duplicates.

  merge : ('a -> 'a list -> bool) -> 'a list -> 'a list -> 'a list *)
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

(* Prop.tautology : Prop Formula -> bool *)
fun tautology fm = onallvaluations (eval fm) (fn _ => false) (vars fm);

(* Prop.simplify : 'a Formula -> 'a Formula *)
local
    val simplify1 =
     fn (Not False) => True
      | (Not True) => False
      | (Not (Not p)) => p
      | (And (p, False)) => False
      | (And (False, p)) => False
      | (And (p, True)) => p
      | (And (True, p)) => p
      | (Or (p, False)) => p
      | (Or (False, p)) => p
      | (Or (p, True)) => True
      | (Or (True, p)) => True
      | (Implies (False, p)) => True
      | (Implies (p, True)) => True
      | (Implies (True, p)) => p
      | (Implies (p, False)) => Not p
      | (Iff (p, True)) => p
      | (Iff (True, p)) => p
      | (Iff (p, False)) => Not p
      | (Iff (False, p)) => Not p
      | fm => fm
in
    fun simplify (Not p) = simplify1 (Not (simplify p))
      | simplify (And (p,q)) = simplify1 (And (simplify p, simplify q))
      | simplify (Or (p,q)) = simplify1 (Or (simplify p, simplify q))
      | simplify (Implies (p,q)) = simplify1 (Implies (simplify p, simplify q))
      | simplify (Iff (p,q)) = simplify1 (Iff (simplify p, simplify q))
      | simplify fm = fm
end;
end; (* structure Prop *)

(* Verify Bourbaki's axioms are tautologies. *)
local
    val A = Atom (P "A")
    val B = Atom (P "B")
    val C = Atom (P "C")
    val s1 = Implies (Or(A,A), A)
    val s2 = Implies (A, Or(A,B))
    val s3 = Implies (Or(A,B), Or(B,A))
    val s4 = Implies (Implies(A,B),
                      Implies(Or(C,A),
                              Or(C,B)))
    val syn1 = Implies(Implies(A,B),
                       Or(Not A,B))
    val syn2 = Implies(Or(Not A,B),
                       Implies(A,B))
in
    val bourbaki_axioms_are_tautologies = Prop.tautology s1 andalso
                                          Prop.tautology s2 andalso
                                          Prop.tautology s3 andalso
                                          Prop.tautology s4 andalso
                                          Prop.tautology syn1 andalso
                                          Prop.tautology syn2;
    val _ = if not bourbaki_axioms_are_tautologies
    then raise Fail "[-] Bourbaki's axiom schemas are somehow invalid"
    else print "[+] Bourbaki's axiom schemas (for propositional logic) are logically valid\n";
end;

(* Supporting Hilbert's choice operator requires simultaneously 
   defining predicate (i.e., `Fol`) and `Term` datatypes.
 *)
datatype Fol = R of string * (Term list)
     and Term = Var of Var
              | Fn of string * (Term list)
              | Choice of Var * (Fol Formula);

(* Checks if terms, formulas are equal to each other or not. *)
fun term_eq (Var x) (Var y) = (x = y)
  | term_eq (Fn (f1,args1)) (Fn (f2,args2))
    = (f1 = f2) andalso (args_eq args1 args2)
  | term_eq (Choice(x,fm1)) (Choice(y,fm2)) = (x=y) andalso (fm_eq fm1 fm2)
  | term_eq _ _ = false
and args_eq [] [] = true
  | args_eq (x::xs) [] = false
  | args_eq [] (y::ys) = false
  | args_eq (x::xs) (y::ys) = (term_eq x y) andalso (args_eq xs ys)
and fm_eq True True = true
  | fm_eq False False = true
  | fm_eq (Atom (R(p1,args1))) (Atom(R(p2,args2))) = (p1 = p2) andalso
                                                     (args_eq args1
                                                              args2)
  | fm_eq (Not fm1) (Not fm2) = fm_eq fm1 fm2
  | fm_eq (And (a1,b1)) (And (a2,b2)) = (fm_eq a1 a2) andalso (fm_eq b1 b2)
  | fm_eq (Or (a1,b1)) (Or (a2,b2)) = (fm_eq a1 a2) andalso (fm_eq b1 b2)
  | fm_eq (Implies (a1,b1)) (Implies (a2,b2)) = (fm_eq a1 a2) andalso (fm_eq b1 b2)
  | fm_eq (Iff (a1,b1)) (Iff (a2,b2)) = (fm_eq a1 a2) andalso (fm_eq b1 b2)
  | fm_eq (Forall (x,fm1)) (Forall (y,fm2)) = (x = y) andalso (fm_eq fm1 fm2)
  | fm_eq (Exists (x,fm1)) (Exists (y,fm2)) = (x = y) andalso (fm_eq fm1 fm2)
  | fm_eq _ _ = false;

(* For arguments, handle commas properly. *)
fun commaify [] = ""
  | commaify (x::y::[]) = (x^", "^y)
  | commaify (x::y::tl) = (x^", "^y^", ")^(commaify tl)
  | commaify (x::[]) = x;

(* Print terms and formulas to string.

Uses Mizar-like syntax for predicates and functions. That is, square
brackets are used for the arguments of a predicate P[t1, t2, ...]
and parentheses are used for functions F(t1, t2, ...).
 *)
fun term_to_s (Var x) = x
  | term_to_s (Fn (f, args)) = f^"("^(commaify (map term_to_s args))^")"
  | term_to_s (Choice (x,fm)) = "\\tau_{"^x^"}("^(fm_to_s fm)^")"
and fm_to_s (Atom (R (pred, args))) = pred^"["^(commaify (map term_to_s args))^"]"
  | fm_to_s True = "true"
  | fm_to_s False = "false"
  | fm_to_s (Not fm) = "Not("^(fm_to_s fm)^")"
  | fm_to_s (And (a,b)) = "And("^(fm_to_s a)^", "^(fm_to_s b)^")"
  | fm_to_s (Or (a,b)) = "Or("^(fm_to_s a)^", "^(fm_to_s b)^")"
  | fm_to_s (Implies (a,b)) = "Implies("^(fm_to_s a)^", "^(fm_to_s b)^")"
  | fm_to_s (Iff (a,b)) = "Iff("^(fm_to_s a)^", "^(fm_to_s b)^")"
  | fm_to_s (Forall (x,fm)) = "Forall("^x^", "^(fm_to_s fm)^")" 
  | fm_to_s (Exists (x,fm)) = "Exists("^x^", "^(fm_to_s fm)^")";

val A = Atom(R("A",[]));
val B = Atom(R("B",[]));
val C = Atom(R("C",[]));

signature BOURBAKI = sig
    type thm;
    val concl : thm -> Fol Formula;
    val a_implies_b : thm;
    val a_implies_b_implies_c : thm;
    val s1 : Fol Formula -> thm;
    val s2 : Fol Formula -> Fol Formula -> thm;
    val s3 : Fol Formula -> Fol Formula -> thm;
    val s4 : Fol Formula -> Fol Formula -> Fol Formula -> thm;
    val axiom_unfold_imp : Fol Formula -> Fol Formula -> thm;
    val axiom_fold_imp : Fol Formula -> Fol Formula -> thm;
    val fold_imp : thm -> thm;
    val unfold_imp : thm -> thm;
    val mp : thm -> thm -> thm;
end;

structure Bourbaki :> BOURBAKI = struct
type thm = Fol Formula;
fun concl fm = fm;
val a_implies_b = Implies(A,B);
val a_implies_b_implies_c = Implies(A,Implies(B,C));
fun s1 A = Implies (Or(A,A), A);
fun s2 A B = Implies (A, Or(A,B));
fun s3 A B = Implies (Or(A,B), Or(B,A));
fun s4 A B C = Implies (Implies(A,B),
                        Implies(Or(C,A),
                                Or(C,B)));

(* Helper functions and axioms for treating the definition of `Implies`
in terms of `Or` and `Not` *)
fun axiom_unfold_imp A B = Implies(Implies(A,B),
                                   Or(Not A,B));
fun axiom_fold_imp A B = Implies(Or(Not A,B),
                                 Implies(A,B));
fun fold_imp (Or(Not(A), B)) = Implies(A, B)
  | fold_imp fm = raise Fail ("fold_imp cannot work on formula "^(fm_to_s fm));
fun unfold_imp (Implies(A,B)) = Or(Not A, B)
  | unfold_imp fm = raise Fail ("unfold_imp cannot work on formula "^(fm_to_s fm));

(* Our only rule of inference: Modus Ponens *)
fun mp (Implies(A,B)) A' = if fm_eq A A' then B
                           else raise Fail "Modus ponens minor argument mismatch" 
  | mp _ _ = raise Fail "Modus ponens given invalid theorems"; 
end;

local
    val turnstile = "|-"
in
    fun thm_to_s (th : Bourbaki.thm) =
        turnstile^" "^(fm_to_s (Bourbaki.concl th));
end;

(* If |- A ==> B and |- B ==> C, then |- A ==> C *) 
fun c6 th1 th2 = case (Bourbaki.concl th1, Bourbaki.concl th2) of
                     (Implies(A,B), Implies(B',C)) =>
                     if fm_eq B B'
                     then  let val th3 = Bourbaki.s4 B C (Not A)
                               val th4 = Bourbaki.mp th3 th2
                               val th5 = Bourbaki.unfold_imp th1
                               val th6 = Bourbaki.mp th4 th5
                           in
                               Bourbaki.fold_imp th6
                           end
                     else raise Fail ("C6: mismatch of B='"^(fm_to_s B)^"' and B'='"^(fm_to_s B')^"';"^"th1 = "^(thm_to_s th1)^", th2 = "^(thm_to_s th2))

                   | (_,_) => raise Fail "Invalid arguments to C6";

(* |- B ==> (A or B) *)
fun c7 (A : Fol Formula) (B : Fol Formula) =
    let val th1 = Bourbaki.s2 B A
        val th2 = Bourbaki.s3 B A
    in c6 th1 th2
    end;

(* |- A ==> A *)
fun c8 (A : Fol Formula) =
    let val th1 = Bourbaki.s2 A A
        val th2 = Bourbaki.s1 A
    in c6 th1 th2
    end;

(* If |- B, then for any formula A we have |- A ==> B *)
fun c9 (th1 : Bourbaki.thm) (A : Fol Formula) =
    let val B = Bourbaki.concl th1
        val th2 = c7 (Not A) B
        val th3 = Bourbaki.mp th1 th2
    in Bourbaki.fold_imp th3
    end;

(* |- a or not a *)
fun c10 (A : Fol Formula) =
    let val th1 = c8 A
        val th2 = Bourbaki.unfold_imp th1
        val th3 = Bourbaki.s3 (Not A) A
    in Bourbaki.mp th3 th2
    end;

(* |- a ==> not (not a) *)
fun c11 (A : Fol Formula) =
    Bourbaki.fold_imp (c10 (Not A));

(* |- (a ==> b) ==> ((not b) ==> (not a)), i.e., the contrapositive tautology *)
fun c12 (A : Fol Formula) (B : Fol Formula) =
    let val th1 = c11 B
        val th2 = Bourbaki.s4 B (Not (Not B)) (Not A)
        val th3 = Bourbaki.mp th2 th1
        val th4 = Bourbaki.s3 (Not A) (Not (Not B))
        val th5 = c6 th3 th4
        val th6 = Bourbaki.axiom_unfold_imp A B
        val th7 = c6 th6 th5
        val th8 = Bourbaki.axiom_fold_imp (Not B) (Not A)
    in c6 th7 th8
    end;

(* If |- a ==> b, then |- (b ==> c) ==> (a ==> c) *)
fun c13 (th1 : Bourbaki.thm) (C : Fol Formula) =
    case Bourbaki.concl(th1) of
        Implies(A,B) => let val th2 = c12 A B
                            val th3 = Bourbaki.mp th2 th1
                            val th4 = Bourbaki.s4 (Not B) (Not A) C
                            val th5 = Bourbaki.mp th4 th3
                            val th6 = c6 (Bourbaki.axiom_unfold_imp B C)
                                         (Bourbaki.s3 (Not B) C)
                            val th7 = c6 th6 th5
                            val th8 = c6 (Bourbaki.s3 C (Not A))
                                         (Bourbaki.axiom_fold_imp A C)
                        in c6 th7 th8
                        end
      | _ => raise Fail "Invalid theorem given to C6";

(* If |- a ==> b, then |- a ==> (c \/ b) *)
fun lm1 th1 (c : Fol Formula) =
    case Bourbaki.concl th1 of
        Implies(a,b) => let val th2 = c7 c b
                        in c6 th1 th2
                        end
      | _ => raise Fail ("Lm1 given invalid theorem: "^(thm_to_s th1));

(* If |- a ==> b, then |- a ==> (b \/ c) *)
fun lm2 th1 (c : Fol Formula) =
    case Bourbaki.concl th1 of
        Implies(a,b) => let val th2 = Bourbaki.s2 b c
                        in c6 th1 th2
                        end
      | _ => raise Fail ("Lm2 given invalid theorem"^(thm_to_s th1));

(* If |- a ==> c and |- b ==> c, then infer |- a \/ b ==> c *)
fun lm3 th1 th2 =
    case (Bourbaki.concl th1, Bourbaki.concl th2) of
        (Implies(a,c), Implies(b,c2)) =>
        if fm_eq c c2
        then let val th3 = Bourbaki.s4 a c c
                 val th4 = Bourbaki.mp th3 th1
                 val th5 = Bourbaki.s1 c
                 val th6 = c6 th4 th5
                 val th7 = Bourbaki.s4 b c a
                 val th8 = Bourbaki.mp th7 th2
                 val th9 = Bourbaki.s3 a c
                 val th10 = c6 th8 th9
             in c6 th10 th6
             end
        else raise Fail ("Lm3: mismatch in conclusions of theorems '"^(thm_to_s th1)^"' and '"^(thm_to_s th2)^"'")
      | _ => raise Fail "Lm3: expects implications in both theorems";

(* Checks |- a1 ==> b and |- a2 ==> b are the theorems given. *)
fun concl_eq (th1 : Bourbaki.thm) (th2 : Bourbaki.thm) =
    case (Bourbaki.concl th1, Bourbaki.concl th2) of
        (Implies (a1,b1), Implies (a2,b2)) => fm_eq b1 b2
      | _ => false;

(* Proves |- (A \/ B) \/ C ==> A \/ (B \/ C) *)
fun disj_assoc1 a b c =
    let val th1 = Bourbaki.s2 a (Or(b,c))
        val th2 = Bourbaki.s2 b c
        val th3 = lm1 th2 a
        val th4 = lm3 th1 th3
        val th5 = c7 b c
        val th6 = lm1 th5 a
    in lm3 th4 th6
    end;

(* |- a \/ (b \/ c) ==> (a \/ b) \/ c *)
fun disj_assoc2 a b c =
    let val th1 = Bourbaki.s2 (Or(a,b)) c (* |- a \/ b ==> (a \/ b) \/ c *)
        val th2 = c7 a b (* |- b ==> a \/ b *)
        val th3 = lm2 th2 c (* |- b ==> (a \/ b) \/ c *)
        val th4 = c7 (Or(a,b)) c (* |- c ==> (a \/ b) \/ c *)
        val th5 = lm3 th3 th4 (* |- b \/ c ==> (a \/ b) \/ c *)
        val th6 = c6 (Bourbaki.s2 a b) th1 (* |- a ==> (a \/ b) \/ c *)
    in lm3 th6 th5
    end;

(* If |- a ==> b and |- a \/ c, then |- a \/ c *)
fun lm6 th1 th2 =
    case (Bourbaki.concl th1, Bourbaki.concl th2) of
        (Implies(a,b), Or(a2,c)) =>
        if fm_eq a a2
        then let val th3 = Bourbaki.s4 a b c
                 val th4 = Bourbaki.mp th3 th1
                 val th5 = Bourbaki.mp (Bourbaki.s3 a c) th2
                 val th6 = Bourbaki.mp th4 th5
             in
                 Bourbaki.mp (Bourbaki.s3 c b) th6
             end
        else raise Fail ("Lm6 error: antecedent of "
                             ^(thm_to_s th1)
                             ^"doesn't match lead disjunct of "^(thm_to_s th2))
      | _ => raise Fail ("Lm6 error: invalid theorems "
                         ^(thm_to_s th1)^" and "^(thm_to_s th2));

(* If |- a ==> b and |- a ==> (b ==> c),
   then infer |- a ==> c *)
fun hypo_syll th1 th2 =
    case (Bourbaki.concl th1, Bourbaki.concl th2) of
        (Implies (a,b), Implies(a2,Implies(b2,c))) =>
        if (fm_eq a a2) andalso (fm_eq b b2)
        then let val th3 = c13 th1 c
                 val th4 = c6 th2 th3
                 val th5 = c6 (Bourbaki.s2 (Not a) c)
                              (Bourbaki.axiom_fold_imp a c)
                 val th6 = (Bourbaki.s4 (Not a) (Implies(a,c)) c)
                 val th7 = c6 (c6 (Bourbaki.axiom_unfold_imp a c)
                                  (Bourbaki.s3 (Not a) c))
                              (Bourbaki.mp th6 th5)
                 val th8 = c6 th4 th7
                 val th9 = Bourbaki.mp (Bourbaki.axiom_unfold_imp a
                                                       (Or(c,Implies(a,c))))
                              th8
                 val th10 = (disj_assoc2 (Not a) c (Implies(a,c)))
                 val th11 = Bourbaki.mp th10 th9
                 val th12 = lm6 (Bourbaki.axiom_fold_imp a c) th11
             in Bourbaki.mp (Bourbaki.s1 (Implies (a,c))) th12
             end
        else raise Fail ("hypo_syll theorems disagree antecedents: "
                         ^(thm_to_s th1)^" and "
                         ^(thm_to_s th2))
      | _ => raise Fail ("hypo_syll not given two implications: "
                         ^(thm_to_s th1)^" and "
                         ^(thm_to_s th2)); 

local
    val result = hypo_syll Bourbaki.a_implies_b Bourbaki.a_implies_b_implies_c;
    val expected = Implies(A,C);
in 
    val double_check_hypo_syll = fm_eq (Bourbaki.concl result) expected
end;

(* Now, for us to actually implement the deduction theorem, we need to
introduce tactics. *)
