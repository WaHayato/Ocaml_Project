(* tautology checker *)
(* Tautology means that a logical expression is always true.*)
(* An example of tautology: ¬ (p ∧ q) → (¬ p ∨ ¬ q) *)
(* The expression is always true for all boolean values of p and q *)

(* Basic algorithm of my tautology checker.
    I define IF operator. It is written as [IF π α β](π, α and β are boolean values
    either true or false) meaning that if π is true [IF π α β] is [α], and if π is false
    then [IF π α β] is [β].
    I rewrite basic logic expressions by using the IF operator.
    *)

(*Types of propositional logic used in the tautology checker*)
type proposition =
  False |
  True |
  Var of string |
  And of proposition * proposition | (* ∧ *)
  Or of proposition * proposition | (* ∨ *)
  Not of proposition | (* ¬ *)
  Imply of proposition * proposition | (* --> *)
  Equiv of proposition * proposition ;; (* = *)

(* Types of conditional logic used in the IF operator*)
type conditional =
  IffyFalse |
  IffyTrue |
  IffyVar of string |
  If of conditional * conditional * conditional ;;

(* p is an expression represented as the types of propositional logic
  This function translate the p into the expression represented as the types of
  conditional logic used in IF operator. *)
let ifify p =
  let rec ififying p =
    match p with
      False -> IffyFalse |
      True -> IffyTrue |
      Var s -> IffyVar s |
      And(left, right) -> If((ififying left), (ififying right), IffyFalse) |
      Or(left, right) -> If((ififying left), IffyTrue, (ififying right)) |
      Not alpha -> If((ififying alpha), IffyFalse, IffyTrue) |
      Imply(left, right) -> If((ififying left), (ififying right), IffyTrue) |
      Equiv(left, right) -> If((ififying left), (ififying right), (If((ififying right), IffyFalse, IffyTrue)))
  in ififying p ;;

  (* c is an expression represented as the types of conditional logic [IF π α β].
    This function normalizes the c.
    Normalized form of [IF π α β] is the π does not have IF operatpr. *)
let normalize c =
  let rec normalizing c =
    match c with
      IffyFalse -> IffyFalse |
      IffyTrue -> IffyTrue |
      IffyVar s -> IffyVar s |
      If(a, b, g) ->
        match a with
          IffyFalse ->  If(IffyFalse, (normalizing b), (normalizing g)) |
          IffyTrue ->  If(IffyTrue, (normalizing b), (normalizing g)) |
          IffyVar t ->  If((IffyVar t), (normalizing b), (normalizing g)) |
          If(d, e, f) ->
            normalizing (If((normalizing d), (If((normalizing e), (normalizing b), (normalizing g))), (If((normalizing f), (normalizing b), (normalizing g)))))
  in  normalizing c ;;
(* c is the normalized IF form expression, v is a variable and b is either
   true or false. it replaces each v with b. *)
let substitute c v b =
  let rec substituting c =
    match c with
      IffyFalse -> IffyFalse |
      IffyTrue -> IffyTrue |
      IffyVar s -> if IffyVar s = v
                    then b
                   else IffyVar s |
      If(e, f, g) -> If((substituting e), (substituting f), (substituting g))
  in substituting c;;

(* c is the normalized IF form of expression and v is a variable. This function
  counts the number of v in c. *)
let have c v =
  let rec having c =
    match c with
      IffyFalse -> 0 |
      IffyTrue -> 0 |
      IffyVar s -> if IffyVar s = v
                    then 1
                   else 0 |

      If(a, b, d) -> (having a) + (having b) + (having d)
    in having c ;;

(* c is a normalized form of conditional expression [IF π α β]
  This function simplifies it even in the IF form*)
let simplify c =
  let rec simplifying c =
    match c with
      IffyFalse -> IffyFalse |
      IffyTrue -> IffyTrue |
      IffyVar s -> IffyVar s |
      If(a, b, d) ->
        if a = IffyTrue
          then simplifying b
        else if a = IffyFalse
          then simplifying d
        else if b = IffyTrue && d = IffyFalse
          then a
        else if b = d
          then simplifying b
        else if (have b a) < 1 && (have d a) < 1
          then c
        else if  (have b a) < 1
          then simplifying (If(a, b, (simplifying (substitute d a IffyFalse))))
        else if   (have d a) < 1
          then simplifying (If(a, (simplifying (substitute b a IffyTrue)), d))
        else simplifying (If(a, (simplifying (substitute b a IffyTrue)), (simplifying (substitute d a IffyFalse))))

  in simplifying c ;;


(* p is a logical proposition and this returns true if it is tautology,
  otherwise returns false. *)
let tautology p =
    let c = simplify (normalize (ifify p))
    in
    if c = IffyTrue
      then true
    else false ;;
(* some tests *)
(*True tests *)
tautology (Imply(
            (Not
              (And(Var "p", Var "q"))),
            (Or
              ((Not(Var "p")), (Not(Var "q"))))));;

tautology (Imply(Var "p", Var "p"));;

tautology (Not(Not(Not(And(True, False)))));;

tautology (Equiv(Var "p", (And(Var "p", Var "p"))));;

tautology (Imply((And(Var "p", Var "q")), Var "p"));;

tautology (Imply((And((Or(Var "p", Var "q")), (Not(Var "p")))), Var "q"));;

tautology (Imply((And(Var "p", Var "q")), (Or(Var "p", Var "q"))));;

tautology (Equiv((And(Var "p", Var "q")), (And(Var "p", Var "q"))));;


(*False tests*)
tautology (Imply((Or(Var "p", Var "q")), (And(Var "p", Var "q"))));;
tautology (And(Var "p", Var "q"));;
tautology (Equiv((Or(Var "p", Var "q")), (And(Var "p", Var "q"))));;
