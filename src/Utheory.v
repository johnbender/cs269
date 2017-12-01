(** * Utheory.v: Specification of [U], interval [ [0,1] ] *)

Require Export Misc.
Require Export Ccpo.
Set Implicit Arguments.
Open Local Scope O_scope.

(** ** Basic operators of U *)
(** 
    - Constants : [0] and [1]
    - Constructor : [ [1/1+] n ] $(\equiv \frac{1}{n+1})$ #(=1/(1+n))#
    - Operations : [x+y] (=min (x+y,1)), [x*y], [ [1-] x]
    - Relations : [x <= y], [x==y]
*)

Parameter U : Type.
Generalizable All Variables.
Declare Instance ordU: ord U.
Declare Instance cpoU: cpo U.
Bind Scope U_scope with U.
Delimit Scope U_scope with U.

Parameters Uplus Umult Udiv: U -> U -> U.
Parameter Uinv : U -> U.
Parameter Unth : nat -> U.


Infix "+" := Uplus : U_scope.
Infix "*"  := Umult  : U_scope.
Infix "/"  := Udiv  : U_scope.
Notation "[1-]  x" := (Uinv x)  (at level 35, right associativity) : U_scope.

Notation "[1/]1+ n" := (Unth n) (at level 35, right associativity) : U_scope.
Open Local Scope U_scope.

Definition U1 : U := [1-] 0. 
Notation "1" := U1 : U_scope.

(** ** Basic Properties *)

Axiom Udiff_0_1 : ~0 == 1.
(*
Axiom Unit : forall x:U, x <= 1. 
*)

Axiom Uplus_sym : forall x y:U, x + y == y + x.
Axiom Uplus_assoc : forall x y z:U, x + (y + z) == x + y + z.
Axiom Uplus_zero_left : forall x:U, 0 + x == x.

Axiom Umult_sym : forall x y:U, x * y == y * x.
Axiom Umult_assoc : forall x y z:U, x * (y * z) == x * y * z.
Axiom Umult_one_left : forall x:U, 1 * x == x.

Axiom Uinv_one : [1-] 1 == 0. 

(*
Axiom Uinv_opp_left : forall x, [1-] x + x == 1.
*)

Axiom Umult_div : forall x y, ~ 0 == y -> x <= y -> y * (x/y) == x.
Axiom Udiv_le_one : forall x y,  ~ 0 == y -> y <= x -> (x/y) == 1.
Axiom Udiv_by_zero : forall x y,  0 == y -> (x/y) == 0.

(** - Property  : [1 - (x + y) + x = 1 - y ] holds when [x+y] does not overflow *)
Axiom Uinv_plus_left : forall x y, y <= [1-] x -> [1-] (x + y) + x == [1-] y.

(** - Property  : [(x + y) * z  = x * z + y * z] holds when [x+y] does not overflow *)
Axiom Udistr_plus_right : forall x y z, x <= [1-] y -> (x + y) * z == x * z + y * z.

(** - Property  : [1 - (x  y) = (1 - x) * y + (1-y) ] *)
Axiom Udistr_inv_right : forall x y:U,  [1-] (x * y) == ([1-] x) * y + [1-] y.

(** - Totality of the order *)
Axiom Ule_class : forall x y : U, class (x <= y).

Axiom Ule_total : forall x y : U, orc (x <= y) (y <= x).
Implicit Arguments Ule_total [].

(** - The relation [x <=  y] is compatible with operators *)

Declare Instance Uplus_mon_right :forall x,monotonic (Uplus x).

(* Instance Uplus_mon_right : forall x, monotonic (Uplus x). *)

Declare Instance Umult_mon_right : forall x, monotonic (Umult x).
(* Instance Umult_mon_right : forall x, monotonic (Umult x). *)

Axiom Uinv_le_compat : forall x y:U, x <= y -> [1-] y <= [1-] x.

(** - Properties of simplification in case there is no overflow *)
Axiom Uplus_le_simpl_right : forall x y z, z <= [1-] x -> x + z <= y + z -> x <= y.

Axiom Umult_le_simpl_left : forall x y z: U, ~ 0 == z -> z * x <= z * y -> x <= y .

(** -  Property of [Unth]: [1 / n+1 == 1 - n  * (1/n+1)] *)
Axiom Unth_prop : forall n, [1/]1+n == [1-](compn Uplus 0 (fun k => [1/]1+n) n).

(** - Archimedian property *)
Axiom archimedian : forall x, ~0 == x -> exc (fun n => [1/]1+n <= x).

(** - Stability properties of lubs with respect to [+] and [*] *)

Axiom Uplus_right_continuous : forall k, continuous (mon (Uplus k)).
Axiom Umult_right_continuous : forall k, continuous (mon (Umult k)).


Hint Resolve Udiff_0_1 Unth_prop.
Hint Resolve Uplus_sym Uplus_assoc Umult_sym Umult_assoc.
Hint Resolve Uinv_one  Uinv_plus_left Umult_div Udiv_le_one Udiv_by_zero.
Hint Resolve Uplus_zero_left Umult_one_left Udistr_plus_right Udistr_inv_right.
Hint Resolve Uplus_mon_right Umult_mon_right Uinv_le_compat.
Hint Resolve lub_le le_lub Uplus_right_continuous Umult_right_continuous. 
(* lub_eq_mult lub_eq_plus_cte_left.*)
Hint Resolve Ule_total Ule_class.