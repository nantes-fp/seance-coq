
(***********************)
(**** Séminaire Coq ****)
(***********************)



(*** Premières définitions ***)

(** Définitions inductives : création de types **)
Inductive bool : Type :=
  | true : bool
  | false : bool.
(** Un élément de "bool" est :
 - soit true
 - soit false
Ainsi :
 - Tous les "bool" sont nécessairement de cette forme, et pas d'une autre
 - Tous les éléments de cette forme sont des "bool" **)

(** Définitions simples : création d'objets à partir de l'existant **)
Definition nope : bool :=
  false.

Check nope.
Compute nope.

Definition f_nope (b:bool) : bool :=
  false.

Check f_nope true.
Check f_nope false.
Check f_nope.
Compute f_nope true.

(** Pattern matching : déconstruction des objets **)
Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | false => b2
    | true => true
  end.



(*** Premières propositions ***)

Definition okay_1 : Prop := 1 < 2 + 3.
Definition okay_2 : Prop := andb true false = false.
Definition dumb_1 : Prop := 8 <= 5.
Definition dumb_2 : Prop := true <> true.

Check okay_1.
Check dumb_1.



(*** Premières preuves ***)

(** Preuve par simplification **)
Theorem test_unitaire_negb_true : negb true = false.
Proof.
  (* simpl = "Essaye d'appliquer les définitions" *)
  simpl.
  (* reflexivity = "Regarde ! C'est bien égal. Conclus." *)
  reflexivity.
Qed.

Theorem test_unitaire_negb_false : negb false = true.
Proof.
  simpl. reflexivity.
Qed.

(** Quantificateurs et preuve par introduction **)
Theorem test_negb_andb : forall b:bool, negb (andb false b) = true.
Proof.
  (* intros b = "Soit b un booléen" *)
  intros b.
  simpl. reflexivity.
Qed.

(** Quantificateurs et preuve par introduction **)
Theorem test_andb : exists b:bool, andb true b = false.
Proof.
  (* exists false = "Posons : b = false" *)
  exists false.
  simpl. reflexivity.
Qed.

(** Prédicats et preuves par réécriture **)
(** Symbole de l'implication : "->" **)
Theorem orb_true : forall b1 b2:bool, b1 = b2 -> orb b1 (negb b2) = orb b2 (negb b1).
Proof.
  intros b1 b2.
  (* Ici, intros H = "On suppose H" *)
  intros H.
  (* rewrite H  = "D'après l'hypothèse "H : X = Y", on peut remplacer tout X par Y" *)
  rewrite H.
  reflexivity.
Qed.

(** Application d'un théorème déjà montré **)
Theorem test_negb_andb_2 : forall b1 b2:bool, negb (andb false b1) = negb (andb false b2).
Proof.
  intros b1 b2.
  rewrite test_negb_andb.
  (* symmetry = "On retourne l'égalité" *)
  symmetry.
  (* apply H = "On conclut en appliquant H" *)
  apply test_negb_andb.
Qed.



(*** Types plus complexes ***)

(** Type paramétré : **)
Inductive option (X:Type) :=
  | None : option X
  | Some : X -> option X.

(** Type récursif : **)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Check nat.
Check nat_ind.

(** Type récursif et paramétré : les listes **)
Inductive list (X:Type) :=
  | nil : list X
  | cons : X -> list X -> list X.

Check list.
Check list_ind.

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].



(*** Définitions récursives ***)

(** Fonctions récursives (obligation de terminaison) **)

Fixpoint plus x y :=
  match x with
    | O => y
    | S x' => S (plus x' y)
  end.

(*(*( FIN DE LA SÉANCE 1 )*)*)

Fixpoint length {X:Type} (l:list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length t)
  end.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
  end.

(** Notations **)
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).



(*** Preuves plus complexes ***)

(** Preuve par analyse de cas **)
Theorem negb_involutive : forall b:bool, negb (negb b) = b.
Proof.
  intro b.
  (* destruct : "On considère chacun des cas possibles" *)
  destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

(** Preuve par inversion **)
Theorem S_eq : forall n m:nat, S n = S m -> n = m.
Proof.
  intros n m H.
  (* inversion : "Par égalité des constructeurs, on a égalité de leur contenu" *)
  inversion H. reflexivity.
Qed.

Theorem S_anything : O = S O -> true = false.
Proof.
  intros H.
  (* inversion : "Par inégalité des constructeurs, on a une contraduction." *)
  inversion H.
Qed.

(** Preuve par récurrence : récurrence et réécriture **)
Theorem app_singleton : forall X:Type, forall x:X, forall l:list X,
  length (app l [x]) = S (length l).
Proof.
  intros X x l.
  (* induction : "On le prouve par récurrence" *)
  induction l.
    simpl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.



(*** Démonstrations inspirées de [3], segment 5.7 ***)

Theorem nil_app : forall T:Type, forall l:list T, nil ++ l = l.
Proof.
  intros T l. simpl. reflexivity.
Qed.

Theorem app_nil : forall T:Type, forall l:list T, l ++ nil = l.
Proof.
  intros T l. induction l.
    simpl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_associative : forall T:Type, forall l1 l2 l3: list T,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros T l1 l2 l3.
  induction l1 as [ | h1 t1].
    simpl. reflexivity.
    simpl. rewrite IHt1. reflexivity.
Qed.

(*** Démonstrations inspirées de [3], segment 5.8 ***)

Fixpoint rev {T:Type} (l:list T) : list T :=
  match l with
    | nil => nil
    | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint map {T:Type} (f: T -> T) (l:list T) : list T :=
  match l with
    | nil => nil
    | cons h t => cons (f h) (map f t)
  end.

Theorem rev_involutive : forall T:Type, forall l:list T,
  rev (rev l) = l.
Proof.
  intros T l. induction l.
    simpl. reflexivity.
    simpl.
    (* remember X as Y : "Notons Y l'expression X" *)
    remember (rev l) as revl.
    rewrite <- IHl.
    (* assert : "Montrons le résultat intermédiaire suivant : ..." *)
    assert (H: forall rl:list T, rev (rl ++ [x]) = x :: rev rl).
      intros rl. induction rl.
        simpl. reflexivity.
        simpl. rewrite IHrl. simpl. reflexivity.
    apply H.
Qed.

Theorem map_lineaire : forall T:Type, forall l1 l2:list T, forall f:T -> T,
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros T l1 l2 f. induction l1.
    simpl. reflexivity.
    simpl. rewrite IHl1. reflexivity.
Qed.



(*** Un dernier mot sur Curry-Howard ***)

Check test_unitaire_negb_true.
Print test_unitaire_negb_true.

Check eq_refl.
Print eq_refl.

Check map_lineaire.
Compute map_lineaire.
Print map_lineaire.

Inductive True := I.
Inductive False := .



(*** Exercices supplémentaires : ***)
(** Propriété de la factorielle, cf. [3], segment 5.7 **)
(** Arbres d'entiers, cf. [3], segment 7.1 **)



(*
Crédits : Maxime Folschette

Séminaire d'introduction à Coq [1]

Cours largement inspiré de l'excellent tutoriel
Software Foundations de Benjamin C. Pierce [2]

Certaines preuves sont retranscrites du cours
Functional Programming Principles in Scala
de Martin Odersky, disponible sur Coursera [3]

Autre ressource pour apprendre à utiliser Coq : [4]

[1] http://coq.inria.fr/
[2] http://www.cis.upenn.edu/~bcpierce/sf/
[3] https://www.coursera.org/course/progfun
[4] http://www.labri.fr/perso/casteran/CoqArt/index.html

Licence : Beerware, réutilisation encouragée
*)
