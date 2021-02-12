/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import data.list.basic

/- outline of Lewis' theory of common knowledge (according to Cubitt and Sugden) -/

variable {indiv : Type}            -- type of individuals
variables {i j k : indiv}

/-- Reason-to-believe is a two-place relation between individuals and propositions -/
variable {R : indiv → Prop → Prop}

/-- Indication is a three-place relation between individuals and two propositions -/
constant Ind : Prop → indiv → Prop → Prop

/-- A and φ are propositions that are used in the definition of a basis for common knowledge -/
constants {A φ : Prop}
variable {p : Prop}

/-- These axioms define a basis for common knowledge -/
axiom C1 : R i A 
axiom C2 : Ind A i (R j A)
axiom C3 : Ind A i φ 

/-- This axiom represents that all individuals share inductive standards and background knowledge -/
axiom C4 : ∀p, Ind A i p → R i (Ind A j p)

/-- This is an alternative to axiom C4 -/
axiom C4_JvdD : ∀p, Ind A i p → Ind A i (Ind A j p)

/-- This axiom represents the meaning of indication -/
axiom A1 : ∀p, Ind A i p → R i A → R i p

/-- This axiom is an assumption that Cubitt and Sugden need in their proof. -/
axiom A6 : ∀p, (Ind A i (R j A) ∧ R i (Ind A j p)) → Ind A i (R j p)

/-- This is an alternative to axiom A6 -/
axiom A6_JvdD : ∀p, (Ind A i (R j A) ∧ Ind A i (Ind A j p) → Ind A i (R j p))

/-- The following lemmas are the first three steps in the proof of Lewis' theorem -/
lemma L1 : ∀i, R i φ := by intro i; exact A1 φ C3 C1

lemma L2 : ∀ i j, (R i (R j φ)) := 
begin
intros i j,
have h7 : ∀ j, R i (Ind A j φ) := by intro j; exact C4 φ C3,
have h8 : ∀ j, Ind A i (R j φ) := by intro j; exact A6 φ (and.intro C2 (h7 j)),
exact A1 (R j φ) (h8 j) C1
end

lemma L3 : ∀ i j k, (R i (R j (R k φ))) := 
begin
have h7 : ∀i j, R i (Ind A j φ) := by intros i j; exact C4 φ C3,
have h8 : ∀i j, Ind A i (R j φ) := by intros i j; exact A6 φ (and.intro C2 (h7 _ _)),
have h9 : ∀i j k, R i (Ind A j (R k φ)) := by intros i j k; exact C4 (R k φ) (h8 _ _),
have h10: ∀i j k, Ind A i (R j (R k φ)) := by intros i j k; exact A6 (R k φ) (and.intro (C2) (h9 _ _ _)), 
intros i j k,
exact A1 (R j (R k φ)) (h10 _ _ _) C1
end

/-- We could go on in this way, like Lewis and Cubitt and Sugden do. 
    The use of ... (and so on) is, however, unsatisfactory. 
    Therefore, we will show that a complete proof by induction is possible. -/

inductive G : Prop → Prop
| base                          : G φ 
| step (p : Prop) (i : indiv)   : G p → G (R i p)


theorem Lewis (p : Prop) {R : indiv → Prop → Prop} (h7 : @G indiv R p) : 
    ∀(i : indiv), R i p :=
begin
intro i,
have h1 : Ind A i p :=
    begin
    induction h7 with u j hu ih,
{   exact C3   },
{   have h3 : R i (Ind A j u) := C4 u ih,
    have h4 : Ind A i (R j u) := A6 u (and.intro C2 h3),
    assumption }
    end,
exact A1 p h1 C1
end

/-- alternative proof that uses C4_JvdD and A6_JvdD instead of C4 -/
theorem Lewis_JvdD (p : Prop) {R : indiv → Prop → Prop} (h7 : @G indiv R p) : 
    ∀(i : indiv), R i p :=
begin
intro i,
have h1 : Ind A i p :=
    begin
    induction h7 with u j hu ih,
{   exact C3   },
{   have h3a : Ind A i (Ind A j u) := C4_JvdD u ih,
    have h4 : Ind A i (R j u) := A6_JvdD u (and.intro C2 h3a),
    assumption }
    end,
exact A1 p h1 C1
end




