/-
Copyright (c) 2022 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import data.list.basic

/- outline of Lewis' theory of common knowledge (according to Cubitt and Sugden) -/

variable {indiv : Type}            -- type of individuals
variables {i j k : indiv}

/-- Reason-to-believe is a two-place relation between individuals and propositions -/
variable {R : indiv → Prop → Prop}

/-- Indication is a three-place relation between individuals and two propositions -/
variable {Ind : Prop → indiv → Prop → Prop}

/-- A and φ are propositions that are used in the definition of a basis for common knowledge -/
constants {A φ : Prop}
--variable {p : Prop}

/-- These axioms define a basis for common knowledge -/
--axiom C1 : R i A
--axiom C2 : Ind A i (R j A)
--axiom C3 : Ind A i φ 

-- This axiom represents that all individuals share inductive standards and background knowledge
axiom C4 : ∀p, Ind A i p → R i (Ind A j p)

/-- This axiom represents the meaning of indication -/
axiom A1 : ∀p, Ind A i p → R i A → R i p

/-- This axiom is an assumption that Cubitt and Sugden need in their proof. -/
axiom A6 : ∀p, (Ind A i (R j A) ∧ R i (Ind A j p)) → Ind A i (R j p)

/-- The following lemmas are the first three steps in the proof of Lewis' theorem -/
lemma L1 
(C1 : ∀ i : indiv, R i A)
(C2 : ∀ i j : indiv, Ind A i (R j A))
(C3 : ∀i : indiv, Ind A i φ)
: ∀i, R i φ := by intro i; exact A1 φ (C3 _) (C1 _)

lemma L2 
(C1 : ∀i, R i A)
(C2 : ∀i j : indiv, Ind A i (R j A))
(C3 : ∀i : indiv, Ind A i φ)
: ∀ i j, (R i (R j φ)) := 
begin
intros i1 i2,
have h7 : R i1 (Ind A i2 φ) := by exact C4 φ (C3 _),
have h8 : Ind A i1 (R i2 φ) := by exact A6 φ (and.intro (C2 _ _) h7),
exact A1 (R i2 φ) h8 (C1 _)
end

lemma L3 
(C1 : ∀i, R i A)
(C2 : ∀i j : indiv, Ind A i (R j A))
(C3 : ∀i : indiv, Ind A i φ)
: ∀ i j k, (R i (R j (R k φ))) := 
begin
    intros i₁ i₂ i₃,
    have h7 : R i₁ (Ind A i₃ φ) := by exact C4 φ (C3 _),
    have h8 : Ind A i₁ (R i₃ φ) := by exact A6 φ (and.intro (C2 _ _) h7),
    have h9 : R i₁ (Ind A i₂ (R i₃ φ)) := by exact C4 (R _ φ) h8,
    have h10: Ind A i₁ (R i₂ (R i₃ φ)) := by exact A6 (R _ φ) (and.intro (C2 _ _) h9), 
    exact A1 (R i₂ (R i₃ φ)) h10 (C1 _),
end

/-- We could go on in this way, like Lewis and Cubitt and Sugden do. 
    The use of ... (and so on) is, however, unsatisfactory. 
    Therefore, we will show that a complete proof by induction is possible. -/

inductive G : Prop → Prop
| base                          : G φ 
| step (p : Prop) (i : indiv)   : G p → G (R i p)


theorem Lewis (p : Prop) {R : indiv → Prop → Prop} 
(h7 : @G indiv R p) 
(C1 : ∀i, R i A)
(C2 : ∀i j : indiv, Ind A i (R j A))
(C3 : ∀i : indiv, Ind A i φ)
: ∀(i : indiv), R i p :=
begin
intro i,
have h1 : Ind A i p :=
    begin
    induction h7 with u j hu ih,
{   exact C3 _ },
{   have h3 : R i (Ind A j u) := C4 u ih,
    have h4 : Ind A i (R j u) := A6 u (and.intro (C2 _ _) h3),
    assumption }
    end,
exact A1 p h1 (C1 _)
end




