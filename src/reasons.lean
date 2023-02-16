/-
Copyright (c) 2022 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import data.list.basic

/-- Type for individuals -/
variable {indiv : Type}
variables {i j : indiv}

/-- Type for reasons to believe -/
variables {reason : Type} [has_mul reason]
variables {r s t : reason}

/-- These reasons will be used in the axioms for reasoning with reasons -/
constants {a b c : reason}

/-- A and φ are propositions that are used in the definition of a basis for common knowledge -/
constants {A φ : Prop}

variables {α β γ : Prop}

/-- `rb` is the property of being a reason for an individual to believe a 
    proposition -/
variable rb : reason → indiv → Prop → Prop

/-- R is defined as having `a` reason to believe a proposition -/
def R (i : indiv) (φ : Prop) : Prop := ∃r, rb r i φ 

/-- Indication is defined as having `a` reason to believe that φ implies ψ -/
def Ind (φ : Prop) (i : indiv) (ψ : Prop) : Prop := R rb i (φ → ψ)

/-- Our logic of reasons has the `application rule` as an axiom. This rule is
based on the justification logic of Artemov (2019). -/
axiom AR : rb s i (α → β ) → rb t i α → rb (s * t) i β

/-- The following axioms define a minimal logic of reasons -/
axiom T1 : rb a i (α → β → (α ∧ β))
axiom T2 : rb b i (((α → β ) ∧ ( β → γ )) → (α → γ ))
axiom T3 : rb c i (R rb j (α → β ) → (R rb j α → R rb j β ))

/-- This lemma is a direct consequence of the application rule `AR` -/
lemma E1 : R rb i (α → β) → R rb i α → R rb i β :=
begin
intros h1 h2,
rw R at *,
cases h1 with s hs,
cases h2 with t ht,
apply exists.intro (s * t),
exact AR rb hs ht,
end

/-- This lemma is needed for proving lemma (E2) -/
lemma L1 : R rb i α → R rb i β → R rb i (α ∧ β) := 
begin
intros h1 h2,
rw R at *,
cases h1 with s hs,
cases h2 with t ht,
have h3 : rb (a * s) i (β → (α ∧ β)) :=
  begin
  have h4 : rb a i (α → (β → (α ∧ β))) := T1 rb,
  exact AR rb h4 hs
  end,
apply exists.intro (a * s * t),
exact AR rb h3 ht,
end

/-- The lemmas (E2) and (E3) are needed for proving lemma (A6) -/
lemma E2 : R rb i (α → β ) → R rb i (β → γ ) → R rb i (α → γ ) :=
begin
intros h1 h2,
have h3 : R rb i ((α → β) ∧ (β → γ)) := L1 rb h1 h2,
cases h3 with s hs,
apply exists.intro (b * s),
exact AR rb (T2 rb) hs
end

lemma E3 : R rb i (R rb j (α → β )) → R rb i (R rb j α → R rb j β ) := 
begin
intros h1,
cases h1 with s hs,
apply exists.intro (c * s),
exact AR rb (T3 rb) hs
end

/-- (A1) follows immediately from the definition of indication and the application 
    rule. So it does not have to be taken as an axiom, like Cubitt and Sugden did. -/
lemma A1 : Ind rb A i α → R rb i A → R rb i α :=
begin
intros h1 h2,
rw Ind at h1,
rw R at *,
cases h2 with t ht,
cases h1 with s hs,
apply exists.intro (s * t),
exact AR rb hs ht
end

/-- Using (E1) provides a simpler proof -/
lemma A1_alternative_proof : Ind rb A i α → R rb i A → R rb i α :=
λ h1 h2, E1 rb h1 h2


/-- (A6) can be proven using lemmas (E2) and (E3). So it does not have to be taken 
    as an axiom anymore, like Cubitt and Sugden did. -/
lemma A6 : ∀α, Ind rb A i (R rb j A) → R rb i (Ind rb A j α) → Ind rb A i (R rb j α) := 
begin
intros p h1 h2,
rw Ind at *,
have h3: R rb i (R rb j A → R rb j p) := E3 rb h2,
have h4 : R rb i (A → R rb j p) := E2 rb h1 h3,
assumption
end 


/-- We are now at the point where we can prove Lewis' theorem -/
inductive G : Prop → Prop
| base                          : G φ 
| step (p : Prop) (i : indiv)   : G p → G (R rb i p)

lemma Lewis (p : Prop) 
(C1 : ∀i, R rb i A)
(C2 : ∀i j, Ind rb A i (R rb j A))
(C3 : ∀i, Ind rb A i φ)
(C4 : ∀α i j, Ind rb A i α → R rb i (Ind rb A j α))
(h7 : G rb p) : 
    ∀i, R rb i p :=
begin
intro i,
have h1 : Ind rb A i p :=
    begin
    induction h7 with u j hu ih,
{   exact C3 _ },
{   have h3 : R rb i (Ind rb A j u) := C4 u _ _ ih,
    have h4 : R rb i (Ind rb A j u) → Ind rb A i (R rb j u) := A6 rb u (C2 _ _),
    have h5 : Ind rb A i (R rb j u) := h4 h3,
    assumption }
    end,
exact A1 rb h1 (C1 _),
end

#lint
