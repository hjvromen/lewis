/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import modal_logic_multi_agent

variable {indiv : Type}
variable {f : m_frame indiv}
variables {s t u v : f.wo}
variables {A φ ψ γ : f.wo → Prop}
variables i j i1 i2 : indiv 

/- Sillari's theory has to represent the two central concepts of Lewis' theory
   of common knowledge. The first one, reason to believe, is captured by the 
   operator R that is defined in the file modal_logic_multi_agent.
   The second one, indication, is defined as follows. -/

/-- Indication is defined in terms of Reason-to-believe and implication -/
def Ind (i : indiv) (φ : f.wo → Prop) (ψ : f.wo → Prop) : f.wo → Prop := 
  λw, R i φ w ∧ (φ w → ψ w) 

/-- this property expresses that a frame has at least three worlds -/
def three_worlds : f.wo → f.wo → f.wo → Prop :=
  λw1 w2 w3, w2 ≠ w1 ∧ w2 ≠ w3 ∧ w3 ≠ w1

/-- this property expresses that a frame has at least two worlds -/
def two_worlds : f.wo → f.wo → Prop :=
  λw1 w2, w1 ≠ w2

/-- this property expresses that there are exactly two individuals -/
def two_agents : indiv → indiv → Prop :=
  λi1 i2, i1 ≠ i2 ∧ ∀i, i = i1 ∨ i = i2

/-- this property expresses that there is exactly one individual -/
def one_agent : indiv → Prop :=
  λi1, ∀i, i = i1

/-- Sillari mixes a proof-theoretic account with eleven axioms B1 - B8 and 
    B10 - B11 and a semantic account with his modal definitions of R and Ind.
    We prove that all but three of the axioms can be derived as lemmas from the 
    definitions of R and Ind. 
    Axiom B3 contradicts the definitions: we provide a counterexample.
    Axioms B7 and B8 will not be discussed because they play no role in Sillari's
    argument. -/

lemma  B1 : ∀w, R i φ w → R i (φ →ₘ ψ) w → R i ψ w :=
begin
intros v h1 h2 u h3,
rw R at *,
have h4 : φ u, from h1 u h3,
have h5 : (φ →ₘ ψ) u, from h2 u h3,
exact h5 h4,
end


lemma B2 : ∀w, R i φ w → (φ →ₘ ψ) w → Ind i φ ψ w :=
begin
intros w h1 h2,
rw Ind,
split,
{ assumption  },
{ intro h3,
  rw m_imp at h2,
  exact h2 h3 }
end


/-- Lemma B3 states: ∀w, R r i φ w → Ind r i φ ψ w → R r i ψ w.
    This is not true, as we will show by a counterexample, a model with two worlds.
    that is problematic for Sillari because he needs this axiom in his proof of 
    Lewis' theorem.
    B3 is the same as Lewis' A1 -/

lemma B3_fails 
(h1 : two_worlds s t)
(h2a : ¬ f.r i s s) (h2b : f.r i s t):
    ¬ (∀w (φ ψ : f.wo → Prop), R i φ w → Ind i φ ψ w → R i ψ w) :=
begin
let ψ := λw : f.wo, w ≠ t,
let φ := λw : f.wo, w ≠ s,
push_neg,
have h4 : R i φ s := by tidy,
have h5 : Ind i φ ψ s := by tidy,
have h6 : ¬ R i ψ s := by simp [R]; exact h2b,
use [s, φ, ψ],
exact and.intro h4 (and.intro h5 h6),
end


lemma B4 : ∀w, Ind i φ γ w → Ind i γ ψ w → Ind i φ ψ w :=
begin
intros w h1 h2,
rw Ind at *,
split,
{ exact h1.1 },
{ have h4 : φ w → γ w, from h1.2,
  have h5 : γ w → ψ w, from h2.2,
  intro hw,
  exact h5 (h4 hw)  }
end


lemma B5 : (⊢ φ) → (⊢ (φ →ₘ ψ)) → (⊢ ψ) :=
begin
intros h1 h2,
rw m_valid at *,
intro w,
exact h2 w (h1 w)
end


lemma B6 {i : indiv} : (⊢ φ) → (⊢ R i φ) := 
begin
intros h1 u,
rw R,
intros v hv,
exact h1 v
end


/-- Sillari also states axioms B7 (positive introspection) and B8 (negative     
    introspection), but he does not use these axioms, and they do not follow from 
    the semantics.
    Axiom B7 : ⊢ (R r i φ →ₘ R r i (R r i φ))
    Axiom B8 : ⊢ (R r i φ →ₘ ¬ₘ (R r i (¬ₘ φ))
    These axioms would imply that the relations of the frame are transitive and 
    serial. -/

lemma B10 : ⊢ CRg φ →ₘ Rg (φ ∧ₘ CRg φ) :=
begin
intros w h1,
have h2 : CRg φ w ↔ Rg (φ ∧ₘ CRg φ) w := fixed_point_theorem φ w,
exact iff.elim_left h2 h1,
end


lemma B11 : (⊢ φ →ₘ Rg (φ ∧ₘ ψ)) → (⊢ (φ →ₘ CRg ψ)) := induction_rule φ ψ 


/-- Cubitt and Sugden's axiom C4 fails. This proves that Sillari's formalisation does not match 
    the account of common knowledge that Lewis gave. -/

lemma C4_fails (h1 : two_worlds s t) (h2a : ¬ f.r i s s) (h2b : f.r i s t) :
    ¬ ∀w (φ ψ : f.wo → Prop), (Ind i φ ψ w → R i (Ind j φ ψ) w) :=
begin
let φ := λw : f.wo, true,
let ψ := λw : f.wo, w = s,
push_neg,
have h3 : Ind i φ ψ s := by tidy,
have h3a : ¬ R i (Ind j φ ψ) s := 
  begin
  simp [R, Ind],
  use t,
  --simp [two_worlds] at h1,
  have h3b : ¬ ψ t := by finish,
  exact and.intro h2b h3b,
  end,
use [s, φ, ψ],
finish,
end

/- Now we discuss Sillari's proof of Lewis' theorem. It is not clear how to
   interpret his proof. Therefore, two options are presented. The first option makes
   it impossible to find a proof. The second option gives a valid proof, but 
   the proof is trivial and thus useless. -/

/-- option 1 : C1 - C3 are only assumed at the world for which the theorem has to 
    hold. First, we provide a counterexample with one agent and a frame with three 
    worlds. In this counterexample, the frame is nor transitive nor serial. -/

lemma Lewis_fails_1i
(h1 : three_worlds s u v)
(h2 : one_agent i1)
(h3 : f.r = λi1 w1 w2, (w1 = s ∧ w2 = u) ∨ (w1 = u ∧ w2 = v))
: ¬ ∀ i (φ ψ : f.wo → Prop), R i1 φ s → Ind i (R i1 φ) (R i1 (R i1 φ)) s → Ind i1 (R i1 φ) (R i1 ψ) s → CRg ψ s :=
begin
let φ := λw, w ≠ s,
let ψ := λw, w = u,
push_neg,
use [i1, φ, ψ],
rw three_worlds at h1,
rw one_agent at h2,
have h4 : R i1 φ s := 
  begin
    rw R,
    intros w hw,
    have h4a : w = u := by finish,
    rw h4a,
    have h4b : u ≠ s := h1.1,
    assumption,
  end,
have h5 : R i1 (R i1 φ) s :=
  begin
  rw R,
  intros w hw,
  rw R,
  intros x hx,
  have h5a : w = u := by finish,
  have h5b : x = v := by finish,
  have h5c : v ≠ s := (h1.2).2,
  rw h5b,
  assumption,
  end,
have h6 : Ind i1 (R i1 φ) (R i1 (R i1 φ)) s := 
  begin
    rw Ind,
    simp *,
  end,
have h7 : Ind i1 (R i1 φ) (R i1 ψ) s :=
  begin
  rw Ind,
  --simp *,
  --rw R,
  --intros w hw,
  finish,
  end,
have h8 : ¬ CRg ψ s :=
  begin
    rw CRg,
    push_neg,
    use v,
    split,
    { have h8a : connected s u := 
        begin
          rw connected,
          use i1,
          finish,
        end,
      have h8b : connected u v := 
      begin
          rw connected,
          use i1,
          finish,
        end,
      exact trcl.trans h8a (trcl.base h8b) },
    { intro h8c,
      have h8d : u ≠ v := (h1.2).1,
      show false, from h8d (eq.symm h8c)   },
  end,
finish,
end

/-- In case we accept axioms B7 and B8, we have to provide a counterexample with a 
    frame that is transitive and serial. That is possible: -/
lemma Lewis_fails_2i
(h1 : three_worlds s u v)
(h2 : two_agents i1 i2)
(h3 : f.r = λi w1 w2, (i = i1 ∧ w1 = s ∧ w2 = u) ∨ (i = i1 ∧ w1 = u ∧ w2 = u) 
∨ (w1 = v ∧ w2 = v) ∨ (i = i2 ∧ w1 = s ∧ w2 = s) ∨ (i = i2 ∧ w1 = u ∧ w2 = v))
: ¬ ∀ i (φ ψ : f.wo → Prop), Rg φ s → Ind i (Rg φ) (Rg (Rg φ)) s → Ind i (Rg φ) (Rg ψ) s → CRg ψ s :=
begin
rw two_agents at h2,
rw three_worlds at h1,
let φ := λw, true,
let ψ := λw, w ≠ v,
push_neg,
use [i1, φ, ψ],
have h4 : Rg φ s :=
  begin
    rw Rg,
    intro i,
    have h4a : i = i1 ∨ i = i2 := h2.right i,
    --rw R,
    cases' h4a; finish,
  end,
have h43 : Rg (Rg φ) s :=
  begin
  rw Rg,
  intro i,
  have h4a : i = i1 ∨ i = i2 := h2.right i,
  cases' h4a; finish,
  end,
have h5 : Ind i1 (Rg φ) (Rg (Rg φ)) s :=
  begin
    rw Ind,
    split,
    { exact h43 i1  },
    { intro h; exact h43},
  end,
have h6 : Ind i1 (Rg φ) (Rg ψ) s :=
  begin
  rw Ind,
  split,
  { exact h43 i1 },
  { simp [h4],
    rw Rg,
    intro i,
    have h4a : i = i1 ∨ i = i2 := h2.right i,
    cases' h4a,
      repeat { rw h,
        rw R,
        simp *,
        finish, },
  },
  end,
have h7 : ¬ CRg ψ s :=
  begin
  rw CRg,
  push_neg,
  use v,
  simp,
  have h7a : connected s u := 
        begin
          rw connected,
          use i1,
          finish,
        end,
      have h7b : connected u v := 
      begin
          rw connected,
          use i2,
          finish,
        end,
      exact trcl.trans h7a (trcl.base h7b),
  end,
finish,
end


/-- option 2 : C1 - C3 are assumed to hold at each world
    Now, the proof is rather trivial -/
lemma lewis_s_2
(C1 : ∀w, Rg φ w) 
(C2 : ∀w, Ind i (Rg φ) (Rg (Rg φ)) w)
(C3 : ∀w, Ind i (Rg φ) (Rg ψ) w) : 
  CRg ψ s :=
begin
intros v hv,
induction' hv with s u ih,
{   have h4 : Rg ψ s := (C3 s).2 (C1 s),
    cases ih with j ihh,
    exact (h4 j) u ihh  },
{   exact ih i C1 C2 C3   },
end

