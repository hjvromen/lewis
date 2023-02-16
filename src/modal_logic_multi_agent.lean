/-
Copyright (c) 2022 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import data.finset.basic  
import tactic.induction

/- Multi-agent propositional modal logic-/

/-- indiv is the type of individuals -/
variable {indiv : Type}  

/-- a frame is a set of worlds with accessibility relations for each individual -/
structure m_frame (indiv : Type) := 
(wo : Type) (h1 : inhabited wo) (h2 : inhabited indiv) (r : indiv → wo → wo → Prop)

variable {f : m_frame indiv}
variables φ ψ : f.wo → Prop

/-- we define `implication`, `conjunction`, `negation` and `validity` for modal propositions 
   (that is, functions `wo → Prop`) -/
def m_imp (φ ψ : f.wo → Prop): f.wo → Prop := λw, φ w → ψ w
infixr ` ⟶ ` : 90 := m_imp

def m_neg (φ : f.wo → Prop) : f.wo → Prop := λw, ¬ φ w
notation ` ¬ₘ ` := m_neg

def m_conj (φ ψ : f.wo → Prop): f.wo → Prop := λw, φ w ∧ ψ w
infixr ` ∧ₘ ` : 90 := m_conj

def m_valid (φ : f.wo → Prop) : Prop := ∀w, φ w
notation `⊢ ` φ := m_valid φ                                   

/-- We define 'agent i has reason to believe φ' -/
def R (i : indiv) (φ : f.wo → Prop) : f.wo → Prop :=    
    λw, ∀v, f.r i w v → φ v

/-- We define 'all agents have reason to believe φ' -/
def Rg : f.wo → Prop :=                               
    λw, ∀i, R i φ w

/-- Two worlds are connected iff the second one is accessible from the first one for 
    some individual  -/
def connected (w v : f.wo) : Prop := ∃i, f.r i w v

/-- We define the transitive closure of r -/
inductive trcl (r : indiv → f.wo → f.wo → Prop) : f.wo → f.wo → Prop
| base {w v : f.wo }    : connected w v → trcl w v
| trans {w v u : f.wo } : connected w u → trcl u v → trcl w v

/-- We define 'common reason to believe φ' -/
def CRg (φ : f.wo → Prop) : f.wo → Prop :=              
    λw, ∀v, trcl f.r w v → φ v

-- Common reason to believe can be axiomatically characterized 

lemma fixed_point_theorem : ∀w, (CRg φ w) ↔ (Rg (φ ∧ₘ CRg φ)) w :=
-- the proof follows Fagin (1995, p. 36-37)
begin
intro s,
split,
{   intro h1,
    rw CRg at h1,
    rw Rg,
    intro i,
    rw R,
    intros u hu,
    simp [m_conj],
    have h2 : connected s u, by apply exists.intro i; assumption,
    split,
    { have h3 : trcl f.r s u := trcl.base h2,
      exact h1 u h3  },
    { rw CRg,
      intros t ht,
      have h4 : trcl f.r s t := trcl.trans h2 ht,
      exact h1 t h4 }   },
{   intros h2,
    rw CRg,
    intros v hv,
    cases' hv,
    {   cases' h with i hi,
        have h5 : R i (φ ∧ₘ CRg φ) s := h2 i,
        rw R at h5,
        have h6 : (φ ∧ₘ CRg φ) v := h5 v hi,
        exact h6.1   },
    {   cases' h with i hu,
        have h5 : R i (φ ∧ₘ CRg φ) s := h2 i,
        rw R at h5,
        have h6 : (φ ∧ₘ CRg φ) u := h5 u hu,
        have h7 : CRg φ u := h6.2,
        exact h7 v hv,   },   },
end


lemma induction_rule : (⊢ φ ⟶ Rg (φ ∧ₘ ψ)) → (⊢ (φ ⟶ CRg ψ)) :=
-- the proof follows Fagin (1995, p. 36-37)
begin
intros h1 s h2 v hv,
have hh : φ v ∧ ψ v :=
    begin
    --rw m_imp at h1,
    have h3 : Rg (φ ∧ₘ ψ) s, from h1 s h2,
    --rw Rg at h3,
    induction' hv with s u,
    {   cases h with k hk,
        have h4 : R k (φ ∧ₘ ψ) s, from h3 k,
        --rw R at h4,
        have h5 : (φ ∧ₘ ψ) u, from h4 u hk,
        --rw m_conj at h5,
        assumption, },
    {   cases' h with k hk,
        have h6 : R k (φ ∧ₘ ψ) s, from h3 k,
        --rw m_conj at h6,
        --rw R at h6,
        have h12 : φ u := (h6 u hk).1,
        have h13 : Rg (φ ∧ₘ ψ) u := h1 u h12,
        have h7 : Rg (φ ∧ₘ ψ) u → (φ v ∧ ψ v) := ih φ ψ h1 h12,
        exact h7 h13,    },
    end,
exact hh.2,
end

