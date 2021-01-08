/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/
import order.bounded_lattice

/- Multi-agent propositional modal logic-/
import modal_logic

open classical
variable {wo : Type}                         -- type of worlds            
variable {indiv : Type}                      -- type of individuals
variable r : indiv → wo → wo → Prop
variable rr : wo → wo → Prop
variables v w : wo
variables φ ψ γ : wo → Prop
variables i j : indiv 
variable A : wo → Prop 

def RB (i : indiv) (φ : wo → Prop) : wo → Prop := 
  λw, ∀v, r i w v → φ v

def Ind (i : indiv) (φ : wo → Prop) (ψ : wo → Prop) : wo → Prop := 
  λw, R r i φ w ∧ (φ w → ψ w) 

def RBg : wo → Prop :=
  λw, ∀i, RB r i φ w

#check @R
#check @Ind
#check @Rg

def rr {r : indiv → wo → wo → Prop} : Prop := ∃i, r i w v 
#check @rr
lemma rr_eq : rr w v = ∃i, r i w v :=
begin
sorry
end

/-
inductive trcl (r : indiv → wo → wo → Prop) : wo → wo → Prop
| base (w v : wo )    : (∃i, r i w v) → trcl w v
| trans (w v u : wo ) : trcl w v → (∃i, r i v u) → trcl w u

inductive trcl₁ (rr : wo → wo → Prop) : wo → wo → Prop
| base (w v : wo )    : rr w v → trcl₁ w v
| trans (w v u : wo ) : trcl₁ w v → rr v u → trcl₁ w u
-/

inductive reachable (rr : wo → wo → Prop) : ℕ → wo → wo → Prop
| one (w v : wo)               : rr w v → reachable 0 w v
| succ (n : ℕ) (w v u : wo)    : reachable n w u → rr u v → reachable (n+1) w v

def CRBg (φ : wo → Prop) : wo → Prop :=
  λw, ∀v, trcl r w v → φ v
#check @CRBg

def CRBg₁ (φ : wo → Prop) : wo → Prop :=
  λw, ∀v, (∃n, reachable rr n w v) → φ v
#check @CRBg₁ 

lemma  B1 : ∀w, R r i φ w → R r i (φ →ₘ ψ) w → R r i ψ w :=
begin
intros v h1 h2 u h3,
rw R at *,
have h4 : φ u, from h1 u h3,
have h5 : (φ →ₘ ψ) u, from h2 u h3,
exact h5 h4,
end

lemma B2 : ∀w, R r i φ w → (φ →ₘ ψ) w → Ind r i φ ψ w :=
begin
intros w h1 h2,
rw Ind,
split,
{ assumption  },
{ intro h3,
  rw imp at h2,
  exact h2 h3 }
end

#lint

lemma B3 : ∀w, R r i φ w → Ind r i φ ψ w → R r i ψ w :=
begin
intros w h1 h2,
intros v h3,
rw Ind at h2,
rw R at h1,
have h4 : φ v, from h1 v h3,
sorry
end

lemma B4 : ∀w, Ind r i φ γ w → Ind r i γ ψ w → Ind r i φ ψ w :=
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
rw valid at *,
intro w,
exact h2 w (h1 w)
end

lemma B6 {i : indiv} : (⊢ φ) → (⊢ R r i φ) := 
begin
intros h1 u,
rw R,
intros v hv,
exact h1 v
end

--axiom B7 : ⊢ (R r i φ →ₘ R r i (R r i φ))
--axiom B8 : ⊢ (R r i φ →ₘ ¬ₘ (R r i (¬ₘ φ))

#lint

axiom B10α  : ⊢ (CRg r φ →ₘ Rg r (φ ∧ₘ CRg r φ) :=
begin

end

lemma B11α  : (⊢ φ →ₘ RBg r (φ ∧ₘ ψ)) → (⊢ (φ →ₘ CRBg r ψ)) :=
begin
intros h1 w h2 v hv,
have hh : φ v ∧ ψ v :=
begin
rw imp at h1,
--simp * at h1,
have h3 : RBg r (φ ∧ₘ ψ) w, from h1 w h2,
--rw RBg at h3,
--clear h1,
induction hv,
{   rename hv_w w,
    rename hv_v v,
    cases hv_ᾰ with i,
    have h4 : RB r i (φ ∧ₘ ψ) w, from h3 i,
    rw RB at h4,
    have h5 : (φ ∧ₘ ψ) v, from h4 v hv_ᾰ_h,
    rw conj at h5,
    assumption },
{   rename hv_w w,
    rename hv_v v,
    rename hv_u u,
    cases hv_ᾰ_1 with k,
    have h6 : RB r k (φ ∧ₘ ψ) w, from h3 k,
    --clear h3,
    rw conj at h6,
    rw RB at h6,
    have h7 : (∀ (i : indiv), R r i (φ ∧ₘ ψ) w) → (φ v ∧ ψ v), by exact hv_ih h2,
    --rw Rg at h3,
    have h8 : φ v ∧ ψ v, by exact h7 h3,
    have h9 : φ v, by exact h8.1,
    have h10 : RBg r (φ ∧ₘ ψ) v, by exact h1 v h9,
    --rw Rg at h10,
    have h11 : RB r k (φ ∧ₘ ψ) v, by exact h10 k,
    --rw R at h11,
    exact h11 u hv_ᾰ_1_h    }
end,
exact hh.2,
end

axiom C1 : ⊢ R r i A
axiom C2 : ⊢ Ind r i A (R r j A)
axiom C3 : ⊢ Ind r i A φ

axiom C4 : ∀p, ⊢ (Ind r i A p →ₘ R r i (Ind r j A p))

axiom A1 : ∀p, ⊢ (Ind r i A p →ₘ R r i A →ₘ R r i p)

axiom A6 : ∀p, ⊢ (Ind r i A (R r j A) →ₘ R r i (Ind r j A p) →ₘ Ind r i A (R r j p))

lemma lewis_s 
(h1 : RBg r φ w) 
(h2 : Ind r i (RBg r φ) (RBg r (RBg r φ)) w)
(h3 : Ind r i (RBg r φ) (RBg r ψ) w) : 
  CRBg r ψ w :=
begin
rw CRBg,
intros v hv,
rw Ind at *,
induction hv with s t ih,
{   have h3 : RBg r φ s → RBg r ψ s, from h3.2,
    have h4 : RBg r ψ s, from h3 h1,
    rw RBg at h4,
    cases ih with j ihh,
    have h5 : RB r j ψ s, from h4 j,
    exact h5 t ihh  },
{   rename hv_u u,
    rename hv_w w,
    rename hv_v v,
    cases hv_ᾰ_1 with j,
    have h6 : RB r i (RBg r φ) w ∧ (RBg r φ w → RBg r (RBg r φ) w) → RB r i (RBg r φ) w ∧ (RBg r φ w → RBg r ψ w) → ψ v := by exact hv_ih h1,
    have h7 : RB r i (RBg r φ) w ∧ (RBg r φ w → RBg r ψ w) → ψ v := by exact h6 h2,
    have h8 : ψ v, by exact h7 h3,
    exact sorry },
end


lemma lewis_s₁ 
(h1 : RBg r φ w) 
(h2 : Ind r i (RBg r φ) (RBg r (RBg r φ)) w)
(h3 : Ind r i (RBg r φ) (RBg r ψ) w) : 
  CRBg₁ rr ψ w :=
begin
rw CRBg₁,
intros v hv,
cases hv with n,
induction n,
{ --rw RBg at h1,
  rw Ind at *,
  have h1 : RBg r ψ w, from h3.2 h1,
  --have h2 : ∃i, r i w v, from exact t,
  --exact h1 t,
    sorry  },
{   sorry },

end

#lint
#list_unused_decls

