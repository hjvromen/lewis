/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import data.finset.basic  
import data.list.basic
import order.bounded_lattice

/- Modal propositional logic -/

/- First, we define some properties of relations that we will need later on -/

variable {α : Type} 

--def reflexive (r: α → α → Prop) : Prop := ∀a, r a a 
--def symmetric (r: α → α → Prop) : Prop := ∀a b , r a b → r b a 
--def transitive (r: α → α → Prop) : Prop := ∀a b c , r a b → r b c → r a c
def euclidean (r: α → α → Prop) : Prop := ∀a b c, r a b → r a c → r b c
def serial (r: α → α → Prop) : Prop := ∀a, ∃b, r a b 
def confluence (r: α → α → Prop) : Prop := ∀a b c, r a b ∧ r a c → ∃d, r b d ∧ r c d

-- see Pacuit p.12 for more

/- We start by defining a frame: a type of "possible worlds" with a relation on this type. -/

variable {wo : Type}                         -- type of worlds            
--variable [has_zero wo]                

variable r : wo → wo → Prop

/- we will study functions `wo → Prop` (modal propositions)
   we define `implication` and `negation` and `validity` for modal propositions 
   and `normality` for functions from modal propositions to modal propositions -/

def imp (φ ψ : wo → Prop): wo → Prop := λw, φ w → ψ w
infixr ` →ₘ ` : 90 := imp

def neg (φ : wo → Prop) : wo → Prop := λw, ¬ φ w
notation ` ¬ₘ ` := neg

def conj (φ ψ : wo → Prop): wo → Prop := λw, φ w ∧ ψ w
infixr ` ∧ₘ ` : 90 := conj

def disj (φ ψ : wo → Prop): wo → Prop := λw, φ w ∨ ψ w
infixr ` ∨ₘ ` : 90 := disj

def valid (φ : wo → Prop) : Prop := ∀w, φ w
notation `⊢ ` φ := valid φ                                   

#check ⊢ (λx : wo, false)

/- we define two functions from modal propositions to modal propositions -/

def box (φ : wo → Prop) : wo → Prop := 
λw, ∀v, r w v → φ v                       

#check @box

def diamond (φ : wo → Prop) : wo → Prop := 
λw, ∃v, r w v ∧ φ v                       
            
--variable {r}
--local notation `□ᵣ` := @box _ r
--local notation `◇ᵣ` := @diamond _ r
--variable (r)  

notation `□` := box
notation `◇` := diamond


/- we define some propositions, the second one is called B after Brouwer -/
def T : Prop := 
∀φ, ⊢ □r φ →ₘ φ

#check @T

def B : Prop := ∀φ w, ◇r (□r φ) w → φ w        
#check @B

def D : Prop := ∀φ w, □r φ w → ◇r φ w

def IV : Prop := ∀φ w, □r φ w → □r (□r φ) w

/- V is equivalent to negative introspection (¬ □ ⟶ □ ¬ □   -/
def V : Prop  := ∀φ w, ◇ r φ w → □r (◇r φ) w

def BDDB : Prop := ∀φ w, ◇r (□r φ) w → □r (◇r φ) w


/- interdefinability of □ and ◇ -/

lemma neg_neg₁ {φ : wo → Prop} :  ¬ₘ (¬ₘ φ) = φ :=
by repeat {rw neg}; simp *

lemma not_box_diamond_not {φ : wo → Prop} : 
    ¬ₘ (□r φ) = ◇r (¬ₘ φ) := by simp [box, diamond, neg]

lemma not_diamond_box_not {φ : wo → Prop} : 
    ¬ₘ (◇r φ) = □r (¬ₘ φ) := by simp [box, diamond, neg]

lemma box_from_diamond {φ : wo → Prop} : 
    □r φ = ¬ₘ (◇r (¬ₘ φ)) :=
begin
simp [not_diamond_box_not],
rw [neg_neg₁]
end

lemma dimaond_from_box {φ : wo → Prop} : 
    ∀w, ◇r φ w = ¬ₘ (□r (¬ₘ φ)) w :=
begin
intro w,
simp [not_box_diamond_not],
rw neg_neg₁ 
end

/- `box` obeys the so-called normal modal axioms K and Nec -/

lemma K {φ ψ: wo → Prop} : 
    ⊢ □r (φ →ₘ ψ) →ₘ □r φ →ₘ □r ψ :=
begin
intros w h1 h2 v hr,
have h3 : (φ →ₘ ψ) v := by exact h1 v hr,
have h4 : φ v := by exact h2 v hr,
exact h3 h4
end


lemma Nec {φ : wo → Prop} : 
    (⊢ φ) → ⊢ □r φ := 
begin
intros h1 w v h2,
exact h1 v    
end


lemma C₁ {φ ψ : wo → Prop} :
    ⊢ □r (φ ∧ₘ ψ) →ₘ (□r φ ∧ₘ □r ψ) :=
begin
intros w h1,
--rw conj,
--rw box at *,
--simp *,
split,
{   intros v hv,
    have h2 : (φ ∧ₘ ψ) v, from h1 v hv,
    --rw conj at h2,
    exact h2.1   },
{   intros v hv,
    have h2 : (φ ∧ₘ ψ) v, from h1 v hv,
    --rw conj at h2,
    exact h2.2    }
end


lemma C₂ {φ ψ : wo → Prop} :
    ⊢ (□r φ ∧ₘ □r ψ) →ₘ □r (φ ∧ₘ ψ) :=
begin
intros w h1,
rw conj at h1,
rw box,
intros v hr,
rw conj,
--simp [box] at h1,
exact and.intro (h1.1 v hr) (h1.2 v hr)
end
 

/- relations betwen the validity of formulas and properties of frames,
   equivalence lemma's (Sahlquist formulas) -/

lemma T_eq_refl : (reflexive r) ↔ T r:=
begin
apply iff.intro,
{   intro hr,
    rw T,
    intros φ w,
    intro hw,
    rw box at hw,
    rw reflexive at hr,
    finish},
{   intro hT,
    rw reflexive,
    simp [T, imp] at hT,
    intro w₀,
    let φ : wo → Prop := (λw, w ≠ w₀),
    apply by_contradiction,
    intro hn,
    have h2 : box r φ w₀ := by finish,
    have h3 : φ w₀ := by exact hT φ w₀ h2,
    finish }
end

#check @T_eq_refl 
#check @reflexive
#check @T

lemma IV_eq_trans : transitive r ↔ IV r:=
begin
split,
{   intro hr,
    rw IV,
    intros φ w h1,
    rw box,
    intros v hv,
    --rw box,
    intros u h2,
    --rw transitive at hr,
    have h3 : r w u := by exact hr _ _ _ hv h2,
    exact h1 _ h3  },
{   intro hIV,
    --rw transitive,
    intros a b c hab hbc,
    rw IV at hIV,
    let φ : wo → Prop := (λw, r a w ),
    have h2 : box r φ a := by finish,
    have h3 : box r (box r φ) a := by exact hIV φ a h2,
    have h4 : φ b := by finish,
    --rw box at h3,
    have h5 : box r φ b := by exact h3 b hab,
    have h6 : φ c := by exact h5 c hbc,
    finish  }
end

lemma B_eq_symm : symmetric r ↔ B r:=             --Gamut p. 301
begin
split,
{   intro hs,
    rw B,
    intros φ w h1,
    rw diamond at h1,
    cases h1 with v h2,
    rw symmetric at hs,
    have h3 : r v w := by exact hs w v (h2.1),
    exact h2.2 w h3},
{   intros hB,
    rw symmetric,
    intros a b hab,
    let φ := (λw, r b w),
    have h1 : box r φ b := by tidy,
    have h2 : diamond r (box r φ) a := by tidy,
    rw B at hB,
    have h3 : φ a := by exact hB φ a h2,
    finish  }
end

lemma V_eq_euclidean : euclidean r ↔ V r:=        
begin                                                                   --Uckelmann p.176
split,                                                                  --OLP
{   intros hE φ w hn,
    rw box,
    intros v hv,
    rw euclidean at hE,
    simp [diamond] at hn,
    cases hn with u hu,
    apply exists.intro u,
    apply and.intro (hE w v u hv (and.elim_left hu)) (and.elim_right hu)    },
{   --haveI := classical.prop_decidable,
    intros hV w u v hwu hwv,
    by_contra hne,
    let φ := (λz, ¬ r u z),
    have h1 : φ v := by tidy,
    have h2 : diamond r φ w := 
        begin
        simp [diamond],
        apply exists.intro v,
        apply and.intro hwv h1
        end,
    have h3 : ¬ diamond r φ u := by tidy,
    have h4 : ¬ (box r (diamond r φ) w) := by tidy,
    rw V at hV,
    have h5 : box r (diamond r φ) w := by exact hV _ _ h2,
    show false, from h4 h5    }
end


lemma D_eq_serial : serial r ↔ D r:=
begin
split,
{   intros hS φ w hB,
    --rw serial at hS,
    have h1 : ∃b, r w b := by exact hS w,
    --rw diamond,
    cases h1 with b hb,
    --rw box at hB,
    have h2 : φ b := by exact hB b hb,
    apply exists.intro b,
    cc  },
{   intros hD,
    --rw serial,
    intro a,
    --rw D at hD,
    let φ := (λw, true),
    have h1 : box r φ a := by finish,
    have h2 : diamond r φ a := by exact hD φ a h1,
    -- rw diamond at h2,
    cases h2 with u h3,
    apply exists.intro u (and.elim_left h3)   }
end

lemma BDDB_eq_confluence : confluence r ↔ BDDB r:=
begin
rw confluence at *,
split,
{   intros hc φ a hd b hr,
    cases hd with c h1,
    cases hc a b c (and.intro hr (and.elim_left h1)) with d h2,
    have h3 : φ d :=
        begin
        simp [box] at h1,
        exact (and.elim_right h1) d (and.elim_right h2)
        end,
    --rw diamond,
    apply exists.intro d,
    apply and.intro (and.elim_left h2) h3   },
{   intros hb a b c habc,
    rw BDDB at hb,
    let φ := (λw, r b w),
    have h1 : box r φ b := by tidy,
    have h2 : diamond r (box r φ) a := by tidy,
    have h3 : box r (diamond r φ) a := by exact hb _ _ h2,
    --rw box at h3,
    have h4 : diamond r φ c := by exact h3 c (and.elim_right habc),
    --rw diamond at h4,
    cases h4 with d h4a,
    have h5 : r b d := by tidy,
    apply exists.intro d (and.intro h5 (and.elim_left h4a))    }
end

-- ***** see Garson p.112 for more *** ********************

/- Multi-agent propositional modal logic-/
open classical
variable {indiv : Type}                      -- type of individuals
variable rᵢ : indiv → wo → wo → Prop
variables v w : wo
variables φ ψ γ : wo → Prop
variables i j : indiv                            

def boxi (i : indiv) (φ : wo → Prop) : wo → Prop := 
    λw, ∀v, rᵢ i w v → φ v                       

def diamondi (i : indiv) (φ : wo → Prop) : wo → Prop := 
    λw, ∃v, rᵢ i w v ∧ φ v                       
   
def R (i : indiv) (φ : wo → Prop) : wo → Prop := 
    λw, ∀v, rᵢ i w v → φ v

def Rg : wo → Prop :=
λw, ∀i, R rᵢ i φ w

#check @R
#check @Rg

def connected : wo → wo → Prop := λw v, ∃i, rᵢ i w v
#check @connected

inductive trcl (rᵢ : indiv → wo → wo → Prop) : wo → wo → Prop
| base (w v : wo )    : connected rᵢ w v → trcl w v
| trans (w v u : wo ) : trcl w v → connected rᵢ v u → trcl w u

/-
inductive reachable (rr : wo → wo → Prop) : ℕ → wo → wo → Prop
| zero (w v : wo)               : reachable 0 w w
| succ (n : ℕ) (w v u : wo)     : reachable n w u → rr u v → reachable (n+1) w v
-/

#check @trcl

def CRg (φ : wo → Prop) : wo → Prop :=
    λw, (∀v, trcl rᵢ w v → φ v)
#check @CRg


lemma B10 : ∀w, (CRg rᵢ φ w) ↔ (Rg rᵢ (φ ∧ₘ CRg rᵢ φ)) w :=
begin
intro w,
split,
{   intro h1,
    rw CRg at h1,
    rw Rg,
    intro i,
    --simp [conj],
    rw R,
    intros v hv,
    simp [conj],
    have h2 : connected rᵢ w v, by apply exists.intro i; assumption,
    have h3 : trcl rᵢ w v :=
        begin
        sorry,
        end,
    
    sorry   },
{   intros h2,
    --rw conj at h2,
    --rw CRg,
    intros v hv,
    --rw Rg at h2,
    have h3 : Rg rᵢ (CRg rᵢ φ) w :=
    begin
        intros i v hv,
        rw Rg at h2,
        have h3 : R rᵢ i (φ ∧ₘ CRg rᵢ φ) w, from h2 i,
        have h4 : (φ ∧ₘ CRg rᵢ φ) v, from h3 v hv,
        rw conj at h4,
        exact h4.2,
    end,
    have h5 : CRg rᵢ φ v, from h3 i v hv,
    sorry   }
end

lemma B11 : (⊢ φ →ₘ Rg rᵢ (φ ∧ₘ ψ)) → (⊢ (φ →ₘ CRg rᵢ ψ)) :=
begin
intros h1 w h2 v hv,
have hh : φ v ∧ ψ v :=
begin
rw imp at h1,
--simp * at h1,
have h3 : Rg rᵢ (φ ∧ₘ ψ) w, from h1 w h2,
--rw Rg at h3,
--clear h1,
induction hv,
{   rename hv_w w,
    rename hv_v v,
    cases hv_ᾰ with i,
    have h4 : R rᵢ i (φ ∧ₘ ψ) w, from h3 i,
    rw R at h4,
    have h5 : (φ ∧ₘ ψ) v, from h4 v hv_ᾰ_h,
    rw conj at h5,
    assumption },
{   rename hv_w w,
    rename hv_v v,
    rename hv_u u,
    cases hv_ᾰ_1 with k,
    have h6 : R rᵢ k (φ ∧ₘ ψ) w, from h3 k,
    --clear h3,
    rw conj at h6,
    rw R at h6,
    have h7 : (∀ (i : indiv), R rᵢ i (φ ∧ₘ ψ) w) → (φ v ∧ ψ v), by exact hv_ih h2,
    --rw Rg at h3,
    have h8 : φ v ∧ ψ v, by exact h7 h3,
    have h9 : φ v, by exact h8.1,
    have h10 : Rg rᵢ (φ ∧ₘ ψ) v, by exact h1 v h9,
    --rw Rg at h10,
    have h11 : R rᵢ k (φ ∧ₘ ψ) v, by exact h10 k,
    --rw R at h11,
    exact h11 u hv_ᾰ_1_h    }
end,
exact hh.2,
end



#lint
