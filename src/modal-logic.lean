/-
Copyright (c) 2023 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import data.finset.basic  

-- # Modal propositional logic 

/- First, we define some not previously defined properties of relations that we will use later on -/

variable {α : Type} 

def euclidean (r: α → α → Prop) : Prop := ∀a b c, r a b → r a c → r b c
def serial (r: α → α → Prop) : Prop := ∀a, ∃b, r a b 
def confluence (r: α → α → Prop) : Prop:= ∀a b c, r a b ∧ r a c → ∃d, r b d ∧ r c d

-- see Pacuit (2017, p.12) for more properties of relations

/-- We start by defining a frame: a type of "possible worlds" with an accessibility  relation on this type. -/
structure frame := (wo : Type) [h : inhabited wo] (r : wo → wo → Prop)   
variable {f : frame}

/-- we define `implication`, `conjunction`, `negation` and `validity` for modal 
propositions (that is, functions `wo → Prop`) -/
def imp (φ ψ : f.wo → Prop): f.wo → Prop := λw, φ w → ψ w
infixr ` ⟶` : 90 := imp

def neg (φ : f.wo → Prop) : f.wo → Prop := λw, ¬ φ w
notation ` ¬ₘ ` := neg

def conj (φ ψ : f.wo → Prop): f.wo → Prop := λw, φ w ∧ ψ w
infixr ` ∧ₘ ` : 90 := conj

def valid (φ : f.wo → Prop) : Prop := ∀w, φ w
notation `⊢ ` φ := valid φ                             

/-- we define two functions from modal propositions to modal propositions -/
def box (φ : f.wo → Prop) : f.wo → Prop := λw, ∀v, f.r w v → φ v                       
notation `□` := box

def diamond (φ : f.wo → Prop) : f.wo → Prop := λw, ∃v, f.r w v ∧ φ v                       
notation `⬦` := diamond


/--  `box` and `diamond` are interdefinable -/

lemma neg_neg₁ {φ : f.wo → Prop} :  
    ¬ₘ (¬ₘ φ) = φ := by repeat {rw neg}; simp *

lemma not_box_diamond_not {φ : f.wo → Prop} : 
    ¬ₘ (□ φ) = ⬦ (¬ₘ φ) := by simp [box, diamond, neg]

lemma not_diamond_box_not {φ : f.wo → Prop} : 
    ¬ₘ (⬦ φ) = □ (¬ₘ φ) := by simp [box, diamond, neg]

lemma box_from_diamond {φ : f.wo → Prop} : 
    □ φ = ¬ₘ (⬦ (¬ₘ φ)) := by simp [not_diamond_box_not]; rw [neg_neg₁]

lemma diamond_from_box {φ : f.wo → Prop} : 
    ⬦ φ = ¬ₘ (□ (¬ₘ φ)) := by simp [not_box_diamond_not]; rw neg_neg₁


/- `box` obeys the 'normal' modal axioms K and Nec, and some other axioms -/

lemma K {φ ψ: f.wo → Prop} : 
    ⊢ □ (φ ⟶ ψ) ⟶ □ φ ⟶ □ ψ :=
begin
intros w h1 h2 v hr,
have h3 : (φ ⟶ ψ) v := by exact h1 v hr,
have h4 : φ v := by exact h2 v hr,
exact h3 h4
end


lemma Nec {φ : f.wo → Prop} : 
    (⊢ φ) → (⊢ □ φ) := 
begin
intros h1 w v h2,
exact h1 v    
end


lemma M {φ ψ : f.wo → Prop} :
    ⊢ □ (φ ∧ₘ ψ) ⟶ (□ φ ∧ₘ □ ψ) :=
begin
intros w h1,
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


lemma C {φ ψ : f.wo → Prop} :
    ⊢ (□ φ ∧ₘ □ ψ) ⟶ □ (φ ∧ₘ ψ) :=
begin
intros w h1,
rw conj at h1,
rw box,
intros v hr,
rw conj,
--simp [box] at h1,
exact and.intro (h1.1 v hr) (h1.2 v hr)
end
 

/- Correspondence results: some properties of frames correspond to formulas that are 
   valid in such frames. First, we define some properties of frames. -/

/-- truth -/
def T (f : frame) : Prop := ∀φ : f.wo → Prop, ⊢ □ φ ⟶ φ            

/-- named after Brouwer -/
def B (f : frame) : Prop := ∀φ : f.wo → Prop, ⊢ ⬦ (□ φ) ⟶ φ              

/-- consistency -/
def D (f : frame) : Prop := ∀φ : f.wo → Prop, ⊢ □ φ ⟶⬦ φ    

/-- positive introspection -/
def IV (f : frame) : Prop := ∀φ : f.wo → Prop, ⊢ □ φ ⟶ □ (□ φ)      

/-- V is equivalent to negative introspection (¬ □ →ₘ □ ¬ □) -/
def V (f : frame) : Prop  := ∀φ : f.wo → Prop, ⊢ ⬦ φ ⟶ □ (⬦ φ)

/-- exchangebility of the order of `box` and `diamond` -/
def BDDB (f : frame) : Prop := ∀φ : f.wo → Prop, ⊢ ⬦ (□ φ) ⟶ □ (⬦ φ)     


-- Now, we prove correspondence results for these properties.

lemma T_eq_refl : (reflexive f.r) ↔ T f:=
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
    let φ : f.wo → Prop := (λw, w ≠ w₀),
    apply by_contradiction,
    intro hn,
    have h2 : □ φ w₀ := by finish,
    have h3 : φ w₀ := by exact hT φ w₀ h2,
    finish }
end


lemma IV_eq_trans : transitive f.r ↔ IV f:=
begin
split,
{   intro hr,
    rw IV,
    intros φ w h1,
    rw box,
    intros v hv,
    --rw box,
    intros u h2,
    rw transitive at hr,
    have h3 : f.r w u, by exact hr hv h2,
    exact h1 _ h3  },
{   intro hIV,
    --rw transitive,
    intros a b c hab hbc,
    rw IV at hIV,
    let φ : f.wo → Prop := (λw, f.r a w ),
    have h2 : □ φ a := by finish,
    have h3 : □ (□ φ) a := by exact hIV φ a h2,
    have h4 : φ b := by finish,
    --rw box at h3,
    have h5 : □ φ b := by exact h3 b hab,
    have h6 : φ c := by exact h5 c hbc,
    finish  }
end


lemma B_eq_symm : symmetric f.r ↔ B f:=          
-- this proof follows Gamut (1991, p. 301)
begin
split,
{   intro hs,
    rw B,
    intros φ w h1,
    rw diamond at h1,
    cases h1 with v h2,
    rw symmetric at hs,
    have h3 : f.r v w := by exact hs h2.1,
    exact h2.2 w h3},
{   intros hB,
    rw symmetric,
    intros a b hab,
    let φ := (λw, f.r b w),
    have h1 : □ φ b := by tidy,
    have h2 : ⬦ (□ φ) a := by tidy,
    rw B at hB,
    have h3 : φ a := by exact hB φ a h2,
    finish  }
end


lemma V_eq_euclidean : euclidean f.r ↔ V f:=        
-- this proof follows Uckelman (2021, p. 176-177)
begin                                                                 
split,                                                                  
{   intros hE φ w hn,
    rw box,
    intros v hv,
    rw euclidean at hE,
    simp [diamond] at hn,
    cases hn with u hu,
    apply exists.intro u,
    apply and.intro (hE w v u hv (and.elim_left hu)) (and.elim_right hu)    },
{   intros hV w u v hwu hwv,
    by_contra hne,
    let φ := (λz, ¬ f.r u z),
    have h1 : φ v := by tidy,
    have h2 : ⬦ φ w := 
        begin
        simp [diamond],
        apply exists.intro v,
        apply and.intro hwv h1
        end,
    have h3 : ¬ ⬦ φ u := by tidy,
    have h4 : ¬ (□ (⬦ φ) w) := by tidy,
    rw V at hV,
    have h5 : □ (⬦ φ) w := by exact hV _ _ h2,
    show false, from h4 h5    }
end


lemma D_eq_serial : serial f.r ↔ D f:=
begin
split,
{   intros hS φ w hB,
    --rw serial at hS,
    have h1 : ∃b, f.r w b := by exact hS w,
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
    have h1 : □ φ a := by finish,
    have h2 : ⬦ φ a := by exact hD φ a h1,
    -- rw diamond at h2,
    cases h2 with u h3,
    apply exists.intro u (and.elim_left h3)   }
end


lemma BDDB_eq_confluence : confluence f.r ↔ BDDB f:=
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
    let φ := (λw, f.r b w),
    have h1 : □ φ b := by tidy,
    have h2 : ⬦ (□ φ) a := by tidy,
    have h3 : □ (⬦ φ) a := by exact hb _ _ h2,
    --rw box at h3,
    have h4 : ⬦ φ c := by exact h3 c (and.elim_right habc),
    --rw diamond at h4,
    cases h4 with d h4a,
    have h5 : f.r b d := by tidy,
    apply exists.intro d (and.intro h5 (and.elim_left h4a))    }
end

-- see Garson (2013, p.112) for more correspondence results

