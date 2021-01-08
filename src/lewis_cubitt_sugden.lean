/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import data.finset.basic  
import data.list.basic

--namespace Lewis_prop

-----------------------------------------------------------------------------------
/- outline of Lewis' theory of common knowledge (according to Cubitt and Sugden) -/

variable {indiv : Type}            -- type of individuals
variable {R : indiv → Prop → Prop}
constant Ind : Prop → indiv → Prop → Prop
variables {i j k : indiv}
variable p : Prop 
constants {A φ : Prop}

#check R i A 
#check Ind A i p


axiom C1 : R i A 
axiom C2 : Ind A i (R j A)
axiom C3 : Ind A i φ 
axiom C4 : ∀p, Ind A i p → R i (Ind A j p)

axiom A1 : ∀p, Ind A i p → R i A → R i p

axiom A6 : ∀p, (Ind A i (R j A) ∧ R i (Ind A j p)) → Ind A i (R j p)

lemma L1 : ∀i, R i φ := by intro i; exact A1 φ C3 C1

lemma L2 : ∀ i j, (R i (R j φ)) := 
begin
intros i j,
have h7 : ∀ j, R i (Ind A j φ) := by intro j; exact C4 φ C3,
have
 h8 : ∀ j, Ind A i (R j φ) := by intro j; exact A6 φ (and.intro C2 (h7 j)),
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

/- We can go on in this way, like Lewis and Cubitt and Sugden do. 
    The use of ... (and so on) is, however, unsatisfactory. 
    Therefore, we will give a complete proof by induction. /- 
-/  First attempt does not work out.

def F : list indiv → Prop
| []           := φ 
| (i :: is)    := R i (F is)

lemma Lewis₁ {a : list indiv} (h7 : @F _ R a) : ∀(i : indiv), Ind A i (@F _ R a) :=
begin
intro i,
induction a,
{   exact C3   },
{   rw F,
    rw F at h7,
    have h1 : F a_tl := sorry,
    have h2 : Ind A i (F a_tl) := by exact a_ih h1,
    have h3 : R i (Ind A a_hd (F a_tl)) := by exact C4 (F a_tl) h2,
    have h4 : Ind A i (R a_hd (F a_tl)) := by exact C6 (F a_tl) (and.intro C2 h3),
    assumption  }
end
-/

inductive G : Prop → Prop
| base                          : G φ 
| step (p : Prop) (i : indiv)   : G p → G (R i p)

#check list indiv
#check @G
#check G φ 

/- first part of the proof
lemma Lewis₁ (p : Prop) {R : indiv → Prop → Prop} (h7 : @G indiv R p) : 
∀(i : indiv), Ind A i p :=
begin
intro i,
induction h7 with u j hu ih,
{   exact C3   },
{   have h3 : R i (Ind A j u) := by exact C4 u ih,
    have h4 : Ind A i (R j u) := by exact A6 u (and.intro C2 h3),
    assumption }
end
-/

lemma Lewis (p : Prop) {R : indiv → Prop → Prop} (h7 : @G indiv R p) : 
    ∀(i : indiv), R i p :=
begin
intro i,
have h1 : Ind A i p :=
    begin
    induction h7 with u j hu ih,
{   exact C3   },
{   have h3 : R i (Ind A j u) := by exact C4 u ih,
    have h4 : Ind A i (R j u) := by exact A6 u (and.intro C2 h3),
    assumption }
    end,
exact A1 p h1 C1
end

/-def is_base {R : indiv → Prop → Prop} (p : Prop) (q : Prop) :=  (R i p) ∧  (Ind p i (R j p)) ∧ (Ind p i q) 
#check is_base A φ 

axiom base : @is_base indiv i j R A φ
#print base -/

#lint


--end Lewis_prop


