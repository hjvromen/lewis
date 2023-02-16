/-
Copyright (c) 2021 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/


/- outline of Lewis' theory of common knowledge (formalisation according to 
the proposal of Jaap van der Does) -/

-- type of individuals in the population P
variable {indiv : Type}            
variables {i j: indiv}

-- states of affairs and propositions are of the same type
variables {p ψ χ : Prop}

-- Reason-to-believe is a two-place relation between individuals and propositions
constant R : indiv → Prop → Prop

-- Indication is a three-place relation between individuals and two propositions
constant Ind : indiv → Prop → Prop → Prop


/-- The following axioms represent that state of affairs α is a basis for common 
knowledge of proposition φ -/
constants {α φ: Prop}
axiom CK1 : R i α
axiom CK2 : Ind i α (R j α)
axiom CK3 : Ind i α φ


/-- `Indicative modus ponens represents the meaning of indication.
    This axiom corresponds to axiom A1 in Cubitt and Sugden's account. -/
axiom I_MP : Ind i ψ χ → R i ψ → R i χ


/-- `I-introspection` represents that all individuals in P share inductive 
    standards and background knowledge. This axiom is a variant of axiom C4 
    in Cubitt and Sugden's account -/
axiom I_introspection : Ind i α ψ → Ind i α (Ind j α ψ)


/-- `LR` (Lewis' Rule) is the assumption that the population allows for introspection
    with regard to using I-MP. This axiom is a variant of axiom A6 in 
    Cubitt and Sugden's account -/
axiom LR : (Ind i α (R j α) ∧ Ind i α (Ind j α ψ) → Ind i α (R j ψ))


/-- Now we can prove Lewis' theorem. First, we inductively define G (`generated 
    by φ), the property of being a proposition `p` for which we have to prove 
    that `R i p` holds. -/
inductive G : Prop → Prop
| base                          : G φ
| step (p : Prop) {i : indiv}   : G p → G (R i p)

theorem Lewis (p : Prop) (hG : @G indiv p) : ∀i : indiv, R i p :=
begin
intro i,
have h1 : Ind i α p :=
    begin
    induction hG with u j hu ih,
{   exact CK3   },
{   have h2 : Ind i α (Ind j α u) := I_introspection ih,
    have h3 : Ind i α (R j u) := LR (and.intro CK2 h2),
    assumption }
    end,
exact I_MP h1 CK1
end

/- Both I-MP and LR can be derived as lemmas in the theory of reasoning with 
    reasons. -/

