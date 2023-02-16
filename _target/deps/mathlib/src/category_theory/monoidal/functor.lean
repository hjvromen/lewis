/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import category_theory.monoidal.category

/-!
# (Lax) monoidal functors

A lax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` (called the unit morphism)
* `μ X Y : (F.obj X) ⊗ (F.obj Y) ⟶ F.obj (X ⊗ Y)` (called the tensorator, or strength).
satisfying various axioms.

A monoidal functor is a lax monoidal functor for which `ε` and `μ` are isomorphisms.

We show that the composition of (lax) monoidal functors gives a (lax) monoidal functor.

See also `category_theory.monoidal.functorial` for a typeclass decorating an object-level
function with the additional data of a monoidal functor.
This is useful when stating that a pre-existing functor is monoidal.

See `category_theory.monoidal.natural_transformation` for monoidal natural transformations.

We show in `category_theory.monoidal.Mon_` that lax monoidal functors take monoid objects
to monoid objects.

## Future work
* Oplax monoidal functors.

## References

See https://stacks.math.columbia.edu/tag/0FFL.
-/

open category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory.category
open category_theory.functor

namespace category_theory

section

open monoidal_category

variables (C : Type u₁) [category.{v₁} C] [monoidal_category.{v₁} C]
          (D : Type u₂) [category.{v₂} D] [monoidal_category.{v₂} D]

/-- A lax monoidal functor is a functor `F : C ⥤ D` between monoidal categories, equipped with morphisms
    `ε : 𝟙 _D ⟶ F.obj (𝟙_ C)` and `μ X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`, satisfying the
    the appropriate coherences. -/
structure lax_monoidal_functor extends C ⥤ D :=
-- unit morphism
(ε               : 𝟙_ D ⟶ obj (𝟙_ C))
-- tensorator
(μ                : Π X Y : C, (obj X) ⊗ (obj Y) ⟶ obj (X ⊗ Y))
(μ_natural'       : ∀ {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y'),
  ((map f) ⊗ (map g)) ≫ μ Y Y' = μ X X' ≫ map (f ⊗ g)
  . obviously)
-- associativity of the tensorator
(associativity'   : ∀ (X Y Z : C),
    (μ X Y ⊗ 𝟙 (obj Z)) ≫ μ (X ⊗ Y) Z ≫ map (α_ X Y Z).hom
  = (α_ (obj X) (obj Y) (obj Z)).hom ≫ (𝟙 (obj X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z)
  . obviously)
-- unitality
(left_unitality'  : ∀ X : C,
    (λ_ (obj X)).hom
  = (ε ⊗ 𝟙 (obj X)) ≫ μ (𝟙_ C) X ≫ map (λ_ X).hom
  . obviously)
(right_unitality' : ∀ X : C,
    (ρ_ (obj X)).hom
  = (𝟙 (obj X) ⊗ ε) ≫ μ X (𝟙_ C) ≫ map (ρ_ X).hom
  . obviously)

restate_axiom lax_monoidal_functor.μ_natural'
attribute [simp, reassoc] lax_monoidal_functor.μ_natural
restate_axiom lax_monoidal_functor.left_unitality'
attribute [simp] lax_monoidal_functor.left_unitality
restate_axiom lax_monoidal_functor.right_unitality'
attribute [simp] lax_monoidal_functor.right_unitality
restate_axiom lax_monoidal_functor.associativity'
attribute [simp] lax_monoidal_functor.associativity

-- When `rewrite_search` lands, add @[search] attributes to
-- lax_monoidal_functor.μ_natural lax_monoidal_functor.left_unitality
-- lax_monoidal_functor.right_unitality lax_monoidal_functor.associativity

/--
A monoidal functor is a lax monoidal functor for which the tensorator and unitor as isomorphisms.

See https://stacks.math.columbia.edu/tag/0FFL.
-/
structure monoidal_functor
extends lax_monoidal_functor.{v₁ v₂} C D :=
(ε_is_iso            : is_iso ε . tactic.apply_instance)
(μ_is_iso            : Π X Y : C, is_iso (μ X Y) . tactic.apply_instance)

attribute [instance] monoidal_functor.ε_is_iso monoidal_functor.μ_is_iso

variables {C D}

/--
The unit morphism of a (strong) monoidal functor as an isomorphism.
-/
def monoidal_functor.ε_iso (F : monoidal_functor.{v₁ v₂} C D) :
  tensor_unit D ≅ F.obj (tensor_unit C) :=
as_iso F.ε
/--
The tensorator of a (strong) monoidal functor as an isomorphism.
-/
def monoidal_functor.μ_iso (F : monoidal_functor.{v₁ v₂} C D) (X Y : C) :
  (F.obj X) ⊗ (F.obj Y) ≅ F.obj (X ⊗ Y) :=
as_iso (F.μ X Y)

end

open monoidal_category

namespace lax_monoidal_functor

variables (C : Type u₁) [category.{v₁} C] [monoidal_category.{v₁} C]

/-- The identity lax monoidal functor. -/
@[simps] def id : lax_monoidal_functor.{v₁ v₁} C C :=
{ ε := 𝟙 _,
  μ := λ X Y, 𝟙 _,
  .. 𝟭 C }

instance : inhabited (lax_monoidal_functor C C) := ⟨id C⟩

end lax_monoidal_functor

namespace monoidal_functor

section
variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D]

lemma map_tensor (F : monoidal_functor.{v₁ v₂} C D) {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
  F.map (f ⊗ g) = inv (F.μ X X') ≫ ((F.map f) ⊗ (F.map g)) ≫ F.μ Y Y' :=
by simp

lemma map_left_unitor (F : monoidal_functor.{v₁ v₂} C D) (X : C) :
  F.map (λ_ X).hom = inv (F.μ (𝟙_ C) X) ≫ (inv F.ε ⊗ 𝟙 (F.obj X)) ≫ (λ_ (F.obj X)).hom :=
begin
  simp only [lax_monoidal_functor.left_unitality],
  slice_rhs 2 3 { rw ←comp_tensor_id, simp, },
  simp,
end

lemma map_right_unitor (F : monoidal_functor.{v₁ v₂} C D) (X : C) :
  F.map (ρ_ X).hom = inv (F.μ X (𝟙_ C)) ≫ (𝟙 (F.obj X) ⊗ inv F.ε) ≫ (ρ_ (F.obj X)).hom :=
begin
  simp only [lax_monoidal_functor.right_unitality],
  slice_rhs 2 3 { rw ←id_tensor_comp, simp, },
  simp,
end

/-- The tensorator as a natural isomorphism. -/
def μ_nat_iso (F : monoidal_functor.{v₁ v₂} C D) :
  (functor.prod F.to_functor F.to_functor) ⋙ (tensor D) ≅ (tensor C) ⋙ F.to_functor :=
nat_iso.of_components
  (by { intros, apply F.μ_iso })
  (by { intros, apply F.to_lax_monoidal_functor.μ_natural })
end

section
variables (C : Type u₁) [category.{v₁} C] [monoidal_category.{v₁} C]

/-- The identity monoidal functor. -/
@[simps] def id : monoidal_functor.{v₁ v₁} C C :=
{ ε := 𝟙 _,
  μ := λ X Y, 𝟙 _,
  .. 𝟭 C }

instance : inhabited (monoidal_functor C C) := ⟨id C⟩

end

end monoidal_functor

variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D]
variables {E : Type u₃} [category.{v₃} E] [monoidal_category.{v₃} E]

namespace lax_monoidal_functor
variables (F : lax_monoidal_functor.{v₁ v₂} C D) (G : lax_monoidal_functor.{v₂ v₃} D E)

-- The proofs here are horrendous; rewrite_search helps a lot.
/-- The composition of two lax monoidal functors is again lax monoidal. -/
@[simps] def comp : lax_monoidal_functor.{v₁ v₃} C E :=
{ ε                := G.ε ≫ (G.map F.ε),
  μ                := λ X Y, G.μ (F.obj X) (F.obj Y) ≫ G.map (F.μ X Y),
  μ_natural'       := λ _ _ _ _ f g,
  begin
    simp only [functor.comp_map, assoc],
    rw [←category.assoc, lax_monoidal_functor.μ_natural, category.assoc, ←map_comp, ←map_comp,
        ←lax_monoidal_functor.μ_natural]
  end,
  associativity'   := λ X Y Z,
  begin
    dsimp,
    rw id_tensor_comp,
    slice_rhs 3 4 { rw [← G.to_functor.map_id, G.μ_natural], },
    slice_rhs 1 3 { rw ←G.associativity, },
    rw comp_tensor_id,
    slice_lhs 2 3 { rw [← G.to_functor.map_id, G.μ_natural], },
    rw [category.assoc, category.assoc, category.assoc, category.assoc, category.assoc,
        ←G.to_functor.map_comp, ←G.to_functor.map_comp, ←G.to_functor.map_comp, ←G.to_functor.map_comp,
        F.associativity],
  end,
  left_unitality'  := λ X,
  begin
    dsimp,
    rw [G.left_unitality, comp_tensor_id, category.assoc, category.assoc],
    apply congr_arg,
    rw [F.left_unitality, map_comp, ←nat_trans.id_app, ←category.assoc,
        ←lax_monoidal_functor.μ_natural, nat_trans.id_app, map_id, ←category.assoc, map_comp],
  end,
  right_unitality' := λ X,
  begin
    dsimp,
    rw [G.right_unitality, id_tensor_comp, category.assoc, category.assoc],
    apply congr_arg,
    rw [F.right_unitality, map_comp, ←nat_trans.id_app, ←category.assoc,
        ←lax_monoidal_functor.μ_natural, nat_trans.id_app, map_id, ←category.assoc, map_comp],
  end,
  .. (F.to_functor) ⋙ (G.to_functor) }.

infixr ` ⊗⋙ `:80 := comp

end lax_monoidal_functor

namespace monoidal_functor

variables (F : monoidal_functor.{v₁ v₂} C D) (G : monoidal_functor.{v₂ v₃} D E)

/-- The composition of two monoidal functors is again monoidal. -/
@[simps]
def comp : monoidal_functor.{v₁ v₃} C E :=
{ ε_is_iso := by { dsimp, apply_instance },
  μ_is_iso := by { dsimp, apply_instance },
  .. (F.to_lax_monoidal_functor).comp (G.to_lax_monoidal_functor) }.

infixr ` ⊗⋙ `:80 := comp -- We overload notation; potentially dangerous, but it seems to work.

end monoidal_functor

end category_theory