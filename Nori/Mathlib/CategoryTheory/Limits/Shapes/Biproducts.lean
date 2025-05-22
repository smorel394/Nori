/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Biproducts and binary biproducts

-/

noncomputable section

universe w w' v u

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J : Type w}
universe uC' uC uD' uD
variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

variable {F : J → C}

variable {J : Type w} {K : Type*}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-
/-- Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map between the biproducts. -/
abbrev biproduct.map {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  IsLimit.map (biproduct.bicone f).toCone (biproduct.isLimit g)
    (Discrete.natTrans (fun j => p j.as))
-/

lemma biproduct.map_comp {f g h : J → C} [HasBiproduct f] [HasBiproduct g] [HasBiproduct h] (p : ∀ b, f b ⟶ g b) (q : ∀ b, g b ⟶ h b) :
    biproduct.map (fun b ↦ p b ≫ q b) = biproduct.map p ≫ biproduct.map q := by
  refine biproduct.hom_ext _ _ (fun j ↦ ?_)
  simp only [map_π, Category.assoc, map_π_assoc]

lemma biproduct.map_id {f : J → C} [HasBiproduct f] :
    biproduct.map (fun b ↦ 𝟙 (f b)) = 𝟙 (biproduct f) := by
  refine biproduct.hom_ext _ _ (fun j ↦ ?_)
  simp only [map_π, Category.comp_id, Category.id_comp]

lemma biproduct.map_zero {f g : J → C} [HasBiproduct f] [HasBiproduct g] :
    biproduct.map (fun p ↦ (0 : f p ⟶ g p)) = 0 := by
  refine biproduct.hom_ext _ _ (fun j ↦ ?_)
  simp only [map_π, comp_zero, zero_comp]


end CategoryTheory.Limits
