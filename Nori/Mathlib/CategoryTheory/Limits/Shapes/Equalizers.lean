/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Equalizers and coequalizers

-/

section

open CategoryTheory Opposite Category

namespace CategoryTheory.Limits

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C]
variable {X Y : C} {f g : X ⟶ Y}
  {c : Fork f g} (i : IsLimit c) {Z : C} (h : Y ⟶ Z) [hm : Mono h]
  {f' g' : X ⟶ Z} (hf' : f' = f ≫ h) (hg' : g' = g ≫ h)

/-- The fork obtained by postcomposing an equalizer fork with a monomorphism is an equalizer. -/
def isEqualizerCompMono₂ :
    have : Fork.ι c ≫ f' = Fork.ι c ≫ g' := by
      simp only [hf', hg', ← Category.assoc]
      exact congrArg (· ≫ h) c.condition
    IsLimit (Fork.ofι c.ι (by simp [this]) : Fork f' g') := by
  refine Fork.IsLimit.mk' _ fun s => ?_
  dsimp
  let s' : Fork f g := Fork.ofι s.ι
    (by apply hm.right_cancellation;
        rw [Category.assoc, ← hf', s.condition, Category.assoc, ← hg'])
  let l := Fork.IsLimit.lift' i s'.ι s'.condition
  refine ⟨l.1, l.2, ?_⟩
  intro m hm
  apply Fork.IsLimit.hom_ext i
  rw [hm, l.2]; rfl
