/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is
the equalizer of `f` and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

The basic definitions are
* `kernel : (X ⟶ Y) → C`

* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts, we prove
* `kernel.ιZeroIsIso`: a kernel map of a zero morphism is an isomorphism
* `kernel.eq_zero_of_epi_kernel`: if `kernel.ι f` is an epimorphism, then `f = 0`
* `kernel.ofMono`: the kernel of a monomorphism is the zero object
* `kernel.liftMono`: the lift of a monomorphism `k : W ⟶ X` such that `k ≫ f = 0`
  is still a monomorphism
* `kernel.isLimitConeZeroCone`: if our category has a zero object, then the map from the zero
  object is a kernel map of any monomorphism
* `kernel.ιOfZero`: `kernel.ι (0 : X ⟶ Y)` is an isomorphism

and the corresponding dual statements.

## Future work
* TODO: connect this with existing work in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/


noncomputable section

universe v v₂ u u' u₂

open CategoryTheory Category

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable [HasZeroMorphisms C]

variable {X Y : C} (f : X ⟶ Y)


section

variable [HasKernel f]
/-
/-- A commuting square induces a morphism of kernels. -/
abbrev kernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : kernel f ⟶ kernel f' :=
  kernel.lift f' (kernel.ι f ≫ p) (by simp [← w])-/

/-
/-- Given a commutative diagram
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
with horizontal arrows composing to zero,
then we obtain a commutative square
   X ---> kernel g
   |         |
   |         | kernel.map
   |         |
   v         v
   X' --> kernel g'
-/
theorem kernel.lift_map {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : f ≫ g = 0)
    (f' : X' ⟶ Y') (g' : Y' ⟶ Z') [HasKernel g'] (w' : f' ≫ g' = 0) (p : X ⟶ X') (q : Y ⟶ Y')
    (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    kernel.lift g f w ≫ kernel.map g g' q r h₂ = p ≫ kernel.lift g' f' w' := by
  ext; simp [h₁]-/

end

section

variable [HasCokernel f]

/-
/-- A commuting square induces a morphism of cokernels. -/
abbrev cokernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : cokernel f ⟶ cokernel f' :=
  cokernel.desc f (q ≫ cokernel.π f') (by
    have : f ≫ q ≫ π f' = p ≫ f' ≫ π f' := by
      simp only [← Category.assoc]
      apply congrArg (· ≫ π f') w
    simp [this])
-/

/-
/-- Given a commutative diagram
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
with horizontal arrows composing to zero,
then we obtain a commutative square
   cokernel f ---> Z
   |               |
   | cokernel.map  |
   |               |
   v               v
   cokernel f' --> Z'
-/
theorem cokernel.map_desc {X Y Z X' Y' Z' : C} (f : X ⟶ Y) [HasCokernel f] (g : Y ⟶ Z)
    (w : f ≫ g = 0) (f' : X' ⟶ Y') [HasCokernel f'] (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0) (p : X ⟶ X')
    (q : Y ⟶ Y') (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    cokernel.map f f' p q h₁ ≫ cokernel.desc f' g' w' = cokernel.desc f g w ≫ r := by
  ext; simp [h₂]
-/

theorem cokernel.map_id (p' : X ⟶ X) (w : f = p' ≫ f) : cokernel.map f f p' (𝟙 Y) (by rw [comp_id, ← w]) = 𝟙 (cokernel f) := by
  rw [← cancel_epi (cokernel.π f)]
  dsimp [map]
  simp only [id_comp, IsColimit.desc_self, Cofork.ofπ_pt, comp_id]

theorem cokernel.map_comp {X' Y' X'' Y'' : C} (f' : X' ⟶ Y') [HasCokernel f'] (f'' : X'' ⟶ Y'') [HasCokernel f''] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') (p' : X' ⟶ X'') (q' : Y' ⟶ Y'') (w' : f' ≫ q' = p' ≫ f'') :
    cokernel.map f f'' (p ≫ p') (q ≫ q') (by rw [← assoc, w, assoc, w', assoc]) = cokernel.map f f' p q w ≫ cokernel.map f' f'' p' q' w' := by
  rw [← cancel_epi (cokernel.π f)]
  dsimp [map]
  simp only [assoc, π_desc, π_desc_assoc]

theorem cokernel.map_zero {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (w : p ≫ f' = 0) :
    cokernel.map f f' p 0 (by rw [comp_zero, w]) = 0 := by
  rw [← cancel_epi (cokernel.π f)]
  dsimp [map]
  simp only [zero_comp, desc_zero, comp_zero]

end
