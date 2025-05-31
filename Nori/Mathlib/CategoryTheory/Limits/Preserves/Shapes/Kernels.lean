import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.Basic

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

namespace CategoryTheory.Limits

namespace KernelFork

variable {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
  (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

namespace CategoryTheory.Limits

def IsCokernelOfSplit {Z : C} {p : Y ⟶ Z} (zero : f ≫ p = 0) (hp : SplitEpi p)
    (hf : ∃ (g : Y ⟶ X), p ≫ hp.section_ = g ≫ f + 𝟙 _) :
    IsColimit (CokernelCofork.ofπ (f := f) p zero) where
  desc s := hp.section_ ≫ Cofork.π s
  fac s j := match j with
  | WalkingParallelPair.zero => by
    dsimp
    rw [CokernelCofork.π_eq_zero s, zero, zero_comp]
  | WalkingParallelPair.one => by
    dsimp
    rw [← assoc, hf.choose_spec]
    simp
  uniq s m hm := by
    have := hp.epi
    rw [← cancel_epi p]
    dsimp
    rw [← assoc, hf.choose_spec]
    simp
    exact hm WalkingParallelPair.one


end CategoryTheory.Limits
