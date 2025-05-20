import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

noncomputable section

universe u v

open CategoryTheory Category Limits Opposite

namespace Nori

variable (C : Type u) [Category.{v} C] [Preadditive C]

abbrev RightMod := Cᵒᵖ ⥤ AddCommGrp.{v}

def IsFinitelyPresented : ObjectProperty (RightMod C) :=
  fun X ↦ ∃ (A B : C) (u : A ⟶ B), Nonempty (cokernel ((preadditiveYoneda).map u) ≅ X)

abbrev FinitelyPresented := (IsFinitelyPresented C).FullSubcategory

instance : (IsFinitelyPresented C).IsClosedUnderIsomorphisms where
  of_iso α h := by
    obtain ⟨A, B, u, h⟩ := h
    use A, B, u
    exact Nonempty.intro (Classical.choice h ≪≫ α)

variable [HasZeroObject C]

instance : (IsFinitelyPresented C).ContainsZero := sorry

#synth HasZeroObject (IsFinitelyPresented C).FullSubcategory

end Nori
