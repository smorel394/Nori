import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

noncomputable section

universe u v

open CategoryTheory Category Limits Opposite ObjectProperty

open scoped ZeroObject

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

section ZeroObject

variable [HasZeroObject C]

instance : (IsFinitelyPresented C).ContainsZero where
  exists_zero := by
    use 0
    refine ⟨isZero_zero _, ?_⟩
    use 0, 0, 0
    exact Nonempty.intro (cokernelIsoOfEq (preadditiveYoneda.map_zero 0 0) ≪≫
      cokernelZeroIsoTarget ≪≫ Functor.mapZeroObject preadditiveYoneda)

instance : HasZeroObject (FinitelyPresented C) where
  zero := by
    obtain ⟨Z, h₁, h₂⟩ := exists_prop_of_containsZero (IsFinitelyPresented C)
    use ⟨Z, h₂⟩
    refine {unique_to Y := ?_, unique_from Y := ?_}
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_src _ _), Nonempty.intro 0⟩
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_tgt _ _), Nonempty.intro 0⟩

end ZeroObject

section FiniteProducts

variable [HasBinaryProducts C]

instance : HasBinaryBiproducts C where
  has_binary_biproduct A B := by
    have : HasBiproduct (pairFunction A B) := HasBiproduct.of_hasProduct _
    exact HasBinaryBiproduct.mk
      { bicone := (biproduct.bicone (pairFunction A B)).toBinaryBicone
        isBilimit := (Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit _) }

instance : HasBinaryBiproducts (FinitelyPresented C) where
  has_binary_biproduct X Y := by
    obtain ⟨A, B, u, h⟩ := X.2
    obtain ⟨A', B', u', h'⟩ := Y.2
    set e := Classical.choice h
    set e' := Classical.choice h'
    refine HasBinaryBiproduct.mk {bicone := ?_, isBilimit := ?_}
    · set Z : RightMod C := cokernel (preadditiveYoneda.map (biprod.map u u'))
      set p : Z ⟶ X.1 :=
        cokernel.map (preadditiveYoneda.map (biprod.map u u')) (preadditiveYoneda.map u)
        (preadditiveYoneda.map biprod.fst) (preadditiveYoneda.map biprod.fst)
        (by rw [← Functor.map_comp, ← Functor.map_comp, biprod.map_fst]) ≫ e.hom
      set q : Z ⟶ Y.1 :=
        cokernel.map (preadditiveYoneda.map (biprod.map u u')) (preadditiveYoneda.map u')
        (preadditiveYoneda.map biprod.snd) (preadditiveYoneda.map biprod.snd)
        (by rw [← Functor.map_comp, ← Functor.map_comp, biprod.map_snd]) ≫ e'.hom
      set a : X.1 ⟶ Z := e.inv ≫ cokernel.map (preadditiveYoneda.map u)
        (preadditiveYoneda.map (biprod.map u u')) (preadditiveYoneda.map biprod.inl)
        (preadditiveYoneda.map biprod.inl) sorry
      set b : Y.1 ⟶ Z := e'.inv ≫ cokernel.map (preadditiveYoneda.map u')
        (preadditiveYoneda.map (biprod.map u u')) (preadditiveYoneda.map biprod.inr)
        (preadditiveYoneda.map biprod.inr) sorry
      have hZ : IsFinitelyPresented C Z := sorry
      refine BinaryBicone.mk ⟨Z, hZ⟩ p q a b ?_ ?_ ?_ ?_
      · dsimp [a, p]
        sorry
      · sorry
      · sorry
      · sorry
    · sorry

end FiniteProducts

end Nori
