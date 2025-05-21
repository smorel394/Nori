import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.Algebra.Category.Grp.Zero
import Nori.Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Nori.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

noncomputable section

universe u v

open CategoryTheory Category Limits Opposite ObjectProperty

open scoped ZeroObject

namespace Nori

variable (C : Type u) [Category.{v} C]

abbrev RightMod := Cᵒᵖ ⥤ AddCommGrp.{v}

--def IsFinitelyPresented : ObjectProperty (RightMod C) :=
--  fun X ↦ ∃ (A B : C) (u : A ⟶ B), Nonempty (cokernel ((preadditiveYoneda).map u) ≅ X)

def IsFinitelyPresented₂ : ObjectProperty (RightMod C) :=
  fun X ↦ ∃ (A B : RightMod C) (u : A ⟶ X) (_ : Epi u) (v : B ⟶ kernel u) (_ : Epi v),
  (A ⋙ forget AddCommGrp).IsRepresentable ∧ (B ⋙ forget AddCommGrp).IsRepresentable

--abbrev FinitelyPresented := (IsFinitelyPresented C).FullSubcategory

abbrev FinitelyPresented := (IsFinitelyPresented₂ C).FullSubcategory

/-
instance : (IsFinitelyPresented C).IsClosedUnderIsomorphisms where
  of_iso α h := by
    obtain ⟨A, B, u, h⟩ := h
    use A, B, u
    exact Nonempty.intro (Classical.choice h ≪≫ α)
-/

instance : (IsFinitelyPresented₂ C).IsClosedUnderIsomorphisms where
  of_iso α h := by
    obtain ⟨A, B, u, _, v, _, _, _⟩ := h
    use A, B, u ≫ α.hom, inferInstance,
      v ≫ (kernel.mapIso u (u ≫ α.hom) (Iso.refl _) α (by simp)).hom, inferInstance

section ZeroObject

variable [HasZeroObject C]

instance (X : Cᵒᵖ) : Unique (((0 : RightMod C) ⋙ forget AddCommGrp).obj X) := by
  have : Unique ((forget AddCommGrp).obj (AddCommGrp.of PUnit.{v + 1})) := by
    change Unique PUnit.{v+1}
    infer_instance
  exact Equiv.unique ((forget AddCommGrp).mapIso (IsZero.isoZero (Functor.zero_obj X))
    ≪≫ ((forget AddCommGrp).mapIso (IsZero.isoZero (AddCommGrp.isZero_of_subsingleton
      (AddCommGrp.of.{v} PUnit)))).symm).toEquiv

instance : ((0 : RightMod C) ⋙ forget AddCommGrp).IsRepresentable where
  has_representation := by
    use 0
    exact Nonempty.intro
      {homEquiv := Equiv.ofUnique _ _, homEquiv_comp _ _ := Subsingleton.elim _ _}

lemma IsFinitelyPresented₂_of_isRepresentable (X : RightMod C)
    (hX : (X ⋙ forget AddCommGrp).IsRepresentable) : IsFinitelyPresented₂ C X := by
  use X, 0, 𝟙 X, inferInstance, 0, IsZero.epi (IsZero.of_iso (isZero_zero _)
    (kernel.ofMono (𝟙 X))) _
  refine ⟨hX, inferInstance⟩

/-instance : (IsFinitelyPresented C).ContainsZero where
  exists_zero := by
    use 0
    refine ⟨isZero_zero _, ?_⟩
    use 0, 0, 0
    exact Nonempty.intro (cokernelIsoOfEq (preadditiveYoneda.map_zero 0 0) ≪≫
      cokernelZeroIsoTarget ≪≫ Functor.mapZeroObject preadditiveYoneda)
-/

instance : (IsFinitelyPresented₂ C).ContainsZero where
  exists_zero := by
    use 0
    refine ⟨isZero_zero _, IsFinitelyPresented₂_of_isRepresentable C _ inferInstance⟩

/-instance : HasZeroObject (FinitelyPresented C) where
  zero := by
    obtain ⟨Z, h₁, h₂⟩ := exists_prop_of_containsZero (IsFinitelyPresented C)
    use ⟨Z, h₂⟩
    refine {unique_to Y := ?_, unique_from Y := ?_}
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_src _ _), Nonempty.intro 0⟩
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_tgt _ _), Nonempty.intro 0⟩
-/

instance : HasZeroObject (FinitelyPresented C) where
  zero := by
    obtain ⟨Z, h₁, h₂⟩ := exists_prop_of_containsZero (IsFinitelyPresented₂ C)
    use ⟨Z, h₂⟩
    refine {unique_to Y := ?_, unique_from Y := ?_}
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_src _ _), Nonempty.intro 0⟩
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_tgt _ _), Nonempty.intro 0⟩

end ZeroObject

section FiniteProducts

variable [Preadditive C] [HasBinaryProducts C]

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
    let Z : RightMod C := cokernel (preadditiveYoneda.map (biprod.map u u'))
    let p : Z ⟶ X.1 :=
        cokernel.map (preadditiveYoneda.map (biprod.map u u')) (preadditiveYoneda.map u)
        (preadditiveYoneda.map biprod.fst) (preadditiveYoneda.map biprod.fst)
        (by rw [← Functor.map_comp, ← Functor.map_comp, biprod.map_fst]) ≫ e.hom
    let q : Z ⟶ Y.1 :=
        cokernel.map (preadditiveYoneda.map (biprod.map u u')) (preadditiveYoneda.map u')
        (preadditiveYoneda.map biprod.snd) (preadditiveYoneda.map biprod.snd)
        (by rw [← Functor.map_comp, ← Functor.map_comp, biprod.map_snd]) ≫ e'.hom
    let a : X.1 ⟶ Z := e.inv ≫ cokernel.map (preadditiveYoneda.map u)
        (preadditiveYoneda.map (biprod.map u u')) (preadditiveYoneda.map biprod.inl)
        (preadditiveYoneda.map biprod.inl) sorry
    let b : Y.1 ⟶ Z := e'.inv ≫ cokernel.map (preadditiveYoneda.map u')
        (preadditiveYoneda.map (biprod.map u u')) (preadditiveYoneda.map biprod.inr)
        (preadditiveYoneda.map biprod.inr) sorry
    have hZ : IsFinitelyPresented C Z := sorry
    refine HasBinaryBiproduct.mk {bicone := ?_, isBilimit := ?_}
    · refine BinaryBicone.mk ⟨Z, hZ⟩ p q a b ?_ ?_ ?_ ?_
      · dsimp [a, p]
        erw [assoc e.inv]
        slice_lhs 2 3 => rw [← cokernel.map_comp]
        conv_lhs => congr; rfl; congr; congr; rw [← Functor.map_comp, biprod.inl_fst, preadditiveYoneda.map_id]; rfl
                    rw [← Functor.map_comp, biprod.inl_fst, preadditiveYoneda.map_id]
        rw [cokernel.map_id (preadditiveYoneda.map u) _ (id_comp _).symm]
        simp only [preadditiveYoneda_obj, id_comp, Iso.inv_hom_id, a, p]
        rfl
      · dsimp [a, q]
        erw [assoc e.inv]
        slice_lhs 2 3 => rw [← cokernel.map_comp]
        conv_lhs => congr; rfl; congr; congr; rfl; rw [← preadditiveYoneda.map_comp, biprod.inl_snd, preadditiveYoneda.map_zero]
        rw [cokernel.map_zero (preadditiveYoneda.map u) (preadditiveYoneda.map u')]
        · simp only [preadditiveYoneda_obj, zero_comp, comp_zero, a, q, p]
        · rw [← Functor.map_comp, biprod.inl_snd, preadditiveYoneda.map_zero, zero_comp]
      · dsimp [b, p]
        erw [assoc e'.inv]
        slice_lhs 2 3 => rw [← cokernel.map_comp]
        conv_lhs => congr; rfl; congr; congr; rfl; rw [← Functor.map_comp, biprod.inr_fst, preadditiveYoneda.map_zero]
        rw [cokernel.map_zero]
        · simp only [preadditiveYoneda_obj, zero_comp, comp_zero, a, b, q, p]
        · rw [← Functor.map_comp, biprod.inr_fst, preadditiveYoneda.map_zero, zero_comp]
      · dsimp [b, q]
        erw [assoc e'.inv]
        slice_lhs 2 3 => rw [← cokernel.map_comp]
        conv_lhs => congr; rfl; congr; congr; rw [← Functor.map_comp, biprod.inr_snd, preadditiveYoneda.map_id]; rfl
                    rw [← Functor.map_comp, biprod.inr_snd, preadditiveYoneda.map_id]
        rw [cokernel.map_id (preadditiveYoneda.map u') _ (id_comp _).symm]
        simp only [preadditiveYoneda_obj, id_comp, Iso.inv_hom_id, a, b, q, p]
        rfl
    · refine {isLimit := ?_, isColimit := ?_}
      · refine {lift s := ?_, fac := ?_, uniq := ?_}
        · sorry
        · sorry
        · sorry
      · sorry

end FiniteProducts

end Nori
