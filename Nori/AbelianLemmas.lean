import Mathlib.CategoryTheory.Abelian.Refinements

noncomputable section

universe u v

open CategoryTheory Category Limits

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Limits

variable [Preadditive C] {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)

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


section Abelian

variable [Abelian C]

abbrev coker_sequence {X₂ X₃ : C} (g : X₂ ⟶ X₃) (S' : ShortComplex C) (v : X₂ ⟶ S'.X₂)
    (w : X₃ ⟶ S'.X₃) (comm : g ≫ w = v ≫ S'.g) : ShortComplex C where
  X₁ := X₂ ⊞ S'.X₁
  X₂ := S'.X₂
  X₃ := cokernel w
  f := biprod.desc v S'.f
  g := S'.g ≫ cokernel.π w
  zero := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp only [biprod.inl_desc_assoc, comp_zero]
      rw [← assoc, ← comm, assoc, cokernel.condition, comp_zero]
    · simp only [biprod.inr_desc_assoc, ShortComplex.zero_assoc, zero_comp, comp_zero]

lemma coker_sequence_epi {X₂ X₃ : C} (g : X₂ ⟶ X₃) (S' : ShortComplex C) [Epi S'.g]
    (v : X₂ ⟶ S'.X₂) (w : X₃ ⟶ S'.X₃) (comm : g ≫ w = v ≫ S'.g) :
    Epi (coker_sequence g S' v w comm).g := by
  dsimp [coker_sequence]; infer_instance

lemma coker_sequence_exact {X₂ X₃ : C} (g : X₂ ⟶ X₃) (S' : ShortComplex C)
    (hS' : S'.Exact) [Epi g] (v : X₂ ⟶ S'.X₂) (w : X₃ ⟶ S'.X₃)
    (comm : g ≫ w = v ≫ S'.g) : (coker_sequence g S' v w comm).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A u zero
  dsimp [coker_sequence] at u zero
  let S'' : ShortComplex C := {X₁ := X₃, X₂ := S'.X₃, X₃ := cokernel w, f := w,
                               g := cokernel.π w, zero := by simp}
  have hS'' : S''.Exact := S''.exact_of_g_is_cokernel (cokernelIsCokernel _)
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hS''
  obtain ⟨A', π, _, a, ha⟩ := hS'' (u ≫ S'.g) (by rw [assoc]; exact zero)
  obtain ⟨A'', π', _, b, hb⟩ := surjective_up_to_refinements_of_epi g a
  obtain ⟨A''', π'', _, c, hc⟩ := hS'.exact_up_to_refinements (b ≫ v - π' ≫ π ≫ u)
    (by rw [Preadditive.sub_comp, assoc, ← comm, ← assoc, ← hb, assoc, assoc, assoc, ha]
        exact sub_self _)
  use A''', π'' ≫ π' ≫ π, inferInstance, biprod.lift (π'' ≫ b) (-c)
  dsimp [coker_sequence]
  rw [biprod.lift_desc, Preadditive.neg_comp, ← hc]
  simp only [assoc, Preadditive.comp_sub, neg_sub, add_sub_cancel]

lemma coker_map_isIso {X₂ X₃ : C} (g : X₂ ⟶ X₃) (S' : ShortComplex C)
    (hS' : S'.Exact) [Epi g] [Epi S'.g] (v : X₂ ⟶ S'.X₂) (w : X₃ ⟶ S'.X₃)
    (comm : g ≫ w = v ≫ S'.g) :
    IsIso (cokernel.map (coker_sequence g S' v w comm).f w (biprod.desc g 0) S'.g
    (biprod.hom_ext' _ _ (by simp [comm.symm]) (by simp))) := by
  set h := Classical.choice ((coker_sequence g S' v w comm).exact_and_epi_g_iff_g_is_cokernel.mp
    ⟨coker_sequence_exact g S' hS' v w comm, coker_sequence_epi g S' v w comm⟩)
  have eq : cokernel.map (coker_sequence g S' v w comm).f w (biprod.desc g 0) S'.g
      (biprod.hom_ext' _ _ (by simp [comm.symm]) (by simp)) =
      ((cokernelIsCokernel (coker_sequence g S' v w comm).f).coconePointUniqueUpToIso h).hom := by
    rw [← cancel_epi (cokernel.π _)]
    have eq : cokernel.π (coker_sequence g S' v w comm).f = (Cofork.ofπ (cokernel.π
      (coker_sequence g S' v w comm).f) ((cokernel.condition _).trans zero_comp.symm)).ι.app
      WalkingParallelPair.one := rfl
    conv_rhs => congr; rw [eq]
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    simp only [cokernel.π_desc, Cofork.ofπ_pt, Cofork.ofπ_ι_app]
  rw [eq]
  infer_instance

end Abelian
