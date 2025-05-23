import Mathlib.CategoryTheory.Abelian.Refinements

noncomputable section

universe u v

open CategoryTheory Category Limits

variable {C : Type u} [Category.{v, u} C] [Abelian C]

def coker_sequence (S : ShortComplex C) (S' : ShortComplex C) (v : S.X₂ ⟶ S'.X₂)
    (w : S.X₃ ⟶ S'.X₃) (comm : S.g ≫ w = v ≫ S'.g) : ShortComplex C where
  X₁ := S.X₂ ⊞ S'.X₁
  X₂ := S'.X₂
  X₃ := cokernel w
  f := biprod.desc v S'.f
  g := S'.g ≫ cokernel.π w
  zero := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp only [biprod.inl_desc_assoc, comp_zero]
      rw [← assoc, ← comm, assoc, cokernel.condition, comp_zero]
    · simp only [biprod.inr_desc_assoc, ShortComplex.zero_assoc, zero_comp, comp_zero]

lemma coker_sequence_epi (S : ShortComplex C) (S' : ShortComplex C) (epiS' : Epi S'.g)
    (v : S.X₂ ⟶ S'.X₂) (w : S.X₃ ⟶ S'.X₃) (comm : S.g ≫ w = v ≫ S'.g) :
    Epi (coker_sequence S S' v w comm).g := by
  dsimp [coker_sequence]; infer_instance

lemma coker_sequence_exact (S : ShortComplex C) (S' : ShortComplex C) (hS : S.Exact)
    (hS' : S'.Exact) (epiS : Epi S.g) (epiS' : Epi S'.g) (v : S.X₂ ⟶ S'.X₂) (w : S.X₃ ⟶ S'.X₃)
    (comm : S.g ≫ w = v ≫ S'.g) : (coker_sequence S S' v w comm).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A u zero
  dsimp [coker_sequence] at u zero
  let S'' : ShortComplex C := {X₁ := S.X₃, X₂ := S'.X₃, X₃ := cokernel w, f := w,
                               g := cokernel.π w, zero := by simp}
  have hS'' : S''.Exact := S''.exact_of_g_is_cokernel (cokernelIsCokernel _)
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hS''
  obtain ⟨A', π, _, a, ha⟩ := hS'' (u ≫ S'.g) (by rw [assoc]; exact zero)
  obtain ⟨A'', π', _, b, hb⟩ := surjective_up_to_refinements_of_epi S.g a
  obtain ⟨A''', π'', _, c, hc⟩ := hS'.exact_up_to_refinements (b ≫ v - π' ≫ π ≫ u)
    (by rw [Preadditive.sub_comp, assoc, ← comm, ← assoc, ← hb, assoc, assoc, assoc, ha]
        exact sub_self _)
  use A''', π'' ≫ π' ≫ π, inferInstance, biprod.lift (π'' ≫ b) (-c)
  dsimp [coker_sequence]
  rw [biprod.lift_desc, Preadditive.neg_comp, ← hc]
  simp only [assoc, Preadditive.comp_sub, neg_sub, add_sub_cancel]
