import Nori.FinitelyPresented

noncomputable section

universe u v w u' v'

open CategoryTheory Category Limits Opposite ObjectProperty

open scoped ZeroObject

namespace Nori

variable (C : Type u) [Category.{v} C]

section Functor

variable [Preadditive C] [HasFiniteProducts C]

def FinitelyPresented.embedding : C ⥤ FinitelyPresented C :=
  (IsFinitelyPresented C).lift preadditiveYoneda
  (fun _ ↦ IsFinitelyPresented_of_isRepresentable _)

instance : (FinitelyPresented.embedding C).Additive where
  map_add {_ _ _ _} := by
    dsimp [FinitelyPresented.embedding]
    rw [preadditiveYoneda.map_add]

instance : PreservesBinaryBiproducts (FinitelyPresented.embedding C) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

instance : (FinitelyPresented.embedding C).Full := by
  dsimp [FinitelyPresented.embedding]
  infer_instance

instance : (FinitelyPresented.embedding C).Faithful := by
  dsimp [FinitelyPresented.embedding]
  infer_instance

instance : PreservesBinaryBiproducts (IsFinitelyPresented C).ι :=
  preservesBinaryBiproducts_of_preservesBiproducts _

instance : PreservesBinaryBiproducts (FinitelyPresented.embedding C ⋙ (IsFinitelyPresented C).ι) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

variable {C}

def IsFinitelyPresented.presentation_iso₂ {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    ⟨X, hX⟩ ≅ cokernel ((FinitelyPresented.embedding C).map (hX.presentation_map_f)) :=
  (IsFinitelyPresented C).isoMk (hX.presentation_iso ≪≫ (PreservesCokernel.iso
  (IsFinitelyPresented C).ι ((FinitelyPresented.embedding C).map hX.presentation_map_f)).symm)

abbrev IsFinitelyPresented.presentation_map_p₂ {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    (FinitelyPresented.embedding C).obj (hX.presentation_B) ⟶ ⟨X, hX⟩ :=
  hX.presentation_map_p

lemma IsFinitelyPresented.presentation_zero {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    (FinitelyPresented.embedding C).map hX.presentation_map_f ≫ hX.presentation_map_p₂ = 0 :=
  hX.presentation_map_f_p

@[reassoc]
lemma IsFinitelyPresented.presentation_map_f_p₂ {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    (FinitelyPresented.embedding C).map hX.presentation_map_f ≫ hX.presentation_map_p₂ = 0 :=
  hX.presentation_map_f_p

def IsFinitelyPresented.presentation_colimit {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    IsColimit (CokernelCofork.ofπ hX.presentation_map_p₂ hX.presentation_map_f_p₂) := by
  refine isColimitOfReflects (IsFinitelyPresented C).ι ?_
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).toFun hX.presentation_cokernel
  · refine NatIso.ofComponents ?_ ?_
    · intro x
      match x with
      | WalkingParallelPair.zero => exact Iso.refl _
      | WalkingParallelPair.one => exact Iso.refl _
    · intro _ _ u
      match u with
      | WalkingParallelPairHom.id _ =>
        dsimp
        simp only [CategoryTheory.Functor.map_id, id_comp]
        rfl
      | WalkingParallelPairHom.left =>
        dsimp
        simp only [comp_id, id_comp]
        rfl
      | WalkingParallelPairHom.right => simp
  · refine Cocones.ext (Iso.refl _) ?_
    intro x
    match x with
    | WalkingParallelPair.zero =>
      dsimp
      simp only [comp_id]
      erw [id_comp]
    | WalkingParallelPair.one =>
      dsimp
      simp only [comp_id]
      erw [id_comp]

def IsFinitelyPresented.presentation_mapB {X X' : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X)
    (hX' : IsFinitelyPresented C X') (u : X ⟶ X') : hX.presentation_B ⟶ hX'.presentation_B :=
  preadditiveYoneda.preimage (IsRepresentable_proj _ _ _  (hX.presentation_map_p ≫ u)
      hX'.presentation_map_p).choose

@[reassoc]
lemma IsFinitelyPresented.presentation_map_comm₂ {X X' : Cᵒᵖ ⥤ AddCommGrp}
    (hX : IsFinitelyPresented C X) (hX' : IsFinitelyPresented C X') (u : X ⟶ X') :
    preadditiveYoneda.map (hX.presentation_mapB hX' u) ≫ hX'.presentation_map_p =
    hX.presentation_map_p ≫ u := by
  dsimp [IsFinitelyPresented.presentation_mapB]
  rw [preadditiveYoneda.map_preimage]
  exact ((IsRepresentable_proj _ _ _  (hX.presentation_map_p ≫ u)
      hX'.presentation_map_p).choose_spec).symm

def IsFinitelyPresented.presentation_mapA {X X' : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X)
    (hX' : IsFinitelyPresented C X') (u : X ⟶ X') : hX.presentation_A ⟶ hX'.presentation_A := by
  set S := ShortComplex.mk (preadditiveYoneda.map hX'.presentation_map_f) hX'.presentation_map_p
    hX'.presentation_map_f_p
  have hS := S.exact_of_g_is_cokernel hX'.presentation_cokernel
  rw [S.exact_iff_epi_kernel_lift] at hS
  exact preadditiveYoneda.preimage (IsRepresentable_proj _ _ _ (kernel.lift hX'.presentation_map_p
    (preadditiveYoneda.map hX.presentation_map_f ≫ preadditiveYoneda.map (hX.presentation_mapB hX'
    u)) (by rw [assoc, hX.presentation_map_comm₂ hX' u, ← assoc,
            hX.presentation_map_f_p, zero_comp])) (kernel.lift S.g S.f S.zero)).choose

@[reassoc]
lemma IsFinitelyPresented.presentation_map_comm₁ {X X' : Cᵒᵖ ⥤ AddCommGrp}
    (hX : IsFinitelyPresented C X) (hX' : IsFinitelyPresented C X') (u : X ⟶ X') :
    hX.presentation_map_f ≫ hX.presentation_mapB hX' u =
    hX.presentation_mapA hX' u ≫ hX'.presentation_map_f := by
  apply preadditiveYoneda.map_injective
  dsimp [IsFinitelyPresented.presentation_mapA]
  rw [Functor.map_comp, Functor.map_comp, preadditiveYoneda.map_preimage]
  set S := ShortComplex.mk (preadditiveYoneda.map hX'.presentation_map_f) hX'.presentation_map_p
    hX'.presentation_map_f_p
  have hS := S.exact_of_g_is_cokernel hX'.presentation_cokernel
  rw [S.exact_iff_epi_kernel_lift] at hS
  have := (IsRepresentable_proj _ _ _ (kernel.lift hX'.presentation_map_p
    (preadditiveYoneda.map hX.presentation_map_f ≫ preadditiveYoneda.map (hX.presentation_mapB hX'
    u)) (by rw [assoc, hX.presentation_map_comm₂ hX' u, ← assoc,
            hX.presentation_map_f_p, zero_comp])) (kernel.lift S.g S.f S.zero)).choose_spec
  apply_fun (fun x ↦ x ≫ kernel.ι S.g) at this
  simp only [preadditiveYoneda_obj, Functor.comp_obj, Functor.flip_obj_obj, kernel.lift_ι, assoc,
    S] at this
  exact this

@[reassoc]
lemma IsFinitelyPresented.presentation_map_comm₂'' (X X' : FinitelyPresented C) (u : X ⟶ X') :
    (FinitelyPresented.embedding C).map (X.2.presentation_mapB X'.2 u) ≫ X'.2.presentation_map_p₂ =
    X.2.presentation_map_p₂ ≫ u := X.2.presentation_map_comm₂ X'.2 u

lemma presentation_cokernel_zero {X Y : FinitelyPresented C} (u : X ⟶ Y) :
    (FinitelyPresented.embedding C).map (biprod.desc (X.2.presentation_mapB Y.2 u) Y.2.presentation_map_f) ≫
    Y.2.presentation_map_p₂ ≫ cokernel.π u  = 0 := by
  rw [← cancel_epi ((FinitelyPresented.embedding C).mapBiprod _ _).inv]
  refine biprod.hom_ext' _ _ ?_ ?_
  · dsimp
    simp only [biprod.inl_desc_assoc, comp_zero]
    slice_lhs 1 2 => rw [← Functor.map_comp, biprod.inl_desc]
    rw [IsFinitelyPresented.presentation_map_comm₂'']
    simp
  · dsimp
    simp only [assoc, biprod.inr_desc_assoc, comp_zero]
    slice_lhs 1 2 => rw [← Functor.map_comp, biprod.inr_desc]
    rw [IsFinitelyPresented.presentation_map_f_p₂, zero_comp]

def presentation_cokernel {X Y : FinitelyPresented C} (u : X ⟶ Y) {c : CokernelCofork u}
    (hc : IsColimit c) : IsColimit (CokernelCofork.ofπ (Z := c.pt)
    (f := (FinitelyPresented.embedding C).map (biprod.desc (X.2.presentation_mapB Y.2 u)
    (Y.2.presentation_map_f))) (Y.2.presentation_map_p₂ ≫ cokernel.π u ≫
    (hc.coconePointUniqueUpToIso (cokernelIsCokernel u)).inv)
    (by rw [← cancel_mono ((hc.coconePointUniqueUpToIso (cokernelIsCokernel u)).hom)]
        simp only [Cofork.ofπ_pt, assoc, Iso.inv_hom_id, comp_id, zero_comp]
        exact presentation_cokernel_zero u)) := by
  refine isColimitOfReflects (IsFinitelyPresented C).ι ?_
  set S := ShortComplex.mk (preadditiveYoneda.map X.2.presentation_map_f) X.2.presentation_map_p
    X.2.presentation_map_f_p
  have hS := S.exact_and_epi_g_iff_g_is_cokernel.mpr (Nonempty.intro X.2.presentation_cokernel)
  set S' := ShortComplex.mk (preadditiveYoneda.map Y.2.presentation_map_f) Y.2.presentation_map_p
    Y.2.presentation_map_f_p
  have hS' := S'.exact_and_epi_g_iff_g_is_cokernel.mpr (Nonempty.intro Y.2.presentation_cokernel)
  have := hS.2
  have := hS'.2
  have exact := coker_sequence_exact S.g S' hS'.1 (preadditiveYoneda.map (X.2.presentation_mapB Y.2 u))
    u (IsFinitelyPresented.presentation_map_comm₂'' X Y u).symm
  have epi := coker_sequence_epi  S.g S' (preadditiveYoneda.map (X.2.presentation_mapB Y.2 u))
    u (IsFinitelyPresented.presentation_map_comm₂'' X Y u).symm
  have := ((ShortComplex.exact_and_epi_g_iff_g_is_cokernel _).mp ⟨exact, epi⟩)
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).toFun (Classical.choice this)
  · refine NatIso.ofComponents ?_ ?_
    · intro x
      match x with
      | WalkingParallelPair.zero =>
        exact ((FinitelyPresented.embedding C ⋙ (IsFinitelyPresented C).ι).mapBiprod _ _).symm
      | WalkingParallelPair.one => exact Iso.refl _
    · intro _ _ u
      match u with
      | WalkingParallelPairHom.id _ =>
        dsimp; simp only [CategoryTheory.Functor.map_id, id_comp]; rfl
      | WalkingParallelPairHom.left =>
        dsimp
        simp only [comp_id]
        conv_rhs => congr; erw [← (FinitelyPresented.embedding C ⋙
                      (IsFinitelyPresented C).ι).mapBiprod_inv]
        erw [biprod.mapBiprod_inv_map_desc]
        dsimp
        rfl
      | WalkingParallelPairHom.right =>
        dsimp
        simp only [comp_id, comp_zero]
  · refine Cocones.ext ?_ ?_
    · exact (PreservesCokernel.iso (IsFinitelyPresented C).ι u).symm ≪≫
        (IsFinitelyPresented C).ι.mapIso ((cokernelIsCokernel u).coconePointUniqueUpToIso hc)
    · intro x
      match x with
      | WalkingParallelPair.zero =>
        dsimp [S, S']
        simp only [biprod.lift_desc_assoc, Preadditive.add_comp, assoc, PreservesCokernel.iso_inv]
        slice_lhs 3 4 => rw [IsFinitelyPresented.presentation_map_f_p]
        simp only [zero_comp, comp_zero, add_zero]
        slice_lhs 4 5 => change cokernel.π ((IsFinitelyPresented C).ι.map u) ≫ _
                         rw [π_comp_cokernelComparison]
        slice_lhs 4 5 => change _ ≫ (IsFinitelyPresented C).ι.map _
                         rw [← Functor.map_comp]
                         erw [IsColimit.comp_coconePointUniqueUpToIso_hom _ hc]
        slice_rhs 3 4 => erw [IsColimit.comp_coconePointUniqueUpToIso_inv hc]
        rw [biprod.desc_eq]
        simp only [Cofork.app_one_eq_π, ι_map, Functor.map_add, Functor.map_comp,
          Preadditive.add_comp, assoc]
        conv_rhs => congr; rfl; congr; rfl; rw [IsFinitelyPresented.presentation_map_f_p₂_assoc]
        simp only [zero_comp, comp_zero, add_zero]
        rfl
      | WalkingParallelPair.one =>
        dsimp [S, S']
        simp only [PreservesCokernel.iso_inv, assoc]
        slice_rhs 2 3 => erw [IsColimit.comp_coconePointUniqueUpToIso_inv hc]
        erw [id_comp]
        slice_lhs 2 3 => change cokernel.π ((IsFinitelyPresented C).ι.map u) ≫ _
                         rw [π_comp_cokernelComparison]
        slice_lhs 2 3 => change _ ≫ (IsFinitelyPresented C).ι.map _
                         rw [← Functor.map_comp]
                         erw [IsColimit.comp_coconePointUniqueUpToIso_hom _ hc]
        simp only [Cofork.app_one_eq_π, ι_map]
        rfl

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCokernels D]
  (F : C ⥤ D) [F.Additive]

lemma IsFinitelyPresented.cokernel_map {A B A' B' : C} (f : B ⟶ A) (f' : B' ⟶ A') (u₁ u₂ : A ⟶ A')
    (v₁ v₂ : B ⟶ B') (comm₁ : f ≫ u₁ = v₁ ≫ f') (comm₂ : f ≫ u₂ = v₂ ≫ f') (comp : cokernel.map
    (preadditiveYoneda.map f) (preadditiveYoneda.map f') (preadditiveYoneda.map v₁)
    (preadditiveYoneda.map u₁) (by rw [← Functor.map_comp, comm₁, Functor.map_comp]) =
    cokernel.map (preadditiveYoneda.map f) (preadditiveYoneda.map f') (preadditiveYoneda.map v₂)
    (preadditiveYoneda.map u₂) (by rw [← Functor.map_comp, comm₂, Functor.map_comp]))
    (F : C ⥤ D) [F.Additive] :
    cokernel.map (F.map f) (F.map f') (F.map v₁) (F.map u₁)
    (by rw [← Functor.map_comp, comm₁, Functor.map_comp]) =
    cokernel.map (F.map f) (F.map f') (F.map v₂) (F.map u₂)
    (by rw [← Functor.map_comp, comm₂, Functor.map_comp]) := by
  have hc : preadditiveYoneda.map (u₁ - u₂) ≫ cokernel.π (preadditiveYoneda.map f') = 0 := by
    simp only [Functor.map_sub, coequalizer_as_cokernel, Preadditive.sub_comp]
    dsimp [cokernel.map] at comp
    apply_fun (fun x ↦ cokernel.π _ ≫ x) at comp
    simp only [cokernel.π_desc] at comp
    rw [comp, sub_self]
  set S := ShortComplex.mk (preadditiveYoneda.map f') (cokernel.π _) (cokernel.condition _)
  have hS := S.exact_of_g_is_cokernel (cokernelIsCokernel _)
  rw [S.exact_iff_epi_kernel_lift] at hS
  obtain ⟨t, ht⟩ := IsRepresentable_proj  _ _ _ (kernel.lift _ (preadditiveYoneda.map (u₁ - u₂)) hc)
    (kernel.lift S.g S.f S.zero)
  set s := (preadditiveYoneda.map_surjective t).choose
  have hs : u₁ = s ≫ f' + u₂ := by
    apply preadditiveYoneda.map_injective
    rw [preadditiveYoneda.map_add, preadditiveYoneda.map_comp,
      (preadditiveYoneda.map_surjective t).choose_spec, ← kernel.lift_ι (cokernel.π _)
      (preadditiveYoneda.map f') (cokernel.condition _), ← assoc, ← ht]
    simp [S]
  rw [← cancel_epi (cokernel.π _), cokernel.π_desc, hs]
  dsimp
  simp

lemma FinitelyPresented.lift_id (X : FinitelyPresented C) :
    cokernel.map (preadditiveYoneda.map X.2.presentation_map_f) (preadditiveYoneda.map
    X.2.presentation_map_f) (preadditiveYoneda.map (X.2.presentation_mapA X.2 (𝟙 X)))
    (preadditiveYoneda.map (X.2.presentation_mapB X.2 (𝟙 X)))
    (by rw [← Functor.map_comp, X.2.presentation_map_comm₁ X.2 (𝟙 X), Functor.map_comp]) =
    cokernel.map (preadditiveYoneda.map X.2.presentation_map_f) (preadditiveYoneda.map
    X.2.presentation_map_f) (preadditiveYoneda.map (𝟙 X.2.presentation_A))
    (preadditiveYoneda.map (𝟙 X.2.presentation_B)) (by simp) := by
  rw [← cancel_epi (cokernel.π _)]
  dsimp
  simp only [cokernel.π_desc, coequalizer_as_cokernel, CategoryTheory.Functor.map_id,
            preadditiveYoneda_obj, id_comp]
  rw [← cancel_mono ((cokernelIsCokernel (preadditiveYoneda.map
            X.2.presentation_map_f)).coconePointUniqueUpToIso X.2.presentation_cokernel).hom]
  slice_lhs 2 3 => erw [IsColimit.comp_coconePointUniqueUpToIso_hom _
            X.2.presentation_cokernel]
  erw [IsColimit.comp_coconePointUniqueUpToIso_hom _ X.2.presentation_cokernel]
  dsimp
  rw [X.2.presentation_map_comm₂ X.2 (𝟙 X)]
  erw [comp_id]

lemma FinitelyPresented.lift_comp {X X' X'' : FinitelyPresented C} (u : X ⟶ X') (v : X' ⟶ X'') :
    cokernel.map (preadditiveYoneda.map X.2.presentation_map_f) (preadditiveYoneda.map
    X''.2.presentation_map_f) (preadditiveYoneda.map (X.2.presentation_mapA X''.2 (u ≫ v)))
    (preadditiveYoneda.map (X.2.presentation_mapB X''.2 (u ≫ v)))
    (by rw [← Functor.map_comp, X.2.presentation_map_comm₁ X''.2, Functor.map_comp]) =
    cokernel.map (preadditiveYoneda.map X.2.presentation_map_f) (preadditiveYoneda.map
    X''.2.presentation_map_f) (preadditiveYoneda.map (X.2.presentation_mapA X'.2 u ≫
    X'.2.presentation_mapA X''.2 v)) (preadditiveYoneda.map (X.2.presentation_mapB X'.2 u ≫
    X'.2.presentation_mapB X''.2 v))
    (by rw [← Functor.map_comp, ← assoc, X.2.presentation_map_comm₁ X'.2, assoc,
            X'.2.presentation_map_comm₁ X''.2, ← assoc, Functor.map_comp]) := by
  rw [← cancel_epi (cokernel.π _)]
  simp only [preadditiveYoneda_obj, cokernel.π_desc, coequalizer_as_cokernel, Functor.map_comp,
    assoc]
  rw [← cancel_mono ((cokernelIsCokernel (preadditiveYoneda.map
            X''.2.presentation_map_f)).coconePointUniqueUpToIso X''.2.presentation_cokernel).hom]
  slice_lhs 2 3 => erw [IsColimit.comp_coconePointUniqueUpToIso_hom _ X''.2.presentation_cokernel]
  slice_rhs 3 4 => erw [IsColimit.comp_coconePointUniqueUpToIso_hom _ X''.2.presentation_cokernel]
  dsimp
  rw [X.2.presentation_map_comm₂ X''.2 (u ≫ v)]
  conv_rhs => rw [X'.2.presentation_map_comm₂ X''.2 v, ← assoc,
                  X.2.presentation_map_comm₂ X'.2 u, assoc]

def FinitelyPresented.lift :
    (FinitelyPresented C) ⥤ D where
  obj X := cokernel (F.map X.2.presentation_map_f)
  map {X X'} u := by
    refine cokernel.map (F.map X.2.presentation_map_f) (F.map X'.2.presentation_map_f) (F.map (X.2.presentation_mapA X'.2 u))
      (F.map (X.2.presentation_mapB X'.2 u)) ?_
    rw [← F.map_comp, X.2.presentation_map_comm₁, F.map_comp]
  map_id X := by
    rw [IsFinitelyPresented.cokernel_map X.2.presentation_map_f X.2.presentation_map_f (X.2.presentation_mapB X.2 (𝟙 X))
      (𝟙 _)  (X.2.presentation_mapA X.2 (𝟙 X)) (𝟙 _) (D := D) (X.2.presentation_map_comm₁ X.2 (𝟙 X)) (by simp)
      (FinitelyPresented.lift_id X) F, ← cancel_epi (cokernel.π _)]
    dsimp
    simp
  map_comp {X X' X''} u v := by
    have := IsFinitelyPresented.cokernel_map X.2.presentation_map_f X''.2.presentation_map_f
      (X.2.presentation_mapB X''.2 (u ≫ v)) (X.2.presentation_mapB X'.2 u ≫
      X'.2.presentation_mapB X''.2 v) (X.2.presentation_mapA X''.2 (u ≫ v))
      (X.2.presentation_mapA X'.2 u ≫ X'.2.presentation_mapA X''.2 v)
      (X.2.presentation_map_comm₁ X''.2 (u ≫ v))
      (by rw [← assoc, X.2.presentation_map_comm₁ X'.2 u, assoc,
              X'.2.presentation_map_comm₁ X''.2 v, assoc])
      (FinitelyPresented.lift_comp u v) F
    erw [this]
    rw [← cancel_epi (cokernel.π _)]
    dsimp
    simp

-- This is nontrivial and will use `IsFinitelyPresented.cokernel_map` again.
instance : (FinitelyPresented.lift F).Additive where
  map_add {X Y} {f g} := by
    dsimp [FinitelyPresented.lift]
    rw [← cancel_epi (cokernel.π _)]
    simp only [cokernel.π_desc, Preadditive.comp_add]
    sorry

def presentation_map_s {B X : C} (p : B ⟶ X)
    [Epi (preadditiveYoneda.map p)] : X ⟶ B :=
  preadditiveYoneda.preimage (IsRepresentable_proj (preadditiveYoneda.obj X)
  (preadditiveYoneda.obj B) (preadditiveYoneda.obj X) (𝟙 _) (preadditiveYoneda.map p)).choose

lemma presentation_map_s_p {B X : C} (p : B ⟶ X) [Epi (preadditiveYoneda.map p)] :
    presentation_map_s p ≫ p = 𝟙 _ := by
  apply preadditiveYoneda.map_injective
  dsimp [presentation_map_s]
  rw [preadditiveYoneda.map_comp, Functor.map_preimage, ← (IsRepresentable_proj
    (preadditiveYoneda.obj X) (preadditiveYoneda.obj B) (preadditiveYoneda.obj X) (𝟙 _)
    (preadditiveYoneda.map p)).choose_spec]
  simp

lemma presentation_map_g_exists {A B X : C} (f : A ⟶ B) (p : B ⟶ X) (zero : f ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ (f := preadditiveYoneda.map f) (preadditiveYoneda.map p)
    (by rw [← Functor.map_comp, zero, Functor.map_zero]))) :
    have : Epi (preadditiveYoneda.map p) := epi_of_isColimit_cofork hc
    ∃ (g : B ⟶ A), g ≫ f = p ≫ presentation_map_s p - 𝟙 _ := by
  have : Epi (preadditiveYoneda.map p) := epi_of_isColimit_cofork hc
  set v : B ⟶ B := p ≫ presentation_map_s p - 𝟙 _
  have zero' : v ≫ p = 0 := by
    dsimp [v]
    simp only [Preadditive.sub_comp, assoc]
    rw [presentation_map_s_p, comp_id, id_comp, sub_self]
  set S := ShortComplex.mk (preadditiveYoneda.map f) (preadditiveYoneda.map p)
    (by rw [← Functor.map_comp, zero, Functor.map_zero])
  have zero' : preadditiveYoneda.map v ≫ S.g = 0 := by
    dsimp [S]
    rw [← Functor.map_comp, zero', Functor.map_zero]
  have hS := S.exact_of_g_is_cokernel hc
  rw [S.exact_iff_epi_kernel_lift] at hS
  have left := IsRepresentable_proj (preadditiveYoneda.obj B) (preadditiveYoneda.obj A) _
    (kernel.lift _ (preadditiveYoneda.map v) zero') (kernel.lift S.g S.f S.zero)
  use preadditiveYoneda.preimage left.choose
  apply preadditiveYoneda.map_injective
  rw [preadditiveYoneda.map_comp, preadditiveYoneda.map_preimage]
  have := left.choose_spec
  apply_fun (fun x ↦ x ≫ kernel.ι _) at this
  simp only [Functor.comp_obj, Functor.flip_obj_obj, kernel.lift_ι, assoc, S] at this
  exact this.symm

def cokernel_persistance {A B X : C} (f : A ⟶ B) (p : B ⟶ X) (zero : f ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ (f := preadditiveYoneda.map f) (preadditiveYoneda.map p)
    (by rw [← Functor.map_comp, zero, Functor.map_zero]))) (F : C ⥤ D) [F.Additive] :
    IsColimit (CokernelCofork.ofπ (f := F.map f) (F.map p)
    (by rw [← F.map_comp, zero, F.map_zero])) := by
  have : Epi (preadditiveYoneda.map p) := epi_of_isColimit_cofork hc
  refine IsCokernelOfSplit (f := F.map f) (p := F.map p) _ ?_ ?_
  · exact SplitEpi.map {section_ := presentation_map_s p, id := presentation_map_s_p p} F
  · use F.map (presentation_map_g_exists f p zero hc).choose
    rw [← F.map_comp, (presentation_map_g_exists f p zero hc).choose_spec]
    simp

def presentation_map_p (X : C) :
    (IsFinitelyPresented_of_isRepresentable (preadditiveYoneda.obj X)).presentation_B ⟶ X :=
  preadditiveYoneda.preimage ((IsFinitelyPresented_of_isRepresentable
  (preadditiveYoneda.obj X)).presentation_map_p)

def presentation_map_f_p (X : C) :
    (IsFinitelyPresented_of_isRepresentable (preadditiveYoneda.obj X)).presentation_map_f
    ≫ presentation_map_p X = 0 := by
  apply preadditiveYoneda.map_injective
  dsimp [presentation_map_p]
  rw [preadditiveYoneda.map_comp, preadditiveYoneda.map_preimage,
    IsFinitelyPresented.presentation_map_f_p, Functor.map_zero]

def presentation_colimit (X : C) : IsColimit (CokernelCofork.ofπ (f := preadditiveYoneda.map
    ((IsFinitelyPresented_of_isRepresentable (preadditiveYoneda.obj X)).presentation_map_f))
    (preadditiveYoneda.map (presentation_map_p X))
    (by rw [← Functor.map_comp, presentation_map_f_p X, Functor.map_zero])) := by
  refine IsColimit.ofIsoColimit (IsFinitelyPresented_of_isRepresentable
    (preadditiveYoneda.obj X)).presentation_cokernel  ?_
  refine Cocones.ext (Iso.refl _) ?_
  intro x
  match x with
  | WalkingParallelPair.zero =>
    dsimp [presentation_map_p]
    simp
  | WalkingParallelPair.one =>
    dsimp [presentation_map_p]
    simp

def cokernel_presentation (X : C) (F : C ⥤ D) [F.Additive] :
    IsColimit (CokernelCofork.ofπ (f := F.map (IsFinitelyPresented_of_isRepresentable
    (preadditiveYoneda.obj X)).presentation_map_f) (F.map (presentation_map_p X))
    (by rw [← F.map_comp, presentation_map_f_p X, F.map_zero])) :=
  cokernel_persistance (IsFinitelyPresented_of_isRepresentable
    (preadditiveYoneda.obj X)).presentation_map_f (presentation_map_p X)
    (presentation_map_f_p X) (presentation_colimit X) F

def FinitelyPresented.embeddingLiftIso :
    FinitelyPresented.embedding C ⋙ FinitelyPresented.lift F ≅ F := by
  refine NatIso.ofComponents ?_ ?_
  · intro X
    have hX := IsFinitelyPresented_of_isRepresentable (preadditiveYoneda.obj X)
    exact (cokernelIsCokernel (F.map hX.presentation_map_f)).coconePointUniqueUpToIso
      (cokernel_presentation X F)
  · intro X Y f
    have hX := IsFinitelyPresented_of_isRepresentable (preadditiveYoneda.obj X)
    rw [← cancel_epi (cokernel.π (F.map hX.presentation_map_f))]
    dsimp [lift]
    simp only [cokernel.π_desc_assoc, assoc]
    have := (cokernelIsCokernel (F.map hX.presentation_map_f)).comp_coconePointUniqueUpToIso_hom
      (cokernel_presentation X F)
      (j := WalkingParallelPair.one)
    dsimp at this
    conv_rhs => congr; congr; congr; change ((cokernelIsCokernel
      (F.map hX.presentation_map_f)).coconePointUniqueUpToIso (cokernel_presentation X F)).hom
    slice_rhs 1 2 => rw [this]
    have hY := IsFinitelyPresented_of_isRepresentable (preadditiveYoneda.obj Y)
    have := (cokernelIsCokernel (F.map hY.presentation_map_f)).comp_coconePointUniqueUpToIso_hom
      (cokernel_presentation Y F)
      (j := WalkingParallelPair.one)
    dsimp at this
    conv_lhs => congr; rfl; congr; change cokernel.π (F.map hY.presentation_map_f); rfl
                change ((cokernelIsCokernel (F.map hY.presentation_map_f)).coconePointUniqueUpToIso
      (cokernel_presentation Y F)).hom
    rw [this]
    rw [← F.map_comp, ← F.map_comp]
    apply congrArg F.map
    apply preadditiveYoneda.map_injective
    dsimp [presentation_map_p]
    simp only [Functor.map_comp, Functor.map_preimage]
    exact hX.presentation_map_comm₂ hY (preadditiveYoneda.map f)

def FinitelyPresented.lift_preservesCokernels_aux₁ (X : FinitelyPresented C) :
    IsColimit (CokernelCofork.ofπ (f := (FinitelyPresented.lift F).map
    (((FinitelyPresented.embedding C).map X.2.presentation_map_f)))
    ((FinitelyPresented.lift F).map X.2.presentation_map_p₂)
    (by rw [← Functor.map_comp, X.2.presentation_zero, Functor.map_zero])) := sorry

def FinitelyPresented.lift_preservesCokernels_aux₂ (X : FinitelyPresented C) {A B : C}
    (f : A ⟶ B) (p : (FinitelyPresented.embedding C).obj B ⟶ X)
    (zero : (FinitelyPresented.embedding C).map f ≫ p = 0)
    (lim : IsColimit (CokernelCofork.ofπ p zero)) :
    IsColimit (CokernelCofork.ofπ (f := (FinitelyPresented.lift F).map
    ((FinitelyPresented.embedding C).map f)) ((FinitelyPresented.lift F).map p)
    (by rw [← Functor.map_comp, zero, Functor.map_zero])) := sorry

def FinitelyPresented.lift_preservesCokernels {X Y : FinitelyPresented C} (u : X ⟶ Y) :
    PreservesColimit (parallelPair u 0) (FinitelyPresented.lift F) where
  preserves {c} hc := by
    refine Nonempty.intro ?_
    set Z := c.pt
    set q : Y ⟶ Z := Cofork.π c
    set A := X.2.presentation_A
    set B := X.2.presentation_B
    set A' := Y.2.presentation_A
    set B' := Y.2.presentation_B
    set f : A ⟶ B := X.2.presentation_map_f
    set f' : A' ⟶ B' := Y.2.presentation_map_f
    set iso := X.2.presentation_iso
    set iso' := Y.2.presentation_iso
    set p : (FinitelyPresented.embedding C).obj B ⟶ X := X.2.presentation_map_p₂
    set p' : (FinitelyPresented.embedding C).obj B' ⟶ Y := Y.2.presentation_map_p₂
    set v : B ⟶ B' := X.2.presentation_mapB Y.2 u
    set w : A ⟶ A' := X.2.presentation_mapA Y.2 u
    have comm₁ : f ≫ v = w ≫ f' := X.2.presentation_map_comm₁ Y.2 u
    have comm₂ : p ≫ u = (FinitelyPresented.embedding C).map v ≫ p' :=
      (IsFinitelyPresented.presentation_map_comm₂'' X Y u).symm
    set e' := hc.coconePointUniqueUpToIso (cokernelIsCokernel u)
    set Q : ((FinitelyPresented.embedding C).obj B').1 ⟶ Z.1 := p' ≫ cokernel.π u ≫ e'.inv
    set G : ((FinitelyPresented.embedding C).obj (B ⊞ A')).1 ⟶
      ((FinitelyPresented.embedding C).obj B').1 :=
      ((FinitelyPresented.embedding C).mapBiprod _ _).hom ≫
      biprod.desc (C := FinitelyPresented C) ((embedding C).map v) ((embedding C).map f')
    have eq₀ : (embedding C).map (biprod.desc v f') ≫ Q = 0 := by
      dsimp [Q]
      rw [← cancel_mono e'.hom, assoc]
      conv_lhs => congr; rfl; erw [assoc]; congr; rfl; erw [assoc _ _ e'.hom]
                  rw [Iso.inv_hom_id, comp_id]
      rw [presentation_cokernel_zero]
      simp
    have colim : IsColimit (CokernelCofork.ofπ (f := (embedding C).map (biprod.desc v f'))
      Q eq₀) := presentation_cokernel u hc
    set Q' := (FinitelyPresented.lift F).map Q
    have eq₀' : (lift F).map ((embedding C).map (biprod.desc v f')) ≫ Q' = 0 := by
      dsimp [Q']
      rw [← Functor.map_comp, eq₀, Functor.map_zero]
    set G' := (FinitelyPresented.lift F).map G
    have eqG : G = (FinitelyPresented.embedding C).map (biprod.desc v f') := by
      dsimp [G]
      conv_lhs => erw [biprod.lift_desc (f := (embedding C).map biprod.fst)]
      rw [biprod.desc_eq]
      simp only [Functor.map_add, Functor.map_comp]
    have ZERO : CategoryStruct.comp (obj := FinitelyPresented C) G Q = 0 := by rw [eqG, eq₀]
    have colim' : IsColimit (CokernelCofork.ofπ (f := (FinitelyPresented.lift F).map
        ((FinitelyPresented.embedding C).map (biprod.desc v f'))) Q' eq₀') := by
      refine lift_preservesCokernels_aux₂ F Z (biprod.desc v f') Q eq₀ colim
    have colim := lift_preservesCokernels_aux₂ F Y f' p' Y.2.presentation_zero
      Y.2.presentation_colimit
    set α : (FinitelyPresented.lift F).obj ((FinitelyPresented.embedding C).obj (B ⊞ A')) ⟶
        (FinitelyPresented.lift F).obj X :=
      (FinitelyPresented.lift F).map (((FinitelyPresented.embedding C).mapBiprod _ _).hom ≫
      biprod.desc p 0)
    set β : (FinitelyPresented.lift F).obj ((FinitelyPresented.embedding C).obj B') ⟶
        (FinitelyPresented.lift F).obj Y := (FinitelyPresented.lift F).map p'
    have comp : (FinitelyPresented.lift F).map ((FinitelyPresented.embedding C).map
        (biprod.desc v f')) ≫ β = α ≫ (FinitelyPresented.lift F).map u := by
      dsimp [α, β]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simp only [biprod.lift_desc, comp_zero, add_zero, assoc]
      rw [comm₂]
      rw [← cancel_epi ((FinitelyPresented.embedding C).mapBiprod _ _).inv]
      refine biprod.hom_ext' _ _ ?_ ?_
      · dsimp
        simp only [biprod.inl_desc_assoc]
        slice_lhs 1 2 => rw [← Functor.map_comp, biprod.inl_desc]
        slice_rhs 1 2 => rw [← Functor.map_comp, biprod.inl_fst]
        simp
      · dsimp
        simp only [biprod.inr_desc_assoc]
        slice_lhs 1 2 => rw [← Functor.map_comp, biprod.inr_desc]
        slice_rhs 1 2 => rw [← Functor.map_comp, biprod.inr_fst]
        simp only [assoc, Functor.map_zero, zero_comp]
        exact IsFinitelyPresented.presentation_map_f_p₂ _
    have eqQ : (lift F).map p' ≫ (lift F).map (Cofork.π c) = Q' := by
      have eq : p' ≫ Cofork.π c = Q := by
        dsimp [Q, e']
        slice_rhs 2 3 => erw [IsColimit.comp_coconePointUniqueUpToIso_inv hc _
                           WalkingParallelPair.one]
        rfl
      dsimp [Q']
      rw [← Functor.map_comp, eq]
    set φ : (FinitelyPresented.lift F).obj Z ⟶ cokernel ((FinitelyPresented.lift F).map u) :=
      CokernelCofork.mapOfIsColimit colim' (CokernelCofork.ofπ (cokernel.π
      ((FinitelyPresented.lift F).map u)) (cokernel.condition _)) (Arrow.homMk α β comp.symm)
    set ψ : cokernel ((FinitelyPresented.lift F).map u) ⟶ (FinitelyPresented.lift F).obj Z :=
      cokernel.desc ((FinitelyPresented.lift F).map u) ((FinitelyPresented.lift F).map (Cofork.π c))
      (by rw [← Functor.map_comp, CokernelCofork.condition, Functor.map_zero])
    have eqQφ : Q' ≫ φ = (FinitelyPresented.lift F).map p' ≫ cokernel.π ((lift F).map u) := by
      change Cofork.π (CokernelCofork.ofπ (f := (FinitelyPresented.lift F).map
          ((FinitelyPresented.embedding C).map (biprod.desc v f'))) Q' eq₀') ≫ _ = _
      rw [CokernelCofork.π_mapOfIsColimit]
      rfl
    have : IsIso ψ := by
      have : Epi ((FinitelyPresented.lift F).map p') := epi_of_isColimit_cofork colim
      have : Epi Q' := epi_of_isColimit_cofork colim'
      refine ⟨φ, ?_, ?_⟩
      · rw [← cancel_epi ((FinitelyPresented.lift F).map p' ≫ cokernel.π _)]
        dsimp [ψ]
        slice_lhs 2 3 => rw [cokernel.π_desc]
        slice_lhs 1 2 => rw [eqQ]
        rw [eqQφ]
        simp
      · rw [← cancel_epi Q']
        dsimp [ψ]
        rw [← assoc, eqQφ]
        simp [eqQ]
    refine (IsColimit.equivOfNatIsoOfIso (F := (parallelPair u 0 ⋙ lift F)) (G := parallelPair
      ((FinitelyPresented.lift F).map u) 0)
      (NatIso.ofComponents (fun x ↦ match x with | WalkingParallelPair.zero => Iso.refl _
                                                 | WalkingParallelPair.one => Iso.refl _  )
      (by intro _ _ f
          match f with
          | WalkingParallelPairHom.left => dsimp; simp
          | WalkingParallelPairHom.right => dsimp; simp
          | WalkingParallelPairHom.id _ => dsimp; simp))
      ((FinitelyPresented.lift F).mapCocone c) (CokernelCofork.ofπ (cokernel.π
      ((FinitelyPresented.lift F).map u)) (cokernel.condition _)) ?_).invFun (cokernelIsCokernel _)
    refine Cocones.ext (asIso ψ).symm ?_
    intro j
    match j with
    | WalkingParallelPair.zero =>
      dsimp
      simp only [Cofork.app_zero_eq_comp_π_left, Functor.const_obj_obj, CokernelCofork.condition,
        Functor.map_zero, comp_zero, zero_comp, cokernel.condition, ψ, Z]
    | WalkingParallelPair.one =>
      dsimp
      simp only [id_comp, IsIso.comp_inv_eq, cokernel.π_desc, ψ, Z]

end Functor

end Nori
