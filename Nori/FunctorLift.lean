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

instance : (FinitelyPresented.embedding C).Full := by
  dsimp [FinitelyPresented.embedding]
  infer_instance

instance : (FinitelyPresented.embedding C).Faithful := by
  dsimp [FinitelyPresented.embedding]
  infer_instance

def IsFinitelyPresented.presentation_iso₂ {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    ⟨X, hX⟩ ≅ cokernel ((FinitelyPresented.embedding C).map (hX.presentation_map_f)) :=
  (IsFinitelyPresented C).isoMk (hX.presentation_iso ≪≫ (PreservesCokernel.iso
  (IsFinitelyPresented C).ι ((FinitelyPresented.embedding C).map hX.presentation_map_f)).symm)

abbrev IsFinitelyPresented.presentation_map_p₂ {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    (FinitelyPresented.embedding C).obj (hX.presentation_B) ⟶ ⟨X, hX⟩ :=
  cokernel.π ((FinitelyPresented.embedding C).map hX.presentation_map_f) ≫ hX.presentation_iso₂.inv

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCokernels D]

variable {C}

def IsFinitelyPresented.presentation_mapA {X X' : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X)
    (hX' : IsFinitelyPresented C X') (u : X ⟶ X') : hX.presentation_A ⟶ hX'.presentation_A := by
  set A := hX.presentation_A
  set B := hX.presentation_B
  set f : A ⟶ B := hX.presentation_map_f
  set e : X ≅ cokernel (preadditiveYoneda.map f) := hX.presentation_iso
  set A' := hX'.presentation_A
  set B' := hX'.presentation_B
  set f' : A' ⟶ B' := hX'.presentation_map_f
  set e' : X' ≅ cokernel (preadditiveYoneda.map f') := hX'.presentation_iso
  set v : preadditiveYoneda.obj B ⟶ preadditiveYoneda.obj B' :=
      (IsRepresentable_proj _ _ _  (cokernel.π (preadditiveYoneda.map f) ≫ e.inv ≫ u)
      (cokernel.π (preadditiveYoneda.map f') ≫ e'.inv)).choose
  have comm : cokernel.π (preadditiveYoneda.map f) ≫ e.inv ≫ u =
      v ≫ cokernel.π (preadditiveYoneda.map f') ≫ e'.inv := (IsRepresentable_proj _ _ _
      (cokernel.π (preadditiveYoneda.map f) ≫ e.inv ≫ u)
      (cokernel.π (preadditiveYoneda.map f') ≫ e'.inv)).choose_spec
  set S := ShortComplex.mk (preadditiveYoneda.map f') (cokernel.π _) (cokernel.condition _)
  have hS := S.exact_of_g_is_cokernel (cokernelIsCokernel _)
  rw [S.exact_iff_epi_kernel_lift] at hS
  have left := IsRepresentable_proj _ _ _ (kernel.lift _ (preadditiveYoneda.map f ≫ v)
      (by rw [← cancel_mono e'.inv, assoc, assoc, ← comm, ← assoc, ← assoc, cokernel.condition,
              zero_comp, zero_comp, zero_comp]))
      (kernel.lift S.g S.f S.zero)
  set w := left.choose
  exact (preadditiveYoneda.map_surjective w).choose

def IsFinitelyPresented.presentation_mapB {X X' : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X)
    (hX' : IsFinitelyPresented C X') (u : X ⟶ X') : hX.presentation_B ⟶ hX'.presentation_B := by
  set A := hX.presentation_A
  set B := hX.presentation_B
  set f : A ⟶ B := hX.presentation_map_f
  set e : X ≅ cokernel (preadditiveYoneda.map f) := hX.presentation_iso
  set A' := hX'.presentation_A
  set B' := hX'.presentation_B
  set f' : A' ⟶ B' := hX'.presentation_map_f
  set e' : X' ≅ cokernel (preadditiveYoneda.map f') := hX'.presentation_iso
  set v : preadditiveYoneda.obj B ⟶ preadditiveYoneda.obj B' :=
      (IsRepresentable_proj _ _ _  (cokernel.π (preadditiveYoneda.map f) ≫ e.inv ≫ u)
      (cokernel.π (preadditiveYoneda.map f') ≫ e'.inv)).choose
  exact (preadditiveYoneda.map_surjective v).choose

@[reassoc]
lemma IsFinitelyPresented.presentation_map_comm₁ {X X' : Cᵒᵖ ⥤ AddCommGrp}
    (hX : IsFinitelyPresented C X) (hX' : IsFinitelyPresented C X') (u : X ⟶ X') :
    hX.presentation_map_f ≫ hX.presentation_mapB hX' u =
    hX.presentation_mapA hX' u ≫ hX'.presentation_map_f := by
  set A := hX.presentation_A
  set B := hX.presentation_B
  set f : A ⟶ B := hX.presentation_map_f
  set e : X ≅ cokernel (preadditiveYoneda.map f) := hX.presentation_iso
  set A' := hX'.presentation_A
  set B' := hX'.presentation_B
  set f' : A' ⟶ B' := hX'.presentation_map_f
  set e' : X' ≅ cokernel (preadditiveYoneda.map f') := hX'.presentation_iso
  set v : preadditiveYoneda.obj B ⟶ preadditiveYoneda.obj B' :=
      (IsRepresentable_proj _ _ _  (cokernel.π (preadditiveYoneda.map f) ≫ e.inv ≫ u)
      (cokernel.π (preadditiveYoneda.map f') ≫ e'.inv)).choose
  have comm : cokernel.π (preadditiveYoneda.map f) ≫ e.inv ≫ u =
      v ≫ cokernel.π (preadditiveYoneda.map f') ≫ e'.inv := (IsRepresentable_proj _ _ _
      (cokernel.π (preadditiveYoneda.map f) ≫ e.inv ≫ u)
      (cokernel.π (preadditiveYoneda.map f') ≫ e'.inv)).choose_spec
  set S := ShortComplex.mk (preadditiveYoneda.map f') (cokernel.π _) (cokernel.condition _)
  have hS := S.exact_of_g_is_cokernel (cokernelIsCokernel _)
  rw [S.exact_iff_epi_kernel_lift] at hS
  have left := IsRepresentable_proj _ _ _ (kernel.lift _ (preadditiveYoneda.map f ≫ v)
      (by rw [← cancel_mono e'.inv, assoc, assoc, ← comm, ← assoc, ← assoc, cokernel.condition,
              zero_comp, zero_comp, zero_comp]))
      (kernel.lift S.g S.f S.zero)
  set w := left.choose
  have comm' := left.choose_spec
  dsimp at comm'
  apply preadditiveYoneda.map_injective
  rw [Functor.map_comp, IsFinitelyPresented.presentation_mapB]
  erw [(preadditiveYoneda.map_surjective v).choose_spec]
  rw [Functor.map_comp, IsFinitelyPresented.presentation_mapA]
  erw [(preadditiveYoneda.map_surjective w).choose_spec]
  have eq : preadditiveYoneda.map f' = _ := (kernel.lift_ι S.g S.f S.zero).symm
  conv_rhs => rw [eq, ← assoc, ← comm', kernel.lift_ι]

@[reassoc]
lemma IsFinitelyPresented.presentation_map_comm₂ {X X' : Cᵒᵖ ⥤ AddCommGrp}
    (hX : IsFinitelyPresented C X) (hX' : IsFinitelyPresented C X') (u : X ⟶ X') :
    preadditiveYoneda.map (hX.presentation_mapB hX' u) ≫ cokernel.π _ ≫ hX'.presentation_iso.inv =
    cokernel.π _ ≫ hX.presentation_iso.inv ≫ u := by
  set A := hX.presentation_A
  set B := hX.presentation_B
  set f : A ⟶ B := hX.presentation_map_f
  set e : X ≅ cokernel (preadditiveYoneda.map f) := hX.presentation_iso
  set A' := hX'.presentation_A
  set B' := hX'.presentation_B
  set f' : A' ⟶ B' := hX'.presentation_map_f
  set e' : X' ≅ cokernel (preadditiveYoneda.map f') := hX'.presentation_iso
  set v : preadditiveYoneda.obj B ⟶ preadditiveYoneda.obj B' :=
      (IsRepresentable_proj _ _ _  (cokernel.π (preadditiveYoneda.map f) ≫ e.inv ≫ u)
      (cokernel.π (preadditiveYoneda.map f') ≫ e'.inv)).choose
  have comm : cokernel.π (preadditiveYoneda.map f) ≫ e.inv ≫ u =
      v ≫ cokernel.π (preadditiveYoneda.map f') ≫ e'.inv := (IsRepresentable_proj _ _ _
      (cokernel.π (preadditiveYoneda.map f) ≫ e.inv ≫ u)
      (cokernel.π (preadditiveYoneda.map f') ≫ e'.inv)).choose_spec
  erw [(preadditiveYoneda.map_surjective v).choose_spec, ← comm]

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

def FinitelyPresented.lift (F : C ⥤ D) [F.Additive] :
    (FinitelyPresented C) ⥤ D where
  obj X := cokernel (F.map X.2.presentation_map_f)
  map {X X'} u := by
    refine cokernel.map (F.map X.2.presentation_map_f) (F.map X'.2.presentation_map_f) (F.map (X.2.presentation_mapA X'.2 u))
      (F.map (X.2.presentation_mapB X'.2 u)) ?_
    rw [← F.map_comp, X.2.presentation_map_comm₁, F.map_comp]
  map_id X := by
    have := IsFinitelyPresented.cokernel_map X.2.presentation_map_f X.2.presentation_map_f (X.2.presentation_mapB X.2 (𝟙 X))
      (𝟙 _)  (X.2.presentation_mapA X.2 (𝟙 X)) (𝟙 _) (D := D) (X.2.presentation_map_comm₁ X.2 (𝟙 X)) (by simp)
      (by rw [← cancel_epi (cokernel.π _)]
          simp only [preadditiveYoneda_obj, cokernel.π_desc, coequalizer_as_cokernel,
            CategoryTheory.Functor.map_id, id_comp]
          rw [← cancel_mono X.2.presentation_iso.inv, assoc, X.2.presentation_map_comm₂ X.2 (𝟙 X)]
          erw [comp_id]) F
    rw [this]
    rw [← cancel_epi (cokernel.π _)]
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
      (by rw [← cancel_epi (cokernel.π _)]
          simp only [preadditiveYoneda_obj, cokernel.π_desc, coequalizer_as_cokernel,
            Functor.map_comp, assoc]
          rw [← cancel_mono X''.2.presentation_iso.inv, assoc, X.2.presentation_map_comm₂ X''.2
              (u ≫ v), assoc, assoc, X'.2.presentation_map_comm₂ X''.2 v,
              X.2.presentation_map_comm₂_assoc X'.2 u]) F
    erw [this]
    rw [← cancel_epi (cokernel.π _)]
    dsimp
    simp

def presentation_map_p {A B X : C} (f : A ⟶ B)
    (iso : preadditiveYoneda.obj X ≅ cokernel (preadditiveYoneda.map f)) : B ⟶ X :=
  (preadditiveYoneda.map_surjective (cokernel.π _ ≫ iso.inv)).choose

 omit [HasFiniteProducts C] in
lemma presentation_map_f_p {A B X : C} (f : A ⟶ B)
    (iso : preadditiveYoneda.obj X ≅ cokernel (preadditiveYoneda.map f)) :
    f ≫ presentation_map_p f iso = 0 := by
  apply preadditiveYoneda.map_injective
  rw [Functor.map_comp, presentation_map_p,
    (preadditiveYoneda.map_surjective (cokernel.π _ ≫ iso.inv)).choose_spec]
  simp

def presentation_map_s {A B X : C} (f : A ⟶ B)
    (iso : preadditiveYoneda.obj X ≅ cokernel (preadditiveYoneda.map f)) :
    X ⟶ B := by
  have ht := IsRepresentable_proj (preadditiveYoneda.obj X) (preadditiveYoneda.obj B)
    (preadditiveYoneda.obj X) (𝟙 _) (cokernel.π _ ≫ iso.inv)
  exact (preadditiveYoneda.map_surjective ht.choose).choose

lemma presentation_map_s_p {A B X : C} (f : A ⟶ B)
    (iso : preadditiveYoneda.obj X ≅ cokernel (preadditiveYoneda.map f)) :
    presentation_map_s f iso ≫ presentation_map_p f iso = 𝟙 _ := by
  apply preadditiveYoneda.map_injective
  have ht := IsRepresentable_proj (preadditiveYoneda.obj X) (preadditiveYoneda.obj B)
    (preadditiveYoneda.obj X) (𝟙 _) (cokernel.π _ ≫ iso.inv)
  rw [preadditiveYoneda.map_comp, presentation_map_s,
    (preadditiveYoneda.map_surjective ht.choose).choose_spec, preadditiveYoneda.map_id,
    presentation_map_p, (preadditiveYoneda.map_surjective
    (cokernel.π _ ≫ iso.inv)).choose_spec, ← ht.choose_spec]

lemma presentation_map_g_exists {A B X : C} (f : A ⟶ B)
    (iso : preadditiveYoneda.obj X ≅ cokernel (preadditiveYoneda.map f)) :
    ∃ (g : B ⟶ A), g ≫ f = presentation_map_p f iso ≫ presentation_map_s f iso - 𝟙 _ := by
  set v : B ⟶ B := presentation_map_p f iso ≫ presentation_map_s f iso - 𝟙 _
  have zero : v ≫ presentation_map_p f iso = 0 := by
    dsimp [v]
    simp only [Preadditive.sub_comp, assoc, v]
    rw [presentation_map_s_p, comp_id]
    erw [id_comp, sub_self]
  set S := ShortComplex.mk (preadditiveYoneda.map f) (cokernel.π _) (cokernel.condition _)
  have zero' : preadditiveYoneda.map v ≫ S.g = 0 := by
    dsimp [S]
    rw [← cancel_mono iso.inv, assoc, ← (preadditiveYoneda.map_surjective
      (cokernel.π _ ≫ iso.inv)).choose_spec, ← preadditiveYoneda.map_comp]
    erw [zero]
    simp
  have hS := S.exact_of_g_is_cokernel (cokernelIsCokernel _)
  rw [S.exact_iff_epi_kernel_lift] at hS
  have left := IsRepresentable_proj (preadditiveYoneda.obj B) (preadditiveYoneda.obj A) _
    (kernel.lift _ (preadditiveYoneda.map v) zero') (kernel.lift S.g S.f S.zero)
  use (preadditiveYoneda.map_surjective left.choose).choose
  apply preadditiveYoneda.map_injective
  rw [preadditiveYoneda.map_comp, (preadditiveYoneda.map_surjective left.choose).choose_spec]
  have := left.choose_spec
  apply_fun (fun x ↦ x ≫ kernel.ι _) at this
  simp only [Functor.comp_obj, Functor.flip_obj_obj, kernel.lift_ι, assoc, S] at this
  exact this.symm

def cokernel_presentation {A B X : C} (f : A ⟶ B)
    (iso : preadditiveYoneda.obj X ≅ cokernel (preadditiveYoneda.map f)) (F : C ⥤ D) [F.Additive] :
    IsColimit (CokernelCofork.ofπ (f := F.map f) (F.map (presentation_map_p f iso))
    (by rw [← F.map_comp, presentation_map_f_p f iso, F.map_zero])) := by
  refine IsCokernelOfSplit (f := F.map f) (p := F.map (presentation_map_p f iso)) _ ?_ ?_
  · exact SplitEpi.map {section_ := presentation_map_s f iso, id := presentation_map_s_p f iso} F
  · use F.map (presentation_map_g_exists f iso).choose
    rw [← F.map_comp, (presentation_map_g_exists f iso).choose_spec]
    simp

def FinitelyPresented.embeddingLiftIso (F : C ⥤ D) [F.Additive] :
    FinitelyPresented.embedding C ⋙ FinitelyPresented.lift F ≅ F := by
  refine NatIso.ofComponents ?_ ?_
  · intro X
    have hX := IsFinitelyPresented_of_isRepresentable (preadditiveYoneda.obj X)
    exact (cokernelIsCokernel (F.map hX.presentation_map_f)).coconePointUniqueUpToIso
      (cokernel_presentation hX.presentation_map_f hX.presentation_iso F)
  · intro X Y f
    have hX := IsFinitelyPresented_of_isRepresentable (preadditiveYoneda.obj X)
    rw [← cancel_epi (cokernel.π (F.map hX.presentation_map_f))]
    dsimp [lift]
    simp only [cokernel.π_desc_assoc, assoc]
    have := (cokernelIsCokernel (F.map hX.presentation_map_f)).comp_coconePointUniqueUpToIso_hom
      (cokernel_presentation hX.presentation_map_f hX.presentation_iso F)
      (j := WalkingParallelPair.one)
    dsimp at this
    conv_rhs => congr; congr; congr; change ((cokernelIsCokernel
      (F.map hX.presentation_map_f)).coconePointUniqueUpToIso (cokernel_presentation
      hX.presentation_map_f hX.presentation_iso F)).hom
    slice_rhs 1 2 => rw [this]
    have hY := IsFinitelyPresented_of_isRepresentable (preadditiveYoneda.obj Y)
    have := (cokernelIsCokernel (F.map hY.presentation_map_f)).comp_coconePointUniqueUpToIso_hom
      (cokernel_presentation hY.presentation_map_f hY.presentation_iso F)
      (j := WalkingParallelPair.one)
    dsimp at this
    conv_lhs => congr; rfl; congr; change cokernel.π (F.map hY.presentation_map_f); rfl
                change ((cokernelIsCokernel (F.map hY.presentation_map_f)).coconePointUniqueUpToIso
      (cokernel_presentation hY.presentation_map_f hY.presentation_iso F)).hom
    rw [this]
    rw [← F.map_comp, ← F.map_comp]
    apply congrArg F.map
    apply preadditiveYoneda.map_injective
    erw [preadditiveYoneda.map_comp, (preadditiveYoneda.map_surjective (cokernel.π _ ≫
      hY.presentation_iso.inv)).choose_spec]
    erw [preadditiveYoneda.map_comp, (preadditiveYoneda.map_surjective (cokernel.π _ ≫
      hX.presentation_iso.inv)).choose_spec]
    exact hX.presentation_map_comm₂ hY (preadditiveYoneda.map f)

def FinitelyPresented.lift_preservesCokernels_aux₁ (X : FinitelyPresented C)
    (F : C ⥤ D) [F.Additive] :
    Epi ((FinitelyPresented.lift F).map X.2.presentation_map_p₂) := sorry

def FinitelyPresented.lift_preservesCokernels {X Y : FinitelyPresented C} (u : X ⟶ Y)
    (F : C ⥤ D) [F.Additive] :
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
    set p : preadditiveYoneda.obj B ⟶ X.1 := cokernel.π (preadditiveYoneda.map f) ≫ iso.inv
    set p' : preadditiveYoneda.obj B' ⟶ Y.1 := cokernel.π (preadditiveYoneda.map f') ≫ iso'.inv
    set v : B ⟶ B' := X.2.presentation_mapB Y.2 u
    set w : A ⟶ A' := X.2.presentation_mapA Y.2 u
    have comm₁ : f ≫ v = w ≫ f' := X.2.presentation_map_comm₁ Y.2 u
    have comm₂ : p ≫ u = preadditiveYoneda.map v ≫ p' := (X.2.presentation_map_comm₂ Y.2 u).symm
    set G := FinitelyPresented.lift F
    sorry


end Functor

end Nori
