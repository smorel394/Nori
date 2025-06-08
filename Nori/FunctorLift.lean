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
  cokernel.π ((FinitelyPresented.embedding C).map hX.presentation_map_f) ≫ hX.presentation_iso₂.inv

lemma IsFinitelyPresented.presentation_zero {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    (FinitelyPresented.embedding C).map hX.presentation_map_f ≫ hX.presentation_map_p₂ = 0 := by
  dsimp [IsFinitelyPresented.presentation_map_p₂]
  rw [← assoc, cokernel.condition, zero_comp]

def IsFinitelyPresented.presentation_colimit {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    IsColimit (CokernelCofork.ofπ hX.presentation_map_p₂ hX.presentation_zero) := sorry

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

@[reassoc]
lemma IsFinitelyPresented.presentation_map_comm₂' (X X' : FinitelyPresented C) (u : X ⟶ X') :
    (FinitelyPresented.embedding C).map (X.2.presentation_mapB X'.2 u) ≫ cokernel.π _ ≫
    X'.2.presentation_iso₂.inv = cokernel.π _ ≫ X.2.presentation_iso₂.inv ≫ u := by
  dsimp [IsFinitelyPresented.presentation_iso₂]
  erw [PreservesCokernel.π_iso_hom_assoc (IsFinitelyPresented C).ι]
  erw [X.2.presentation_map_comm₂ X'.2 u]
  slice_rhs 1 2 => erw [PreservesCokernel.π_iso_hom_assoc (IsFinitelyPresented C).ι]
  rfl

lemma presentation_cokernel_zero {X Y : FinitelyPresented C} (u : X ⟶ Y) :
    (FinitelyPresented.embedding C).map (biprod.desc (X.2.presentation_mapB Y.2 u) Y.2.presentation_map_f) ≫
    Y.2.presentation_map_p₂ ≫ cokernel.π u  = 0 := by
  rw [← cancel_epi ((FinitelyPresented.embedding C).mapBiprod _ _).inv]
  refine biprod.hom_ext' _ _ ?_ ?_
  · dsimp
    simp only [assoc, biprod.inl_desc_assoc, comp_zero]
    slice_lhs 1 2 => rw [← Functor.map_comp, biprod.inl_desc]
    conv_lhs => congr; rw [assoc, IsFinitelyPresented.presentation_map_comm₂']
    simp
  · dsimp
    simp only [assoc, biprod.inr_desc_assoc, comp_zero]
    slice_lhs 1 2 => rw [← Functor.map_comp, biprod.inr_desc]
    simp

def presentation_cokernel {X Y : FinitelyPresented C} (u : X ⟶ Y) {c : CokernelCofork u}
    (hc : IsColimit c) : IsColimit (CokernelCofork.ofπ (Z := c.pt)
    (f := (FinitelyPresented.embedding C).map (biprod.desc (X.2.presentation_mapB Y.2 u)
    (Y.2.presentation_map_f))) (Y.2.presentation_map_p₂ ≫ cokernel.π u ≫
    (hc.coconePointUniqueUpToIso (cokernelIsCokernel u)).inv)
    (by rw [← cancel_mono ((hc.coconePointUniqueUpToIso (cokernelIsCokernel u)).hom)]
        simp only [Cofork.ofπ_pt, assoc, Iso.inv_hom_id, comp_id, zero_comp]
        exact presentation_cokernel_zero u)) := by
  refine isColimitOfReflects (IsFinitelyPresented C).ι ?_
  refine (IsColimit.equivOfNatIsoOfIso (F := parallelPair (biprod.desc (preadditiveYoneda.map
    (X.2.presentation_mapB Y.2 u)) (preadditiveYoneda.map Y.2.presentation_map_f)) 0) (G :=
    (parallelPair ((FinitelyPresented.embedding C).map (biprod.desc (X.2.presentation_mapB Y.2 u)
    Y.2.presentation_map_f)) 0 ⋙ (IsFinitelyPresented C).ι)) ?_
    (CokernelCofork.ofπ (f := (biprod.desc (preadditiveYoneda.map
    (X.2.presentation_mapB Y.2 u)) (preadditiveYoneda.map Y.2.presentation_map_f)))
    (Y.2.presentation_p ≫ sorry) sorry (Z := (IsFinitelyPresented C).ι.obj c.pt))
    _ ?_).toFun ?_
  · sorry
  · sorry
  · sorry


/-
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
      (IsFinitelyPresented.presentation_map_comm₂' X Y u).symm
    set S := coker_sequence (C := Cᵒᵖ ⥤ AddCommGrp) p (ShortComplex.mk
      ((FinitelyPresented.embedding C).map f')
      p' Y.2.presentation_zero) ((FinitelyPresented.embedding C).map v) u comm₂
    set e := PreservesCokernel.iso (IsFinitelyPresented C).ι u
    set e' := hc.coconePointUniqueUpToIso (cokernelIsCokernel u)
    set Q : ((FinitelyPresented.embedding C).obj B').1 ⟶ Z.1 := S.g ≫ e.inv ≫ e'.inv
    set G : ((FinitelyPresented.embedding C).obj (B ⊞ A')).1 ⟶
      ((FinitelyPresented.embedding C).obj B').1 :=
      ((FinitelyPresented.embedding C).mapBiprod _ _).hom ≫
      ((IsFinitelyPresented C).ι.mapBiprod _ _).hom ≫ S.f
    have eq₀ : (embedding C).map (biprod.desc v f') ≫ Q = 0 := by
      apply (IsFinitelyPresented C).ι.map_injective
      rw [← cancel_epi ((FinitelyPresented.embedding C ⋙
        (IsFinitelyPresented C).ι).mapBiprod B A').inv]
      rw [Functor.map_comp, Functor.map_zero, ← cancel_mono
        ((IsFinitelyPresented C).ι.mapIso e').hom]
      rw [← cancel_mono e.hom]
      dsimp [Q]
      slice_lhs 6 7 => change ((IsFinitelyPresented C).ι.mapIso e').inv ≫
                         ((IsFinitelyPresented C).ι.mapIso e').hom
                       rw [Iso.inv_hom_id]
      rw [id_comp]
      slice_lhs 5 6 => rw [Iso.inv_hom_id]
      dsimp
      simp only [comp_id, comp_zero, zero_comp, Q]
      refine biprod.hom_ext' _ _ ?_ ?_
      · dsimp
        simp only [biprod.inl_desc_assoc, comp_zero, S, Z, Q]
        slice_lhs 1 2 => erw [← (FinitelyPresented.embedding C).map_comp]
                         rw [biprod.inl_desc]
        erw [← comm₂]
        change (IsFinitelyPresented C).ι.map _ ≫ cokernel.π ((IsFinitelyPresented C).ι.map u) = 0
        rw [Functor.map_comp, assoc, cokernel.condition, comp_zero]
      · dsimp
        simp only [biprod.inr_desc_assoc, comp_zero, S, Z, Q]
        slice_lhs 1 2 => erw [← (FinitelyPresented.embedding C).map_comp]
                         rw [biprod.inr_desc]
        dsimp [f', p']
        conv_lhs => congr; erw [Y.2.presentation_zero]
        rw [zero_comp]
    have colim : IsColimit (CokernelCofork.ofπ
      (f := (embedding C).map (biprod.desc v f')) Q eq₀) := sorry
-/

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

def FinitelyPresented.lift :
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

-- This is nontrivial and will use `IsFinitelyPresented.cokernel_map` again.
instance : (FinitelyPresented.lift F).Additive where
  map_add {X Y} {f g} := by
    dsimp [FinitelyPresented.lift]
    rw [← cancel_epi (cokernel.π _)]
    simp only [cokernel.π_desc, Preadditive.comp_add]
    sorry

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

def FinitelyPresented.embeddingLiftIso :
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
      (IsFinitelyPresented.presentation_map_comm₂' X Y u).symm
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
    have colim : IsColimit (CokernelCofork.ofπ
      (f := (embedding C).map (biprod.desc v f')) Q eq₀) := sorry
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
        rw [cokernel.condition_assoc, zero_comp]
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
