import GaloisForLFunctions.HTGeometry.HankelSliceRing
import GaloisForLFunctions.HTGeometry.HankelResolutionMorphism
import GaloisForLFunctions.HTGeometry.CechKernelChase

/-!
# The slice `v_0 = 1` of the incidence variety: cohomology and global sections

`Y_1 = Proj(B_j / (v_0 - 1))`.  Its Čech complexes are exact (`sliceCech_exactAt`), so
`H^q(Y_1, 𝒪) = 0` for `q > 0` and every global section comes from a moment polynomial.  The kernel
of `K[x] → Γ(Y_1, 𝒪)` is `secantIdealUpTo + (x_0 - 1)`: a polynomial dying on the slice is, chart by
chart, `(v_0 - 1)` times a section of `𝒪_Y`; these glue (the slice element is a nonzerodivisor on the
overlaps) to a global section `Q` of `𝒪_Y`, and `P - (x_0 - 1) Q` dies on `Y`.

* `HTGeometry.SliceY`, `HTGeometry.iSup_sliceChart_eq_top`, `HTGeometry.sliceY_cohomology_vanishing`.
* `HTGeometry.sliceMomentToGlobal`, `HTGeometry.ker_sliceMomentToGlobal`,
  `HTGeometry.sliceGlobalEquiv`.
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open GaloisForLFunctions.HTGeometry.StableCoordinate.HomogeneousQuotient

universe u

variable {K : Type u} [Field K] {r N j : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local notation "𝒵" => projGrading K (Fin (r + 1)) (Fin N)

variable (K r N j) in
/-- **The slice** `Y_1 = Proj(B_j / (v_0 - 1))`. -/
noncomputable abbrev SliceY : Scheme.{u} := Proj (sliceGrading K r N j)

variable (K r N j) in
/-- The evaluation charts of the slice. -/
noncomputable abbrev sliceChart (k : Fin (r + 1)) : (SliceY K r N j).Opens :=
  Proj.basicOpen (sliceGrading K r N j) (sChart K r N j k)

/-- **The evaluation charts cover the slice.** -/
theorem iSup_sliceChart_eq_top [CharZero K] : ⨆ k, sliceChart K r N j k = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _ (fun k => ⟨1, sChart_mem j k⟩) ?_
  rw [eq_top_iff]
  rintro x -
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction a using MvPolynomial.induction_on with
  | C c =>
    have : Ideal.Quotient.mk (sliceIdeal K r N j) (MvPolynomial.C c)
        = algebraMap (sliceGrading K r N j 0) _ ⟨_, mk_mem_piece 𝒵 _
          (show MvPolynomial.C c ∈ 𝒵 0 from MvPolynomial.isWeightedHomogeneous_C _ _)⟩ := rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq =>
    rw [map_add]
    exact Subalgebra.add_mem _ hp hq
  | mul_X p v hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp ?_
    rcases v with i | n
    · rw [show (MvPolynomial.X (Sum.inl i) : IncRing K r N) = zv K r N i from rfl,
        zv_eq_sum_chartForm, map_sum]
      refine Subalgebra.sum_mem _ fun k _ => ?_
      rw [MvPolynomial.smul_eq_C_mul, map_mul]
      refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨k, rfl⟩)
      have : Ideal.Quotient.mk (sliceIdeal K r N j) (MvPolynomial.C ((nodeMatrix K r)⁻¹ i k))
          = algebraMap (sliceGrading K r N j 0) _ ⟨_, mk_mem_piece 𝒵 _
            (show MvPolynomial.C ((nodeMatrix K r)⁻¹ i k) ∈ 𝒵 0 from
              MvPolynomial.isWeightedHomogeneous_C _ _)⟩ := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    · have : Ideal.Quotient.mk (sliceIdeal K r N j) (MvPolynomial.X (Sum.inr n))
          = algebraMap (sliceGrading K r N j 0) _ ⟨_, mk_mem_piece 𝒵 _ (vv_mem (K := K) (r := r) n)⟩ :=
        rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _

/-- **`H^q(Y_1, 𝒪) = 0` for every `q > 0`.** -/
theorem sliceY_cohomology_vanishing [CharZero K]
    [CategoryTheory.HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} (SliceY K r N j))] (hj : j + r ≤ N)
    (q : ℕ) (x : RHTower.deningerSheafCohomology.{u} ⊤ (schemeAbSheaf (SliceY K r N j)) (q + 1)) :
    x = 0 :=
  proj_cohomology_vanishing (𝒜 := sliceGrading K r N j) (w := sChart K r N j) (sChart_mem j)
    iSup_sliceChart_eq_top (fun _ => sliceCech_exactAt hj (Nat.zero_le _)) q x

/-! ## Global sections -/

variable (K r N j) in
/-- The moments in degree zero of the slice ring. -/
noncomputable def sliceMomentToZero : MvPolynomial (Fin N) K →+* sliceGrading K r N j 0 where
  toFun P := ⟨Ideal.Quotient.mk _ (momentEmbed K r N P), mk_mem_piece 𝒵 _ (momentEmbed_mem P)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' P Q := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' P Q := Subtype.ext (by simp)

theorem sliceMomentToZero_surjective : Function.Surjective (sliceMomentToZero K r N j) := by
  rintro ⟨x, a, ha, rfl⟩
  obtain ⟨P, rfl⟩ := exists_momentEmbed_eq ha
  exact ⟨P, rfl⟩

variable (K r N j) in
/-- **The moments as global sections of `𝒪_{Y_1}`.** -/
noncomputable def sliceMomentToGlobal : MvPolynomial (Fin N) K →+* Γ(SliceY K r N j, ⊤) :=
  (zeroToGlobal (sliceGrading K r N j)).hom.comp (sliceMomentToZero K r N j)

/-- **Every global section of `𝒪_{Y_1}` is a moment polynomial.** -/
theorem sliceMomentToGlobal_surjective [CharZero K] (hj : j + r ≤ N) :
    Function.Surjective (sliceMomentToGlobal K r N j) := by
  intro σ
  obtain ⟨b, hb⟩ := exists_zeroToGlobal_eq (𝒜 := sliceGrading K r N j) (w := sChart K r N j)
    (sChart_mem j) iSup_sliceChart_eq_top (sliceCech_exactAt hj le_rfl) σ
  obtain ⟨P, rfl⟩ := sliceMomentToZero_surjective (K := K) (r := r) (N := N) (j := j) b
  exact ⟨P, hb⟩

/-! ## The kernel -/

variable (K N) in
/-- The first moment `x_0` (zero when `N = 0`). -/
noncomputable def firstMoment : MvPolynomial (Fin N) K :=
  if h : 0 < N then MvPolynomial.X ⟨0, h⟩ else 0

theorem momentEmbed_firstMoment : momentEmbed K r N (firstMoment K N) = vAt K r N 0 := by
  rw [firstMoment, vAt]
  split_ifs with h
  · exact momentEmbed_X _
  · exact map_zero _

/-- **The ideal of the affine chart `x_0 = 1`** of the secant variety of the first `j + r` moments. -/
noncomputable def sliceKernel (K : Type u) [Field K] (N r j : ℕ) : Ideal (MvPolynomial (Fin N) K) :=
  secantIdealUpTo K N r j ⊔ Ideal.span {firstMoment K N - 1}

theorem fromZero_eq_zero_iff' {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {f : A} (y : 𝒜 0) :
    HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) y = 0 ↔
      ∃ m : ℕ, f ^ m * (y : A) = 0 := by
  rw [← HomogeneousLocalization.val_injective _ |>.eq_iff, HomogeneousLocalization.val_zero]
  change HomogeneousLocalization.val (HomogeneousLocalization.mk ⟨0, y, 1, _⟩) = 0 ↔ _
  rw [HomogeneousLocalization.val_mk]
  change Localization.mk (y : A) 1 = 0 ↔ _
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.map_eq_zero_iff (Submonoid.powers f)]
  constructor
  · rintro ⟨⟨_, m, rfl⟩, hm⟩
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨f ^ m, m, rfl⟩, hm⟩

theorem sliceMomentToGlobal_restrict (k : Fin (r + 1)) (P : MvPolynomial (Fin N) K) :
    ((SliceY K r N j).presheaf.map (homOfLE (le_top : sliceChart K r N j k ≤ ⊤)).op).hom
        (sliceMomentToGlobal K r N j P)
      = (Proj.awayToSection (sliceGrading K r N j) (sChart K r N j k)).hom
          (HomogeneousLocalization.fromZeroRingHom _ _ (sliceMomentToZero K r N j P)) :=
  zeroToGlobal_restrict _ (sChart_mem j k) one_pos _

theorem sliceAwayToSection_injective (k : Fin (r + 1)) :
    Function.Injective (Proj.awayToSection (sliceGrading K r N j) (sChart K r N j k)).hom := by
  haveI : IsIso (Proj.awayToSection (sliceGrading K r N j) (sChart K r N j k)) := by
    rw [← Proj.basicOpenIsoAway_hom _ _ (sChart_mem (K := K) (r := r) (N := N) j k) one_pos]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso _).1

theorem sliceMomentToGlobal_eq_zero_iff_chart (k : Fin (r + 1)) (P : MvPolynomial (Fin N) K) :
    ((SliceY K r N j).presheaf.map (homOfLE (le_top : sliceChart K r N j k ≤ ⊤)).op).hom
        (sliceMomentToGlobal K r N j P) = 0 ↔
      ∃ m : ℕ, chartForm K r N (node K k) ^ m * momentEmbed K r N P ∈ sliceIdeal K r N j := by
  rw [sliceMomentToGlobal_restrict, ← map_zero (Proj.awayToSection (sliceGrading K r N j)
    (sChart K r N j k)).hom, (sliceAwayToSection_injective k).eq_iff, fromZero_eq_zero_iff']
  simp only [sChart, sliceMomentToZero, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

/-- **Global sections of the slice are determined on the charts.** -/
theorem sliceGlobalSection_ext [CharZero K] {σ τ : Γ(SliceY K r N j, ⊤)}
    (h : ∀ k, ((SliceY K r N j).presheaf.map (homOfLE (le_top : sliceChart K r N j k ≤ ⊤)).op).hom σ
      = ((SliceY K r N j).presheaf.map (homOfLE (le_top : sliceChart K r N j k ≤ ⊤)).op).hom τ) :
    σ = τ :=
  TopCat.Sheaf.eq_of_locally_eq' (schemeAbSheaf (SliceY K r N j)) (sliceChart K r N j) ⊤
    (fun _ => homOfLE le_top) (le_of_eq iSup_sliceChart_eq_top.symm) σ τ h

theorem algebraMap_singleton_eq_zero_iff {M : Type*} [CommRing M] {ι : Type*} {w : ι → M} (k : ι)
    (x : M) : algebraMap M (LocAt w {k}) x = 0 ↔ ∃ m : ℕ, w k ^ m * x = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (wProd w {k}))]
  constructor
  · rintro ⟨⟨_, m, rfl⟩, hm⟩
    refine ⟨m, ?_⟩
    simpa [wProd] using hm
  · rintro ⟨m, hm⟩
    exact ⟨⟨_, m, rfl⟩, by simpa [wProd] using hm⟩

variable (K r N j) in
/-- The section `P` of `𝒪_{B_j}` over the covered set (degree zero). -/
noncomputable def emptySection (P : MvPolynomial (Fin N) K) :
    twPart (quotGrading K r N j) (qChart K r N j) ∅ 0 :=
  ⟨frac (qChart K r N j) ∅ 0 (Ideal.Quotient.mk _ (momentEmbed K r N P)),
    frac_mem_twPart (mk_mem_piece 𝒵 _ (momentEmbed_mem P)) (by simp)⟩

theorem twVal_res_emptySection (P : MvPolynomial (Fin N) K) (k : Fin (r + 1)) :
    twVal (𝒜 := quotGrading K r N j) (w := qChart K r N j) (qChart_mem j)
        ((hankelCech K r N j 0).res (Finset.empty_subset {k}) (emptySection K r N j P))
      = algebraMap (HankelQuot K r N j) (LocAt (qChart K r N j) {k})
          (Ideal.Quotient.mk _ (momentEmbed K r N P)) := by
  rw [twCech_res_val]
  change resLoc _ _ (frac (qChart K r N j) ∅ 0 _) = _
  rw [frac_zero_eq]
  exact resLoc_algebraMap _ _

/-- **The kernel of the moments on the slice is the ideal of the chart `x_0 = 1`.** -/
theorem ker_sliceMomentToGlobal [CharZero K] (hj : j + r ≤ N) :
    RingHom.ker (sliceMomentToGlobal K r N j) = sliceKernel K N r j := by
  refine le_antisymm (fun P hP => ?_) (sup_le ?_ ?_)
  · rw [RingHom.mem_ker] at hP
    have hzero : ∀ k, ∃ m, chartForm K r N (node K k) ^ m * momentEmbed K r N P
        ∈ sliceIdeal K r N j := fun k =>
      (sliceMomentToGlobal_eq_zero_iff_chart k P).mp (by rw [hP, map_zero])
    -- the section `P` is `(v_0 - 1)` times a section of `𝒪_{B_j}`, chart by chart
    obtain ⟨b, hb⟩ := FinsetCechDatum.exists_bot_of_kernel
      (twMul0 (𝒜 := quotGrading K r N j) (qChart_mem j) (qSlice_mem j) 0)
      (twMap (𝒜 := quotGrading K r N j) (𝒜' := sliceGrading K r N j) (sliceMap K r N j)
        (sliceMap_qChart j) (fun _ _ hx => sliceMap_mem j hx) (qChart_mem j) (sChart_mem j) 0)
      (fun s hs y hy => twMap_exact0 (𝒜 := quotGrading K r N j) (𝒜' := sliceGrading K r N j)
        (sliceMap K r N j) (sliceMap_qChart j) (fun _ _ hx => sliceMap_mem j hx) (qChart_mem j)
        (sChart_mem j) (qSlice_mem j) (sliceMap_ker j) 0 (Finset.card_pos.mp (by omega)) y hy)
      (fun s hs => twMul0_injective (𝒜 := quotGrading K r N j) (qChart_mem j) (qSlice_mem j) 0
        (algebraMap_qSlice_mem_nonZeroDivisors j (sliceReg_wProd hj (Finset.card_pos.mp (by omega)))
          (wProd_qChart j s)))
      (hankelCech_exactAt (K := K) j hj 0 0 le_rfl) (emptySection K r N j P) (fun k => by
        apply twVal_injective (𝒜 := sliceGrading K r N j) (w := sChart K r N j) (sChart_mem j)
        rw [twMap_app_val, twVal_res_emptySection, locMap_algebraMap]
        change algebraMap _ (LocAt (sChart K r N j) {k})
          (Ideal.Quotient.mk (sliceIdeal K r N j) (momentEmbed K r N P)) = 0
        rw [algebraMap_singleton_eq_zero_iff]
        obtain ⟨m, hm⟩ := hzero k
        exact ⟨m, by rw [sChart, ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact hm⟩)
    -- the glued section comes from a moment polynomial `Q`
    obtain ⟨bb, hbb⟩ := exists_zero_of_mem_twPart_empty (𝒜 := quotGrading K r N j)
      (w := qChart K r N j) (b : twPart _ _ ∅ 0).2
    obtain ⟨Q, rfl⟩ := momentToZero_surjective (K := K) (r := r) (N := N) j bb
    have hdiff : P - (firstMoment K N - 1) * Q ∈ RingHom.ker (momentToGlobal K r N j) := by
      rw [RingHom.mem_ker]
      refine globalSection_ext fun k => ?_
      rw [map_zero, momentToGlobal_eq_zero_iff_chart]
      have h1 := congrArg (twVal (𝒜 := quotGrading K r N j) (w := qChart K r N j) (qChart_mem j)) (hb k)
      rw [twCech_res_val, twMul0_app_val, twVal_res_emptySection, map_mul,
        resLoc_algebraMap] at h1
      change algebraMap _ (LocAt (qChart K r N j) {k}) (qSlice K r N j) *
          resLoc (qChart K r N j) (Finset.empty_subset {k}) (b : twPart _ _ ∅ 0).1 = _ at h1
      rw [hbb, resLoc_algebraMap, ← map_mul, ← sub_eq_zero, ← map_sub,
        algebraMap_singleton_eq_zero_iff] at h1
      obtain ⟨m, hm⟩ := h1
      refine ⟨m, ?_⟩
      rw [qChart, momentToZero_coe, qSlice, ← map_mul, ← map_sub, ← map_pow, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem] at hm
      convert neg_mem_iff.mpr hm using 1
      rw [map_sub, map_mul, map_sub, map_one, momentEmbed_firstMoment, sliceElem]
      ring
    rw [ker_momentToGlobal hj] at hdiff
    have : P = (P - (firstMoment K N - 1) * Q) + (firstMoment K N - 1) * Q := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hdiff)
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨c, hbound, -, hc, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    refine sliceGlobalSection_ext fun k => ?_
    rw [map_zero, sliceMomentToGlobal_eq_zero_iff_chart]
    exact ⟨1, by rw [pow_one]; exact Ideal.mem_sup_left (chartForm_mul_minor_mem _ hbound hc)⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      sliceMomentToGlobal, RingHom.comp_apply]
    have : sliceMomentToZero K r N j (firstMoment K N - 1) = 0 := by
      apply Subtype.ext
      change Ideal.Quotient.mk _ (momentEmbed K r N (firstMoment K N - 1)) = 0
      rw [map_sub, map_one, momentEmbed_firstMoment, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.subset_span rfl)
    rw [this, map_zero]

/-! ## The resolution morphism of the chart `x_0 = 1` -/

/-- **`Γ(Y_1, 𝒪) ≅ K[x] / (secantIdealUpTo + (x_0 - 1))`.** -/
noncomputable def sliceGlobalEquiv [CharZero K] (hj : j + r ≤ N) :
    MvPolynomial (Fin N) K ⧸ sliceKernel K N r j ≃+* Γ(SliceY K r N j, ⊤) :=
  (Ideal.quotEquivOfEq (ker_sliceMomentToGlobal hj).symm).trans
    (RingHom.quotientKerEquivOfSurjective (sliceMomentToGlobal_surjective hj))

theorem sliceGlobalEquiv_mk [CharZero K] (hj : j + r ≤ N) (P : MvPolynomial (Fin N) K) :
    sliceGlobalEquiv hj (Ideal.Quotient.mk _ P) = sliceMomentToGlobal K r N j P := rfl

variable (K r N j) in
/-- The coordinate ring of the chart `x_0 = 1`. -/
abbrev ChartRing := MvPolynomial (Fin N) K ⧸ sliceKernel K N r j

variable (K r N) in
/-- `K[x]/(…) ≅ Γ(Y_1, 𝒪)` in `CommRingCat`. -/
noncomputable def sliceGlobalIso [CharZero K] (hj : j + r ≤ N) :
    CommRingCat.of (ChartRing K r N j) ≅ Γ(SliceY K r N j, ⊤) where
  hom := CommRingCat.ofHom (sliceGlobalEquiv hj).toRingHom
  inv := CommRingCat.ofHom (sliceGlobalEquiv hj).symm.toRingHom
  hom_inv_id := CommRingCat.hom_ext (RingHom.ext (sliceGlobalEquiv hj).symm_apply_apply)
  inv_hom_id := CommRingCat.hom_ext (RingHom.ext (sliceGlobalEquiv hj).apply_symm_apply)

variable (K r N) in
/-- **The resolution morphism of the chart** `Y_1 → Spec (K[x]/(…))`. -/
noncomputable def sliceResolution [CharZero K] (hj : j + r ≤ N) :
    SliceY K r N j ⟶ Spec (CommRingCat.of (ChartRing K r N j)) :=
  (SliceY K r N j).toSpecΓ ≫ Spec.map (sliceGlobalIso K r N hj).hom

theorem sliceResolution_appTop_isIso [CharZero K] (hj : j + r ≤ N) :
    IsIso (sliceResolution K r N hj).appTop := by
  set e := sliceGlobalIso K r N hj
  have h : (Spec.map e.hom).appTop = (Scheme.ΓSpecIso _).hom ≫ e.hom ≫ (Scheme.ΓSpecIso _).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [sliceResolution, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, h]
  infer_instance

instance finiteType_sliceGrading :
    Algebra.FiniteType (sliceGrading K r N j 0) (SliceQuot K r N j) := by
  haveI : IsScalarTower K (sliceGrading K r N j 0) (SliceQuot K r N j) :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := sliceGrading K r N j 0)
      (A := SliceQuot K r N j) fun _ => rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType K _ _

theorem sliceResolution_comp_quotient [CharZero K] (hj : j + r ≤ N) :
    sliceResolution K r N hj ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))
      = Proj.toSpecZero (sliceGrading K r N j) ≫
          Spec.map (CommRingCat.ofHom (sliceMomentToZero K r N j)) := by
  rw [toSpecZero_eq, sliceResolution, Category.assoc, Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  rfl

/-- **The resolution of the chart is proper.** -/
theorem sliceResolution_isProper [CharZero K] (hj : j + r ≤ N) :
    IsProper (sliceResolution K r N hj) := by
  set g : Spec (CommRingCat.of (ChartRing K r N j)) ⟶ Spec (CommRingCat.of (MvPolynomial (Fin N) K)) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))
  have hcomp := sliceResolution_comp_quotient (K := K) hj
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (sliceMomentToZero K r N j))) :=
    IsClosedImmersion.spec_of_surjective _ sliceMomentToZero_surjective
  haveI : IsProper (sliceResolution K r N hj ≫ g) := by
    rw [hcomp]
    infer_instance
  exact IsProper.of_comp _ g

variable (K r N j) in
/-- The structure map `Y_1 → Spec K`. -/
noncomputable def sliceYStruct : SliceY K r N j ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (sliceGrading K r N j) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (sliceGrading K r N j 0)))

/-- **The resolution of the chart is a morphism over `K`.** -/
theorem sliceResolution_over [CharZero K] (hj : j + r ≤ N) :
    sliceResolution K r N hj ≫ Spec.map (CommRingCat.ofHom (algebraMap K (ChartRing K r N j)))
      = sliceYStruct K r N j := by
  have h1 : CommRingCat.ofHom (algebraMap K (ChartRing K r N j))
      = CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin N) K)) ≫
          CommRingCat.ofHom (Ideal.Quotient.mk (sliceKernel K N r j)) := rfl
  have h2 : CommRingCat.ofHom (algebraMap K (sliceGrading K r N j 0))
      = CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin N) K)) ≫
          CommRingCat.ofHom (sliceMomentToZero K r N j) := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => Subtype.ext ?_)
    simp [sliceMomentToZero, momentEmbed]
    rfl
  rw [h1, Spec.map_comp, ← Category.assoc, sliceResolution_comp_quotient, sliceYStruct, h2,
    Spec.map_comp, Category.assoc]

end HTGeometry
