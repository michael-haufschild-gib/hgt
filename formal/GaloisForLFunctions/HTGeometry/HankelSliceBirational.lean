import GaloisForLFunctions.HTGeometry.HankelSliceChart
import GaloisForLFunctions.HTGeometry.HankelRationalSingularities

/-!
# The affine chart `x_0 = 1` of the secant variety has rational singularities

The slice `Y_1 = Proj(B_j/(v_0 - 1))` is integral: its charts are the linear hypersurfaces
`K[a][b]/(∑ c_{0,m} b_m - 1)` (domains), and each meets the chart `z_0 ≠ 0` (the chart forms are
polynomials in `a` with constant term `1`, and `K[a]` embeds in the hypersurface).  The resolution
`Y_1 → Spec(K[x]/(secantIdealUpTo + (x_0 - 1)))` is birational: on the chart `z_0 ≠ 0` Cramer's rule
applies as for `Y`, and the trailing minor `δ` survives the slice — in the chart coordinates `δ` is a
form of degree `r` in the free moments, and the dehomogenization `b ↦ b / v_0` kills `v_0 - 1` and
multiplies `δ` by the unit `v_0^{-r}`.

* `HTGeometry.sliceY_isIntegral`.
* `HTGeometry.sliceResolution_birational`.
* `HTGeometry.chartRing_hasRationalSingularities`,
  `HTGeometry.hankelChartRing_hasRationalSingularities`.
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open GaloisForLFunctions.HTGeometry.StableCoordinate.HomogeneousQuotient

variable {K : Type} [Field K] {r N j : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local notation "𝒵" => projGrading K (Fin (r + 1)) (Fin N)
local notation "𝒜" => quotGrading K r N j
local notation "𝒜'" => sliceGrading K r N j

/-! ## Forms in the free moments survive the slice -/

/-- **Dehomogenization**: a determinant of solved moments vanishing modulo `v_0 - 1` vanishes.  The
map `b ↦ b / v_0` (into `K[a, b][v_0⁻¹]`) kills `v_0 - 1` and sends the determinant `D` (a form of
degree `r` in `b`) to `v_0^{-r} D`. -/
theorem det_chartSol_eq_zero (hr : 0 < r) (hj : j + r ≤ N) (e : Fin r → Fin r → ℕ)
    (h : (Matrix.of fun i i' => chartSol K r N j (e i i')).det ∈ Ideal.span {chartSol K r N j 0 - 1}) :
    (Matrix.of fun i i' => chartSol K r N j (e i i')).det = 0 := by
  set L := chartSol K r N j 0 with hLdef
  have hL : L ≠ 0 := by
    intro hL0
    haveI := sliceChartPoly_isDomain (K := K) hr hj
    have htop : Ideal.span {L - 1} = ⊤ := by
      rw [hL0, zero_sub, Ideal.span_singleton_neg, Ideal.span_singleton_one]
    exact not_subsingleton (SliceChartPoly K r N j) (Ideal.Quotient.subsingleton_iff.mpr htop)
  set u : Localization.Away L := IsLocalization.Away.invSelf L
  have hu : IsUnit u := IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf L)
  set Ψ : ChartPoly K r (N - j) →ₐ[K] Localization.Away L := aeval (Sum.elim
    (fun i => algebraMap (ChartPoly K r (N - j)) (Localization.Away L) (X (Sum.inl i)))
    (fun m => algebraMap (ChartPoly K r (N - j)) (Localization.Away L) (X (Sum.inr m)) * u))
  have hΨc : ∀ p : MvPolynomial (Fin r) K,
      Ψ (rename Sum.inl p) = algebraMap (ChartPoly K r (N - j)) (Localization.Away L) (rename Sum.inl p) := by
    intro p
    have : Ψ.comp (rename Sum.inl) = (IsScalarTower.toAlgHom K (ChartPoly K r (N - j))
        (Localization.Away L)).comp (rename Sum.inl) := algHom_ext fun i => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, aeval_X, Sum.elim_inl,
        IsScalarTower.coe_toAlgHom']
    exact DFunLike.congr_fun this p
  have hΨ : ∀ n, Ψ (chartSol K r N j n)
      = algebraMap (ChartPoly K r (N - j)) (Localization.Away L) (chartSol K r N j n) * u := by
    intro n
    rw [chartSol_eq_sum (by omega), map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_mul, hΨc, aeval_X, Sum.elim_inr, mul_assoc]
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h
  have h1 : Ψ (L - 1) = 0 := by
    have h0 := hΨ 0
    rw [← hLdef] at h0
    rw [map_sub, map_one, h0, IsLocalization.Away.mul_invSelf, sub_self]
  have h2 : Ψ (Matrix.of fun i i' => chartSol K r N j (e i i')).det = 0 := by
    rw [← hq, map_mul, h1, mul_zero]
  have h3 : Ψ (Matrix.of fun i i' => chartSol K r N j (e i i')).det
      = u ^ r * algebraMap (ChartPoly K r (N - j)) (Localization.Away L)
          (Matrix.of fun i i' => chartSol K r N j (e i i')).det := by
    rw [AlgHom.map_det, RingHom.map_det]
    have hM : Ψ.mapMatrix (Matrix.of fun i i' => chartSol K r N j (e i i'))
        = u • (algebraMap (ChartPoly K r (N - j)) (Localization.Away L)).mapMatrix
            (Matrix.of fun i i' => chartSol K r N j (e i i')) := by
      refine Matrix.ext fun i i' => ?_
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hΨ, Matrix.smul_apply,
        RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, mul_comm]
    rw [hM, Matrix.det_smul, Fintype.card_fin]
  rw [h3] at h2
  have h4 := (hu.pow r).mul_right_eq_zero.mp h2
  exact IsLocalization.injective (Localization.Away L) (powers_le_nonZeroDivisors_of_noZeroDivisors hL)
    (h4.trans (map_zero _).symm)

/-! ## The slice is integral -/

variable (K r) in
/-- The chart form `G(s)` on the chart `z_0 = 1`: `1 + ∑_i s^{i+1} a_i`. -/
noncomputable def chartFormPoly (s : K) : MvPolynomial (Fin r) K :=
  ∑ i : Fin (r + 1), (Fin.cons 1 X : Fin (r + 1) → MvPolynomial (Fin r) K) i * C (s ^ (i : ℕ))

/-- The chart forms in the chart coordinates are polynomials in `a`. -/
theorem incChartEval_chartForm (s : K) :
    incChartEval K r N j (chartForm K r N s) = rename Sum.inl (chartFormPoly K r s) := by
  have hcf : chartForm K r N s = ∑ i : Fin (r + 1), zv K r N i * algebraMap K _ (s ^ (i : ℕ)) := by
    rw [chartForm, gPoly, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_pow]
  rw [hcf, map_sum, chartFormPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, incChartEval_zv, AlgHom.commutes, rename_C, MvPolynomial.algebraMap_eq]
  congr 1
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [chartZ]
  · simp [chartZ]

theorem constantCoeff_chartFormPoly (s : K) : constantCoeff (chartFormPoly K r s) = 1 := by
  rw [chartFormPoly, map_sum, Fin.sum_univ_succ]
  simp

theorem isDomain_sliceChart (hr : 0 < r) (hj : j + r ≤ N) (k : Fin (r + 1)) :
    IsDomain (Away 𝒜' (sChart K r N j k)) := by
  haveI := sliceChartPoly_isDomain (K := K) hr hj
  exact (sliceChartEquiv K r N hj (node K k)).symm.toMulEquiv.isDomain _

/-- **Every chart of the slice meets the chart `z_0 ≠ 0`.** -/
theorem sliceChart_inter_nonempty (hr : 0 < r) (hj : j + r ≤ N) (k : Fin (r + 1)) :
    ((sliceChart K r N j k : Set (SliceY K r N j)) ∩ sliceChart K r N j 0).Nonempty := by
  haveI := isDomain_sliceChart (K := K) hr hj k
  have hpre := Proj.awayι_preimage_basicOpen 𝒜' (sChart_mem (K := K) (r := r) (N := N) j k)
    one_pos (sChart_mem j 0) one_pos
  set x := Away.isLocalizationElem (sChart_mem (K := K) (r := r) (N := N) j k) (sChart_mem j 0)
  have hu : sChart K r N j 0 ^ 1 ∈ 𝒜' 1 := by rw [pow_one]; exact sChart_mem _ _
  have hx : x ≠ 0 := by
    intro h0
    have h1 : (linFrac (sT_mem (node K k)) hu : Away 𝒜' (sT K r N j (node K k))) = 0 := h0
    have h2 := congrArg (slicePsi K r N hj (node K k)) h1
    rw [slicePsi_linFrac, map_zero, pow_one] at h2
    change Ideal.Quotient.mk _ (incChartEval K r N j (momentShift K r N (-node K k)
      (chartForm K r N (node K 0)))) = 0 at h2
    rw [node_zero, chartForm_zero_eq, momentShift_zv_zero, incChartEval_chartForm] at h2
    have h3 := sliceChartPoly_rename_injective (K := K) hr hj (a₂ := 0)
      (h2.trans (by simp only [map_zero]))
    have h4 := congrArg constantCoeff h3
    rw [constantCoeff_chartFormPoly, map_zero] at h4
    exact one_ne_zero h4
  have hne : Proj.awayι 𝒜' _ (sChart_mem j k) one_pos ⁻¹ᵁ sliceChart K r N j 0 ≠ ⊥ := by
    intro hbot
    rw [sliceChart, hpre] at hbot
    exact hx (isNilpotent_iff_eq_zero.mp ((PrimeSpectrum.basicOpen_eq_bot_iff x).mp hbot))
  obtain ⟨p, hp⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne
  refine ⟨Proj.awayι 𝒜' _ (sChart_mem j k) one_pos p, ?_, hp⟩
  rw [SetLike.mem_coe, sliceChart, ← Proj.opensRange_awayι 𝒜' _ (sChart_mem j k) one_pos]
  exact ⟨p, rfl⟩

theorem sliceChart_isIrreducible (hr : 0 < r) (hj : j + r ≤ N) (k : Fin (r + 1)) :
    IsIrreducible (sliceChart K r N j k : Set (SliceY K r N j)) := by
  haveI := isDomain_sliceChart (K := K) hr hj k
  rw [sliceChart, ← Proj.opensRange_awayι 𝒜' _ (sChart_mem j k) one_pos,
    Scheme.Hom.coe_opensRange, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _
    (Proj.awayι 𝒜' _ (sChart_mem j k) one_pos).continuous.continuousOn

/-- **The slice is irreducible.** -/
theorem sliceY_irreducibleSpace [CharZero K] (hr : 0 < r) (hj : j + r ≤ N) :
    IrreducibleSpace (SliceY K r N j) := by
  have hcl : closure (sliceChart K r N j 0 : Set (SliceY K r N j)) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    have hy : y ∈ (⨆ k, sliceChart K r N j k) := by
      rw [iSup_sliceChart_eq_top (K := K) (r := r) (N := N) (j := j)]
      trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact closure_mono Set.inter_subset_right
      (subset_closure_inter_of_isPreirreducible_of_isOpen (sliceChart_isIrreducible hr hj k).2
        (sliceChart K r N j 0).isOpen (sliceChart_inter_nonempty hr hj k) hk)
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hcl]
  exact (sliceChart_isIrreducible hr hj 0).closure

/-- **The slice is reduced.** -/
theorem sliceY_isReduced [CharZero K] (hr : 0 < r) (hj : j + r ≤ N) : IsReduced (SliceY K r N j) := by
  haveI : ∀ k, IsReduced (sliceChart K r N j k).toScheme := fun k => by
    haveI := isDomain_sliceChart (K := K) hr hj k
    exact isReduced_of_isOpenImmersion
      (Proj.basicOpenIsoSpec 𝒜' _ (sChart_mem j k) one_pos).hom
  let 𝒰 := (SliceY K r N j).openCoverOfIsOpenCover (sliceChart K r N j)
    (iSup_sliceChart_eq_top (K := K) (r := r) (N := N) (j := j))
  haveI : ∀ k, IsReduced (𝒰.X k) := fun k => (inferInstance : IsReduced (sliceChart K r N j k).toScheme)
  exact IsReduced.of_openCover _ 𝒰

/-- **The slice is integral.** -/
theorem sliceY_isIntegral [CharZero K] (hr : 0 < r) (hj : j + r ≤ N) : IsIntegral (SliceY K r N j) := by
  haveI := sliceY_isReduced (K := K) hr hj
  haveI := sliceY_irreducibleSpace (K := K) hr hj
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-! ## The trailing minor on the slice -/

theorem chartPsi_chartAlpha_coord (hj : j + r ≤ N) (m : ℕ) :
    chartPsi K r N hj (node K (0 : Fin (r + 1)))
        (chartAlpha K r N j (GaloisForLFunctions.HTGeometry.hankelCoord K N m)) = chartSol K r N j m := by
  rw [chartAlpha_coord, chartPsi_fromZero, chartQuotEval_shiftV]

theorem chartPsi_chartAlpha_trailMinor (hj : j + r ≤ N) :
    chartPsi K r N hj (node K (0 : Fin (r + 1))) (chartAlpha K r N j (trailMinor K r N j))
      = (Matrix.of fun j' i : Fin r => chartSol K r N j (j - r + 1 + i + j')).det := by
  rw [trailMinor, ← RingHom.comp_apply, RingHom.map_det]
  congr 1
  refine Matrix.ext fun j' i => ?_
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, trailMat, Matrix.of_apply, Matrix.of_apply,
    RingHom.comp_apply, chartPsi_chartAlpha_coord]

variable (K r N j) in
/-- The moments on the slice chart `z_0 ≠ 0`. -/
noncomputable def sliceAlpha : MvPolynomial (Fin N) K →+* Away 𝒜' (sT K r N j (node K (0 : Fin (r + 1)))) :=
  (fromZeroRingHom 𝒜' _).comp (sliceMomentToZero K r N j)

theorem sliceAlpha_eq (P : MvPolynomial (Fin N) K) :
    sliceAlpha K r N j P = sliceRho K r N j (node K (0 : Fin (r + 1))) (chartAlpha K r N j P) := by
  rw [chartAlpha, RingHom.comp_apply, sliceRho_fromZero]
  rfl

/-- **The trailing minor survives on the slice.** -/
theorem sliceAlpha_trailMinor_ne_zero [CharZero K] (hr : 0 < r) (hrj : r ≤ j) (hj : j + r ≤ N) :
    sliceAlpha K r N j (trailMinor K r N j) ≠ 0 := by
  intro h0
  have h1 := congrArg (slicePsi K r N hj (node K (0 : Fin (r + 1)))) h0
  rw [map_zero, sliceAlpha_eq, chartAlpha, RingHom.comp_apply, sliceRho_fromZero,
    slicePsi_fromZero] at h1
  have h2 : sliceQuotEval K r N hj (node K (0 : Fin (r + 1)))
      (sliceMap K r N j (momentToZero K r N j (trailMinor K r N j)))
      = Ideal.Quotient.mk _ (chartPsi K r N hj (node K (0 : Fin (r + 1)))
          (chartAlpha K r N j (trailMinor K r N j))) := by
    rw [sliceQuotEval_sliceMap, chartAlpha, RingHom.comp_apply, chartPsi_fromZero]
  rw [h2, Ideal.Quotient.eq_zero_iff_mem, chartPsi_chartAlpha_trailMinor] at h1
  have h3 := det_chartSol_eq_zero hr hj _ h1
  rw [← chartPsi_chartAlpha_trailMinor hj] at h3
  have h4 : chartAlpha K r N j (trailMinor K r N j) = 0 := by
    have := congrArg (chartPhi K r N j (node K (0 : Fin (r + 1)))) h3
    rwa [chartPhi_chartPsi, map_zero] at this
  exact trailMinor_notMem hrj hj ((chartAlpha_eq_zero_iff hj _).mp h4)

/-! ## Birationality -/

theorem sliceResolution_appTop_apply [CharZero K] (hj : j + r ≤ N) (x : ChartRing K r N j) :
    (sliceResolution K r N hj).appTop ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing K r N j))).inv x)
      = sliceGlobalEquiv hj x := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of (ChartRing K r N j))).inv ≫
      (sliceResolution K r N hj).appTop = (sliceGlobalIso K r N hj).hom := by
    rw [sliceResolution, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have h' := congrArg (fun φ => φ.hom x) h
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at h'
  exact h'

theorem sliceAwayToSection_bijective {f : SliceQuot K r N j} (hf : f ∈ 𝒜' 1) :
    Function.Bijective (Proj.awayToSection 𝒜' f).hom := by
  haveI : IsIso (Proj.awayToSection 𝒜' f) := by
    rw [← Proj.basicOpenIsoAway_hom _ _ hf one_pos]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

variable (K r N j) in
/-- The chart `z_0 ≠ 0` of the slice. -/
noncomputable abbrev sliceZeroOpen : (SliceY K r N j).Opens :=
  Proj.basicOpen 𝒜' (sT K r N j (node K (0 : Fin (r + 1))))

theorem sliceZeroOpen_isAffineOpen : IsAffineOpen (sliceZeroOpen K r N j) :=
  Proj.isAffineOpen_basicOpen _ _ (sT_mem _) one_pos

variable (K r N) in
/-- The moments restricted to the slice chart `z_0 ≠ 0`, from `Γ(Spec A_1)`. -/
noncomputable def sliceBeta [CharZero K] (hj : j + r ≤ N) :
    Γ(Spec (CommRingCat.of (ChartRing K r N j)), ⊤) →+* Γ(SliceY K r N j, sliceZeroOpen K r N j) :=
  ((SliceY K r N j).presheaf.map (homOfLE (le_top : sliceZeroOpen K r N j ≤ ⊤)).op).hom.comp
    (sliceResolution K r N hj).appTop.hom

theorem sliceBeta_apply [CharZero K] (hj : j + r ≤ N) (P : MvPolynomial (Fin N) K) :
    sliceBeta K r N hj ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ P))
      = (Proj.awayToSection 𝒜' (sT K r N j (node K (0 : Fin (r + 1))))).hom (sliceAlpha K r N j P) := by
  rw [sliceBeta, RingHom.comp_apply, sliceResolution_appTop_apply, sliceGlobalEquiv_mk]
  exact zeroToGlobal_restrict _ (sT_mem _) one_pos _

theorem sliceZeroOpen_nonempty (hr : 0 < r) (hj : j + r ≤ N) : Nonempty (sliceZeroOpen K r N j) := by
  obtain ⟨p, hp, -⟩ := sliceChart_inter_nonempty (K := K) hr hj 0
  exact ⟨⟨p, hp⟩⟩

theorem sliceBeta_injective [CharZero K] (hr : 0 < r) (hj : j + r ≤ N) :
    Function.Injective (sliceBeta K r N hj) := by
  haveI := sliceY_isIntegral (K := K) hr hj
  haveI := sliceZeroOpen_nonempty (K := K) hr hj
  haveI := sliceResolution_appTop_isIso (K := K) (r := r) (N := N) hj
  exact (map_injective_of_isIntegral _ (homOfLE (le_top : sliceZeroOpen K r N j ≤ ⊤))).comp
    (ConcreteCategory.bijective_of_isIso (sliceResolution K r N hj).appTop).1

variable (K r N j) in
/-- The trailing minor as a global function on the chart `Spec A_1`. -/
noncomputable def trailSlice : Γ(Spec (CommRingCat.of (ChartRing K r N j)), ⊤) :=
  (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ (trailMinor K r N j))

theorem sliceBeta_trailSlice_ne_zero [CharZero K] (hr : 0 < r) (hrj : r ≤ j) (hj : j + r ≤ N) :
    sliceBeta K r N hj (trailSlice K r N j) ≠ 0 := by
  rw [trailSlice, sliceBeta_apply, ← map_zero (Proj.awayToSection 𝒜' _).hom, Ne,
    (sliceAwayToSection_bijective (sT_mem _)).1.eq_iff]
  exact sliceAlpha_trailMinor_ne_zero hr hrj hj

theorem sliceBeta_gen [CharZero K] (hrj : r ≤ j) (hj : j + r ≤ N)
    (s : Γ(SliceY K r N j, sliceZeroOpen K r N j)) :
    ∃ (n : ℕ) (x : Γ(Spec (CommRingCat.of (ChartRing K r N j)), ⊤)),
      sliceBeta K r N hj (trailSlice K r N j) ^ n * s = sliceBeta K r N hj x := by
  obtain ⟨c, rfl⟩ := (sliceAwayToSection_bijective (sT_mem (K := K) (r := r) (N := N) (j := j)
    (node K (0 : Fin (r + 1))))).2 s
  obtain ⟨c₀, rfl⟩ := sliceRho_surjective (node K (0 : Fin (r + 1))) c
  obtain ⟨n, P, hP⟩ := chartZero_exists_pow_mul_eq hrj hj c₀
  refine ⟨n, (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ P), ?_⟩
  rw [trailSlice, sliceBeta_apply, sliceBeta_apply, ← map_pow, ← map_mul, sliceAlpha_eq,
    sliceAlpha_eq, ← map_pow, ← map_mul, hP]

variable (K r N) in
/-- **The source of the birational isomorphism**: `{δ ≠ 0}` inside the slice chart `z_0 ≠ 0`. -/
noncomputable abbrev sliceBirSource [CharZero K] (hj : j + r ≤ N) : (SliceY K r N j).Opens :=
  (SliceY K r N j).basicOpen (sliceBeta K r N hj (trailSlice K r N j))

variable (K r N j) in
/-- **The target**: `D(δ) ⊆ Spec A_1`. -/
noncomputable abbrev sliceBirTarget : (Spec (CommRingCat.of (ChartRing K r N j))).Opens :=
  (Spec (CommRingCat.of (ChartRing K r N j))).basicOpen (trailSlice K r N j)

theorem sliceBirSource_le [CharZero K] (hj : j + r ≤ N) :
    sliceBirSource K r N hj ≤ sliceResolution K r N hj ⁻¹ᵁ sliceBirTarget K r N j := by
  rw [Scheme.preimage_basicOpen_top, sliceBirSource, sliceBeta, RingHom.comp_apply,
    Scheme.basicOpen_res]
  exact inf_le_right

theorem sliceAppLE_bijective [CharZero K] (hr : 0 < r) (hrj : r ≤ j) (hj : j + r ≤ N) :
    Function.Bijective ((sliceResolution K r N hj).appLE (sliceBirTarget K r N j)
      (sliceBirSource K r N hj) (sliceBirSource_le _)).hom := by
  haveI := sliceZeroOpen_isAffineOpen.isLocalization_basicOpen
    (sliceBeta K r N hj (trailSlice K r N j))
  refine bijective_of_away (trailSlice K r N j) (sliceBeta K r N _) _ ?_
    (sliceBeta_injective hr _) (sliceBeta_gen hrj hj)
  intro x
  have e1 := congrArg (fun φ => φ.hom x) (Scheme.Hom.map_appLE (sliceResolution K r N hj)
    (sliceBirSource_le (K := K) hj)
    (homOfLE ((Spec (CommRingCat.of (ChartRing K r N j))).basicOpen_le (trailSlice K r N j))).op)
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at e1
  change _ = ((SliceY K r N j).presheaf.map _).hom (((SliceY K r N j).presheaf.map _).hom
    ((sliceResolution K r N hj).appTop.hom x))
  rw [RingHom.algebraMap_toAlgebra, e1, ← CommRingCat.comp_apply, ← Functor.map_comp,
    Scheme.Hom.appLE, CommRingCat.comp_apply]
  rfl

/-- **The slice resolution restricts to an isomorphism `{δ ≠ 0} ≅ D(δ)`.** -/
theorem sliceResLE_isIso [CharZero K] (hr : 0 < r) (hrj : r ≤ j) (hj : j + r ≤ N) :
    IsIso ((sliceResolution K r N hj).resLE (sliceBirTarget K r N j) (sliceBirSource K r N hj)
      (sliceBirSource_le _)) := by
  haveI : IsAffine (sliceBirTarget K r N j).toScheme :=
    (isAffineOpen_top (Spec (CommRingCat.of (ChartRing K r N j)))).basicOpen _
  haveI : IsAffine (sliceBirSource K r N hj).toScheme :=
    sliceZeroOpen_isAffineOpen.basicOpen _
  haveI : IsIso ((sliceResolution K r N hj).appLE (sliceBirTarget K r N j)
      (sliceBirSource K r N hj) (sliceBirSource_le _)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (sliceAppLE_bijective hr hrj hj)
  rw [← MorphismProperty.isomorphisms.iff,
    HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)]
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  infer_instance

/-- **The chart ring is a domain.** -/
theorem chartRing_isDomain [CharZero K] (hr : 0 < r) (hj : j + r ≤ N) : IsDomain (ChartRing K r N j) := by
  haveI := sliceY_isIntegral (K := K) hr hj
  haveI : Nonempty (⊤ : (SliceY K r N j).Opens) := by
    obtain ⟨p⟩ := sliceZeroOpen_nonempty (K := K) hr hj
    exact ⟨⟨p.1, trivial⟩⟩
  exact (sliceGlobalEquiv (K := K) (r := r) (N := N) hj).toMulEquiv.isDomain _

theorem sliceBirTarget_dense [CharZero K] (hr : 0 < r) (hrj : r ≤ j) (hj : j + r ≤ N) :
    Dense (sliceBirTarget K r N j : Set (Spec (CommRingCat.of (ChartRing K r N j)))) := by
  haveI := chartRing_isDomain (K := K) hr hj
  have hne : sliceBirTarget K r N j ≠ ⊥ := by
    rw [Ne, basicOpen_eq_bot_iff]
    intro h0
    exact sliceBeta_trailSlice_ne_zero hr hrj hj (by rw [h0, map_zero])
  exact (sliceBirTarget K r N j).isOpen.dense ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)

theorem sliceBirSource_dense [CharZero K] (hr : 0 < r) (hrj : r ≤ j) (hj : j + r ≤ N) :
    Dense (sliceBirSource K r N hj : Set (SliceY K r N j)) := by
  haveI := sliceY_isIntegral (K := K) hr hj
  have hne : sliceBirSource K r N hj ≠ ⊥ := by
    rw [Ne, basicOpen_eq_bot_iff]
    exact sliceBeta_trailSlice_ne_zero hr hrj hj
  exact (sliceBirSource K r N _).isOpen.dense ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)

variable (K r N) in
/-- **The partial isomorphism** `{δ ≠ 0} ≅ D(δ)` of the slice resolution. -/
noncomputable def slicePartialIso [CharZero K] (hr : 0 < r) (hrj : r ≤ j) (hj : j + r ≤ N) :
    (SliceY K r N j).PartialIso (Spec (CommRingCat.of (ChartRing K r N j))) where
  source := sliceBirSource K r N hj
  dense_source := sliceBirSource_dense hr hrj hj
  target := sliceBirTarget K r N j
  dense_target := sliceBirTarget_dense hr hrj hj
  iso := haveI := sliceResLE_isIso (K := K) hr hrj hj
    asIso ((sliceResolution K r N hj).resLE (sliceBirTarget K r N j) (sliceBirSource K r N hj)
      (sliceBirSource_le _))

/-- **The slice resolution is birational.** -/
theorem sliceResolution_birational [CharZero K] (hr : 0 < r) (hrj : r ≤ j) (hj : j + r ≤ N) :
    Scheme.BirationalOver (sliceResolution K r N hj) (𝟙 _) :=
  ⟨slicePartialIso K r N hr hrj hj, by
    rw [Scheme.PartialIso.IsOver, Category.comp_id]
    exact Scheme.Hom.resLE_comp_ι _ _⟩

/-! ## Rational singularities -/

/-- **The affine chart `x_0 = 1` of the secant variety of the first `j + r` moments has rational
singularities** (`K` of characteristic zero, `0 < r ≤ j`, `j + r ≤ N`), resolved by the slice
`Proj(B_j/(v_0 - 1))`. -/
theorem chartRing_hasRationalSingularities (K : Type) [Field K] [CharZero K] {N r j : ℕ}
    (hr : 0 < r) (hrj : r ≤ j) (hj : j + r ≤ N) : HasRationalSingularities K (ChartRing K r N j) := by
  refine ⟨SliceY K r N j, sliceResolution K r N hj, ?_, sliceResolution_isProper _,
    sliceResolution_birational hr hrj hj, sliceResolution_appTop_isIso _,
    fun q x => sliceY_cohomology_vanishing hj q x⟩
  rw [sliceResolution_over]
  exact sliceYStruct_smooth hj

/-- **The standard affine chart `x_0 = 1` of the Hankel secant variety has rational singularities**:
for `K` of characteristic zero and `0 < r`, `2r ≤ N`, the ring
`K[x_0, …, x_{N-1}] / (I_r + (x_0 - 1))` has rational singularities. -/
theorem hankelChartRing_hasRationalSingularities (K : Type) [Field K] [CharZero K] {N r : ℕ}
    (hr : 0 < r) (hrN : 2 * r ≤ N) :
    HasRationalSingularities K (MvPolynomial (Fin N) K ⧸
      (RHTower.finiteHankelSecantIdeal K N r ⊔ Ideal.span {firstMoment K N - 1})) :=
  (chartRing_hasRationalSingularities K (j := N - r) hr (by omega) (by omega)).of_algEquiv
    (Ideal.quotientEquivAlgOfEq K (by rw [sliceKernel, secantIdealUpTo_self]))

end HTGeometry
