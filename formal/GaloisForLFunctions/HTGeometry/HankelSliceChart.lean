import GaloisForLFunctions.HTGeometry.HankelSliceResolution
import GaloisForLFunctions.HTGeometry.LinearHypersurface
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The charts of the slice `v_0 = 1`

On the chart `z_0 = 1` of the incidence variety the solved moments are linear in the free moments:
`v_n = ∑_m c_{n,m}(a) b_m` (`chartSol_eq_sum`).  Hence the chart ring of the slice `v_0 = 1` is the
hypersurface `K[a][b] / (∑_m c_{0,m}(a) b_m - 1)`, which is smooth over `K` and a domain (the
coefficient `c_{0,0}` is `1` at `a = (-1, 0, …, 0)`, where the recursion reads `v_n = v_{n+1}`).

* `HTGeometry.chartCoef`, `HTGeometry.chartSol_eq_sum`, `HTGeometry.chartCoef_zero_ne_zero`.
* `HTGeometry.sliceHypEquiv` : `K[a, b]/(v_0 - 1) ≃ₐ[K] K[a][b]/(∑ c_{0,m} b_m - 1)`.
* `HTGeometry.sliceChartPoly_smooth`, `HTGeometry.sliceChartPoly_isDomain`.
* `HTGeometry.sliceChartEquiv` : `K[a, b]/(v_0 - 1) ≃+* (B_j/(v_0 - 1))_{(G(t))}`.
-/

namespace HTGeometry

open MvPolynomial

universe u

variable {K : Type u} [Field K] {r N j : ℕ}

/-! ## The solved moments are linear in the free moments -/

variable (K r N) in
/-- **The coefficients of the solved moments**: `v_n = ∑_m c_{n,m}(a) b_m`. -/
noncomputable def chartCoef (j n : ℕ) (m : Fin (N - j)) : MvPolynomial (Fin r) K :=
  if h : j ≤ n then (if n = j + m then 1 else 0)
  else -∑ i : Fin r, X i * chartCoef j (n + i + 1) m
termination_by j - n
decreasing_by omega

theorem chartCoef_of_ge {n : ℕ} (h : j ≤ n) (m : Fin (N - j)) :
    chartCoef K r N j n m = if n = j + m then 1 else 0 := by
  rw [chartCoef, dif_pos h]

theorem chartCoef_of_lt {n : ℕ} (h : n < j) (m : Fin (N - j)) :
    chartCoef K r N j n m = -∑ i : Fin r, X i * chartCoef K r N j (n + i + 1) m := by
  rw [chartCoef, dif_neg (by omega)]

/-- **The solved moments are linear in the free moments.** -/
theorem chartSol_eq_sum (hj : j ≤ N) (n : ℕ) :
    chartSol K r N j n = ∑ m : Fin (N - j), rename Sum.inl (chartCoef K r N j n m) * X (Sum.inr m) := by
  induction hk : j - n using Nat.strong_induction_on generalizing n with
  | _ k ih =>
    by_cases h : j ≤ n
    · simp_rw [chartCoef_of_ge h]
      by_cases h' : n < N
      · rw [chartSol, dif_pos h, dif_pos h', Finset.sum_eq_single ⟨n - j, by omega⟩]
        · rw [if_pos (by simp only; omega), map_one, one_mul]
        · intro m _ hm
          rw [if_neg (fun e => hm (Fin.ext (by simp only; omega))), map_zero, zero_mul]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · rw [chartSol, dif_pos h, dif_neg h']
        refine (Finset.sum_eq_zero fun m _ => ?_).symm
        rw [if_neg (by have := m.isLt; omega), map_zero, zero_mul]
    · rw [chartSol_of_lt (by omega)]
      simp_rw [chartCoef_of_lt (show n < j by omega)]
      have e : ∀ i : Fin r, chartSol K r N j (n + i + 1)
          = ∑ m : Fin (N - j), rename Sum.inl (chartCoef K r N j (n + i + 1) m) * X (Sum.inr m) :=
        fun i => ih (j - (n + i + 1)) (by omega) _ rfl
      simp_rw [e, Finset.mul_sum, map_neg, map_sum, map_mul, rename_X, neg_mul, Finset.sum_mul,
        Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]

/-- At `a = (-1, 0, …, 0)` the recursion reads `v_n = v_{n+1}`, so `c_{n,0} = 1` for `n ≤ j`. -/
theorem eval_chartCoef (hr : 0 < r) (hjN : j < N) {n : ℕ} (hn : n ≤ j) :
    eval (fun i : Fin r => if (i : ℕ) = 0 then (-1 : K) else 0)
      (chartCoef K r N j n ⟨0, by omega⟩) = 1 := by
  induction hk : j - n using Nat.strong_induction_on generalizing n with
  | _ k ih =>
    rcases hn.lt_or_eq with h | h
    · rw [chartCoef_of_lt h, map_neg, map_sum, Finset.sum_eq_single ⟨0, hr⟩]
      · have := ih (j - (n + 1)) (by omega) (show n + 1 ≤ j by omega) rfl
        rw [map_mul, eval_X, if_pos rfl]
        simp only [add_zero] at this ⊢
        rw [this]
        ring
      · intro i _ hi
        rw [map_mul, eval_X, if_neg (fun e => hi (Fin.ext e)), zero_mul]
      · intro h0; exact absurd (Finset.mem_univ _) h0
    · rw [chartCoef_of_ge h.ge, if_pos (by simp only; omega), map_one]

theorem chartCoef_zero_ne_zero (hr : 0 < r) (hjN : j < N) :
    chartCoef K r N j 0 ⟨0, by omega⟩ ≠ 0 := by
  intro h
  have := eval_chartCoef (K := K) hr hjN (Nat.zero_le j)
  rw [h, map_zero] at this
  exact zero_ne_one this

/-! ## The slice chart is a linear hypersurface -/

variable (K r) in
/-- `K[a, b] ≃ₐ[K] K[a][b]`. -/
noncomputable def chartSplit (f : ℕ) : ChartPoly K r f ≃ₐ[K] MvPolynomial (Fin f) (MvPolynomial (Fin r) K) :=
  (renameEquiv K (Equiv.sumComm (Fin r) (Fin f))).trans (sumAlgEquiv K (Fin f) (Fin r))

theorem chartSplit_X_inr {f : ℕ} (m : Fin f) : chartSplit K r f (X (Sum.inr m)) = X m := by
  rw [chartSplit, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, Equiv.sumComm_apply,
    Sum.swap_inr, sumAlgEquiv_X_inl]

theorem chartSplit_rename_inl {f : ℕ} (p : MvPolynomial (Fin r) K) :
    chartSplit K r f (rename Sum.inl p) = C p := by
  have h : (chartSplit K r f).toAlgHom.comp (rename Sum.inl)
      = IsScalarTower.toAlgHom K (MvPolynomial (Fin r) K) (MvPolynomial (Fin f) (MvPolynomial (Fin r) K)) := by
    refine algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, rename_X]
    change chartSplit K r f (X (Sum.inl i)) = _
    rw [chartSplit, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, Equiv.sumComm_apply, Sum.swap_inl,
      sumAlgEquiv_X_inr, IsScalarTower.coe_toAlgHom', algebraMap_eq]
  exact DFunLike.congr_fun h p

variable (K r N j) in
/-- The chart ring of the slice: `K[a, b] / (v_0 - 1)`. -/
abbrev SliceChartPoly := ChartPoly K r (N - j) ⧸ Ideal.span {chartSol K r N j 0 - 1}

theorem chartSplit_chartSol (hj : j ≤ N) :
    chartSplit K r (N - j) (chartSol K r N j 0) = hypLinForm (chartCoef K r N j 0) := by
  rw [chartSol_eq_sum hj, map_sum, hypLinForm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, chartSplit_rename_inl, chartSplit_X_inr]

variable (K r N) in
/-- **The slice chart is the linear hypersurface** `∑_m c_{0,m}(a) b_m = 1` over `K[a]`. -/
noncomputable def sliceHypEquiv (hj : j ≤ N) :
    SliceChartPoly K r N j ≃ₐ[K] LinHypersurface (chartCoef K r N j 0) :=
  Ideal.quotientEquivAlg _ _ (chartSplit K r (N - j)) (by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change _ = chartSplit K r (N - j) _
    rw [map_sub, map_one, chartSplit_chartSol hj])

/-- **The slice chart is smooth over `K`.** -/
theorem sliceChartPoly_smooth (hj : j ≤ N) : (algebraMap K (SliceChartPoly K r N j)).Smooth := by
  have hR : (algebraMap K (MvPolynomial (Fin r) K)).Smooth := by
    haveI : Algebra.Smooth K (MvPolynomial (Fin r) K) := {}
    exact RingHom.smooth_algebraMap.mpr inferInstance
  have h : algebraMap K (SliceChartPoly K r N j)
      = (sliceHypEquiv K r N hj).symm.toRingEquiv.toRingHom.comp
          (algebraMap K (LinHypersurface (chartCoef K r N j 0))) := by
    refine RingHom.ext fun c => ?_
    exact ((sliceHypEquiv K r N hj).symm.commutes c).symm
  rw [h]
  exact RingHom.Smooth.comp (hypersurface_smooth _ hR)
    (RingHom.Smooth.of_bijective (sliceHypEquiv K r N hj).symm.bijective)

/-- **The slice chart is a domain.** -/
theorem sliceChartPoly_isDomain (hr : 0 < r) (hj : j + r ≤ N) : IsDomain (SliceChartPoly K r N j) := by
  haveI := hypersurface_isDomain (chartCoef K r N j 0) (chartCoef_zero_ne_zero (K := K) hr (by omega))
  exact (sliceHypEquiv K r N (by omega)).toMulEquiv.isDomain _

/-- **The polynomials in `a` embed in the slice chart.** -/
theorem sliceChartPoly_rename_injective (hr : 0 < r) (hj : j + r ≤ N) :
    Function.Injective fun p : MvPolynomial (Fin r) K =>
      (Ideal.Quotient.mk (Ideal.span {chartSol K r N j 0 - 1}) (rename Sum.inl p)) := by
  intro p q hpq
  have h := congrArg (sliceHypEquiv K r N (show j ≤ N by omega)) hpq
  simp only [sliceHypEquiv, Ideal.quotientEquivAlg_mk, chartSplit_rename_inl] at h
  exact hypersurface_C_injective (chartCoef K r N j 0) (chartCoef_zero_ne_zero (K := K) hr (by omega)) h

/-! ## The chart rings of the slice -/

/-- `x ↦ x / f^0`. -/
theorem fromZero_eq_awayMk {σ B : Type*} [CommRing B] [SetLike σ B] [AddSubgroupClass σ B]
    {𝒢 : ℕ → σ} [GradedRing 𝒢] {f : B} (hf : f ∈ 𝒢 1) (x : 𝒢 0) :
    HomogeneousLocalization.fromZeroRingHom 𝒢 (Submonoid.powers f) x
      = HomogeneousLocalization.Away.mk 𝒢 hf 0 x (by simp) := by
  apply HomogeneousLocalization.val_injective
  rw [val_fromZeroRingHom, HomogeneousLocalization.Away.val_mk, ← Localization.mk_one_eq_algebraMap]
  congr 1
  exact Subtype.ext (pow_zero f).symm

section SliceChart

open HomogeneousLocalization GaloisForLFunctions.HTGeometry.StableCoordinate.HomogeneousQuotient

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local notation "𝒵" => projGrading K (Fin (r + 1)) (Fin N)
local notation "𝒜" => quotGrading K r N j
local notation "𝒜'" => sliceGrading K r N j

variable (K r N j) in
/-- The chart form `G(t)` in the slice ring. -/
noncomputable abbrev sT (t : K) : SliceQuot K r N j := Ideal.Quotient.mk _ (chartForm K r N t)

theorem sT_mem (t : K) : sT K r N j t ∈ 𝒜' 1 := mk_mem_piece 𝒵 _ (chartForm_mem t)

variable (K r N j) in
/-- `B_j → B_j/(v_0 - 1)` as a graded ring map. -/
noncomputable def sliceGradedHom : 𝒜 →+*ᵍ 𝒜' where
  toRingHom := sliceMap K r N j
  map_mem hx := sliceMap_mem j hx

variable (K r N j) in
/-- The chart rings of `B_j` to those of the slice. -/
noncomputable def sliceRho (t : K) : Away 𝒜 (tChart K r N j t) →+* Away 𝒜' (sT K r N j t) :=
  HomogeneousLocalization.map (sliceGradedHom K r N j) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, (map_pow (sliceMap K r N j) (tChart K r N j t) n).symm⟩)

theorem sliceRho_awayMk (t : K) (n : ℕ) {x : HankelQuot K r N j} (hx : x ∈ 𝒜 (n • 1)) :
    sliceRho K r N j t (Away.mk 𝒜 (tChart_mem t) n x hx)
      = Away.mk 𝒜' (sT_mem t) n (sliceMap K r N j x) (sliceMap_mem j hx) := by
  apply HomogeneousLocalization.val_injective
  rw [sliceRho, Away.mk, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, Away.val_mk]
  congr 1

theorem sliceRho_fromZero (t : K) (x : 𝒜 0) :
    sliceRho K r N j t (fromZeroRingHom 𝒜 _ x)
      = fromZeroRingHom 𝒜' _ ⟨sliceMap K r N j x, sliceMap_mem j x.2⟩ := by
  rw [fromZero_eq_awayMk (tChart_mem t), sliceRho_awayMk, fromZero_eq_awayMk (sT_mem t)]

theorem sliceRho_linFrac (t : K) {u : HankelQuot K r N j} (hu : u ∈ 𝒜 1) :
    sliceRho K r N j t (linFrac (tChart_mem t) hu) = linFrac (sT_mem t) (sliceMap_mem j hu) := by
  rw [linFrac, linFrac, sliceRho_awayMk]

theorem sliceRho_surjective (t : K) : Function.Surjective (sliceRho K r N j t) := by
  intro y
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜' (sT_mem t) y
  obtain ⟨x, hx, rfl⟩ := sliceMap_lift j ha
  exact ⟨Away.mk 𝒜 (tChart_mem t) n x hx, sliceRho_awayMk t n hx⟩

theorem momentShift_vAt_zero (t : K) : momentShift K r N t (vAt K r N 0) = vAt K r N 0 := by
  have h := momentShift_sliceElem (K := K) (r := r) (N := N) t
  rw [sliceElem, map_sub, map_one] at h
  exact sub_left_injective h

theorem mk_vAt_zero : (Ideal.Quotient.mk (sliceIdeal K r N j) (vAt K r N 0)) = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.subset_span rfl)

variable (K r N) in
/-- **The chart evaluation of the slice ring**: `x ↦ incChartEval (σ_{-t} x)` modulo `v_0 - 1`. -/
noncomputable def sliceQuotEval (hj : j + r ≤ N) (t : K) : SliceQuot K r N j →+* SliceChartPoly K r N j :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp
      ((incChartEval K r N j).comp (momentShift K r N (-t))).toRingHom) (by
    have hle : sliceIdeal K r N j ≤ RingHom.ker ((Ideal.Quotient.mk
        (Ideal.span {chartSol K r N j 0 - 1})).comp
          ((incChartEval K r N j).comp (momentShift K r N (-t))).toRingHom) := by
      refine sup_le (fun x hx => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      · rw [RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          AlgHom.comp_apply, incChartEval_mem_hankelIdeal hj (momentShift_mem_hankelIdeal (-t) hj hx),
          map_zero]
      · rw [RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          AlgHom.comp_apply, momentShift_sliceElem, sliceElem, map_sub, map_one,
          incChartEval_vAt (by omega), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
    exact fun x hx => hle hx)

theorem sliceQuotEval_sliceMap (hj : j + r ≤ N) (t : K) (x : HankelQuot K r N j) :
    sliceQuotEval K r N hj t (sliceMap K r N j x) = Ideal.Quotient.mk _ (chartQuotEval K r N hj t x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem sliceQuotEval_sT (hj : j + r ≤ N) (t : K) : sliceQuotEval K r N hj t (sT K r N j t) = 1 := by
  rw [show sT K r N j t = sliceMap K r N j (tChart K r N j t) from rfl, sliceQuotEval_sliceMap,
    chartQuotEval_tChart, map_one]

variable (K r N) in
/-- **The slice chart ring to the hypersurface.** -/
noncomputable def slicePsi (hj : j + r ≤ N) (t : K) : Away 𝒜' (sT K r N j t) →+* SliceChartPoly K r N j :=
  (IsLocalization.Away.lift (sT K r N j t) (S := Localization.Away (sT K r N j t))
    (g := sliceQuotEval K r N hj t) (by rw [sliceQuotEval_sT]; exact isUnit_one)).comp
    (algebraMap (Away 𝒜' (sT K r N j t)) (Localization.Away (sT K r N j t)))

theorem slicePsi_fromZero (hj : j + r ≤ N) (t : K) (x : 𝒜' 0) :
    slicePsi K r N hj t (fromZeroRingHom 𝒜' _ x) = sliceQuotEval K r N hj t x := by
  rw [slicePsi, RingHom.comp_apply]
  change IsLocalization.Away.lift _ _ (fromZeroRingHom 𝒜' _ x).val = _
  rw [val_fromZeroRingHom, IsLocalization.Away.lift_eq]

theorem slicePsi_linFrac (hj : j + r ≤ N) (t : K) {u : SliceQuot K r N j} (hu : u ∈ 𝒜' 1) :
    slicePsi K r N hj t (linFrac (sT_mem t) hu) = sliceQuotEval K r N hj t u := by
  rw [slicePsi, RingHom.comp_apply]
  change IsLocalization.Away.lift _ _ (linFrac (sT_mem t) hu).val = _
  set L := IsLocalization.Away.lift (sT K r N j t) (S := Localization.Away (sT K r N j t))
    (g := sliceQuotEval K r N hj t) (by rw [sliceQuotEval_sT]; exact isUnit_one)
  have h1 : (linFrac (sT_mem t) hu).val * algebraMap _ (Localization.Away (sT K r N j t))
      (sT K r N j t) = algebraMap _ _ u := by
    rw [val_linFrac, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  have h2 := congrArg L h1
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, sliceQuotEval_sT,
    mul_one] at h2
  exact h2

theorem chartPhi_chartPsi (hj : j + r ≤ N) (t : K) (y : Away 𝒜 (tChart K r N j t)) :
    chartPhi K r N j t (chartPsi K r N hj t y) = y := by
  obtain ⟨p, rfl⟩ := chartPhi_surjective hj t y
  rw [chartPsi_chartPhi]

theorem chartPhi_chartSol (hj : j + r ≤ N) (t : K) (m : ℕ) :
    chartPhi K r N j t (chartSol K r N j m) = fromZeroRingHom 𝒜 _ (shiftV K r N j t m) := by
  rw [← chartQuotEval_shiftV hj t m, ← chartPsi_fromZero, chartPhi_chartPsi]

theorem sliceRho_chartPhi_chartSol_zero (hj : j + r ≤ N) (t : K) :
    sliceRho K r N j t (chartPhi K r N j t (chartSol K r N j 0)) = 1 := by
  rw [chartPhi_chartSol hj, sliceRho_fromZero, ← map_one (fromZeroRingHom 𝒜' _)]
  congr 1
  apply Subtype.ext
  change Ideal.Quotient.mk _ (momentShift K r N t (vAt K r N 0)) = 1
  rw [momentShift_vAt_zero, mk_vAt_zero]

variable (K r N) in
/-- **The hypersurface to the slice chart ring.** -/
noncomputable def slicePhi (hj : j + r ≤ N) (t : K) : SliceChartPoly K r N j →+* Away 𝒜' (sT K r N j t) :=
  Ideal.Quotient.lift _ ((sliceRho K r N j t).comp (chartPhi K r N j t)) (fun a ha => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [RingHom.comp_apply, map_mul, map_mul, map_sub, map_sub, map_one, map_one,
      sliceRho_chartPhi_chartSol_zero hj, sub_self, mul_zero])

theorem slicePsi_slicePhi (hj : j + r ≤ N) (t : K) (x : SliceChartPoly K r N j) :
    slicePsi K r N hj t (slicePhi K r N hj t x) = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h : (slicePsi K r N hj t).comp ((sliceRho K r N j t).comp (chartPhi K r N j t))
      = Ideal.Quotient.mk _ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun k => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, chartPhi, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        sliceRho_fromZero, slicePsi_fromZero]
      change sliceQuotEval K r N hj t (sliceMap K r N j _) = _
      rw [sliceQuotEval_sliceMap, SetLike.GradeZero.coe_algebraMap, AlgHom.commutes]
      rfl
    · rcases k with i | n
      · rw [RingHom.comp_apply, RingHom.comp_apply, chartPhi, MvPolynomial.eval₂Hom_X', Sum.elim_inl,
          sliceRho_linFrac, slicePsi_linFrac, sliceQuotEval_sliceMap, chartQuotEval_shiftZ]
        rfl
      · rw [RingHom.comp_apply, RingHom.comp_apply, chartPhi, MvPolynomial.eval₂Hom_X', Sum.elim_inr,
          sliceRho_fromZero, slicePsi_fromZero]
        change sliceQuotEval K r N hj t (sliceMap K r N j _) = _
        rw [sliceQuotEval_sliceMap, chartQuotEval_shiftV, chartSol_tail n (by omega)]
  rw [slicePhi, Ideal.Quotient.lift_mk]
  exact DFunLike.congr_fun h p

theorem slicePhi_surjective (hj : j + r ≤ N) (t : K) : Function.Surjective (slicePhi K r N hj t) := by
  intro y
  obtain ⟨x, rfl⟩ := sliceRho_surjective t y
  obtain ⟨p, rfl⟩ := chartPhi_surjective hj t x
  exact ⟨Ideal.Quotient.mk _ p, by rw [slicePhi, Ideal.Quotient.lift_mk, RingHom.comp_apply]⟩

variable (K r N) in
/-- **The chart rings of the slice are linear hypersurfaces.** -/
noncomputable def sliceChartEquiv (hj : j + r ≤ N) (t : K) :
    SliceChartPoly K r N j ≃+* Away 𝒜' (sT K r N j t) :=
  RingEquiv.ofBijective (slicePhi K r N hj t)
    ⟨Function.LeftInverse.injective (slicePsi_slicePhi hj t), slicePhi_surjective hj t⟩

theorem sliceChartEquiv_C (hj : j + r ≤ N) (t : K) (c : K) :
    sliceChartEquiv K r N hj t (algebraMap K _ c) = fromZeroRingHom 𝒜' _ (algebraMap K (𝒜' 0) c) := by
  change slicePhi K r N hj t (Ideal.Quotient.mk _ (MvPolynomial.C c)) = _
  rw [slicePhi, Ideal.Quotient.lift_mk, RingHom.comp_apply, chartPhi, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply, sliceRho_fromZero]
  rfl

/-! ## The slice is smooth -/

section Smooth

open AlgebraicGeometry CategoryTheory

/-- The structure map of the slice on a chart. -/
theorem awayι_sliceYStruct (k : Fin (r + 1)) :
    Proj.awayι 𝒜' (sChart K r N j k) (sChart_mem j k) one_pos ≫ sliceYStruct K r N j
      = Spec.map (CommRingCat.ofHom ((fromZeroRingHom _ _).comp (algebraMap K (𝒜' 0)))) := by
  rw [sliceYStruct, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- **The chart rings of the slice are smooth over `K`.** -/
theorem smooth_sliceChart (hj : j + r ≤ N) (k : Fin (r + 1)) :
    ((fromZeroRingHom 𝒜' (Submonoid.powers (sChart K r N j k))).comp (algebraMap K (𝒜' 0))).Smooth := by
  have h : (fromZeroRingHom 𝒜' (Submonoid.powers (sChart K r N j k))).comp (algebraMap K (𝒜' 0))
      = (sliceChartEquiv K r N hj (node K k)).toRingHom.comp (algebraMap K (SliceChartPoly K r N j)) :=
    RingHom.ext fun c => (sliceChartEquiv_C hj (node K k) c).symm
  rw [h]
  exact RingHom.Smooth.comp (sliceChartPoly_smooth (by omega))
    (RingHom.Smooth.of_bijective (sliceChartEquiv K r N hj (node K k)).bijective)

/-- **The slice `Y_1` is smooth over `K`.** -/
theorem sliceYStruct_smooth [CharZero K] (hj : j + r ≤ N) : Smooth (sliceYStruct K r N j) := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top (sliceChart K r N j)
    (iSup_sliceChart_eq_top (K := K) (r := r) (N := N) (j := j)) fun k => ?_
  have hι : (sliceChart K r N j k).ι = (Proj.basicOpenIsoSpec 𝒜' (sChart K r N j k) (sChart_mem j k)
      one_pos).hom ≫ Proj.awayι 𝒜' (sChart K r N j k) (sChart_mem j k) one_pos := by
    rw [Proj.awayι, Iso.hom_inv_id_assoc]
  rw [hι, Category.assoc, MorphismProperty.cancel_left_of_respectsIso @Smooth, awayι_sliceYStruct,
    HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact smooth_sliceChart hj k

end Smooth

end SliceChart

end HTGeometry
