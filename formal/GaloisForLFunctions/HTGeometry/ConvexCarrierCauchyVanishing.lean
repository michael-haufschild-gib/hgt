import GaloisForLFunctions.HTGeometry.ContinuousMapCauchyTransform

/-!
# The Cauchy transform of a polynomial annihilator vanishes off a convex carrier

Outside a disc containing the carrier the Cauchy kernel is a norm-convergent power series in the
coordinate, so a functional killing every power of the coordinate has vanishing transform there.
Recentring the series shows the same for any disc containing the carrier, and for a *convex* compact
carrier every exterior point admits such a disc: the nearest carrier point supplies a supporting
direction, and pushing the centre far along it makes the carrier closer to the centre than the
exterior point is.  Hence the transform vanishes on the whole complement.

* `GaloisForLFunctions.HTGeometry.exists_far_center`;
* `GaloisForLFunctions.HTGeometry.cauchyTransform_eq_zero_of_convex`.
-/

noncomputable section

open Complex Set
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

variable {K : Set ℂ} [CompactSpace K]

/-- The carrier coordinate recentred at a point of the plane. -/
def shiftedCoordMap (K : Set ℂ) (c : ℂ) : C(K, ℂ) := coordMap K - c • 1

omit [CompactSpace K] in
@[simp] theorem shiftedCoordMap_apply (c : ℂ) (z : K) :
    shiftedCoordMap K c z = (z : ℂ) - c := by
  simp [shiftedCoordMap]

omit [CompactSpace K] in
theorem shiftedCoordMap_pow_apply (c : ℂ) (m : ℕ) (z : K) :
    (shiftedCoordMap K c ^ m) z = ((z : ℂ) - c) ^ m := by
  induction m with
  | zero => simp
  | succ n ih => rw [pow_succ, ContinuousMap.mul_apply, ih, shiftedCoordMap_apply, pow_succ]

/-! ## Polynomial annihilation -/

omit [CompactSpace K] in
/-- A functional killing every power of the coordinate kills every polynomial in it. -/
theorem map_aeval_coordMap_eq_zero (A : C(K, ℂ) →L[ℂ] ℂ)
    (hA : ∀ m : ℕ, A (coordMap K ^ m) = 0) (P : Polynomial ℂ) :
    A (Polynomial.aeval (coordMap K) P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, ← Algebra.smul_def, map_smul, hA n, smul_zero]

omit [CompactSpace K] in
/-- A functional killing every power of the coordinate kills every power of the recentred
coordinate. -/
theorem map_shiftedCoordMap_pow_eq_zero (A : C(K, ℂ) →L[ℂ] ℂ)
    (hA : ∀ m : ℕ, A (coordMap K ^ m) = 0) (c : ℂ) (m : ℕ) :
    A (shiftedCoordMap K c ^ m) = 0 := by
  have hrep : shiftedCoordMap K c ^ m
      = Polynomial.aeval (coordMap K) ((Polynomial.X - Polynomial.C c) ^ m) := by
    rw [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, shiftedCoordMap,
      Algebra.algebraMap_eq_smul_one]
  rw [hrep]
  exact map_aeval_coordMap_eq_zero A hA _

/-! ## The recentred geometric expansion -/

theorem norm_shiftedCoordMap_pow_le {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hK : ∀ z ∈ K, ‖z - c‖ ≤ r) (m : ℕ) : ‖shiftedCoordMap K c ^ m‖ ≤ r ^ m := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun z => ?_
  rw [shiftedCoordMap_pow_apply, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hK z z.2) m

theorem summable_shiftedGeometricKernel {v c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hK : ∀ z ∈ K, ‖z - c‖ ≤ r) (hv : r < ‖v - c‖) :
    Summable fun m : ℕ => (((v - c)⁻¹) ^ (m + 1)) • (shiftedCoordMap K c ^ m) := by
  have hv0 : v - c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    linarith
  refine Summable.of_norm ?_
  have hbound : ∀ m : ℕ, ‖(((v - c)⁻¹) ^ (m + 1)) • (shiftedCoordMap K c ^ m)‖
      ≤ ‖v - c‖⁻¹ * (r / ‖v - c‖) ^ m := by
    intro m
    rw [norm_smul, norm_pow, norm_inv]
    calc ‖v - c‖⁻¹ ^ (m + 1) * ‖shiftedCoordMap K c ^ m‖
        ≤ ‖v - c‖⁻¹ ^ (m + 1) * r ^ m :=
          mul_le_mul_of_nonneg_left (norm_shiftedCoordMap_pow_le hr hK m) (by positivity)
      _ = ‖v - c‖⁻¹ * (r / ‖v - c‖) ^ m := by
          rw [div_pow, pow_succ, inv_pow, div_eq_mul_inv]
          ring
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound ?_
  refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
  rw [div_lt_one (by positivity)]
  exact hv

theorem tsum_shiftedGeometricKernel_eq {v c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hKr : ∀ z ∈ K, ‖z - c‖ ≤ r) (hv : r < ‖v - c‖) (hvK : v ∉ K) :
    ∑' m : ℕ, (((v - c)⁻¹) ^ (m + 1)) • (shiftedCoordMap K c ^ m) = kernelFun K hvK := by
  have hsum := summable_shiftedGeometricKernel (K := K) hr hKr hv
  ext z
  have heval := (ContinuousMap.evalCLM ℂ z).map_tsum hsum
  change (ContinuousMap.evalCLM ℂ z)
      (∑' m : ℕ, (((v - c)⁻¹) ^ (m + 1)) • (shiftedCoordMap K c ^ m)) = (kernelFun K hvK) z
  rw [heval]
  have hz : ‖(z : ℂ) - c‖ < ‖v - c‖ := lt_of_le_of_lt (hKr z z.2) hv
  have hterm : ∀ m : ℕ,
      (ContinuousMap.evalCLM ℂ z) ((((v - c)⁻¹) ^ (m + 1)) • (shiftedCoordMap K c ^ m))
        = (((v - c)⁻¹) ^ (m + 1)) * ((z : ℂ) - c) ^ m := by
    intro m
    change (((v - c)⁻¹) ^ (m + 1)) • (shiftedCoordMap K c ^ m) z = _
    rw [smul_eq_mul, shiftedCoordMap_pow_apply]
  rw [tsum_congr hterm, tsum_kernel_pointwise hz, kernelFun_apply]
  congr 1
  ring

/-- **A polynomial annihilator has vanishing Cauchy transform at every point farther from some
centre than the whole carrier.** -/
theorem cauchyTransform_eq_zero_of_far_center (A : C(K, ℂ) →L[ℂ] ℂ)
    (hA : ∀ m : ℕ, A (coordMap K ^ m) = 0)
    {v c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hKr : ∀ z ∈ K, ‖z - c‖ ≤ r) (hv : r < ‖v - c‖) :
    functionalCauchyTransform A v = 0 := by
  have hvK : v ∉ K := fun hc => absurd (hKr v hc) (not_le.mpr hv)
  rw [cauchyTransform_eq A hvK, ← tsum_shiftedGeometricKernel_eq hr hKr hv hvK,
    A.map_tsum (summable_shiftedGeometricKernel hr hKr hv)]
  have hterm : ∀ m : ℕ,
      A ((((v - c)⁻¹) ^ (m + 1)) • (shiftedCoordMap K c ^ m)) = 0 := by
    intro m
    rw [map_smul, map_shiftedCoordMap_pow_eq_zero A hA c m, smul_zero]
  rw [tsum_congr hterm, tsum_zero]

/-! ## Convex carriers admit a far centre at every exterior point -/

/-- The supporting inequality at the nearest point of a convex compact set. -/
theorem re_mul_conj_le_zero_of_isMinOn {K : Set ℂ} (hconv : Convex ℝ K) {v p : ℂ}
    (hpK : p ∈ K) (hp : ∀ w ∈ K, ‖v - p‖ ≤ ‖v - w‖) {z : ℂ} (hzK : z ∈ K) :
    ((v - p) * (starRingEnd ℂ) (z - p)).re ≤ 0 := by
  have hBnonneg : 0 ≤ normSq (z - p) := normSq_nonneg _
  have hstep : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ((v - p) * (starRingEnd ℂ) (z - p)).re ≤ t * normSq (z - p) / 2 := by
    intro t ht ht1
    have hmem : (1 - t) • p + t • z ∈ K :=
      hconv hpK hzK (by linarith) ht.le (by ring)
    have hpt : (1 - t) • p + t • z = p + (t : ℂ) * (z - p) := by
      simp only [Complex.real_smul]
      push_cast
      ring
    have hmem' : p + (t : ℂ) * (z - p) ∈ K := hpt ▸ hmem
    have hnorm : ‖v - p‖ ≤ ‖v - (p + (t : ℂ) * (z - p))‖ := hp _ hmem'
    have hsub : v - (p + (t : ℂ) * (z - p)) = (v - p) - (t : ℂ) * (z - p) := by ring
    rw [hsub] at hnorm
    have hsq : normSq (v - p) ≤ normSq ((v - p) - (t : ℂ) * (z - p)) := by
      rw [normSq_eq_norm_sq, normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hexpand : normSq ((v - p) - (t : ℂ) * (z - p))
        = normSq (v - p) + t ^ (2 : ℕ) * normSq (z - p)
          - 2 * (t * ((v - p) * (starRingEnd ℂ) (z - p)).re) := by
      rw [normSq_sub (v - p) ((t : ℂ) * (z - p)), normSq_mul, normSq_ofReal, map_mul,
        Complex.conj_ofReal,
        show (v - p) * ((t : ℂ) * (starRingEnd ℂ) (z - p))
          = (t : ℂ) * ((v - p) * (starRingEnd ℂ) (z - p)) by ring,
        Complex.re_ofReal_mul]
      ring
    rw [hexpand] at hsq
    nlinarith [hsq]
  by_contra hcon
  push Not at hcon
  set A : ℝ := ((v - p) * (starRingEnd ℂ) (z - p)).re with hA
  set B : ℝ := normSq (z - p) with hB
  have hApos : 0 < A := hcon
  have hBpos : 0 < B + 1 := by linarith
  set t : ℝ := min 1 (A / (B + 1)) with hts
  have hpos : 0 < t := lt_min one_pos (by positivity)
  have hle : t ≤ 1 := min_le_left _ _
  have hkey := hstep t hpos hle
  have ht2 : t ≤ A / (B + 1) := min_le_right _ _
  have hprod : t * B ≤ A * B / (B + 1) := by
    have h := mul_le_mul_of_nonneg_right ht2 hBnonneg
    calc t * B ≤ (A / (B + 1)) * B := h
      _ = A * B / (B + 1) := by ring
  have hfrac : A * B / (B + 1) < A := by
    rw [div_lt_iff₀ hBpos]
    nlinarith
  linarith

/-- **Every point outside a compact convex plane set is farther from a suitable centre than the
whole set.** -/
theorem exists_far_center {K : Set ℂ} (hK : IsCompact K) (hconv : Convex ℝ K) {v : ℂ}
    (hv : v ∉ K) :
    ∃ (c : ℂ) (r : ℝ), 0 ≤ r ∧ (∀ z ∈ K, ‖z - c‖ ≤ r) ∧ r < ‖v - c‖ := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · refine ⟨v - 1, 0, le_rfl, fun z hz => absurd (hemp ▸ hz) (by simp), ?_⟩
    simp
  obtain ⟨p, hpK, hp⟩ := hK.exists_isMinOn hne
    (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => ‖v - z‖))
  have hpmin : ∀ w ∈ K, ‖v - p‖ ≤ ‖v - w‖ := fun w hw => hp hw
  set n : ℂ := v - p with hn
  have hn0 : n ≠ 0 := by
    rw [hn, sub_ne_zero]
    intro hc
    exact hv (hc ▸ hpK)
  have hnpos : 0 < normSq n := normSq_pos.mpr hn0
  obtain ⟨q, hqK, hq⟩ := hK.exists_isMaxOn hne
    (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => normSq (z - p)))
  set Bm : ℝ := normSq (q - p) with hBm
  have hBmax : ∀ z ∈ K, normSq (z - p) ≤ Bm := fun z hz => hq hz
  have hBmnonneg : 0 ≤ Bm := normSq_nonneg _
  set s : ℝ := Bm / normSq n with hs
  have hsnonneg : 0 ≤ s := by positivity
  set c : ℂ := p - (s : ℂ) * n with hc
  have hvc : v - c = ((1 + s : ℝ) : ℂ) * n := by
    rw [hc, hn]
    push_cast
    ring
  have hnormvc : normSq (v - c) = (1 + s) ^ (2 : ℕ) * normSq n := by
    rw [hvc, normSq_mul, normSq_ofReal]
    ring
  have hzc : ∀ z ∈ K, normSq (z - c) < normSq (v - c) := by
    intro z hz
    have hzcv : z - c = (z - p) + (s : ℂ) * n := by rw [hc]; ring
    have hre := re_mul_conj_le_zero_of_isMinOn hconv hpK hpmin hz
    have hexp : normSq (z - c)
        = normSq (z - p) + s ^ (2 : ℕ) * normSq n + 2 * (s * ((z - p) * (starRingEnd ℂ) n).re) := by
      rw [hzcv, normSq_add (z - p) ((s : ℂ) * n), normSq_mul, normSq_ofReal, map_mul,
        Complex.conj_ofReal,
        show (z - p) * ((s : ℂ) * (starRingEnd ℂ) n)
          = (s : ℂ) * ((z - p) * (starRingEnd ℂ) n) by ring,
        Complex.re_ofReal_mul]
      ring
    have hswap : ((z - p) * (starRingEnd ℂ) n).re = (n * (starRingEnd ℂ) (z - p)).re := by
      have : (starRingEnd ℂ) ((z - p) * (starRingEnd ℂ) n) = n * (starRingEnd ℂ) (z - p) := by
        rw [map_mul, Complex.conj_conj]
        ring
      rw [← Complex.conj_re ((z - p) * (starRingEnd ℂ) n), this]
    rw [hswap] at hexp
    have hneg : 2 * (s * (n * (starRingEnd ℂ) (z - p)).re) ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hsnonneg hre
      linarith
    have hBz : normSq (z - p) ≤ Bm := hBmax z hz
    have hkey : Bm < (1 + 2 * s) * normSq n := by
      rw [hs]
      field_simp
      nlinarith
    rw [hnormvc]
    nlinarith
  obtain ⟨z₀, hz₀K, hz₀⟩ := hK.exists_isMaxOn hne
    (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => ‖z - c‖))
  refine ⟨c, ‖z₀ - c‖, norm_nonneg _, fun z hz => hz₀ hz, ?_⟩
  have hlt := hzc z₀ hz₀K
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hlt
  nlinarith [norm_nonneg (z₀ - c), norm_nonneg (v - c)]

/-- **Between a plane compact and an open convex set containing it there is a compact convex
set.**  The closed convex hull of the compact set is compact, and a metric thickening keeps it
inside the open set. -/
theorem exists_compact_convex_between {K₁ D : Set ℂ} (hK₁ : IsCompact K₁) (hD : IsOpen D)
    (hDconv : Convex ℝ D) (hK₁D : K₁ ⊆ D) :
    ∃ K : Set ℂ, IsCompact K ∧ Convex ℝ K ∧ K₁ ⊆ K ∧ K ⊆ D := by
  obtain ⟨δ, hδ, hsub⟩ := hK₁.exists_cthickening_subset_open hD hK₁D
  obtain ⟨R, hR⟩ := hK₁.isBounded.subset_closedBall (0 : ℂ)
  have hEball : convexHull ℝ K₁ ⊆ Metric.closedBall (0 : ℂ) R :=
    convexHull_min hR (convex_closedBall _ _)
  refine ⟨closure (convexHull ℝ K₁), ?_, (convex_convexHull ℝ K₁).closure,
    fun z hz => subset_closure (subset_convexHull ℝ K₁ hz), ?_⟩
  · refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
    exact ((Metric.isBounded_closedBall).subset hEball).closure
  · intro x hx
    obtain ⟨e, heE, hde⟩ := Metric.mem_closure_iff.mp hx δ hδ
    have hxe : x - e ∈ Metric.closedBall (0 : ℂ) δ := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [← dist_eq_norm]
      exact hde.le
    have hxsum : x ∈ convexHull ℝ K₁ + Metric.closedBall (0 : ℂ) δ :=
      ⟨e, heE, x - e, hxe, by ring⟩
    have hball : convexHull ℝ (Metric.closedBall (0 : ℂ) δ) = Metric.closedBall (0 : ℂ) δ :=
      (convex_closedBall _ _).convexHull_eq
    have hadd : convexHull ℝ K₁ + Metric.closedBall (0 : ℂ) δ
        = convexHull ℝ (K₁ + Metric.closedBall (0 : ℂ) δ) := by
      rw [convexHull_add, hball]
    rw [hadd] at hxsum
    refine (convexHull_min ?_ hDconv) hxsum
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine hsub (Metric.mem_cthickening_of_dist_le _ a δ K₁ ha ?_)
    simp only [Metric.mem_closedBall, dist_zero_right] at hb
    rw [dist_eq_norm]
    simpa using hb

/-- **A polynomial annihilator of a convex carrier has Cauchy transform vanishing off the
carrier.** -/
theorem cauchyTransform_eq_zero_of_convex (hK : IsCompact K) (hconv : Convex ℝ K)
    (A : C(K, ℂ) →L[ℂ] ℂ) (hA : ∀ m : ℕ, A (coordMap K ^ m) = 0) :
    ∀ v, v ∉ K → functionalCauchyTransform A v = 0 := by
  intro v hv
  obtain ⟨c, r, hr, hKr, hvr⟩ := exists_far_center hK hconv hv
  exact cauchyTransform_eq_zero_of_far_center A hA hr hKr hvr

end GaloisForLFunctions.HTGeometry
