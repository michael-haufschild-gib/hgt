import GaloisForLFunctions.SurfaceOfSpecZ.TheOtherSideAtEveryGapSet

/-!
# Polynomially sparse degrees suffice

The `k`-th powers `nᵏ` have gaps `O(x^{1 − 1/k})` (`powGaps_kthPowers`), so by the iterated gap
method (`TheGapMethodIterates`, `TheOtherSideAtEveryGapSet`) the traces `2 Re S(k log n)` decide the
line from either side for every configuration, with the cubic spline
(`onLine_of_bddBelow_kthPowers`, `onLine_of_bddAbove_kthPowers`). For `ζ`
(`riemannHypothesis_iff_bddBelow_kthPowers`, `riemannHypothesis_iff_bddAbove_kthPowers`): for every
`k ≥ 1`, RH holds iff the smoothed point counts of degree `nᵏ` are bounded on one side.

A degree set with `O(x^{1/k})` elements up to `x` decides RH, for every `k`; the geometric degrees
`qⁿ`, with `O(log x)` elements, do not (`TheGeometricDegreesAlias`).
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **The `k`-th powers have gaps `x^{1 − 1/k}`.** -/
theorem powGaps_kthPowers {k : ℕ} (hk : 1 ≤ k) :
    PowGaps (1 - 1 / k) {d : ℕ | ∃ n : ℕ, 0 < n ∧ d = n ^ k} := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  refine ⟨fun d ⟨n, hn, hd⟩ => hd ▸ pow_pos hn k, k, 1, hk0.le, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set y := x ^ ((1 : ℝ) / k) with hydef
  have hy1 : 1 ≤ y := Real.one_le_rpow hx (by positivity)
  have hyk : y ^ k = x := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    rw [show (1 : ℝ) / k * k = 1 by field_simp, Real.rpow_one]
  set n := ⌊y⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hy1)
  have hny : (n : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyn : y < n + 1 := Nat.lt_floor_add_one y
  refine ⟨n ^ k, ⟨n, by omega, rfl⟩, ?_, ?_⟩
  · have := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) n) hny k
    push_cast; linarith
  · have h1 := pow_sub_pow_le_mul (Nat.cast_nonneg (α := ℝ) n) hny k
    rw [hyk] at h1
    have hyk1 : y ^ (k - 1) = x ^ (1 - 1 / (k : ℝ)) := by
      rw [← Real.rpow_natCast, hydef, ← Real.rpow_mul hx0.le]
      congr 1
      rw [Nat.cast_sub hk, Nat.cast_one, mul_sub, mul_one, one_div_mul_cancel hk0.ne']
    push_cast
    calc x - (n : ℝ) ^ k ≤ k * y ^ (k - 1) * (y - n) := h1
      _ ≤ k * y ^ (k - 1) * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = k * x ^ (1 - 1 / (k : ℝ)) := by rw [hyk1, mul_one]

/-- `θ = 1 − 1/k < 1`. -/
theorem one_sub_inv_lt_one {k : ℕ} (hk : 1 ≤ k) : 1 - 1 / (k : ℝ) < 1 := by
  have : (0 : ℝ) < k := by exact_mod_cast hk
  have := one_div_pos.mpr this
  linarith

/-- **From below, the `k`-th powers decide the line** for every configuration without real zeros. -/
theorem onLine_of_bddBelow_kthPowers (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {k : ℕ} (hk : 1 ≤ k) {K : ℝ}
    (hK : ∀ n : ℕ, 0 < n → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (k * Real.log n)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  refine onLine_of_bddBelow_of_powGaps Z hZ hnoreal (K := K) (one_sub_inv_lt_one hk)
    (powGaps_kthPowers hk) ?_
  rintro d ⟨n, hn, rfl⟩
  have := hK n hn
  rwa [Nat.cast_pow, Real.log_pow]

/-- **From above, the `k`-th powers decide the line** for every configuration in the open strip. -/
theorem onLine_of_bddAbove_kthPowers (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {k : ℕ} (hk : 1 ≤ k) {K : ℝ}
    (hK : ∀ n : ℕ, 0 < n → 2 * (lagStructure Z (boxSpline 1 3) (k * Real.log n)).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  refine onLine_of_bddAbove_of_powGaps Z hZ hlt (K := K) (one_sub_inv_lt_one hk)
    (powGaps_kthPowers hk) ?_
  rintro d ⟨n, hn, rfl⟩
  have := hK n hn
  rwa [Nat.cast_pow, Real.log_pow]

/-- **RH at the degrees `nᵏ`, from below**, with the cubic spline, for every `k ≥ 1`. -/
theorem riemannHypothesis_iff_bddBelow_kthPowers {k : ℕ} (hk : 1 ≤ k) :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, 0 < n →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log n)).re := by
  constructor
  · intro hRH
    refine ⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖, fun n hn => ?_⟩
    have hu : 0 ≤ (k : ℝ) * Real.log n := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)
    exact (abs_le.mp (abs_two_re_lagStructure_le_of_RH hRH hu)).1
  · rintro ⟨K, hK⟩
    exact riemannHypothesis_iff_zetaZeroConfig_onLine.mpr
      (onLine_of_bddBelow_kthPowers _ temperedConfig_zetaZeroConfig zetaZeroConfig_im_ne_zero' hk hK)

/-- **RH at the degrees `nᵏ`, from above.** -/
theorem riemannHypothesis_iff_bddAbove_kthPowers {k : ℕ} (hk : 1 ≤ k) :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ n : ℕ, 0 < n →
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log n)).re ≤ K := by
  constructor
  · intro hRH
    refine ⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖, fun n hn => ?_⟩
    have hu : 0 ≤ (k : ℝ) * Real.log n := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)
    exact (abs_le.mp (abs_two_re_lagStructure_le_of_RH hRH hu)).2
  · rintro ⟨K, hK⟩
    exact riemannHypothesis_iff_zetaZeroConfig_onLine.mpr
      (onLine_of_bddAbove_kthPowers _ temperedConfig_zetaZeroConfig (fun _ hρ => hρ.2.2) hk hK)

end GaloisForLFunctions.SurfaceOfSpecZ
