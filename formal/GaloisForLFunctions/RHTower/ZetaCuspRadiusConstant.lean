import GaloisForLFunctions.HTGeometry.CosineShiftRootLimsup
import GaloisForLFunctions.HTGeometry.ShiftLatticeVerification
import GaloisForLFunctions.RHTower.XiSourceNormalConeDivisorConservation

/-!
# The cusp constant of the zeta shift lattice

Assembling the functional-equation decomposition of `ζ(s₀-k)/k!` against the
root-growth laws leaves only the geometric factor: the constant, the Gamma
quotient and the zeta value all have `k`-th roots tending to one, and the
oscillating cosine has root `limsup` one.  The growth functional of the shifted
zeta coefficients is therefore exactly `1/(2π)`.

This is the independent computation of the cusp constant for the Riemann zeta
function, degree one and conductor one, matching the spectral prediction
`1/(2πΔ(0))` with `Δ(0) = 1`.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ENNReal NNReal

namespace RHTower

section CuspConstant

variable {s₀ : ℂ}

/-- The remainder of the functional-equation decomposition. -/
noncomputable def zetaShiftRemainder (s₀ : ℂ) (k : ℕ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s₀))
    * (Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ)))
    * Complex.cos ((Real.pi : ℂ) * (1 - s₀ + (k : ℂ)) / 2)
    * riemannZeta (1 - s₀ + (k : ℂ))

private theorem shift_ne_zero (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) (k : ℕ) :
    1 - s₀ + (k : ℂ) ≠ 0 := by
  have h := shift_ne_negNat hs k 0
  simpa using h

/-- The Gamma quotient of the decomposition has `k`-th roots tending to one. -/
theorem tendsto_gammaQuotient (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) :
    Tendsto (fun k : ℕ =>
        ‖Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖
          ^ (1 / (k : ℝ))) atTop (𝓝 1) :=
  tendsto_norm_gammaRatio_rpow_inv
    (fun k => Complex.Gamma_ne_zero (shift_ne_negNat hs k)) (shift_ne_zero hs)

/-- The shifted zeta value has `k`-th roots tending to one. -/
theorem tendsto_zetaShiftValue (s₀ : ℂ) :
    Tendsto (fun k : ℕ => ‖riemannZeta (1 - s₀ + (k : ℂ))‖ ^ (1 / (k : ℝ)))
      atTop (𝓝 1) := by
  have hre : Tendsto (fun k : ℕ => (1 - s₀ + (k : ℂ)).re) atTop atTop := by
    have : ∀ k : ℕ, (1 - s₀ + (k : ℂ)).re = (1 - s₀.re) + (k : ℝ) := by
      intro k
      simp [Complex.add_re, Complex.sub_re]
    refine Tendsto.congr (fun k => (this k).symm) ?_
    exact tendsto_atTop_add_const_left atTop (1 - s₀.re) tendsto_natCast_atTop_atTop
  have hzeta : Tendsto (fun k : ℕ => ‖riemannZeta (1 - s₀ + (k : ℂ))‖) atTop (𝓝 1) := by
    have := (tendsto_riemannZeta_of_re_atTop hre).norm
    simpa using this
  refine tendsto_rpow_inv_of_polynomial_bounds (C₁ := 1 / 2) (C₂ := 2) (B := 0)
    (by norm_num) (by norm_num) ?_ ?_
  · filter_upwards [hzeta.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)] with k hk
    rw [neg_zero, Real.rpow_zero, mul_one]
    exact hk.le
  · filter_upwards [hzeta.eventually_lt_const (by norm_num : (1 : ℝ) < 2)] with k hk
    rw [Real.rpow_zero, mul_one]
    exact hk.le

/-- **The remainder has growth functional one.** -/
theorem hadamardLimsup_zetaShiftRemainder (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) :
    hadamardLimsup (zetaShiftRemainder s₀) = 1 := by
  set Cst : ℝ := ‖2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s₀))‖ with hCst
  have hCpos : 0 < Cst := by
    rw [hCst, norm_pos_iff]
    refine mul_ne_zero two_ne_zero ?_
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl two_pi_ne_zero)
  have hsplit : ∀ k : ℕ, ‖zetaShiftRemainder s₀ k‖
      = (Cst * ‖Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖
          * ‖riemannZeta (1 - s₀ + (k : ℂ))‖) * cosShift s₀ k := by
    intro k
    rw [zetaShiftRemainder, norm_mul, norm_mul, norm_mul, hCst, cosShift]
    ring
  have hconv : Tendsto (fun k : ℕ =>
      (Cst * ‖Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖
        * ‖riemannZeta (1 - s₀ + (k : ℂ))‖) ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
    have hprod := ((tendsto_const_rpow_inv_nat hCpos).mul
      (tendsto_gammaQuotient hs)).mul (tendsto_zetaShiftValue s₀)
    rw [one_mul, one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards with k
    rw [← Real.mul_rpow (by positivity) (norm_nonneg _),
      ← Real.mul_rpow (by positivity) (norm_nonneg _)]
  have hbnn : ∀ k : ℕ, 0 ≤ (cosShift s₀ k) ^ (1 / (k : ℝ)) := fun k =>
    Real.rpow_nonneg (cosShift_nonneg s₀ k) _
  have hbbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => (cosShift s₀ k) ^ (1 / (k : ℝ))) := by
    obtain ⟨C, hC⟩ :=
      GaloisForLFunctions.HTGeometry.exists_bound_of_periodic_nat
        (f := cosShift s₀) (p := 4) (by norm_num) (cosShift_periodic s₀)
    have hCp : 0 < C := by
      rcases exists_cosShift_pos s₀ with h | h
      · exact lt_of_lt_of_le h (hC 0)
      · exact lt_of_lt_of_le h (hC 1)
    exact isBoundedUnder_rpow_inv hCp (cosShift_nonneg s₀) hC
  have hcongr : ∀ k : ℕ, ‖zetaShiftRemainder s₀ k‖ ^ (1 / (k : ℝ))
      = (Cst * ‖Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖
          * ‖riemannZeta (1 - s₀ + (k : ℂ))‖) ^ (1 / (k : ℝ))
        * (cosShift s₀ k) ^ (1 / (k : ℝ)) := by
    intro k
    rw [hsplit k, Real.mul_rpow (by positivity) (cosShift_nonneg s₀ k)]
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => ‖zetaShiftRemainder s₀ k‖ ^ (1 / (k : ℝ))) := by
    obtain ⟨B, hB⟩ := id hbbdd
    rw [Filter.eventually_map] at hB
    refine ⟨2 * max B 0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hconv.eventually_lt_const (by norm_num : (1 : ℝ) < 2), hB]
      with k h2 hBk
    rw [hcongr k]
    exact mul_le_mul h2.le (le_trans hBk (le_max_left _ _)) (hbnn k) (by norm_num)
  have hlim : limsup (fun k : ℕ => ‖zetaShiftRemainder s₀ k‖ ^ (1 / (k : ℝ)))
      atTop = 1 := by
    rw [limsup_congr (Filter.Eventually.of_forall hcongr)]
    exact limsup_mul_eq_one_of_tendsto_one hconv hbnn hbbdd
      (limsup_cosShift_rpow_inv_eq_one s₀)
  exact hadamardLimsup_eq_one_of_limsup_eq_one hbdd hlim

/-- **The cusp constant of the zeta shift lattice.**  The factorially normalized
shifted zeta values grow exactly like `1/(2π)`, matching the spectral prediction
`1/(2πΔ(0))` for degree one and conductor one, where the cusp gap is `Δ(0) = 1`. -/
theorem hadamardLimsup_zetaShift (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) :
    hadamardLimsup (fun k : ℕ => riemannZeta (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ))
      = ENNReal.ofReal (1 / (2 * Real.pi)) := by
  have hfun : (fun k : ℕ => riemannZeta (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ))
      = fun k : ℕ => ((2 * (Real.pi : ℂ))⁻¹) ^ k * zetaShiftRemainder s₀ k :=
    funext fun k => zetaShift_decomposition hs k
  rw [hfun, hadamardLimsup_geometric, hadamardLimsup_zetaShiftRemainder hs, mul_one]
  have hnorm : ‖((2 * (Real.pi : ℂ))⁻¹)‖ = 1 / (2 * Real.pi) := by
    rw [norm_inv, one_div]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  have hcoe : ((‖((2 * (Real.pi : ℂ))⁻¹)‖₊ : ℝ≥0∞))
      = ENNReal.ofReal ‖((2 * (Real.pi : ℂ))⁻¹)‖ := by
    rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
    rfl
  rw [hcoe, hnorm]

/-- **The local--global identity at the cusp, for the zeta function.**  The
analytic constant computed from the functional equation and the spectral
constant computed from the standard-twist spectrum agree: both are
`1/(2π Δ(0))`.  The two computations use disjoint data — the first only the
archimedean functional equation, the second only `a(1) ≠ 0` and the location of
the first prime-side singularity. -/
theorem hadamardLimsup_zetaShift_eq_spectral (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ))
    {a : ℕ → ℂ} (ha : a 1 ≠ 0) :
    hadamardLimsup (fun k : ℕ => riemannZeta (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ))
      = ENNReal.ofReal
          (1 / (2 * Real.pi * Metric.infDist 0 (shiftSpectrum a 1 1))) := by
  rw [hadamardLimsup_zetaShift hs, infDist_zero_shiftSpectrum_zeta ha, mul_one]

end CuspConstant

end RHTower
