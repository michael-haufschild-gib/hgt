import GaloisForLFunctions.RHTower.PMPowerDampedMobiusMellin
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDiscreteEnergy
import GaloisForLFunctions.ArithmeticDefectRigidity.TwoEulerFactorsDetermineThePoleTrace

/-!
# The Laplace form of the cofactor profile

`TheCofactorGramIsATranslationGram` writes the cofactor Gram as a translation Gram of the log
profile `g(u) = e^{−u/2} A(⌊e^u⌋)` of the receiver row `A(n) = Σ_{m ≤ n} a(m)`. Its Laplace
transform at `z = s − ½` is `∫ A(⌊e^u⌋) e^{−su} du`, and summation by parts identifies it with the
Dirichlet series of `a` divided by `s`.

* **Every horizon** (`integral_prefix_exp_eq`). For `s ≠ 0`,
  `∫_0^{log(N+1)} A(⌊e^u⌋) e^{−su} du = (Σ_{n ≤ N} a(n) n^{−s} − A(N)(N+1)^{−s})/s`: on the cell
  `[log n, log(n+1))` the integral is `A(n)(n^{−s} − (n+1)^{−s})/s`, and Abel summation
  (`sum_prefix_cpow_diff`) collects the cells.
* **The cofactor symbol** (`LSeries_centeredDivisorCoeff`). For the centered divisor coefficients
  `c̃_ε(n) = Σ_{d∣n} μ(d) d^{−ε} − Re(1/ζ(1+ε))` of the damped Möbius receiver,
  `Σ c̃_ε(n) n^{−s} = ζ(s)/ζ(s + ε) − Re(1/ζ(1+ε)) ζ(s)` on `Re s > 1`.
* **The Laplace form** (`tendsto_laplace_cofactorProfile`). The truncated Laplace transform plus the
  boundary term `A(N)(N+1)^{−s}/s` tends to
  `G(s) = ζ(s)(1/ζ(s + ε) − Re(1/ζ(1+ε)))/s` on `Re s > 1`.

So the escape states of the cofactor are normalized limits of translation Grams of one profile
whose Laplace transform is `G`. Its singularities in `Re s > ½` are the translated zeros `ρ − ε`
(zeros of `ζ(s + ε)`), with the pole of `ζ` at `s = 1` cancelled by the centering; each simple one
contributes the exponential `e^{(ρ − ε − ½)u}` to the profile and the power character
`j^{−(ρ−ε)} k^{−(ρ̄−ε)}` to the Gram. Escape completeness is the statement that, after these
exponentials are removed, the remaining profile has subdominant energy.
-/

open Complex MeasureTheory Set Finset Filter Topology
open GaloisForLFunctions.ArithmeticDefectRigidity (mem_Ico_log_iff)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The partial sums `A(n) = Σ_{1 ≤ m ≤ n} a(m)`. -/
def prefixSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, a m

theorem prefixSum_zero (a : ℕ → ℝ) : prefixSum a 0 = 0 := by simp [prefixSum]

theorem prefixSum_succ (a : ℕ → ℝ) (n : ℕ) : prefixSum a (n + 1) = prefixSum a n + a (n + 1) := by
  rw [prefixSum, prefixSum, ← Nat.Icc_insert_succ_right (by omega), sum_insert (by simp), add_comm]

/-- **Abel summation.** `Σ_{n < N} A(n+1)((n+1)^{−s} − (n+2)^{−s}) = Σ_{n ≤ N} a(n) n^{−s} − A(N)(N+1)^{−s}`. -/
theorem sum_prefix_cpow_diff (a : ℕ → ℝ) (s : ℂ) (N : ℕ) :
    ∑ n ∈ range N, (prefixSum a (n + 1) : ℂ) *
        (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) =
      ∑ n ∈ Icc 1 N, (a n : ℂ) * (n : ℂ) ^ (-s) - (prefixSum a N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp [prefixSum_zero]
  | succ N ih =>
    rw [sum_range_succ, ih, ← Nat.Icc_insert_succ_right (by omega), sum_insert (by simp),
      prefixSum_succ]
    push_cast
    ring

/-- The cell integral `∫_{log(n+1)}^{log(n+2)} e^{−su} du = ((n+1)^{−s} − (n+2)^{−s})/s`. -/
theorem integral_cell_cexp {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    ∫ u in Real.log ((n : ℝ) + 1)..Real.log ((n : ℝ) + 2), Complex.exp (-s * u) =
      (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) / s := by
  have hc : -s ≠ 0 := neg_ne_zero.mpr hs
  rw [integral_exp_mul_complex hc]
  have e : ∀ x : ℝ, 0 < x → Complex.exp (-s * (Real.log x : ℂ)) = (x : ℂ) ^ (-s) := by
    intro x hx
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
      mul_comm]
  rw [e _ (by positivity), e _ (by positivity)]
  push_cast
  field_simp
  ring

/-- **The Laplace transform at every horizon.** -/
theorem integral_prefix_exp_eq (a : ℕ → ℝ) {s : ℂ} (hs : s ≠ 0) (N : ℕ) :
    ∫ u in (0 : ℝ)..Real.log ((N : ℝ) + 1),
        (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u) =
      (∑ n ∈ Icc 1 N, (a n : ℂ) * (n : ℂ) ^ (-s) -
        (prefixSum a N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s)) / s := by
  -- on each cell the prefix is constant
  have hcell : ∀ n : ℕ, ∫ u in Real.log ((n : ℝ) + 1)..Real.log ((n : ℝ) + 2),
      (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u) =
      (prefixSum a (n + 1) : ℂ) * ((((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) / s) := by
    intro n
    have hab : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hae : ∀ᵐ u ∂volume, u ∈ Ι (Real.log ((n : ℝ) + 1)) (Real.log ((n : ℝ) + 2)) →
        (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u) =
          (prefixSum a (n + 1) : ℂ) * Complex.exp (-s * u) := by
      have hb : ∀ᵐ u ∂volume, u ≠ Real.log ((n : ℝ) + 2) := by
        simpa using (measure_singleton (μ := volume) (Real.log ((n : ℝ) + 2)))
      filter_upwards [hb] with u hu hmem
      rw [uIoc_of_le hab] at hmem
      rw [(mem_Ico_log_iff n).mp ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hu⟩]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
      integral_cell_cexp hs]
  have hint : ∀ n < N, IntervalIntegrable
      (fun u : ℝ => (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u)) volume
      (Real.log ((n : ℝ) + 1)) (Real.log (((n + 1 : ℕ) : ℝ) + 1)) := by
    intro n _
    rw [show (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 by push_cast; ring]
    have hab : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    refine ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
      ).intervalIntegrable _ _ |>.const_mul (prefixSum a (n + 1) : ℂ)).congr ?_
    rw [uIoc_of_le hab]
    have hb : ∀ᵐ u ∂volume.restrict (Ioc (Real.log ((n : ℝ) + 1)) (Real.log ((n : ℝ) + 2))),
        u ≠ Real.log ((n : ℝ) + 2) :=
      ae_restrict_of_ae (by simpa using (measure_singleton (μ := volume) (Real.log ((n : ℝ) + 2))))
    filter_upwards [hb, ae_restrict_mem measurableSet_Ioc] with u hu hmem
    simp only
    rw [(mem_Ico_log_iff n).mp ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hu⟩]
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun u : ℝ => (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u))
    (a := fun n : ℕ => Real.log ((n : ℝ) + 1)) (n := N) hint
  simp only [Nat.cast_zero, zero_add, Real.log_one] at hsplit
  rw [← hsplit]
  have hcell' : ∀ n : ℕ, ∫ u in Real.log ((n : ℝ) + 1)..Real.log (((n + 1 : ℕ) : ℝ) + 1),
      (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u) =
      (prefixSum a (n + 1) : ℂ) * ((((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) / s) := by
    intro n
    rw [show (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 by push_cast; ring]
    exact hcell n
  simp_rw [hcell']
  rw [← sum_prefix_cpow_diff a s N, sum_div]
  refine sum_congr rfl fun n _ => ?_
  ring

/-! ### The cofactor symbol -/

/-- The divisor coefficients are the convolution of `μ(n) n^{−ε}` with `1`. -/
theorem divisorCoeff_eq_convolution (ε : ℝ) :
    (fun n => (RHTower.pmPowerDampedDivisorCoeff ε n : ℂ)) =
      LSeries.convolution (RHTower.pmPowerDampedMobiusCoeff ε) 1 := by
  rw [LSeries.convolution_def]
  funext n
  rw [RHTower.pmPowerDampedDivisorCoeff, Nat.sum_divisorsAntidiagonal
    (fun d _ => RHTower.pmPowerDampedMobiusCoeff ε d * (1 : ℕ → ℂ) _)]
  simp [RHTower.pmPowerDampedMobiusCoeff]

/-- **The cofactor symbol**: `Σ c̃_ε(n) n^{−s} = ζ(s)/ζ(s+ε) − Re(1/ζ(1+ε)) ζ(s)` on `Re s > 1`. -/
theorem LSeries_centeredDivisorCoeff {ε : ℝ} (hε : 0 ≤ ε) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (RHTower.pmPowerDampedCenteredDivisorCoeff ε n : ℂ)) s =
      riemannZeta s / riemannZeta (s + ε) -
        ((RHTower.pmPowerDampedDivisorDensity ε).re : ℂ) * riemannZeta s := by
  have hμ : LSeriesSummable (RHTower.pmPowerDampedMobiusCoeff ε) s :=
    RHTower.pmPowerDampedMobiusCoeff_lSeriesSummable ε (by linarith)
  have h1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have hconv : LSeries (fun n => (RHTower.pmPowerDampedDivisorCoeff ε n : ℂ)) s =
      riemannZeta s / riemannZeta (s + ε) := by
    rw [divisorCoeff_eq_convolution, LSeries_convolution' hμ h1,
      RHTower.pmPowerDampedMobiusCoeff_lSeries ε (by linarith), LSeries_one_eq_riemannZeta hs]
    ring
  have hsum : LSeriesSummable (fun n => (RHTower.pmPowerDampedDivisorCoeff ε n : ℂ)) s := by
    rw [divisorCoeff_eq_convolution]; exact hμ.convolution h1
  have hd : (fun n => (RHTower.pmPowerDampedCenteredDivisorCoeff ε n : ℂ)) =
      (fun n => (RHTower.pmPowerDampedDivisorCoeff ε n : ℂ)) -
        ((RHTower.pmPowerDampedDivisorDensity ε).re : ℂ) • (1 : ℕ → ℂ) := by
    funext n; simp [RHTower.pmPowerDampedCenteredDivisorCoeff]
  rw [hd, LSeries_sub hsum (h1.smul _), LSeries_smul, hconv, LSeries_one_eq_riemannZeta hs]

/-- The cofactor function `G(s) = ζ(s)(1/ζ(s + ε) − Re(1/ζ(1+ε)))/s`. -/
def cofactorG (ε : ℝ) (s : ℂ) : ℂ :=
  (riemannZeta s / riemannZeta (s + ε) -
    ((RHTower.pmPowerDampedDivisorDensity ε).re : ℂ) * riemannZeta s) / s

/-- **The Laplace form of the cofactor profile.** On `Re s > 1` the truncated Laplace transform of
`A(⌊e^u⌋)`, `A` the centered prefix, plus the boundary term `A(N)(N+1)^{−s}/s` tends to `G(s)`. -/
theorem tendsto_laplace_cofactorProfile {ε : ℝ} (hε : 0 ≤ ε) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ =>
        (∫ u in (0 : ℝ)..Real.log ((N : ℝ) + 1),
          (prefixSum (RHTower.pmPowerDampedCenteredDivisorCoeff ε) ⌊Real.exp u⌋₊ : ℂ) *
            Complex.exp (-s * u)) +
        (prefixSum (RHTower.pmPowerDampedCenteredDivisorCoeff ε) N : ℂ) *
          ((N + 1 : ℕ) : ℂ) ^ (-s) / s)
      atTop (𝓝 (cofactorG ε s)) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  set a := RHTower.pmPowerDampedCenteredDivisorCoeff ε
  have hrw : ∀ N : ℕ, (∫ u in (0 : ℝ)..Real.log ((N : ℝ) + 1),
      (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u)) +
        (prefixSum a N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s) / s =
      (∑ n ∈ range (N + 1), LSeries.term (fun n => (a n : ℂ)) s n) / s := by
    intro N
    rw [integral_prefix_exp_eq a hs0 N, ← add_div, sub_add_cancel]
    congr 1
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), LSeries.term_zero, zero_add,
      ← Nat.Ico_succ_right]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by rw [mem_Ico] at hn; omega
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
  simp_rw [hrw]
  rw [cofactorG, ← LSeries_centeredDivisorCoeff hε hs]
  have hsum : LSeriesSummable (fun n => (a n : ℂ)) s := by
    have hμ : LSeriesSummable (RHTower.pmPowerDampedMobiusCoeff ε) s :=
      RHTower.pmPowerDampedMobiusCoeff_lSeriesSummable ε (by linarith)
    have h1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
    have hd : (fun n => (a n : ℂ)) = (fun n => (RHTower.pmPowerDampedDivisorCoeff ε n : ℂ)) -
        ((RHTower.pmPowerDampedDivisorDensity ε).re : ℂ) • (1 : ℕ → ℂ) := by
      funext n; simp [a, RHTower.pmPowerDampedCenteredDivisorCoeff]
    rw [hd, divisorCoeff_eq_convolution]
    exact (hμ.convolution h1).sub (h1.smul _)
  exact (hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).div_const s

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
