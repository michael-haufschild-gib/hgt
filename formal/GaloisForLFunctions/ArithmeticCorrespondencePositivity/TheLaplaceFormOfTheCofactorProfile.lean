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

open Complex MeasureTheory Finset Filter Topology
open GaloisForLFunctions.ArithmeticDefectRigidity (mem_Ico_log_iff)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The partial sums `A(n) = Σ_{1 ≤ m ≤ n} a(m)`. -/
def prefixSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ m ∈ Icc 1 n, a m

theorem prefixSum_zero (a : ℕ → ℝ) : prefixSum a 0 = 0 := by simp [prefixSum]

theorem prefixSum_succ (a : ℕ → ℝ) (n : ℕ) : prefixSum a (n + 1) = prefixSum a n + a (n + 1) := by
  rw [prefixSum, prefixSum, sum_Icc_succ_top (by omega)]

/-- **Abel summation.** `Σ_{n < N} A(n+1)(f(n+1) − f(n+2)) = Σ_{n ≤ N} a(n) f(n) − A(N) f(N+1)`. -/
theorem sum_prefix_diff (a : ℕ → ℝ) (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range N, (prefixSum a (n + 1) : ℂ) * (f (n + 1) - f (n + 2)) =
      ∑ n ∈ Icc 1 N, (a n : ℂ) * f n - (prefixSum a N : ℂ) * f (N + 1) := by
  induction N with
  | zero => simp [prefixSum_zero]
  | succ N ih =>
    rw [sum_range_succ, ih, sum_Icc_succ_top (by omega), prefixSum_succ,
      show N + 1 + 1 = N + 2 from rfl]
    push_cast
    ring

/-- The cell integral `∫_{log(n+1)}^{log(n+2)} e^{−su} du = ((n+1)^{−s} − (n+2)^{−s})/s`. -/
theorem integral_cell_cexp {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    ∫ u in Real.log ((n : ℝ) + 1)..Real.log ((n : ℝ) + 2), Complex.exp (-s * u) =
      (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) / s := by
  have hc : -s ≠ 0 := neg_ne_zero.mpr hs
  have e : ∀ x : ℝ, 0 < x → Complex.exp (-s * (Real.log x : ℂ)) = (x : ℂ) ^ (-s) := by
    intro x hx
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
      mul_comm]
  rw [integral_exp_mul_complex hc, e ((n : ℝ) + 2) (by positivity),
    e ((n : ℝ) + 1) (by positivity)]
  push_cast
  field_simp
  ring

/-- On the open cell `(log(n+1), log(n+2))` the prefix profile is `A(n+1)`. -/
theorem prefix_cell_eqOn (a : ℕ → ℝ) (s : ℂ) (n : ℕ) :
    Set.EqOn (fun u : ℝ => (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u))
      (fun u : ℝ => (prefixSum a (n + 1) : ℂ) * Complex.exp (-s * u))
      (Set.uIoo (Real.log ((n : ℝ) + 1)) (Real.log ((n : ℝ) + 2))) := by
  intro u hu
  rw [Set.uIoo_of_le (Real.log_le_log (by positivity) (by linarith))] at hu
  simp only
  rw [(mem_Ico_log_iff n).mp ⟨hu.1.le, hu.2⟩]

/-- **The Laplace transform at every horizon.** -/
theorem integral_prefix_exp_eq (a : ℕ → ℝ) {s : ℂ} (hs : s ≠ 0) (N : ℕ) :
    ∫ u in (0 : ℝ)..Real.log ((N : ℝ) + 1),
        (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u) =
      (∑ n ∈ Icc 1 N, (a n : ℂ) * (n : ℂ) ^ (-s) -
        (prefixSum a N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s)) / s := by
  have hcast : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := fun n => by push_cast; ring
  -- split `[0, log(N+1)]` into the cells `[log(n+1), log(n+2)]`, `n < N`
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun u : ℝ => (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u))
    (a := fun n : ℕ => Real.log ((n : ℝ) + 1)) (n := N) fun n _ => by
      simp only [hcast]
      exact (((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
        ).intervalIntegrable _ _).const_mul _).congr_uIoo fun u hu =>
          (prefix_cell_eqOn a s n hu).symm
  simp only [Nat.cast_zero, zero_add, Real.log_one] at hsplit
  rw [← hsplit]
  have hcell : ∀ n : ℕ, ∫ u in Real.log ((n : ℝ) + 1)..Real.log (((n + 1 : ℕ) : ℝ) + 1),
      (prefixSum a ⌊Real.exp u⌋₊ : ℂ) * Complex.exp (-s * u) =
      (prefixSum a (n + 1) : ℂ) * ((((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) / s) := by
    intro n
    rw [hcast, intervalIntegral.integral_congr_uIoo (prefix_cell_eqOn a s n),
      intervalIntegral.integral_const_mul, integral_cell_cexp hs]
  simp_rw [hcell]
  have habel := sum_prefix_diff a (fun n : ℕ => (n : ℂ) ^ (-s)) N
  simp only at habel
  rw [← habel, sum_div]
  refine sum_congr rfl fun n _ => ?_
  ring

/-! ### The cofactor symbol -/

/-- The divisor coefficients are the convolution of `μ(n) n^{−ε}` with `1`. -/
theorem divisorCoeff_eq_convolution (ε : ℝ) :
    (fun n => (RHTower.pmPowerDampedDivisorCoeff ε n : ℂ)) =
      LSeries.convolution (RHTower.pmPowerDampedMobiusCoeff ε) 1 := by
  rw [LSeries.convolution_def]
  funext n
  rw [Nat.sum_divisorsAntidiagonal
    (fun x y => RHTower.pmPowerDampedMobiusCoeff ε x * (1 : ℕ → ℂ) y),
    RHTower.pmPowerDampedDivisorCoeff]
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
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel,
      sum_range_succ', LSeries.term_zero, add_zero]
    refine sum_congr rfl fun n _ => ?_
    rw [LSeries.term_of_ne_zero (by omega), add_comm 1 n, Complex.cpow_neg, div_eq_mul_inv]
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
