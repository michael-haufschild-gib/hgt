import GaloisForLFunctions.HTGeometry.HardyDiskModelSpace
import GaloisForLFunctions.RHTower.FinitePecherskyUnimodularApproximation
import GaloisForLFunctions.RHTower.ExponentialTypeNotSummableOnPrimeLogsNaturalRate
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The Pechersky density lemma for the prime vectors in the Hardy space of a disc

Fix a centre `z₀` with `1/2 < Re z₀ < 1` and a radius `ρ` with `ρ < Re z₀ − 1/2`,
`ρ < 1 − Re z₀` and `2ρ < 5/12`.  The disc `|z − z₀| < ρ` is the unit disc in the coordinate `q = (z − z₀)/ρ`, and
the Hardy space `H²` of that disc is the coefficient model `HardyDisk = ℓ²(ℕ)` of the corpus.  The
function `q ↦ p^{−(z₀ + ρq)}` has the coefficient vector

  `primeVector z₀ ρ p = p^{−z₀} · ((−ρ log p)^k / k!)_k`,

of squared norm at most `p^{2ρ − 2 Re z₀}`, hence square-summable over the primes
(`summable_norm_primeTerm_sq`).  Its pairing with a vector `e` is
`conj(p^{−z₀}) · Φ_e(log p)`, where `Φ_e(ξ) = Σ_k ((−ρξ)^k/k!) e_k` is entire of exponential type
`ρ` and vanishes identically only for `e = 0` (`coefficientTransform_ne_zero`).  The prime-sum lower
bound `exists_primeLogWeightedSum_gt_of_lt_one_sub` therefore makes the partial sums `Σ_{p<N} |⟪u_p, e⟫|`
unbounded for every `e ≠ 0`, and the finite Pechersky lemma `exists_unimodular_finite_approx`
gives:

**every `h ∈ H²` is within `ε` of a finite unimodular prime sum `Σ_{p<N} ω_p u_p`, with `N` as
large as desired** (`exists_unimodular_primeTerm_sum_approx`).  Read through the Szegő kernel, this is
uniform approximation on every smaller disc: `|h(q) − Σ_{p<N} ω_p p^{−(z₀+ρq)}| < ε/√(1−|q|²)`
(`exists_unimodular_prime_sum_approx_on_disc`).
-/

open Complex Filter Topology Finset
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

/-! ## The prime vectors -/

/-- Coefficients of `q ↦ p^{−(z₀ + ρ q)}` at `q = 0`. -/
def primeVectorCoeff (z₀ : ℂ) (ρ : ℝ) (p : ℕ) (k : ℕ) : ℂ :=
  (p : ℂ) ^ (-z₀) * (((-(ρ * Real.log p)) ^ k / k.factorial : ℝ) : ℂ)

theorem norm_primeVectorCoeff (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    ‖primeVectorCoeff z₀ ρ p k‖
      = (p : ℝ) ^ (-z₀.re) * ((ρ * Real.log p) ^ k / k.factorial) := by
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  rw [primeVectorCoeff, norm_mul, Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]

/-- The squared coefficients are dominated by the terms of `e^{t} · Σ t^k/k!` with `t = ρ log p`. -/
theorem summable_norm_primeVectorCoeff_sq (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p) :
    Summable (fun k => ‖primeVectorCoeff z₀ ρ p k‖ ^ 2) := by
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  set t : ℝ := ρ * Real.log p with ht
  have ht0 : 0 ≤ t := by positivity
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (((Real.summable_pow_div_factorial t).mul_left (Real.exp t)).mul_left
      (((p : ℝ) ^ (-z₀.re)) ^ 2))
  rw [norm_primeVectorCoeff z₀ hρ hp, mul_pow, ← ht]
  gcongr
  calc (t ^ k / k.factorial) ^ 2 = (t ^ k / k.factorial) * (t ^ k / k.factorial) := sq _
    _ ≤ Real.exp t * (t ^ k / k.factorial) := by
        gcongr
        exact Real.pow_div_factorial_le_exp t ht0 k

/-- The squared norm of the prime vector is at most `p^{2ρ − 2 Re z₀}`. -/
theorem tsum_norm_primeVectorCoeff_sq_le (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p) :
    ∑' k, ‖primeVectorCoeff z₀ ρ p k‖ ^ 2 ≤ (p : ℝ) ^ (2 * ρ - 2 * z₀.re) := by
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have ht0 : 0 ≤ ρ * Real.log p := by positivity
  have hexp : HasSum (fun k : ℕ => (ρ * Real.log p) ^ k / k.factorial)
      (Real.exp (ρ * Real.log p)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hbound : ∀ k, ‖primeVectorCoeff z₀ ρ p k‖ ^ 2
      ≤ ((p : ℝ) ^ (-z₀.re)) ^ 2 * Real.exp (ρ * Real.log p)
        * ((ρ * Real.log p) ^ k / k.factorial) := fun k => by
    rw [norm_primeVectorCoeff z₀ hρ hp, mul_pow, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((ρ * Real.log p) ^ k / k.factorial) ^ 2
        = ((ρ * Real.log p) ^ k / k.factorial) * ((ρ * Real.log p) ^ k / k.factorial) := sq _
      _ ≤ Real.exp (ρ * Real.log p) * ((ρ * Real.log p) ^ k / k.factorial) :=
          mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp _ ht0 k) (by positivity)
  have hsum2 := hexp.mul_left (((p : ℝ) ^ (-z₀.re)) ^ 2 * Real.exp (ρ * Real.log p))
  have hle := (summable_norm_primeVectorCoeff_sq z₀ hρ hp).tsum_le_tsum hbound hsum2.summable
  rw [hsum2.tsum_eq] at hle
  refine hle.trans (le_of_eq ?_)
  have h1 : Real.exp (ρ * Real.log p) = (p : ℝ) ^ ρ := by
    rw [Real.rpow_def_of_pos hp', mul_comm]
  have h2 : ((p : ℝ) ^ (-z₀.re)) ^ 2 = (p : ℝ) ^ (-(2 * z₀.re)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp'.le]
    congr 1
    push_cast
    ring
  rw [h1, h2, ← Real.rpow_add hp', ← Real.rpow_add hp']
  congr 1
  ring

theorem memℓp_primeVectorCoeff (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p) :
    Memℓp (primeVectorCoeff z₀ ρ p) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine (summable_norm_primeVectorCoeff_sq z₀ hρ hp).congr fun k => ?_
  rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The prime vector `p^{−z₀} ((−ρ log p)^k/k!)_k` in the Hardy space. -/
def primeVector (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p) : HardyDisk :=
  ⟨primeVectorCoeff z₀ ρ p, memℓp_primeVectorCoeff z₀ hρ hp⟩

theorem primeVector_apply (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (primeVector z₀ hρ hp) k = primeVectorCoeff z₀ ρ p k := rfl

theorem norm_primeVector_sq_le (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p) :
    ‖primeVector z₀ hρ hp‖ ^ 2 ≤ (p : ℝ) ^ (2 * ρ - 2 * z₀.re) := by
  rw [hardyDisk_norm_sq]
  exact tsum_norm_primeVectorCoeff_sq_le z₀ hρ hp

/-- **The prime vector represents `q ↦ p^{−(z₀ + ρ q)}` on the unit disc.** -/
theorem hardyFun_primeVector (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p) (q : ℂ) :
    hardyFun (primeVector z₀ hρ hp) q = (p : ℂ) ^ (-(z₀ + ρ * q)) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hexp : HasSum (fun k : ℕ => (-(ρ : ℂ) * q * Real.log p) ^ k / k.factorial)
      (Complex.exp (-(ρ : ℂ) * q * Real.log p)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hterm : ∀ k : ℕ, (primeVector z₀ hρ hp) k * q ^ k
      = (p : ℂ) ^ (-z₀) * ((-(ρ : ℂ) * q * Real.log p) ^ k / k.factorial) := fun k => by
    rw [primeVector_apply, primeVectorCoeff]
    push_cast
    ring
  unfold hardyFun
  simp_rw [hterm]
  rw [tsum_mul_left, hexp.tsum_eq, neg_add, Complex.cpow_add _ _ hp0,
    Complex.cpow_def_of_ne_zero hp0 (-((ρ : ℂ) * q)), ← Complex.natCast_log]
  congr 2
  ring

/-! ## The coefficient transform -/

/-- `Φ_e(ξ) = Σ_k ((−ρξ)^k/k!) e_k`: the pairing of `e` with the family `p^{−(z₀+ρq)}` read at
`ξ = log p`, up to the factor `conj(p^{−z₀})`. -/
def coefficientTransform (ρ : ℝ) (e : HardyDisk) (ξ : ℂ) : ℂ :=
  ∑' k, ((-(ρ : ℂ) * ξ) ^ k / k.factorial) * e k

/-- The scalar coefficients of `Φ_e` as a power series in `ξ`. -/
def coefficientTransformScalars (ρ : ℝ) (e : HardyDisk) (k : ℕ) : ℂ :=
  (-(ρ : ℂ)) ^ k / k.factorial * e k

theorem norm_coefficientTransformScalars_le (ρ : ℝ) (e : HardyDisk) (k : ℕ) :
    ‖coefficientTransformScalars ρ e k‖ ≤ ‖e‖ * (|ρ| ^ k / k.factorial) := by
  rw [coefficientTransformScalars, norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast]
  calc |ρ| ^ k / (k.factorial : ℝ) * ‖e k‖ ≤ |ρ| ^ k / (k.factorial : ℝ) * ‖e‖ := by
        gcongr
        exact hardyDisk_norm_coord_le e k
    _ = ‖e‖ * (|ρ| ^ k / k.factorial) := by ring

/-- The terms of the transform are the scalar coefficients times `ξ^k`. -/
theorem coefficientTransform_term (ρ : ℝ) (e : HardyDisk) (ξ : ℂ) (k : ℕ) :
    ((-(ρ : ℂ) * ξ) ^ k / k.factorial) * e k = coefficientTransformScalars ρ e k * ξ ^ k := by
  rw [coefficientTransformScalars, mul_pow]
  ring

theorem summable_norm_coefficientTransform_terms (ρ : ℝ) (e : HardyDisk) (ξ : ℂ) :
    Summable (fun k => ‖((-(ρ : ℂ) * ξ) ^ k / k.factorial) * e k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((Real.summable_pow_div_factorial (|ρ| * ‖ξ‖)).mul_left ‖e‖)
  rw [coefficientTransform_term, norm_mul, norm_pow]
  calc ‖coefficientTransformScalars ρ e k‖ * ‖ξ‖ ^ k
      ≤ ‖e‖ * (|ρ| ^ k / k.factorial) * ‖ξ‖ ^ k := by
        gcongr
        exact norm_coefficientTransformScalars_le ρ e k
    _ = ‖e‖ * ((|ρ| * ‖ξ‖) ^ k / k.factorial) := by
        rw [mul_pow]
        ring

/-- **Exponential type.**  `‖Φ_e(ξ)‖ ≤ ‖e‖ e^{ρ‖ξ‖}` for `ρ ≥ 0`. -/
theorem norm_coefficientTransform_le {ρ : ℝ} (hρ : 0 ≤ ρ) (e : HardyDisk) (ξ : ℂ) :
    ‖coefficientTransform ρ e ξ‖ ≤ ‖e‖ * Real.exp (ρ * ‖ξ‖) := by
  have hexp : HasSum (fun k : ℕ => (ρ * ‖ξ‖) ^ k / k.factorial) (Real.exp (ρ * ‖ξ‖)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  calc ‖coefficientTransform ρ e ξ‖
      ≤ ∑' k, ‖((-(ρ : ℂ) * ξ) ^ k / k.factorial) * e k‖ :=
        norm_tsum_le_tsum_norm (summable_norm_coefficientTransform_terms ρ e ξ)
    _ ≤ ∑' k, ‖e‖ * ((ρ * ‖ξ‖) ^ k / k.factorial) := by
        refine (summable_norm_coefficientTransform_terms ρ e ξ).tsum_le_tsum (fun k => ?_)
          (hexp.summable.mul_left _)
        rw [coefficientTransform_term, norm_mul, norm_pow]
        calc ‖coefficientTransformScalars ρ e k‖ * ‖ξ‖ ^ k
            ≤ ‖e‖ * (|ρ| ^ k / k.factorial) * ‖ξ‖ ^ k := by
              gcongr
              exact norm_coefficientTransformScalars_le ρ e k
          _ = ‖e‖ * ((ρ * ‖ξ‖) ^ k / k.factorial) := by
              rw [abs_of_nonneg hρ, mul_pow]
              ring
    _ = ‖e‖ * Real.exp (ρ * ‖ξ‖) := by rw [tsum_mul_left, hexp.tsum_eq]

/-- `Φ_e` is the sum of the scalar power series `coefficientTransformScalars ρ e`. -/
theorem coefficientTransform_eq_ofScalarsSum (ρ : ℝ) (e : HardyDisk) :
    coefficientTransform ρ e
      = FormalMultilinearSeries.ofScalarsSum (coefficientTransformScalars ρ e) := by
  funext ξ
  rw [FormalMultilinearSeries.ofScalars_sum_eq, coefficientTransform]
  refine tsum_congr fun k => ?_
  rw [coefficientTransform_term, smul_eq_mul]

/-- The scalar power series of `Φ_e` has infinite radius. -/
theorem coefficientTransform_radius (ρ : ℝ) (e : HardyDisk) :
    (FormalMultilinearSeries.ofScalars ℂ (coefficientTransformScalars ρ e)).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine FormalMultilinearSeries.le_radius_of_bound _ (‖e‖ * Real.exp (|ρ| * r)) fun k => ?_
  rw [FormalMultilinearSeries.ofScalars_norm]
  calc ‖coefficientTransformScalars ρ e k‖ * (r : ℝ) ^ k
      ≤ ‖e‖ * (|ρ| ^ k / k.factorial) * (r : ℝ) ^ k := by
        gcongr
        exact norm_coefficientTransformScalars_le ρ e k
    _ = ‖e‖ * ((|ρ| * r) ^ k / k.factorial) := by
        rw [mul_pow]
        ring
    _ ≤ ‖e‖ * Real.exp (|ρ| * r) := by
        gcongr
        exact Real.pow_div_factorial_le_exp _ (by positivity) k

/-- `Φ_e` has the scalar power series on the whole plane. -/
theorem hasFPowerSeriesOnBall_coefficientTransform (ρ : ℝ) (e : HardyDisk) :
    HasFPowerSeriesOnBall (coefficientTransform ρ e)
      (FormalMultilinearSeries.ofScalars ℂ (coefficientTransformScalars ρ e)) 0 ⊤ := by
  have h := (FormalMultilinearSeries.ofScalars ℂ (coefficientTransformScalars ρ e)).hasFPowerSeriesOnBall
    (by rw [coefficientTransform_radius]; exact ENNReal.zero_lt_top)
  rw [coefficientTransform_radius] at h
  rw [coefficientTransform_eq_ofScalarsSum]
  exact h

/-- `Φ_e` is entire. -/
theorem differentiable_coefficientTransform (ρ : ℝ) (e : HardyDisk) :
    Differentiable ℂ (coefficientTransform ρ e) := fun ξ =>
  ((hasFPowerSeriesOnBall_coefficientTransform ρ e).analyticAt_of_mem
    (by simp)).differentiableAt

/-- **`Φ_e` vanishes identically only for `e = 0`** (`ρ ≠ 0`). -/
theorem coefficientTransform_ne_zero {ρ : ℝ} (hρ : ρ ≠ 0) {e : HardyDisk} (he : e ≠ 0) :
    coefficientTransform ρ e ≠ 0 := by
  intro h0
  have hseries := (hasFPowerSeriesOnBall_coefficientTransform ρ e).hasFPowerSeriesAt
  rw [h0] at hseries
  have hzero := hseries.eq_zero
  rw [FormalMultilinearSeries.ofScalars_series_eq_zero] at hzero
  apply he
  refine lp.ext (funext fun k => ?_)
  have hk := congrFun hzero k
  simp only [coefficientTransformScalars, Pi.zero_apply, mul_eq_zero, div_eq_zero_iff,
    pow_eq_zero_iff', neg_eq_zero, Complex.ofReal_eq_zero, Nat.cast_eq_zero,
    Nat.factorial_ne_zero, or_false] at hk
  rcases hk with ⟨hρ', _⟩ | hk
  · exact absurd hρ' hρ
  · simpa using hk

/-! ## Pairing with the prime vectors -/

/-- **The pairing with a prime vector is the coefficient transform at `log p`.** -/
theorem inner_primeVector (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p) (e : HardyDisk) :
    ⟪primeVector z₀ hρ hp, e⟫_ℂ
      = conj ((p : ℂ) ^ (-z₀)) * coefficientTransform ρ e (Real.log p) := by
  rw [lp.inner_eq_tsum, coefficientTransform, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [RCLike.inner_apply, primeVector_apply, primeVectorCoeff, map_mul, Complex.conj_ofReal]
  push_cast
  ring

theorem norm_inner_primeVector (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p)
    (e : HardyDisk) :
    ‖⟪primeVector z₀ hρ hp, e⟫_ℂ‖
      = (p : ℝ) ^ (-z₀.re) * ‖coefficientTransform ρ e (Real.log p)‖ := by
  rw [inner_primeVector, norm_mul, Complex.norm_conj, Complex.norm_natCast_cpow_of_pos hp,
    Complex.neg_re]

/-- The prime vector at `n` when `n` is prime, and `0` otherwise. -/
def primeTerm (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) : HardyDisk :=
  if hn : n.Prime then primeVector z₀ hρ hn.pos else 0

theorem primeTerm_of_prime (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {n : ℕ} (hn : n.Prime) :
    primeTerm z₀ hρ n = primeVector z₀ hρ hn.pos := dif_pos hn

theorem primeTerm_of_not_prime (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {n : ℕ} (hn : ¬ n.Prime) :
    primeTerm z₀ hρ n = 0 := dif_neg hn

/-- **Square-summability of the prime vectors**: `Σ_p ‖u_p‖² ≤ Σ_p p^{2ρ−2 Re z₀} < ∞`. -/
theorem summable_norm_primeTerm_sq (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρσ : 2 * ρ - 2 * z₀.re < -1) :
    Summable (fun n => ‖primeTerm z₀ hρ n‖ ^ 2) := by
  have hprimes : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (2 * ρ - 2 * z₀.re)) :=
    Nat.Primes.summable_rpow.mpr hρσ
  have hind : Summable ({p : ℕ | p.Prime}.indicator fun n : ℕ => (n : ℝ) ^ (2 * ρ - 2 * z₀.re)) :=
    summable_subtype_iff_indicator.mp hprimes
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hind
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hn : n.Prime
  · rw [if_pos hn, primeTerm_of_prime z₀ hρ hn]
    exact norm_primeVector_sq_le z₀ hρ hn.pos
  · rw [if_neg hn, primeTerm_of_not_prime z₀ hρ hn]
    simp

/-- The partial absolute pairings with the prime terms are the weighted prime sums of `Φ_e`. -/
theorem sum_norm_inner_primeTerm (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (e : HardyDisk) (N : ℕ) :
    ∑ n ∈ range N, ‖⟪primeTerm z₀ hρ n, e⟫_ℂ‖
      = primeLogWeightedSum (coefficientTransform ρ e) z₀.re N := by
  unfold primeLogWeightedSum
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : n.Prime
  · rw [if_pos hn, primeTerm_of_prime z₀ hρ hn, norm_inner_primeVector]
  · rw [if_neg hn, primeTerm_of_not_prime z₀ hρ hn, inner_zero_left, norm_zero]

/-- **Divergence of the absolute pairings**: for `e ≠ 0` the sums `Σ_{p<N} |⟪u_p, e⟫|` are
unbounded. -/
theorem exists_sum_norm_inner_primeTerm_gt (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hσ : 1 / 2 ≤ z₀.re)
    (hρσ : ρ < 1 - z₀.re) (hρ5 : 2 * ρ < 5 / 12) {e : HardyDisk} (he : e ≠ 0) (M : ℝ) :
    ∃ N : ℕ, M < ∑ n ∈ range N, ‖⟪primeTerm z₀ hρ.le n, e⟫_ℂ‖ := by
  obtain ⟨N, hN⟩ := exists_primeLogWeightedSum_gt_of_lt_one_sub
    (differentiable_coefficientTransform ρ e) hρ.le (norm_coefficientTransform_le hρ.le e)
    (coefficientTransform_ne_zero hρ.ne' he) (by linarith) hρσ hρ5 M
  exact ⟨N, by rwa [sum_norm_inner_primeTerm]⟩

/-! ## The Pechersky density lemma -/

/-- **Pechersky density for the prime vectors.**  Every `h ∈ H²` is within `ε` of a finite
unimodular prime sum `Σ_{n<N} ω_n • u_n` (`u_n = 0` for composite `n`), with `N ≥ N₀`. -/
theorem exists_unimodular_primeTerm_sum_approx (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ z₀.re) (hρσ₁ : 2 * ρ - 2 * z₀.re < -1) (hρσ₂ : ρ < 1 - z₀.re)
    (hρ5 : 2 * ρ < 5 / 12)
    (h : HardyDisk) {ε : ℝ} (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∃ ω : ℕ → ℂ, (∀ n, ‖ω n‖ = 1) ∧
      ‖h - ∑ n ∈ range N, ω n • primeTerm z₀ hρ.le n‖ < ε :=
  exists_unimodular_finite_approx (primeTerm z₀ hρ.le) (summable_norm_primeTerm_sq z₀ hρ.le hρσ₁)
    (fun _ he M => exists_sum_norm_inner_primeTerm_gt z₀ hρ hσ hρσ₂ hρ5 he M) h hε N₀

/-! ## Uniform approximation on the disc -/

/-- The squared norm of the Szegő kernel. -/
theorem norm_hardyDiskKernel_sq {a : ℂ} (ha : ‖a‖ < 1) :
    ‖GaloisForLFunctions.HTGeometry.hardyKernel ha‖ ^ 2 = (1 - ‖a‖ ^ 2)⁻¹ := by
  rw [hardyDisk_norm_sq]
  have hsq : ‖a‖ ^ 2 < 1 := by nlinarith [norm_nonneg a]
  rw [← tsum_geometric_of_lt_one (by positivity) hsq]
  refine tsum_congr fun n => ?_
  show ‖hardyKernelCoeff a n‖ ^ 2 = (‖a‖ ^ 2) ^ n
  rw [hardyKernelCoeff, norm_pow, Complex.norm_conj]
  ring

/-- The Hardy function of a prime term at `q`: `p^{−(z₀+ρq)}` for prime `n`, `0` otherwise. -/
theorem hardyFun_primeTerm (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    hardyFun (primeTerm z₀ hρ n) q
      = if n.Prime then (n : ℂ) ^ (-(z₀ + ρ * q)) else 0 := by
  by_cases hn : n.Prime
  · rw [if_pos hn, primeTerm_of_prime z₀ hρ hn, hardyFun_primeVector]
  · rw [if_neg hn, primeTerm_of_not_prime z₀ hρ hn,
      ← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq, inner_zero_right]

/-- **Uniform approximation on the disc by unimodular prime sums.**  For `h ∈ H²` and `|q| < 1`,
the approximant of `exists_unimodular_primeTerm_sum_approx` satisfies
`‖h(q) − Σ_{p<N} ω_p p^{−(z₀+ρq)}‖ < ε (1 − |q|²)^{−1/2}`. -/
theorem exists_unimodular_prime_sum_approx_on_disc (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ z₀.re) (hρσ₁ : 2 * ρ - 2 * z₀.re < -1) (hρσ₂ : ρ < 1 - z₀.re)
    (hρ5 : 2 * ρ < 5 / 12)
    (h : HardyDisk) {ε : ℝ} (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∃ ω : ℕ → ℂ, (∀ n, ‖ω n‖ = 1) ∧
      ∀ q : ℂ, ‖q‖ < 1 →
        ‖hardyFun h q - ∑ n ∈ range N,
            ω n * (if n.Prime then (n : ℂ) ^ (-(z₀ + ρ * q)) else 0)‖
          < ε * Real.sqrt ((1 - ‖q‖ ^ 2)⁻¹) := by
  obtain ⟨N, hN, ω, hω, hclose⟩ :=
    exists_unimodular_primeTerm_sum_approx z₀ hρ hσ hρσ₁ hρσ₂ hρ5 h hε N₀
  refine ⟨N, hN, ω, hω, fun q hq => ?_⟩
  have hsq : ‖q‖ ^ 2 < 1 := by nlinarith [norm_nonneg q]
  have hinv : 0 < (1 - ‖q‖ ^ 2)⁻¹ := by
    have : 0 < 1 - ‖q‖ ^ 2 := by linarith
    positivity
  set κ : HardyDisk := GaloisForLFunctions.HTGeometry.hardyKernel hq with hκ
  have hker : ‖κ‖ = Real.sqrt ((1 - ‖q‖ ^ 2)⁻¹) := by
    rw [hκ, ← norm_hardyDiskKernel_sq hq, Real.sqrt_sq (norm_nonneg _)]
  have hval : hardyFun h q - ∑ n ∈ range N,
      ω n * (if n.Prime then (n : ℂ) ^ (-(z₀ + ρ * q)) else 0)
      = ⟪κ, h - ∑ n ∈ range N, ω n • primeTerm z₀ hρ.le n⟫_ℂ := by
    rw [inner_sub_right, inner_sum, hκ, GaloisForLFunctions.HTGeometry.inner_hardyKernel]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [inner_smul_right, GaloisForLFunctions.HTGeometry.inner_hardyKernel,
      hardyFun_primeTerm z₀ hρ.le n hq]
  rw [hval]
  calc ‖⟪κ, h - ∑ n ∈ range N, ω n • primeTerm z₀ hρ.le n⟫_ℂ‖
      ≤ ‖κ‖ * ‖h - ∑ n ∈ range N, ω n • primeTerm z₀ hρ.le n‖ := norm_inner_le_norm _ _
    _ < ‖κ‖ * ε := by
        have hkpos : 0 < ‖κ‖ := by
          rw [hker]
          exact Real.sqrt_pos.mpr hinv
        exact mul_lt_mul_of_pos_left hclose hkpos
    _ = ε * Real.sqrt ((1 - ‖q‖ ^ 2)⁻¹) := by rw [hker, mul_comm]

end RHTower
