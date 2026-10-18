import GaloisForLFunctions.«arithmetic-positivity-theory».GeneralDivisorBernoulliFilterClassification

/-! Envelope-critical prime-dilation phase transition (`β > 1/2` vs. `β ≤ 1/2`),
explicit prime and polar span budgets, and oscillatory prime-dilation cancellation
beyond Cauchy–Schwarz.

For a half-line arithmetic source `f_β(x) = e^{β x} B(e^{-x}) 1_{x ≤ 0}` with envelope
exponent `β > 0`, prime-power translations `t = log r` (`r ≥ 2`) rescale the envelope by
`r^{-β}`, producing a prime-sum majorant with weights `Λ(r) / r^{β + 1/2}` dominated by
the logarithmic envelope series `log r / r^{β + 1/2}`.

We prove:
1. **Exact Envelope-Critical Phase Transition (`iff`):** The logarithmic prime-envelope
   majorant `r ↦ (log r) / r^{β + 1/2}` (`r ≥ 2`) is summable if and only if `1 / 2 < β`.
2. **Subcritical Prime Majorant Summability:** For every `β > 1/2` (and in particular at
   the canonical factorial tail exponent `β = 3/2`), the literal von Mangoldt majorant
   `r ↦ Λ(r) / r^{β + 1/2}` (`r ≥ 2`) is unconditionally summable.
3. **Polar Unit-Interval Weight Bounds and Product Inequality:** For every `M ≥ 1`,
   `∑_{j = 1}^M 1 / j^2 ≤ 2` and `∑_{j = 1}^M 1 / j^3 ≤ 3 / 2`; consequently, polar
   readouts satisfying `‖P₀‖ ≤ 2 √(J S)` and `‖P₁‖ ≤ (3/2) √(J S)` obey
   `|2 Re(P₀ conj P₁)| ≤ 6 J S`.
4. **Oscillatory Prime-Dilation Cancellation Beyond Cauchy–Schwarz:** While Cauchy–Schwarz
   bounds the `[a, b]` correlation of unit-modulus phases `e^{i ω v}` and `e^{i ω r v}`
   only by `|b - a|`, their exact oscillatory integral satisfies
   `‖∫_{a}^{b} e^{i ω (1 - r) v} dv‖ ≤ 2 / (|ω| (r - 1))` for all `r > 1` and `ω ≠ 0`,
   yielding `O(1 / (|ω| r))` high-frequency and large-dilation decay. -/

open Complex MeasureTheory Set Filter intervalIntegral
open scoped BigOperators Topology ComplexConjugate

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The logarithmic prime-envelope majorant `log r / r^{β + 1/2}` for `r ≥ 2`. -/
def envelopeLogMajorant (β : ℝ) (r : ℕ) : ℝ :=
  if 2 ≤ r then Real.log (r : ℝ) / (r : ℝ) ^ (β + 1 / 2) else 0

/-- The von Mangoldt prime-envelope majorant `Λ(r) / r^{β + 1/2}` for `r ≥ 2`. -/
def envelopePrimeMajorant (β : ℝ) (r : ℕ) : ℝ :=
  if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (β + 1 / 2) else 0

theorem envelopePrimeMajorant_nonneg (β : ℝ) (r : ℕ) :
    0 ≤ envelopePrimeMajorant β r := by
  unfold envelopePrimeMajorant
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg r) _)
  · exact le_rfl

theorem envelopeLogMajorant_nonneg (β : ℝ) (r : ℕ) :
    0 ≤ envelopeLogMajorant β r := by
  unfold envelopeLogMajorant
  split_ifs with hr
  · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
    exact div_nonneg (Real.log_nonneg hr1) (Real.rpow_nonneg (Nat.cast_nonneg r) _)
  · exact le_rfl

theorem envelopePrimeMajorant_le_logMajorant (β : ℝ) (r : ℕ) :
    envelopePrimeMajorant β r ≤ envelopeLogMajorant β r := by
  unfold envelopePrimeMajorant envelopeLogMajorant
  split_ifs with hr
  · exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
      (Real.rpow_nonneg (Nat.cast_nonneg r) _)
  · exact le_rfl

/-- Elementary power bound `log x ≤ x^ε / ε` for all `x > 0` and `ε > 0`. -/
theorem log_le_rpow_div {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    Real.log x ≤ x ^ ε / ε := by
  have h1 : Real.log (x ^ ε) ≤ x ^ ε - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx ε)
  rw [Real.log_rpow hx] at h1
  rw [le_div_iff₀ hε, mul_comm]
  linarith

/-- For every `β > 1/2`, the logarithmic prime-envelope majorant is summable. -/
theorem summable_envelopeLogMajorant_of_half_lt {β : ℝ} (hβ : 1 / 2 < β) :
    Summable (envelopeLogMajorant β) := by
  let ε : ℝ := (β - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hp : -(1 + ε) < -1 := by linarith
  have hsum : Summable (fun r : ℕ => (1 / ε) * (r : ℝ) ^ (-(1 + ε))) :=
    (Real.summable_nat_rpow.mpr hp).mul_left (1 / ε)
  refine Summable.of_nonneg_of_le (envelopeLogMajorant_nonneg β) (fun r => ?_) hsum
  unfold envelopeLogMajorant
  split_ifs with hr
  · have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    have hlog := log_le_rpow_div hr_pos hε
    calc
      Real.log (r : ℝ) / (r : ℝ) ^ (β + 1 / 2) ≤
          ((r : ℝ) ^ ε / ε) / (r : ℝ) ^ (β + 1 / 2) :=
        div_le_div_of_nonneg_right hlog (Real.rpow_nonneg hr_pos.le _)
      _ = (1 / ε) * ((r : ℝ) ^ ε * (r : ℝ) ^ (-(β + 1 / 2))) := by
        rw [Real.rpow_neg hr_pos.le]
        ring
      _ = (1 / ε) * (r : ℝ) ^ (-(1 + ε)) := by
        rw [← Real.rpow_add hr_pos]
        congr 2
        dsimp [ε]
        ring
  · exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg r) _)

/-- For `β ≤ 1/2`, the logarithmic prime-envelope majorant diverges by comparison with
the harmonic series. -/
theorem not_summable_envelopeLogMajorant_of_le_half {β : ℝ} (hβ : β ≤ 1 / 2) :
    ¬ Summable (envelopeLogMajorant β) := by
  intro hsum
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdom : ∀ r : ℕ, 2 ≤ r → Real.log 2 * (r : ℝ)⁻¹ ≤ envelopeLogMajorant β r := by
    intro r hr
    unfold envelopeLogMajorant
    rw [if_pos hr]
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hlog_ge : Real.log 2 ≤ Real.log (r : ℝ) := Real.log_le_log (by norm_num) hr2
    have hrpow_le : (r : ℝ) ^ (β + 1 / 2) ≤ (r : ℝ) := by
      calc
        (r : ℝ) ^ (β + 1 / 2) ≤ (r : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
        _ = (r : ℝ) := Real.rpow_one _
    calc
      Real.log 2 * (r : ℝ)⁻¹ = Real.log 2 / (r : ℝ) := div_eq_mul_inv _ _
      _ ≤ Real.log 2 / (r : ℝ) ^ (β + 1 / 2) :=
        div_le_div_of_nonneg_left hlog2.le (Real.rpow_pos_of_pos hr_pos _) hrpow_le
      _ ≤ Real.log (r : ℝ) / (r : ℝ) ^ (β + 1 / 2) :=
        div_le_div_of_nonneg_right hlog_ge (Real.rpow_nonneg hr_pos.le _)
  have hshift : Summable (fun k : ℕ => envelopeLogMajorant β (k + 2)) :=
    (summable_nat_add_iff 2).mpr hsum
  have hharm_shift : Summable (fun k : ℕ => Real.log 2 * ((k + 2 : ℕ) : ℝ)⁻¹) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg hlog2.le (inv_nonneg.mpr (Nat.cast_nonneg _)))
      (fun k => hdom (k + 2) (by omega)) hshift
  have hharm : Summable (fun r : ℕ => ((r : ℝ))⁻¹) := by
    have h1 := hharm_shift.mul_left (Real.log 2)⁻¹
    have h2 : Summable (fun k : ℕ => ((k + 2 : ℕ) : ℝ)⁻¹) := by
      refine h1.congr fun k => ?_
      rw [← mul_assoc, inv_mul_cancel₀ hlog2.ne', one_mul]
    exact (summable_nat_add_iff 2).mp h2
  exact Real.not_summable_natCast_inv hharm

/-- **Exact Envelope-Critical Phase Transition (`iff`).** The logarithmic prime-envelope
majorant `r ↦ log r / r^{β + 1/2}` (`r ≥ 2`) is summable if and only if `1 / 2 < β`. -/
theorem summable_envelopeLogMajorant_iff {β : ℝ} :
    Summable (envelopeLogMajorant β) ↔ 1 / 2 < β := by
  constructor
  · intro h
    by_contra hle
    exact not_summable_envelopeLogMajorant_of_le_half (not_lt.mp hle) h
  · exact summable_envelopeLogMajorant_of_half_lt

/-- **Subcritical Prime Majorant Summability.** For every `β > 1/2`, the von Mangoldt
prime-envelope majorant `r ↦ Λ(r) / r^{β + 1/2}` (`r ≥ 2`) is unconditionally summable. -/
theorem summable_envelopePrimeMajorant_of_half_lt {β : ℝ} (hβ : 1 / 2 < β) :
    Summable (envelopePrimeMajorant β) :=
  Summable.of_nonneg_of_le (envelopePrimeMajorant_nonneg β)
    (envelopePrimeMajorant_le_logMajorant β)
    (summable_envelopeLogMajorant_of_half_lt hβ)

/-- Summability of the canonical `β = 3/2` prime majorant `Λ(r) / r^2` (`r ≥ 2`). -/
theorem summable_canonicalPrimeMajorant :
    Summable (envelopePrimeMajorant (3 / 2)) :=
  summable_envelopePrimeMajorant_of_half_lt (by norm_num)

/-- The canonical prime majorant constant `∑'_{r ≥ 2} Λ(r) / r^2`. -/
def canonicalPrimeMajorantConstant : ℝ :=
  ∑' r : ℕ, envelopePrimeMajorant (3 / 2) r

theorem canonicalPrimeMajorantConstant_nonneg :
    0 ≤ canonicalPrimeMajorantConstant :=
  tsum_nonneg (envelopePrimeMajorant_nonneg (3 / 2))

/-- Unit-interval polar weight bound `∑_{j = 1}^M 1 / j^2 ≤ 2` for all `M : ℕ`. -/
theorem sum_Icc_one_inv_sq_le_two (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, 1 / (j : ℝ) ^ 2) ≤ 2 := by
  rcases eq_or_ne M 0 with rfl | hM0
  · norm_num
  · rcases eq_or_ne M 1 with rfl | hM1
    · norm_num
    · have hM2 : 2 ≤ M := by omega
      have hsplit : Finset.Icc 1 M = insert 1 (insert 2 (Finset.Icc 3 M)) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      have htel := sum_Icc_three_inv_sq_le M hM2
      have hM_inv : 0 ≤ 1 / (M : ℝ) := by positivity
      have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
      have h2 : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 1 / 4 := by norm_num
      linarith

/-- Unit-interval polar weight bound `∑_{j = 1}^M 1 / j^3 ≤ 3 / 2` for all `M : ℕ`. -/
theorem sum_Icc_one_inv_cube_le_three_halves (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, 1 / (j : ℝ) ^ 3) ≤ 3 / 2 := by
  rcases eq_or_ne M 0 with rfl | hM0
  · norm_num
  · rcases eq_or_ne M 1 with rfl | hM1
    · norm_num
    · have hM2 : 2 ≤ M := by omega
      have hsplit : Finset.Icc 1 M = insert 1 (insert 2 (Finset.Icc 3 M)) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      have hle : (∑ j ∈ Finset.Icc 3 M, 1 / (j : ℝ) ^ 3) ≤
          ∑ j ∈ Finset.Icc 3 M, 1 / (j : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
          exact_mod_cast (show 1 ≤ j by linarith [(Finset.mem_Icc.mp hj).1])
        have hj_pos : (0 : ℝ) < (j : ℝ) := by linarith
        have hj_pow : (j : ℝ) ^ 2 ≤ (j : ℝ) ^ 3 := by
          calc
            (j : ℝ) ^ 2 = (j : ℝ) ^ 2 * 1 := by ring
            _ ≤ (j : ℝ) ^ 2 * (j : ℝ) := mul_le_mul_of_nonneg_left hj1 (sq_nonneg _)
            _ = (j : ℝ) ^ 3 := by ring
        exact one_div_le_one_div_of_le (by positivity) hj_pow
      have htel := sum_Icc_three_inv_sq_le M hM2
      have hM_inv : 0 ≤ 1 / (M : ℝ) := by positivity
      have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ 3 = 1 := by norm_num
      have h2 : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ 3 = 1 / 8 := by norm_num
      linarith

/-- **Polar Readout Product Bound.** If the two polar readouts `P₀, P₁ ∈ ℂ` satisfy
`‖P₀‖ ≤ 2 √(J S)` and `‖P₁‖ ≤ (3 / 2) √(J S)` with `0 ≤ J` and `0 ≤ S`, then
`|2 Re(P₀ conj P₁)| ≤ 6 J S`. -/
theorem polar_readout_product_bound {P₀ P₁ : ℂ} {J S : ℝ}
    (hJ : 0 ≤ J) (hS : 0 ≤ S)
    (hP0 : ‖P₀‖ ≤ 2 * Real.sqrt (J * S))
    (hP1 : ‖P₁‖ ≤ (3 / 2 : ℝ) * Real.sqrt (J * S)) :
    |2 * (P₀ * conj P₁).re| ≤ 6 * J * S := by
  have hJS : 0 ≤ J * S := mul_nonneg hJ hS
  calc
    |2 * (P₀ * conj P₁).re| = 2 * |(P₀ * conj P₁).re| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * ‖P₀ * conj P₁‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ = 2 * (‖P₀‖ * ‖P₁‖) := by rw [norm_mul, RCLike.norm_conj]
    _ ≤ 2 * ((2 * Real.sqrt (J * S)) * ((3 / 2 : ℝ) * Real.sqrt (J * S))) := by
      gcongr
    _ = 6 * (Real.sqrt (J * S) ^ 2) := by ring
    _ = 6 * J * S := by rw [Real.sq_sqrt hJS]; ring

/-- **Oscillatory Prime-Dilation Cancellation Beyond Cauchy–Schwarz.**
For any non-zero base frequency `ω ≠ 0`, any dilation factor `r > 1`, and any interval
`[a, b]`, the oscillatory correlation integral of `e^{i ω v}` against `e^{i ω r v}`
satisfies `‖∫_{a}^{b} e^{i ω (1 - r) v} dv‖ ≤ 2 / (|ω| * (r - 1))`, decaying as
`O(1 / (|ω| (r - 1)))` independently of the interval length `|b - a|`. -/
theorem oscillatory_dilation_correlation_bound {ω r : ℝ} (hω : ω ≠ 0) (hr : 1 < r)
    (a b : ℝ) :
    ‖∫ v in a..b, cexp ((I * ((ω * (1 - r) : ℝ) : ℂ)) * (v : ℂ))‖ ≤
      2 / (|ω| * (r - 1)) := by
  have hr_sub : 0 < r - 1 := sub_pos.mpr hr
  have hω_pos : 0 < |ω| := abs_pos.mpr hω
  have hne_real : ω * (1 - r) ≠ 0 := mul_ne_zero hω (by linarith)
  have hne : I * ((ω * (1 - r) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hne_real)
  rw [integral_exp_mul_complex hne, norm_div]
  have hnum : ‖cexp ((I * ((ω * (1 - r) : ℝ) : ℂ)) * (b : ℂ)) -
      cexp ((I * ((ω * (1 - r) : ℝ) : ℂ)) * (a : ℂ))‖ ≤ 2 := by
    have hnorm (x : ℝ) : ‖cexp ((I * ((ω * (1 - r) : ℝ) : ℂ)) * (x : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : ((I * ((ω * (1 - r) : ℝ) : ℂ)) * (x : ℂ)).re = 0 := by simp
      rw [hre, Real.exp_zero]
    calc
      ‖cexp ((I * ((ω * (1 - r) : ℝ) : ℂ)) * (b : ℂ)) -
          cexp ((I * ((ω * (1 - r) : ℝ) : ℂ)) * (a : ℂ))‖ ≤
          ‖cexp ((I * ((ω * (1 - r) : ℝ) : ℂ)) * (b : ℂ))‖ +
            ‖cexp ((I * ((ω * (1 - r) : ℝ) : ℂ)) * (a : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm b, hnorm a]; norm_num
  have hden : ‖I * ((ω * (1 - r) : ℝ) : ℂ)‖ = |ω| * (r - 1) := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_neg (by linarith : 1 - r < 0)]
    ring
  rw [hden]
  exact div_le_div_of_nonneg_right hnum (by positivity)

end

end GaloisForLFunctions.ArithmeticPositivityTheory
