import GaloisForLFunctions.«arithmetic-positivity-theory».GeneralDivisorBernoulliFilterClassification
import GaloisForLFunctions.RHTower.VanDerCorputIBP

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
   yielding `O(1 / (|ω| r))` high-frequency and large-dilation decay.
5. **General `β ∈ (1/2, 2]` Physical `L^2` Weight, Polar `s = 1` Transition at `β = 1`, and
   Weighted `[1, ∞)` Oscillatory Prime-Dilation Gain:** We establish the exact `1 / (2 β)`
   integral of `v^{-(2 β + 1)}` on `(1, ∞)` for all `β > 0`, the `s = 1` polar summability
   transition `∑ j^{-β} < ∞ ↔ β > 1`, the weighted `[1, ∞)` integration-by-parts bound
   `‖∫_{1}^{∞} v^{-(2 β + 1)} e^{i ω (1 - r) v} dv‖ ≤ 2 / (|ω| (r - 1))` for all `β > 0`,
   and the resulting summability of the oscillatory prime-dilation series
   `Λ(r) / (r^{β + 1/2} (r - 1))` for all `β > -1/2` (including the critical exponent `β = 1/2`). -/

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
          (1 / 3 : ℝ) * ∑ j ∈ Finset.Icc 3 M, 1 / (j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => ?_
        have hj3 : (3 : ℝ) ≤ (j : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hj).1
        have hj_pos : (0 : ℝ) < (j : ℝ) := by linarith
        have hj_pow : 3 * (j : ℝ) ^ 2 ≤ (j : ℝ) ^ 3 := by
          calc
            3 * (j : ℝ) ^ 2 ≤ (j : ℝ) * (j : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hj3 (sq_nonneg _)
            _ = (j : ℝ) ^ 3 := by ring
        rw [one_div_mul_one_div]
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

/-! ### General `β ∈ (1/2, 2]` Physical `L^2` Weight, Polar `s = 1` Transition, and Weighted
`[1, ∞)` Oscillatory Prime-Dilation Cancellation -/

/-- Physical `L^2` envelope weight `v^{-(2 β + 1)}` on `[1, ∞)` induced by `v = e^{-x}`
(`dx = -dv / v`) on the half-line source `f_β(x) = e^{β x} B(e^{-x}) 1_{x ≤ 0}`. -/
def physicalEnvelopeWeight (β : ℝ) (v : ℝ) : ℝ :=
  v ^ (-(2 * β + 1))

/-- For every `β > 0` (including the critical window `β ∈ (1/2, 2]`), the physical `L^2`
envelope weight `v^{-(2 β + 1)}` is integrable on `(1, ∞)`. -/
theorem integrableOn_Ioi_one_physicalEnvelopeWeight {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (physicalEnvelopeWeight β) (Ioi (1 : ℝ)) := by
  unfold physicalEnvelopeWeight
  exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one

/-- Exact evaluation of the physical `L^2` envelope mass `∫_{1}^{∞} v^{-(2 β + 1)} dv = 1 / (2 β)`
for every `β > 0`. -/
theorem integral_Ioi_one_physicalEnvelopeWeight {β : ℝ} (hβ : 0 < β) :
    (∫ v in Ioi (1 : ℝ), physicalEnvelopeWeight β v) = 1 / (2 * β) := by
  unfold physicalEnvelopeWeight
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
  have hβ_ne : β ≠ 0 := hβ.ne'
  field_simp [hβ_ne]
  ring

/-- Unit-interval discrete `L^2` envelope weight `j^{-(2 β + 1)}`. -/
def unitIntervalPhysicalWeight (β : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) ^ (-(2 * β + 1))

/-- For every `β > 0`, the unit-interval discrete `L^2` envelope weight `j^{-(2 β + 1)}`
is summable. -/
theorem summable_unitIntervalPhysicalWeight {β : ℝ} (hβ : 0 < β) :
    Summable (unitIntervalPhysicalWeight β) := by
  unfold unitIntervalPhysicalWeight
  exact Real.summable_nat_rpow.mpr (by linarith)

/-- Unit-interval polar `s = 0` decay weight `j^{-(β + 1)}`. -/
def polarZeroExponentWeight (β : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) ^ (-(β + 1))

/-- Unit-interval polar `s = 1` uncancelled decay weight `j^{-β}`. -/
def polarOneExponentWeight (β : ℝ) (j : ℕ) : ℝ :=
  (j : ℝ) ^ (-β)

/-- **Exact Polar `s = 0` Summability Classification (`iff`).**
The `s = 0` unit-interval polar weight `j^{-(β + 1)}` is summable if and only if `0 < β`. -/
theorem summable_polarZeroExponentWeight_iff {β : ℝ} :
    Summable (polarZeroExponentWeight β) ↔ 0 < β := by
  unfold polarZeroExponentWeight
  rw [Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-- **Exact Polar `s = 1` Phase Transition (`iff`).**
The uncancelled `s = 1` unit-interval polar weight `j^{-β}` is summable if and only if `1 < β`. -/
theorem summable_polarOneExponentWeight_iff {β : ℝ} :
    Summable (polarOneExponentWeight β) ↔ 1 < β := by
  unfold polarOneExponentWeight
  rw [Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-- **Three-Regime Envelope Phase-Transition Theorem (`β ∈ (1/2, 2]` Window).**
For any envelope exponent `β`:
1. If `1 / 2 < β`, then the physical `L^2` weight `v^{-(2 β + 1)}` is integrable on `(1, ∞)`,
   the `s = 0` polar series `j^{-(β + 1)}` is summable, and both the logarithmic and von Mangoldt
   prime-dilation majorants `log r / r^{β + 1/2}` and `Λ(r) / r^{β + 1/2}` are summable.
2. In the sub-polar window `β ∈ (1/2, 1]`, the prime-dilation majorant is summable while the
   uncancelled `s = 1` polar series `j^{-β}` diverges (requiring rank-1 pole cancellation).
3. In the supercritical window `β ∈ (1, 2]`, both the prime-dilation majorant and the uncancelled
   `s = 1` polar series `j^{-β}` converge absolutely. -/
theorem envelope_three_regime_phase_transition (β : ℝ) :
    (1 / 2 < β →
      IntegrableOn (physicalEnvelopeWeight β) (Ioi (1 : ℝ)) ∧
      Summable (polarZeroExponentWeight β) ∧
      Summable (envelopeLogMajorant β) ∧
      Summable (envelopePrimeMajorant β)) ∧
    ((1 / 2 < β ∧ β ≤ 1) →
      Summable (envelopePrimeMajorant β) ∧ ¬ Summable (polarOneExponentWeight β)) ∧
    ((1 < β ∧ β ≤ 2) →
      Summable (envelopePrimeMajorant β) ∧ Summable (polarOneExponentWeight β)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hβ
    have hβ0 : 0 < β := by linarith
    exact ⟨integrableOn_Ioi_one_physicalEnvelopeWeight hβ0,
      summable_polarZeroExponentWeight_iff.mpr hβ0,
      summable_envelopeLogMajorant_of_half_lt hβ,
      summable_envelopePrimeMajorant_of_half_lt hβ⟩
  · rintro ⟨hβ1, hβ2⟩
    exact ⟨summable_envelopePrimeMajorant_of_half_lt hβ1,
      fun h => by linarith [summable_polarOneExponentWeight_iff.mp h]⟩
  · rintro ⟨hβ1, _⟩
    exact ⟨summable_envelopePrimeMajorant_of_half_lt (by linarith),
      summable_polarOneExponentWeight_iff.mpr hβ1⟩

/-- For every `β > 0`, the negative derivative `(2 β + 1) v^{-(2 β + 2)}` of the physical `L^2`
weight `v^{-(2 β + 1)}` integrates to `1` on `(1, ∞)`. -/
theorem integral_Ioi_one_weighted_amplitude_deriv {β : ℝ} (hβ : 0 < β) :
    (∫ v in Ioi (1 : ℝ), (2 * β + 1) * v ^ (-(2 * β + 2))) = 1 := by
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
    Real.one_rpow]
  have hne : -(2 * β + 2) + 1 ≠ 0 := by linarith
  field_simp [hne]
  ring

/-- **Weighted `[1, ∞)` Oscillatory Prime-Dilation Integration-by-Parts Bound.**
For any `β > 0` (including the critical exponent `β = 1/2`), any non-zero base frequency `ω ≠ 0`,
and any dilation factor `r > 1`, the physical `L^2`-weighted oscillatory correlation integral on
`(1, ∞)` is integrable and satisfies
`‖∫_{1}^{∞} v^{-(2 β + 1)} e^{i ω (1 - r) v} dv‖ ≤ 2 / (|ω| * (r - 1))`. -/
theorem weighted_oscillatory_dilation_integral_Ioi_bound
    {β ω r : ℝ} (hβ : 0 < β) (hω : ω ≠ 0) (hr : 1 < r) :
    IntegrableOn (fun v : ℝ =>
        ((physicalEnvelopeWeight β v : ℝ) : ℂ) *
          cexp (I * ((ω * (1 - r) * v : ℝ) : ℂ))) (Ioi (1 : ℝ)) ∧
      ‖∫ v in Ioi (1 : ℝ),
          ((physicalEnvelopeWeight β v : ℝ) : ℂ) *
            cexp (I * ((ω * (1 - r) * v : ℝ) : ℂ))‖ ≤
        2 / (|ω| * (r - 1)) := by
  set Δ : ℝ := ω * (1 - r) with hΔ
  have hr_sub : 0 < r - 1 := sub_pos.mpr hr
  have hω_pos : 0 < |ω| := abs_pos.mpr hω
  have hΔ_abs : |Δ| = |ω| * (r - 1) := by
    rw [hΔ, abs_mul, abs_of_neg (by linarith : 1 - r < 0)]
    ring
  have hΔ_pos : 0 < |Δ| := by rw [hΔ_abs]; positivity
  have hΔ_ne : Δ ≠ 0 := abs_pos.mp hΔ_pos
  set A : ℝ → ℂ := fun v => ((physicalEnvelopeWeight β v : ℝ) : ℂ) with hA
  set φ : ℝ → ℝ := fun v => Δ * v with hφ
  have hpos : ∀ v ∈ Ici (1 : ℝ), 0 < v := fun v hv => lt_of_lt_of_le one_pos hv
  have hAc : ContinuousOn A (Ici 1) := Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_id.rpow_const fun v hv => Or.inl (hpos v hv).ne')
  have hφc : ContinuousOn φ (Ici 1) := continuousOn_const.mul continuousOn_id
  have hFc : ContinuousOn (fun v => A v * cexp (I * (φ v : ℂ))) (Ici 1) :=
    hAc.mul (Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφc)))
  have hw : IntegrableOn (physicalEnvelopeWeight β) (Ioi 1) :=
    integrableOn_Ioi_one_physicalEnvelopeWeight hβ
  have hFi : IntegrableOn (fun v => A v * cexp (I * (φ v : ℂ))) (Ioi 1) := by
    refine hw.mono' ((hFc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, hA, Complex.norm_real]
    unfold physicalEnvelopeWeight
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _)]
  refine ⟨hFi, ?_⟩
  set m : ℝ → ℝ := fun v => (1 / |Δ|) * ((2 * β + 1) * v ^ (-(2 * β + 2))) with hm
  have hmi : IntegrableOn m (Ioi 1) :=
    ((integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul (2 * β + 1)).const_mul _
  have hm0 : ∀ v ∈ Ioi (1 : ℝ), 0 ≤ m v := fun v hv => by
    have hv0 : 0 < v := lt_trans one_pos hv
    have := Real.rpow_nonneg hv0.le (-(2 * β + 2))
    simp only [hm]
    positivity
  set Im : ℝ := ∫ v in Ioi (1 : ℝ), m v with hIm
  have hIm_eq : Im = 1 / |Δ| := by
    rw [hIm, hm, MeasureTheory.integral_const_mul,
      integral_Ioi_one_weighted_amplitude_deriv hβ, mul_one]
  have hfin : ∀ X : ℝ, 1 ≤ X →
      ‖∫ v in (1 : ℝ)..X, A v * cexp (I * (φ v : ℂ))‖ ≤
        (1 / |Δ|) * X ^ (-(2 * β + 1)) + 1 / |Δ| + Im := by
    intro X hX
    have hsub : uIcc (1 : ℝ) X ⊆ Ici 1 := by
      rw [uIcc_of_le hX]
      exact Icc_subset_Ici_self
    set B : ℝ → ℂ := fun v => (((v ^ (-(2 * β + 1)) / Δ) : ℝ) : ℂ) / I with hB
    set B' : ℝ → ℂ := fun v => (((-(2 * β + 1) * v ^ (-(2 * β + 2)) / Δ) : ℝ) : ℂ) / I with hB'
    have hφd : ∀ x ∈ uIcc (1 : ℝ) X, HasDerivAt φ Δ x := fun x _ => by
      simpa [hφ] using (hasDerivAt_id x).const_mul Δ
    have hBd : ∀ x ∈ uIcc (1 : ℝ) X, HasDerivAt B (B' x) x := fun x hx => by
      have hx0 : 0 < x := hpos x (hsub hx)
      have hrp := Real.hasDerivAt_rpow_const (p := -(2 * β + 1)) (x := x) (Or.inl hx0.ne')
      rw [show -(2 * β + 1) - 1 = -(2 * β + 2) by ring] at hrp
      exact ((hrp.div_const Δ).ofReal_comp).div_const I
    have hB'c : ContinuousOn B' (uIcc (1 : ℝ) X) := by
      refine ((Complex.continuous_ofReal.comp_continuousOn ?_).div_const I).mono hsub
      exact ((continuousOn_const.mul
        (continuousOn_id.rpow_const fun v hv => Or.inl (hpos v hv).ne')).div_const Δ)
    have hrel : ∀ x ∈ uIcc (1 : ℝ) X, B x * (I * (Δ : ℂ)) = A x := fun x _ => by
      simp only [hB, hA, physicalEnvelopeWeight]
      have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
      have hΔc : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ_ne
      push_cast
      field_simp [hI, hΔc]
    have hmain := RHTower.norm_integral_cexp_le_of_antiderivative hX hφd hBd hB'c
      (hAc.mono hsub) hrel
    have hBn (v : ℝ) (hv : 1 ≤ v) : ‖B v‖ = (1 / |Δ|) * v ^ (-(2 * β + 1)) := by
      have hv0 : 0 < v := lt_of_lt_of_le one_pos hv
      simp only [hB, norm_div, Complex.norm_I, div_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hv0.le _)]
      ring
    have hB'n : ∀ v ∈ Icc (1 : ℝ) X, ‖B' v‖ ≤ m v := fun v hv => by
      have hv0 : 0 < v := lt_of_lt_of_le one_pos hv.1
      have hpos_coeff : 0 ≤ (2 * β + 1) * v ^ (-(2 * β + 2)) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hv0.le _)
      simp only [hB', hm, norm_div, Complex.norm_I, div_one, Complex.norm_real, Real.norm_eq_abs]
      rw [show -(2 * β + 1) * v ^ (-(2 * β + 2)) = -((2 * β + 1) * v ^ (-(2 * β + 2))) by ring,
        abs_neg, abs_of_nonneg hpos_coeff]
      exact le_of_eq (by ring)
    have hint1 : (∫ v in (1 : ℝ)..X, ‖B' v‖) ≤ Im := by
      have hmon : (∫ v in (1 : ℝ)..X, ‖B' v‖) ≤ ∫ v in (1 : ℝ)..X, m v :=
        intervalIntegral.integral_mono_on hX (hB'c.norm.intervalIntegrable)
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr
            (hmi.mono_set Ioc_subset_Ioi_self)) hB'n
      refine hmon.trans ?_
      rw [intervalIntegral.integral_of_le hX]
      exact setIntegral_mono_set hmi (ae_restrict_of_forall_mem measurableSet_Ioi hm0)
        (Eventually.of_forall fun v hv => hv.1)
    have h1 : (1 : ℝ) ^ (-(2 * β + 1)) = 1 := Real.one_rpow _
    have hB1 := hBn 1 le_rfl
    rw [h1, mul_one] at hB1
    have hBX := hBn X hX
    linarith
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) (1 : ℝ) hFi tendsto_id
  have hrhs : Tendsto (fun X : ℝ => (1 / |Δ|) * X ^ (-(2 * β + 1)) + 1 / |Δ| + Im) atTop
      (𝓝 ((1 / |Δ|) * 0 + 1 / |Δ| + Im)) := by
    have h := tendsto_rpow_neg_atTop (show 0 < 2 * β + 1 by linarith)
    exact ((h.const_mul _).add_const _).add_const _
  have hle := le_of_tendsto_of_tendsto (hlim.norm) hrhs
    (Filter.eventually_atTop.mpr ⟨1, fun X hX => hfin X hX⟩)
  rw [mul_zero, zero_add, hIm_eq, hΔ_abs] at hle
  refine le_trans hle ?_
  ring_nf
  exact le_rfl

/-- Oscillatory logarithmic prime-envelope majorant `log r / (r^{β + 1/2} (r - 1))` for `r ≥ 2`,
incorporating the `1 / (r - 1)` oscillatory dilation gain from integration by parts. -/
def oscillatoryEnvelopeLogMajorant (β : ℝ) (r : ℕ) : ℝ :=
  envelopeLogMajorant β r / ((r : ℝ) - 1)

/-- Oscillatory von Mangoldt prime-envelope majorant `Λ(r) / (r^{β + 1/2} (r - 1))` for `r ≥ 2`,
incorporating the `1 / (r - 1)` oscillatory dilation gain from integration by parts. -/
def oscillatoryEnvelopePrimeMajorant (β : ℝ) (r : ℕ) : ℝ :=
  envelopePrimeMajorant β r / ((r : ℝ) - 1)

theorem oscillatoryEnvelopePrimeMajorant_nonneg (β : ℝ) (r : ℕ) :
    0 ≤ oscillatoryEnvelopePrimeMajorant β r := by
  unfold oscillatoryEnvelopePrimeMajorant envelopePrimeMajorant
  split_ifs with hr
  · have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    exact div_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg r) _))
      hr1.le
  · simp

theorem oscillatoryEnvelopeLogMajorant_nonneg (β : ℝ) (r : ℕ) :
    0 ≤ oscillatoryEnvelopeLogMajorant β r := by
  unfold oscillatoryEnvelopeLogMajorant
  by_cases hr : 2 ≤ r
  · have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    exact div_nonneg (envelopeLogMajorant_nonneg β r) (by linarith)
  · unfold envelopeLogMajorant
    simp [hr]

/-- Pointwise shift dominance: for every `β ∈ ℝ` and `r ∈ ℕ`, the `1 / (r - 1)` oscillatory
dilation factor shifts the envelope exponent by `+1`:
`oscillatoryEnvelopeLogMajorant β r ≤ 2 * envelopeLogMajorant (β + 1) r`. -/
theorem oscillatoryEnvelopeLogMajorant_le_two_mul_shift (β : ℝ) (r : ℕ) :
    oscillatoryEnvelopeLogMajorant β r ≤ 2 * envelopeLogMajorant (β + 1) r := by
  unfold oscillatoryEnvelopeLogMajorant envelopeLogMajorant
  split_ifs with hr
  · have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
    have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
    have hlog_nn : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by linarith)
    have hinv : 1 / ((r : ℝ) - 1) ≤ 2 / (r : ℝ) := by
      rw [div_le_div_iff₀ hr1_pos hr_pos]
      linarith
    have hrpow : (r : ℝ) ^ (β + 1 + 1 / 2) = (r : ℝ) ^ (β + 1 / 2) * (r : ℝ) := by
      rw [show β + 1 + 1 / 2 = (β + 1 / 2) + 1 by ring, Real.rpow_add_one hr_pos.ne']
    calc
      (Real.log (r : ℝ) / (r : ℝ) ^ (β + 1 / 2)) / ((r : ℝ) - 1) =
          (Real.log (r : ℝ) / (r : ℝ) ^ (β + 1 / 2)) * (1 / ((r : ℝ) - 1)) :=
        div_eq_mul_one_div _ _
      _ ≤ (Real.log (r : ℝ) / (r : ℝ) ^ (β + 1 / 2)) * (2 / (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv
          (div_nonneg hlog_nn (Real.rpow_nonneg hr_pos.le _))
      _ = 2 * (Real.log (r : ℝ) / ((r : ℝ) ^ (β + 1 / 2) * (r : ℝ))) := by ring
      _ = 2 * (Real.log (r : ℝ) / (r : ℝ) ^ (β + 1 + 1 / 2)) := by rw [hrpow]
  · simp

/-- **Oscillatory Prime-Dilation Summability Across the Critical Threshold (`β > -1/2`).**
For every `β > -1/2` — and in particular throughout the entire window `β ∈ [1/2, 2]` including
the critical exponent `β = 1/2` where the un-cancelled Cauchy–Schwarz majorant diverges —
both `oscillatoryEnvelopeLogMajorant β` and `oscillatoryEnvelopePrimeMajorant β` are
unconditionally summable. -/
theorem summable_oscillatoryEnvelopeMajorants_of_neg_half_lt {β : ℝ} (hβ : -1 / 2 < β) :
    Summable (oscillatoryEnvelopeLogMajorant β) ∧
      Summable (oscillatoryEnvelopePrimeMajorant β) := by
  have hshift : Summable (fun r : ℕ => 2 * envelopeLogMajorant (β + 1) r) :=
    (summable_envelopeLogMajorant_of_half_lt (by linarith : 1 / 2 < β + 1)).mul_left 2
  have hlog : Summable (oscillatoryEnvelopeLogMajorant β) :=
    Summable.of_nonneg_of_le (oscillatoryEnvelopeLogMajorant_nonneg β)
      (oscillatoryEnvelopeLogMajorant_le_two_mul_shift β) hshift
  refine ⟨hlog, Summable.of_nonneg_of_le (oscillatoryEnvelopePrimeMajorant_nonneg β) (fun r => ?_) hlog⟩
  unfold oscillatoryEnvelopePrimeMajorant oscillatoryEnvelopeLogMajorant
  by_cases hr : 2 ≤ r
  · have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    exact div_le_div_of_nonneg_right (envelopePrimeMajorant_le_logMajorant β r) (by linarith)
  · unfold envelopePrimeMajorant envelopeLogMajorant
    simp [hr]

/-- **Critical `β = 1/2` Contrast Theorem (Divergent Cauchy–Schwarz vs. Convergent Oscillatory
Prime-Dilation Series).** At the critical envelope exponent `β = 1/2`, the un-cancelled
Cauchy–Schwarz logarithmic majorant `envelopeLogMajorant (1/2)` diverges, whereas both the
oscillatory logarithmic majorant `oscillatoryEnvelopeLogMajorant (1/2)` and the oscillatory
von Mangoldt majorant `oscillatoryEnvelopePrimeMajorant (1/2)` converge unconditionally. -/
theorem critical_half_cauchy_schwarz_vs_oscillatory_summability :
    ¬ Summable (envelopeLogMajorant (1 / 2)) ∧
      Summable (oscillatoryEnvelopeLogMajorant (1 / 2)) ∧
      Summable (oscillatoryEnvelopePrimeMajorant (1 / 2)) :=
  ⟨not_summable_envelopeLogMajorant_of_le_half le_rfl,
    (summable_oscillatoryEnvelopeMajorants_of_neg_half_lt (by norm_num)).1,
    (summable_oscillatoryEnvelopeMajorants_of_neg_half_lt (by norm_num)).2⟩

end

end GaloisForLFunctions.ArithmeticPositivityTheory
