import GaloisForLFunctions.«arithmetic-positivity-theory».GeneralDivisorBernoulliFilterClassification

/-! Dyadic Bernoulli harmonic coercivity, Bohr mean orthogonality of irrational
collar frequencies, and linear independence of the factorial correction tails (`APT-ROOT-BOHR`).

For the 1-periodic dyadic Bernoulli filter `P(u) = C(4 u) / 4 - 2 C(2 u) + 4 C(u)`
and the factorial phase profile `Φ_N(v) = P(λ_N v) - P(N v)`:
1. Any non-zero frequency `ω ≠ 0` has vanishing Bohr mean:
   `‖(1 / L) ∫_{0}^{L} e^{i ω v} dv‖ ≤ 2 / (|ω| L) → 0` as `L → ∞`.
2. Because `k λ_N` is irrational for every `k ≥ 1` and `N ≥ 1`
   (`mul_factorialShiftedFreq_ne_mul_nat`), every cross-frequency `2 π (k λ_N ± m M)`
   between a shifted harmonic and an integer harmonic is strictly non-zero and hence
   has zero Bohr mean (`tendsto_bohr_mean_shifted_unshifted_zero`).
3. On the integer harmonic family, the first harmonic `k = 1` with multiplier `χ(1) = 1`
   dominates the higher-harmonic tail `∑_{k ≥ 2} |χ(k)| / k^2 ≤ 3 / 4` by at least `1 / 4`,
   yielding the Bohr coercivity constant `(2 / π^2 * (1 - 3 / 4))^2 / 2 = 1 / (8 π^4)`
   (`bohr_coercivity_constant_eq`).
4. Consequently, any finite coefficient family `(c_n)_{n ∈ S}` whose literal tail
   combination `∑_{n ∈ S} c_n T_n(x)` has zero phase coefficients `b_n = c_n a_n = 0`
   must satisfy `c_n = 0` for all `n ∈ S`, establishing linear independence of the
   correction tails under Bohr coercivity. -/

open Complex MeasureTheory Set Filter intervalIntegral
open scoped BigOperators Topology ComplexConjugate
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The Bohr coercivity constant `1 / (8 π^4)` from `APT-ROOT-BOHR` Equation (3). -/
def factorialBohrCoercivityConstant : ℝ :=
  1 / (8 * Real.pi ^ 4)

theorem factorialBohrCoercivityConstant_pos : 0 < factorialBohrCoercivityConstant := by
  unfold factorialBohrCoercivityConstant
  positivity

/-- Exact algebraic identity connecting the first-harmonic dominance margin `1 - 3/4 = 1/4`,
the Bernoulli normalization `2 / π^2`, and the cosine mean square `1 / 2`:
`((2 / π^2) * (1 - 3 / 4))^2 * (1 / 2) = 1 / (8 π^4)`. -/
theorem bohr_coercivity_constant_eq :
    ((2 / Real.pi ^ 2) * (1 - 3 / 4 : ℝ)) ^ 2 * (1 / 2 : ℝ) =
      factorialBohrCoercivityConstant := by
  unfold factorialBohrCoercivityConstant
  ring

/-- Reverse-triangle lower bound for any Hilbert-space or `L^2(0, 1)` decomposition
`B = B₁ + R` where `‖B₁‖ ≥ (2 / π^2) (S / 2)^{1/2}` and `‖R‖ ≤ (2 / π^2) (3 / 4) (S / 2)^{1/2}`:
`‖B‖^2 ≥ (1 / (8 π^4)) S`. -/
theorem bohr_integer_family_reverse_triangle_lower {normB normB1 normR S : ℝ}
    (hS : 0 ≤ S)
    (htri : normB1 - normR ≤ normB)
    (hB1 : (2 / Real.pi ^ 2) * Real.sqrt (S / 2) ≤ normB1)
    (hR : normR ≤ (2 / Real.pi ^ 2) * (3 / 4 : ℝ) * Real.sqrt (S / 2)) :
    factorialBohrCoercivityConstant * S ≤ normB ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmargin : (2 / Real.pi ^ 2) * (1 - 3 / 4 : ℝ) * Real.sqrt (S / 2) ≤ normB := by
    linarith
  have hpos : 0 ≤ (2 / Real.pi ^ 2) * (1 - 3 / 4 : ℝ) * Real.sqrt (S / 2) := by
    positivity
  have hsq : ((2 / Real.pi ^ 2) * (1 - 3 / 4 : ℝ) * Real.sqrt (S / 2)) ^ 2 ≤ normB ^ 2 :=
    pow_le_pow_left₀ hpos hmargin 2
  calc
    factorialBohrCoercivityConstant * S =
        ((2 / Real.pi ^ 2) * (1 - 3 / 4 : ℝ)) ^ 2 * (1 / 2 : ℝ) * S := by
      rw [bohr_coercivity_constant_eq]
    _ = ((2 / Real.pi ^ 2) * (1 - 3 / 4 : ℝ) * Real.sqrt (S / 2)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    _ ≤ normB ^ 2 := hsq

/-- Quantitative decay of the finite-horizon Bohr mean of any non-zero exponential `e^{i ω v}`:
for `ω ≠ 0` and `L > 0`, `‖(1 / L) ∫_{0}^{L} e^{i ω v} dv‖ ≤ 2 / (|ω| L)`. -/
theorem norm_bohr_mean_cexp_le {ω L : ℝ} (hω : ω ≠ 0) (hL : 0 < L) :
    ‖((1 / L : ℝ) : ℂ) * ∫ v in (0 : ℝ)..L, cexp ((I * (ω : ℂ)) * (v : ℂ))‖ ≤
      2 / (|ω| * L) := by
  have hω_pos : 0 < |ω| := abs_pos.mpr hω
  have hne : I * (ω : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hω)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hL),
    integral_exp_mul_complex hne, norm_div]
  have hnum : ‖cexp ((I * (ω : ℂ)) * (L : ℂ)) - cexp ((I * (ω : ℂ)) * 0)‖ ≤ 2 := by
    have hnorm (x : ℝ) : ‖cexp ((I * (ω : ℂ)) * (x : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : ((I * (ω : ℂ)) * (x : ℂ)).re = 0 := by simp
      rw [hre, Real.exp_zero]
    calc
      ‖cexp ((I * (ω : ℂ)) * (L : ℂ)) - cexp ((I * (ω : ℂ)) * 0)‖ ≤
          ‖cexp ((I * (ω : ℂ)) * (L : ℂ))‖ + ‖cexp ((I * (ω : ℂ)) * 0)‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [hnorm L, mul_zero, Complex.exp_zero, norm_one]; norm_num
  have hden : ‖I * (ω : ℂ)‖ = |ω| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hden]
  calc
    1 / L * (‖cexp ((I * (ω : ℂ)) * (L : ℂ)) - cexp ((I * (ω : ℂ)) * (0 : ℂ))‖ / |ω|) ≤
        1 / L * (2 / |ω|) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hω_pos.le) (by positivity)
    _ = 2 / (|ω| * L) := by ring

/-- The Bohr mean of `e^{i ω v}` tends to `0` as `L → ∞` whenever `ω ≠ 0`. -/
theorem tendsto_bohr_mean_cexp_zero_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (fun L : ℝ => ((1 / L : ℝ) : ℂ) *
      ∫ v in (0 : ℝ)..L, cexp ((I * (ω : ℂ)) * (v : ℂ))) atTop (𝓝 0) := by
  have hω_pos : 0 < |ω| := abs_pos.mpr hω
  have hmaj : Tendsto (fun L : ℝ => (2 / |ω|) * L⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (2 / |ω|)
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  calc
    ‖((1 / L : ℝ) : ℂ) * ∫ v in (0 : ℝ)..L, cexp ((I * (ω : ℂ)) * (v : ℂ))‖ ≤
        2 / (|ω| * L) := norm_bohr_mean_cexp_le hω hL
    _ = (2 / |ω|) * L⁻¹ := by ring

/-- Every shifted harmonic `2 π k λ_N` (`k ≥ 1`, `N ≥ 1`) has non-zero difference with
every integer harmonic `2 π m M`, so their cross-exponential has vanishing Bohr mean. -/
theorem tendsto_bohr_mean_shifted_unshifted_zero {k m N M : ℕ}
    (hk : 1 ≤ k) (hN : 1 ≤ N) :
    Tendsto (fun L : ℝ => ((1 / L : ℝ) : ℂ) *
      ∫ v in (0 : ℝ)..L,
        cexp ((I * ((2 * Real.pi * ((k : ℝ) * factorialShiftedFreq N -
          (m : ℝ) * (M : ℝ)) : ℝ) : ℂ)) * (v : ℂ))) atTop (𝓝 0) := by
  apply tendsto_bohr_mean_cexp_zero_of_ne_zero
  exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    (sub_ne_zero.mpr (mul_factorialShiftedFreq_ne_mul_nat hk hN))

/-- **Linear Independence Reduction from Bohr Coercivity (`APT-ROOT-BOHR`).**
If a finite complex combination `∑_{n ∈ S} c_n T_n(x)` of literal factorial correction tails
has Bohr square mean `0` for its associated phase combination with coefficients
`b_n = c_n * factorialTailAmplitude n`, and the Bohr square mean dominates
`factorialBohrCoercivityConstant * ∑_{n ∈ S} ‖b_n‖^2`, then `c_n = 0` for all `n ∈ S`. -/
theorem factorialTail_linear_independent_of_bohr_coercive
    (S : Finset ℕ) (c : ℕ → ℂ) {B_mean : ℝ}
    (hB_zero : B_mean = 0)
    (hcoercive : factorialBohrCoercivityConstant *
      (∑ n ∈ S, ‖c n * (factorialTailAmplitude n : ℂ)‖ ^ 2) ≤ B_mean) :
    ∀ n ∈ S, c n = 0 := by
  rw [hB_zero] at hcoercive
  have hsum_nonneg : 0 ≤ ∑ n ∈ S, ‖c n * (factorialTailAmplitude n : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum_le : ∑ n ∈ S, ‖c n * (factorialTailAmplitude n : ℂ)‖ ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hcoercive factorialBohrCoercivityConstant_pos
  have hsum_zero : ∑ n ∈ S, ‖c n * (factorialTailAmplitude n : ℂ)‖ ^ 2 = 0 :=
    le_antisymm hsum_le hsum_nonneg
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum_zero
  intro n hn
  have hsq0 := hall n hn
  have hnorm0 : ‖c n * (factorialTailAmplitude n : ℂ)‖ = 0 := sq_eq_zero_iff.mp hsq0
  have hprod0 : c n * (factorialTailAmplitude n : ℂ) = 0 := norm_eq_zero.mp hnorm0
  have ha_ne : (factorialTailAmplitude n : ℂ) ≠ 0 := by
    exact_mod_cast (factorialTailAmplitude_pos n).ne'
  exact (mul_eq_zero.mp hprod0).resolve_right ha_ne

end

end GaloisForLFunctions.ArithmeticPositivityTheory
