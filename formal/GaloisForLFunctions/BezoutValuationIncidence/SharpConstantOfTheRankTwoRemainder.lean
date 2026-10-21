import GaloisForLFunctions.BezoutValuationIncidence.TwistedShortIntervalCancellationGivesWindowDispersion

/-!
# The sharp constant of the rank-two remainder

The residue potential is largest at the residue zero: `Φ_d(M) ≤ Φ_d(0) = (d² - 1)/12`, and
`Φ_d(M) ≥ -(d² + 2)/24 ≥ -(d² - 1)/12` for `d ≥ 2`. Hence the Bernoulli kernel satisfies

`|𝔅(d, n)| ≤ 𝔅(d, 0) = ζ(2)(d² - 1)/12 = π²(d² - 1)/72`,

with equality exactly at `n ≡ 0 (mod d)`. With the second-order law this gives the sharp form of the
rank-two law. For all rows `c` on `[2, N]` and `c'`,

`|B + m R' + β H'| ≤ (π²/72) Σ_d |c(d)| (d² - 1)/d · Σ_n |c'(n)|/n² + ¾ Σ_d |c(d)| d² Σ_n |c'(n)|/n³`.

The constant is attained. If the large modulus `n₀` is divisible by every small modulus of a
nonnegative row `c`,

`B(c, δ_{n₀}) + m R(δ_{n₀}) + β H(δ_{n₀}) ≥ (π²/72) Σ_d c(d)(d² - 1)/(d n₀²) - ¾ Σ_d c(d) d²/n₀³`.

The rank-two remainder bound `(Σ|c|d)(Σ|c'|/n²)` therefore improves to the exact constant `π²/72`,
reached by large moduli that are common multiples of the small ones. Coherence at the residue zero
is the extremal configuration.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

theorem residuePotential_le_zero_value {d : ℕ} (hd : 0 < d) (M : ℕ) :
    residuePotential d M ≤ residuePotential d 0 := by
  unfold residuePotential
  simp only [Nat.zero_mod, Nat.cast_zero, zero_mul, zero_div, sub_zero]
  have h0 : (0 : ℝ) ≤ ((M % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlt : ((M % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt M hd).le
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr hlt)]

theorem abs_residuePotential_le_zero_value {d : ℕ} (hd : 2 ≤ d) (M : ℕ) :
    |residuePotential d M| ≤ ((d : ℝ) ^ 2 - 1) / 12 := by
  have hup := residuePotential_le_zero_value (d := d) (by omega) M
  have hlow := residuePotential_ge (d := d) M
  have h0 : residuePotential d 0 = ((d : ℝ) ^ 2 - 1) / 12 := by simp [residuePotential]
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [abs_le]
  constructor <;> nlinarith

/-- `𝔅(d, 0) = π²(d² - 1)/72`. -/
theorem bernoulliKernel_zero {d : ℕ} (hd : 0 < d) :
    bernoulliKernel d 0 = Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 := by
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have h := (hasSum_bernoulliKernel hd 0).unique
    ((hz.mul_left (((d : ℝ) ^ 2 - 1) / 12)).congr_fun fun j => by
      simp only [mul_zero, residuePotential, Nat.zero_mod, Nat.cast_zero, zero_mul, zero_div,
        sub_zero]
      ring)
  rw [h]; ring

/-- **The sharp kernel bound.** `|𝔅(d, n)| ≤ π²(d² - 1)/72` for `d ≥ 2`. -/
theorem abs_bernoulliKernel_le_sharp {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    |bernoulliKernel d n| ≤ Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 := by
  have hd0 : 0 < d := by omega
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hS := summable_residuePotential_div_sq hd0 n
  rw [← Real.norm_eq_abs, bernoulliKernel]
  refine (norm_tsum_le_tsum_norm hS.norm).trans ?_
  rw [show Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 = ∑' j : ℕ, ((d : ℝ) ^ 2 - 1) / 12 *
      (1 / ((j : ℝ) + 1) ^ 2) by rw [(hz.mul_left _).tsum_eq]; ring]
  refine Summable.tsum_le_tsum (fun j => ?_) hS.norm (hz.mul_left _).summable
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2),
    div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_right (abs_residuePotential_le_zero_value hd _) (by positivity)

/-- **The sharp rank-two law.** For rows `c` on `[2, N]` and every `c'`,
`|B + m R' + β H'| ≤ (π²/72) Σ_d |c(d)|(d² - 1)/d · Σ_n |c'(n)|/n² + ¾ Σ_d |c(d)| d² Σ_n |c'(n)|/n³`. -/
theorem abs_rowBilinear_add_mean_add_beta_le_sharp (N : ℕ) {c : ℕ → ℝ} (hc1 : c 1 = 0)
    (c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'| ≤
      Real.pi ^ 2 / 72 * (∑ d ∈ Icc 1 N, |c d| * ((d : ℝ) ^ 2 - 1) / d) *
          ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 +
        3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'
  set M := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)
  have hM : |M| ≤ Real.pi ^ 2 / 72 * (∑ d ∈ Icc 1 N, |c d| * ((d : ℝ) ^ 2 - 1) / d) *
      ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := by
    have hrhs : Real.pi ^ 2 / 72 * (∑ d ∈ Icc 1 N, |c d| * ((d : ℝ) ^ 2 - 1) / d) *
        ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
          Real.pi ^ 2 / 72 * (|c d| * ((d : ℝ) ^ 2 - 1) / d * (|c' n| / (n : ℝ) ^ 2)) := by
      rw [mul_assoc, sum_mul_sum, mul_sum, sum_comm]
      refine sum_congr rfl fun n _ => ?_
      rw [mul_sum]
    rw [hrhs]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hd1 := (mem_Icc.mp hd).1
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · have : d = 1 := by omega
      subst this
      simp [hc1]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
    have hk := abs_bernoulliKernel_le_sharp hd2 n
    rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos hdR, abs_of_pos (by positivity :
      (0 : ℝ) < (n : ℝ) ^ 2)]
    calc |c' n| * (|c d| / d) * (|bernoulliKernel d n| / (n : ℝ) ^ 2)
        ≤ |c' n| * (|c d| / d) * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 / (n : ℝ) ^ 2) := by
          gcongr
      _ = Real.pi ^ 2 / 72 * (|c d| * ((d : ℝ) ^ 2 - 1) / d * (|c' n| / (n : ℝ) ^ 2)) := by
          field_simp
  have := abs_sub_abs_le_abs_sub (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c') M
  linarith

/-- **The constant is attained.** If every modulus of a nonnegative row `c` on `[1, N]` divides
`n₀ ≤ N`, then
`B(c, δ_{n₀}) + m R(δ_{n₀}) + β H(δ_{n₀}) ≥ (π²/72) Σ_d c(d)(d² - 1)/(d n₀²) - ¾ Σ_d c(d) d²/n₀³`. -/
theorem rowBilinear_unitRow_ge_of_dvd {N n₀ : ℕ} (hn₀ : n₀ ∈ Icc 1 N) {c : ℕ → ℝ}
    (hc0 : ∀ d, 0 ≤ c d) (hdvd : ∀ d ∈ Icc 1 N, c d ≠ 0 → d ∣ n₀) :
    Real.pi ^ 2 / 72 * (∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / d) / (n₀ : ℝ) ^ 2 -
        3 / 4 * (∑ d ∈ Icc 1 N, c d * (d : ℝ) ^ 2) / (n₀ : ℝ) ^ 3 ≤
      rowBilinear N c (unitRow n₀) + rowMean N c * vonMangoldtReadout N (unitRow n₀) +
        rowBeta N c * finiteHarmonicSum N (unitRow n₀) := by
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c (unitRow n₀)
  have hn0 : (0 : ℝ) < n₀ := by exact_mod_cast (mem_Icc.mp hn₀).1
  have hM : ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, unitRow n₀ n * (c d / d) *
      (bernoulliKernel d n / (n : ℝ) ^ 2) =
      Real.pi ^ 2 / 72 * (∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / d) / (n₀ : ℝ) ^ 2 := by
    rw [sum_eq_single n₀ (fun n _ hn => by simp [unitRow, hn]) (fun h => absurd hn₀ h)]
    simp only [unitRow, if_true, one_mul]
    rw [mul_sum, sum_div]
    refine sum_congr rfl fun d hd => ?_
    by_cases hcd : c d = 0
    · simp [hcd]
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [bernoulliKernel_mod, Nat.eq_zero_of_dvd_of_lt (hdvd d hd hcd) |> fun _ =>
      Nat.mod_eq_zero_of_dvd (hdvd d hd hcd), bernoulliKernel_zero hd0]
    field_simp
  have hL : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 = ∑ d ∈ Icc 1 N, c d * (d : ℝ) ^ 2 :=
    sum_congr rfl fun d _ => by rw [abs_of_nonneg (hc0 d)]
  have hR : ∑ n ∈ Icc 1 N, |unitRow n₀ n| / (n : ℝ) ^ 3 = 1 / (n₀ : ℝ) ^ 3 := by
    rw [sum_eq_single n₀ (fun n _ hn => by simp [unitRow, hn]) (fun h => absurd hn₀ h)]
    simp [unitRow]
  rw [hM, hL, hR] at hlaw
  have := (abs_le.mp hlaw).1
  have heq : 3 / 4 * (∑ d ∈ Icc 1 N, c d * (d : ℝ) ^ 2) * (1 / (n₀ : ℝ) ^ 3) =
      3 / 4 * (∑ d ∈ Icc 1 N, c d * (d : ℝ) ^ 2) / (n₀ : ℝ) ^ 3 := by ring
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
