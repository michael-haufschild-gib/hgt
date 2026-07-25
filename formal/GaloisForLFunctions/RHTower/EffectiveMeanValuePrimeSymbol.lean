import GaloisForLFunctions.RHTower.SmoothCommaExclusionBand

/-!
# An effective mean-value theorem for the prime symbol

Cycle 14 showed that the Bohr-torus model becomes valid along the Kronecker line only beyond a
height threshold, and that the threshold is forced by a volume count.  This module supplies the
missing quantitative transfer in the opposite form: an **effective** mean-value estimate at finite
height, with the error controlled by the integrality separation of prime logarithms.

For a real trigonometric polynomial `Q(ξ) = Σ_j a_j cos(μ_j ξ)` with every frequency satisfying
`|μ_j| ≥ δ > 0`,

```text
| (1/T) ∫₀^T Q(ξ) dξ |  ≤  (Σ_j |a_j|) / (T δ),
```

because `∫₀^T cos(μξ)dξ = sin(μT)/μ` has modulus at most `1/|μ|`.  Applied to a power `P_N^{2k}` of
the prime symbol, the frequencies that appear are `log(A/B)` with `A, B` products of `2k` integers
at most `N`, hence `A, B ≤ N^{2k}`, and the separation bound of the previous modules — for distinct
positive integers `log A - log B ≥ 1/max(A,B)` — gives `δ ≥ N^{-2k}`.  The coefficient sum is at
most `‖P_N‖₁^{2k} = (2Σ_{n≤N} Λ(n)n^{-1/2})^{2k}`.  So

```text
| (1/T) ∫₀^T P_N^{2k} - E[P_N^{2k}] |  ≤  ( N^{2} ‖P_N‖₁^{2} )^{k} / T ,
```

with `E` the Bohr-torus expectation.  Combined with the exact torus moments — mean zero, variance
`Σ_p 2(log p)²/(p-1)`, uniform amplitude `4` per prime — this turns Chebyshev's inequality into a
completely explicit, unconditional bound on the measure of the set of heights at which the prime
symbol is large.

The mechanism is worth isolating: the error term is small precisely because two distinct products of
primes cannot have nearly equal logarithms, which is integrality again, exactly as in the exclusion
bands of the previous module.
-/

open Real intervalIntegral

noncomputable section

namespace RHTower

/-- `∫₀^T cos(μ ξ) dξ = sin(μT)/μ`. -/
theorem integral_cos_mul {μ T : ℝ} (hμ : μ ≠ 0) :
    (∫ x in (0 : ℝ)..T, Real.cos (μ * x)) = Real.sin (μ * T) / μ := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hμ]
  rw [integral_cos]
  simp [mul_zero, Real.sin_zero]
  ring

/-- The oscillatory integral is bounded by the reciprocal of the frequency. -/
theorem abs_integral_cos_mul_le {μ T : ℝ} (hμ : μ ≠ 0) :
    |∫ x in (0 : ℝ)..T, Real.cos (μ * x)| ≤ 1 / |μ| := by
  rw [integral_cos_mul hμ, abs_div]
  have h1 : |Real.sin (μ * T)| ≤ 1 := Real.abs_sin_le_one _
  have h2 : (0 : ℝ) < |μ| := abs_pos.mpr hμ
  exact div_le_div_of_nonneg_right h1 h2.le

/-- The same bound in terms of a uniform lower bound `δ` on the frequency. -/
theorem abs_integral_cos_mul_le_of_sep {μ T δ : ℝ} (hδ : 0 < δ) (hsep : δ ≤ |μ|) :
    |∫ x in (0 : ℝ)..T, Real.cos (μ * x)| ≤ 1 / δ := by
  have hμ : μ ≠ 0 := by
    intro h
    rw [h] at hsep
    simp at hsep
    linarith
  refine le_trans (abs_integral_cos_mul_le hμ) ?_
  exact one_div_le_one_div_of_le hδ hsep

/-- **Effective mean value for a trigonometric polynomial with separated frequencies.**  Every
frequency bounded away from zero by `δ` forces the average over `[0,T]` to be at most
`‖a‖₁/(Tδ)`. -/
theorem abs_integral_trigPoly_le {ι : Type*} (s : Finset ι) (a μ : ι → ℝ) (T δ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ i ∈ s, δ ≤ |μ i|) :
    |∑ i ∈ s, a i * ∫ x in (0 : ℝ)..T, Real.cos (μ i * x)| ≤ (∑ i ∈ s, |a i|) / δ := by
  calc |∑ i ∈ s, a i * ∫ x in (0 : ℝ)..T, Real.cos (μ i * x)|
      ≤ ∑ i ∈ s, |a i * ∫ x in (0 : ℝ)..T, Real.cos (μ i * x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |a i| * |∫ x in (0 : ℝ)..T, Real.cos (μ i * x)| := by
        exact Finset.sum_congr rfl fun i _ => abs_mul _ _
    _ ≤ ∑ i ∈ s, |a i| * (1 / δ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact mul_le_mul_of_nonneg_left
          (abs_integral_cos_mul_le_of_sep hδ (hsep i hi)) (abs_nonneg _)
    _ = (∑ i ∈ s, |a i|) / δ := by
        rw [← Finset.sum_mul]; ring

/-- **Integrality supplies the separation.**  Frequencies of a product of prime symbols are
`log A - log B` with `A ≠ B` positive integers bounded by `M`; the separation bound of
`LiouvillePointReachability` gives `|log A - log B| ≥ 1/M`. -/
theorem freq_sep_of_integers {A B M : ℝ} (hB : 0 < B) (hAB : B + 1 ≤ A) (hM : A ≤ M) :
    1 / M ≤ |Real.log A - Real.log B| := by
  have hA : (0 : ℝ) < A := by linarith
  have hstep : 1 / A ≤ Real.log A - Real.log B := log_sep_of_int_lt hB hAB
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le hA hM
  have hmono : 1 / M ≤ 1 / A := one_div_le_one_div_of_le hA hM
  exact le_trans (le_trans hmono hstep) (le_abs_self _)

/-- **Assembled effective mean value.**  With coefficient mass `S` and integrality separation
`1/M`, the average of the trigonometric part over `[0,T]` is at most `S·M/T`; the mean over the Bohr
torus is exactly the constant term, so this is the transfer error. -/
theorem transfer_error_bound {ι : Type*} (s : Finset ι) (a μ : ι → ℝ) (T M S : ℝ)
    (hM : 0 < M) (hT : 0 < T) (hsep : ∀ i ∈ s, 1 / M ≤ |μ i|)
    (hmass : ∑ i ∈ s, |a i| ≤ S) :
    |(1 / T) * ∑ i ∈ s, a i * ∫ x in (0 : ℝ)..T, Real.cos (μ i * x)| ≤ S * M / T := by
  have hδ : (0 : ℝ) < 1 / M := by positivity
  have hbase := abs_integral_trigPoly_le s a μ T (1 / M) hδ hsep
  have hstep : (∑ i ∈ s, |a i|) / (1 / M) ≤ S * M := by
    have hrw : (∑ i ∈ s, |a i|) / (1 / M) = (∑ i ∈ s, |a i|) * M := by field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hmass hM.le
  have hle : |∑ i ∈ s, a i * ∫ x in (0 : ℝ)..T, Real.cos (μ i * x)| ≤ S * M :=
    le_trans hbase hstep
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / T),
    show (1 : ℝ) / T * |∑ i ∈ s, a i * ∫ x in (0 : ℝ)..T, Real.cos (μ i * x)|
      = |∑ i ∈ s, a i * ∫ x in (0 : ℝ)..T, Real.cos (μ i * x)| / T from by ring,
    div_le_div_iff₀ hT hT]
  nlinarith [hle, hT]

end RHTower
