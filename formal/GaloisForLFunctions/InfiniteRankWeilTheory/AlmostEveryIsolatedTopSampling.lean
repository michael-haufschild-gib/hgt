import GaloisForLFunctions.InfiniteRankWeilTheory.AlmostEveryOscillatorySampling
import GaloisForLFunctions.InfiniteRankWeilTheory.IsolatedTopExcursionDensity
import GaloisForLFunctions.InfiniteRankWeilTheory.TheExceptionalCoordinate

/-!
# Almost every base detects an isolated top at every large level

The finite top is a growing scalar times an oscillatory sum. Outside a null set of bases, the
latter eventually exceeds every decaying exponential. Absolute summability bounds the whole
lower layer by a smaller exponential, which cannot cancel the top at arbitrarily large levels.
-/

open Complex Filter Topology MeasureTheory Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- Two smaller exponential rates are eventually dominated by any larger positive rate. -/
theorem eventually_two_powers_lt {r s Q : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hQ : 0 < Q) (hrQ : r < Q) (hsQ : s < Q) (W C : ℝ) :
    ∀ᶠ n : ℕ in atTop, W * r ^ n + C * s ^ n < Q ^ n := by
  have hlim : Tendsto (fun n : ℕ => W * (r / Q) ^ n + C * (s / Q) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr hQ.le)
        ((div_lt_one hQ).mpr hrQ)).const_mul W).add
        ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hs hQ.le)
          ((div_lt_one hQ).mpr hsQ)).const_mul C)
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  have hmul := mul_lt_mul_of_pos_right hn (pow_pos hQ n)
  have heq : (W * (r / Q) ^ n + C * (s / Q) ^ n) * Q ^ n = W * r ^ n + C * s ^ n := by
    rw [div_pow, div_pow]
    field_simp
  simpa only [heq, one_mul] using hmul

/-- The top part of an exponential trace splits into its common growth factor and a finite
oscillatory sum at the actual ordinates. -/
theorem top_sum_eq_growth_mul_trigSum {ι : Type*} (ρ b : ι → ℂ) (F : Finset ι)
    {Θ : ℝ} (hF : ∀ i ∈ F, (ρ i).re = Θ) (ℓ : ℝ) (n : ℕ) :
    (∑ i ∈ F, b i * frobTower ℓ ρ i ^ n) =
      (Real.exp ((Θ - 1 / 2) * ((n : ℝ) * ℓ)) : ℂ) *
        TrigSum.trigSum F b (fun i => (ρ i).im) ((n : ℝ) * ℓ) := by
  unfold TrigSum.trigSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [frobTower_pow]
  have hsplit : (((n : ℝ) * ℓ : ℝ) : ℂ) * (ρ i - 1 / 2) =
      (((Θ - 1 / 2) * ((n : ℝ) * ℓ) : ℝ) : ℂ) +
        I * ((ρ i).im * ((n : ℝ) * ℓ)) := by
    conv_lhs => rw [← Complex.re_add_im (ρ i)]
    rw [hF i hi]
    push_cast
    ring
  rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]
  simp only [Complex.ofReal_mul]
  ring

/-- Almost every positive base detects a finite visible isolated top at every sufficiently
large level, simultaneously for every exponent below the top and every constant. -/
theorem ae_eventually_isolatedTop_exp_lower {ι : Type*} (ρ b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) (F : Finset ι) {Θ Θ₂ : ℝ}
    (hgap : Θ₂ < Θ) (hF : ∀ i ∈ F, (ρ i).re = Θ)
    (hrest : ∀ i ∉ F, (ρ i).re ≤ Θ₂)
    (hvis : ∃ j ∈ F, (∑ i ∈ F with (ρ i).im = (ρ j).im, b i) ≠ 0) :
    ∀ᵐ ℓ ∂volume, 0 < ℓ → ∀ a : ℝ, a < Θ - 1 / 2 → ∀ C : ℝ,
      ∀ᶠ n : ℕ in atTop,
        C * Real.exp (a * (n : ℝ) * ℓ) < ‖levelSum (frobTower ℓ ρ) b n‖ := by
  filter_upwards [ae_eventually_finset_oscillatory_exp_lower F (fun i => (ρ i).im) b hvis]
    with ℓ hℓ
  intro hℓpos a ha C
  let δ : ℝ := min (Θ - 1 / 2 - a) (Θ - Θ₂) / 2
  have hmin : 0 < min (Θ - 1 / 2 - a) (Θ - Θ₂) :=
    lt_min (sub_pos.mpr ha) (sub_pos.mpr hgap)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδmin : δ < min (Θ - 1 / 2 - a) (Θ - Θ₂) := by dsimp [δ]; linarith only [hmin]
  have hδa := hδmin.trans_le (min_le_left (Θ - 1 / 2 - a) (Θ - Θ₂))
  have hδgap := hδmin.trans_le (min_le_right (Θ - 1 / 2 - a) (Θ - Θ₂))
  let Q : ℝ := Real.exp (ℓ * (Θ - 1 / 2 - δ))
  let r : ℝ := Real.exp (ℓ * (Θ₂ - 1 / 2))
  let s : ℝ := Real.exp (a * ℓ)
  have hQ : 0 < Q := Real.exp_pos _
  have hrQ : r < Q := Real.exp_lt_exp.mpr
    (mul_lt_mul_of_pos_left (by linarith only [hδgap]) hℓpos)
  have hsQ : s < Q := Real.exp_lt_exp.mpr (by
    have h := mul_lt_mul_of_pos_left (show a < Θ - 1 / 2 - δ by linarith only [hδa]) hℓpos
    simpa only [mul_comm] using h)
  obtain ⟨htop, hlow, _⟩ := frobTower_isolatedTop hℓpos hgap hF hrest
  filter_upwards [hℓ hℓpos δ hδ,
    eventually_two_powers_lt (Real.exp_pos _).le (Real.exp_pos _).le hQ hrQ hsQ
      (∑' i, ‖b i‖) C] with n hn hsmall
  have htoplow : Q ^ n < ‖∑ i ∈ F, b i * frobTower ℓ ρ i ^ n‖ := by
    rw [top_sum_eq_growth_mul_trigSum ρ b F hF, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Q ^ n = Real.exp ((Θ - 1 / 2) * ((n : ℝ) * ℓ)) *
          Real.exp (-δ * ((n : ℝ) * ℓ)) := by
            dsimp [Q]
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            ring
      _ < _ := mul_lt_mul_of_pos_left hn (Real.exp_pos _)
  have hbound := norm_top_le_norm_levelSum_add (frobTower ℓ ρ) b hb F hlow
    (fun i hi => (htop i hi).le) (Real.exp_pos _).le n
  have hfinal : C * s ^ n < ‖levelSum (frobTower ℓ ρ) b n‖ := by
    change Q ^ n < ‖∑ i ∈ F, b i * frobTower ℓ ρ i ^ n‖ at htoplow
    change ‖∑ i ∈ F, b i * frobTower ℓ ρ i ^ n‖ ≤
      ‖levelSum (frobTower ℓ ρ) b n‖ + (∑' i, ‖b i‖) * r ^ n at hbound
    linarith only [htoplow, hbound, hsmall]
  simpa only [s, ← Real.exp_nat_mul, show (n : ℝ) * (a * ℓ) = a * n * ℓ by ring]
    using hfinal

#print axioms ae_eventually_isolatedTop_exp_lower

end GaloisForLFunctions.InfiniteRankWeilTheory
