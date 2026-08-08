import GaloisForLFunctions.RHTower.Sieve.TruncatedPrimeSieveMeanSquare
import GaloisForLFunctions.RHTower.Sieve.TruncatedVerticalSplit
import GaloisForLFunctions.RHTower.Sieve.LSeriesTrivialSize
import GaloisForLFunctions.RHTower.Sieve.GhsStepFour
/-!
# Step 4 on a truncated height range

The same assembly as the global step 4, with the vertical integral split at height `T`:

`2π‖∑ₙ (a ⍟ (b ⍟ f))(n)w(n)‖ ≤ E·((N+H)^σ/σ)·√(trunc a)·√(trunc b) + (ℓ¹a)(ℓ¹b)·E·C·(π − 2 arctan T)`,

`E = (1 + 1/(σ−1))e^{7/2}` the Euler bound, `trunc` the truncated Selberg majorant at neighbour scale `1/T`,
and `ℓ¹` the mass of the damped coefficients.

The point of the truncation is which constant multiplies the mean squares.  Here it is `(N+H)^σ/σ`, the
*uniform* size of the smoothed Perron kernel — of order `N` for `H ≤ N` — whereas the global route multiplies
them by the quadratic-decay constant `C ≍ N^σ(N/H)²`, which no choice of `H` can reconcile with the smoothing
error.  In this form `C` appears only against `π − 2 arctan T`, which decays like `1/T`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Finset

/-- The `ℓ¹` mass of the damped coefficients on the line `Re s = σ`. -/
def dampedL1 (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) : ℝ := ∑ n ∈ s, ‖a n‖ * (n : ℝ) ^ (-σ)

/-- The truncated Selberg majorant of a prime weight's mean square at truncation height `T`. -/
def truncSieveSum (a : ℕ → ℂ) (s : Finset ℕ) (σ T : ℝ) (z Y : ℕ) : ℝ :=
  2 * Real.pi * ((5 * T / 4) * ∑ n ∈ s,
    (2 * ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) + 1) / Real.log Y
      + selbergFibreError z Y + (z : ℝ)) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2)

/-- **Step 4 on a truncated height range.**  The smoothed sum of the Granville–Harper–Soundararajan
convolution, estimated by Cauchy–Schwarz against the *uniform* kernel bound below height `T` and by the
kernel's decay above it:

`2π‖∑ₙ (a ⍟ (b ⍟ f))(n)w(n)‖ ≤ E·((N+H)^σ/σ)·√(trunc a)·√(trunc b) + (ℓ¹a)(ℓ¹b)E·C·(π − 2 arctan T)`,

`E = (1 + 1/(σ−1))e^{7/2}` the Euler bound.  The quadratic-decay constant `C` appears only in the tail. -/
theorem norm_tsum_ghs_smoothWeight_le_truncated_of_kernelBound {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    (N₀ : ℕ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ) {T : ℝ} (hT : 0 < T)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hCb : ∀ y : ℝ, ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((σ : ℂ) + (y : ℝ) * I)‖ ≤ C * (1 + y ^ 2)⁻¹) :
      (2 * Real.pi) * ‖∑' n : ℕ,
            (LSeries.convolution (ghsOuter f N₀) (LSeries.convolution (ghsInner f N₀) f)) n
              * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
        ≤ ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * ((N + H) ^ σ / σ)
              * (Real.sqrt (truncSieveSum (ghsOuter f N₀) (Finset.Icc 1 N₀) σ T z Y)
                  * Real.sqrt (truncSieveSum (ghsInner f N₀) (Finset.Icc 1 N₀) σ T z Y))
          + (dampedL1 (ghsOuter f N₀) (Finset.Icc 1 N₀) σ
                * dampedL1 (ghsInner f N₀) (Finset.Icc 1 N₀) σ
                * ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)))
              * C * (Real.pi - 2 * Real.arctan T) := by
  classical
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hE0 : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by
    have h1 : 0 < σ - 1 := by linarith
    positivity
  have hWsup0 : (0 : ℝ) ≤ (N + H) ^ σ / σ := by positivity
  set a : ℕ → ℂ := ghsOuter f N₀ with ha
  set b : ℕ → ℂ := ghsInner f N₀ with hb
  set s : Finset ℕ := Finset.Icc 1 N₀ with hs
  have hs0 : (0 : ℕ) ∉ s := by rw [hs]; simp
  have hsuppa : ∀ n : ℕ, a n ≠ 0 → n ∈ s := fun n hn => ghsOuter_mem_Icc hn
  have hsuppb : ∀ n : ℕ, b n ≠ 0 → n ∈ s := fun n hn => ghsInner_mem_Icc hn
  have hprimea : ∀ n ∈ s, a n ≠ 0 → n.Prime := fun n _ hn => ghsOuter_support hn
  have hprimeb : ∀ n ∈ s, b n ≠ 0 → n.Prime := fun n _ hn => ghsInner_support hn
  -- the three factors and the kernel
  set W : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
      ((σ : ℂ) + (y : ℝ) * I) with hW
  have hcont1 : Continuous fun y : ℝ => LSeries a ((σ : ℂ) + (y : ℝ) * I) :=
    continuous_LSeries_line_of_support hs0 hsuppa σ
  have hcont2 : Continuous fun y : ℝ => LSeries b ((σ : ℂ) + (y : ℝ) * I) :=
    continuous_LSeries_line_of_support hs0 hsuppb σ
  have hcont3 : Continuous fun y : ℝ => LSeries f ((σ : ℂ) + (y : ℝ) * I) :=
    continuous_LSeries_line_of_bounded hbdd hσ
  have hWint : Integrable W :=
    GaloisForLFunctions.HTGeometry.verticalIntegrable_mellin_smoothWeight (σ := σ) hN hH hσ0
  -- the Perron identity
  have hperron := tsum_mul_smoothWeight_ghs_eq_integral hbdd N₀ N₀ hN hH hσ
  have hnorm : (2 * Real.pi) * ‖∑' n : ℕ,
      (LSeries.convolution a (LSeries.convolution b f)) n
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
      = ‖∫ y : ℝ, (LSeries a ((σ : ℂ) + (y : ℝ) * I) * LSeries b ((σ : ℂ) + (y : ℝ) * I)
            * LSeries f ((σ : ℂ) + (y : ℝ) * I)) * W y‖ := by
    rw [hW, ← hperron, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [hnorm]
  -- the trivial sizes
  have hMg : ∀ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I) * LSeries b ((σ : ℂ) + (y : ℝ) * I)
      * LSeries f ((σ : ℂ) + (y : ℝ) * I)‖
      ≤ dampedL1 a s σ * dampedL1 b s σ * ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) := by
    intro y
    rw [dampedL1, dampedL1]
    exact norm_LSeries_mul_three_le hs0 hsuppa hs0 hsuppb
      (fun y' => norm_LSeries_line_le_trivial hf1 hmul hbdd hσ y') y
  have hMg0 : (0 : ℝ) ≤ dampedL1 a s σ * dampedL1 b s σ
      * ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) := by
    rw [dampedL1, dampedL1]
    exact mul_nonneg (mul_nonneg (sum_norm_mul_rpow_nonneg a s σ)
      (sum_norm_mul_rpow_nonneg b s σ)) hE0
  -- integrability of the whole integrand
  have hint : Integrable fun y : ℝ => (LSeries a ((σ : ℂ) + (y : ℝ) * I)
      * LSeries b ((σ : ℂ) + (y : ℝ) * I) * LSeries f ((σ : ℂ) + (y : ℝ) * I)) * W y := by
    refine hWint.bdd_mul
      (c := dampedL1 a s σ * dampedL1 b s σ * ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)))
      ((hcont1.mul hcont2).mul hcont3).aestronglyMeasurable ?_
    filter_upwards with y using hMg y
  -- the truncated part
  have hI1 : IntegrableOn (fun y : ℝ => ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      (Set.Icc (-T) T) := (hcont1.norm.pow 2).integrableOn_Icc
  have hI2 : IntegrableOn (fun y : ℝ => ‖LSeries b ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      (Set.Icc (-T) T) := (hcont2.norm.pow 2).integrableOn_Icc
  have hmain := norm_integral_mul_three_le_truncated_add_tail (T := T) hT.le hE0 hWsup0 hMg0 hC0
    hcont1.aestronglyMeasurable.restrict hcont2.aestronglyMeasurable.restrict
    (fun y => norm_LSeries_line_le_trivial hf1 hmul hbdd hσ y)
    (fun y => by rw [hW]; exact norm_perronKernel_le hN.le hH hσ0 y)
    hMg (fun y => by rw [hW]; exact hCb y) hint hI1 hI2
  refine hmain.trans ?_
  refine add_le_add ?_ (le_refl _)
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hE0 hWsup0)
  have hb1 := integral_Icc_normSq_LSeries_le_prime_sieve hs0 hsuppa hprimea σ hT z Y hY hYz hz hlog
  have hb2 := integral_Icc_normSq_LSeries_le_prime_sieve hs0 hsuppb hprimeb σ hT z Y hY hYz hz hlog
  rw [truncSieveSum, truncSieveSum]
  exact mul_le_mul (Real.sqrt_le_sqrt hb1) (Real.sqrt_le_sqrt hb2) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-- **The truncated GHS step-four bound with the kernel constant discharged.**  The instance at the
Mellin kernel bound, whose constant depends only on `N`, `H`, `σ`. -/
theorem exists_norm_tsum_ghs_smoothWeight_le_truncated {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    (N₀ : ℕ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ) {T : ℝ} (hT : 0 < T)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    ∃ C : ℝ, 0 ≤ C ∧
      (2 * Real.pi) * ‖∑' n : ℕ,
            (LSeries.convolution (ghsOuter f N₀) (LSeries.convolution (ghsInner f N₀) f)) n
              * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
        ≤ ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * ((N + H) ^ σ / σ)
              * (Real.sqrt (truncSieveSum (ghsOuter f N₀) (Finset.Icc 1 N₀) σ T z Y)
                  * Real.sqrt (truncSieveSum (ghsInner f N₀) (Finset.Icc 1 N₀) σ T z Y))
          + (dampedL1 (ghsOuter f N₀) (Finset.Icc 1 N₀) σ
                * dampedL1 (ghsInner f N₀) (Finset.Icc 1 N₀) σ
                * ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)))
              * C * (Real.pi - 2 * Real.arctan T) := by
  obtain ⟨C, hC0, hCb⟩ := GaloisForLFunctions.HTGeometry.exists_bound_mellin_smoothWeight_line
    hN hH (show (0 : ℝ) < σ by linarith)
  exact ⟨C, hC0, norm_tsum_ghs_smoothWeight_le_truncated_of_kernelBound hf1 hmul hbdd N₀ hN hH hσ
    hT z Y hY hYz hz hlog hC0 hCb⟩

end RHTower.Sieve
end
