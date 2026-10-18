import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailArchimedeanGrowth

/-! Unbounded normalized Weil energy of the literal smoothed correction tails. -/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower _root_.Zeta23
noncomputable section
set_option autoImplicit false

def factorialMuntzTailWeilLoss : ℝ := factorialMuntzTailArchLoss+
  512*(factorialMuntzTailPrimeBudget+144*Real.exp 1^2)

/-- The actual prime and pole contribution costs only a fixed multiple of
mass, while the actual archimedean contribution grows logarithmically. -/
theorem factorialMuntzSmoothedTail_weil_log_lower (n : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      (Real.log ((n+1 : ℕ) : ℝ)/2-factorialMuntzTailWeilLoss)*
        (∫ x : ℝ, factorialMuntzSmoothedTail n k x^2) ≤
      (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
        (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re := by
  filter_upwards [factorialMuntzSmoothedTail_arch_log_lower n,
    factorialMuntzSmoothedTail_zero_arch_mass_budget n] with k hA hW
  change |(zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
      (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re-factorialMuntzTailArchEnergy n k| ≤
    (512*(factorialMuntzTailPrimeBudget+144*Real.exp 1^2))*
      (∫ x : ℝ, factorialMuntzSmoothedTail n k x^2) at hW
  have hlo := (abs_le.mp hW).1
  unfold factorialMuntzTailWeilLoss
  nlinarith

private theorem log_index_tendsto :
    Tendsto (fun n : ℕ => Real.log ((n+1 : ℕ) : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

/-- Every fixed normalized lower bound is eventually attained by the actual
tails. The smoothing threshold is allowed to depend on n. -/
theorem factorialMuntzSmoothedTail_weil_coercive (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ k : ℕ in atTop,
      B*(∫ x : ℝ, factorialMuntzSmoothedTail n k x^2) ≤
      (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
        (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re := by
  filter_upwards [log_index_tendsto.eventually
    (eventually_ge_atTop (2*(B+factorialMuntzTailWeilLoss)))] with n hn
  filter_upwards [factorialMuntzSmoothedTail_weil_log_lower n] with k hk
  exact (mul_le_mul_of_nonneg_right (by linarith)
    (integral_nonneg fun x => sq_nonneg (factorialMuntzSmoothedTail n k x))).trans hk

/-- A literal lower bound of logarithmic size, with no source-family,
boundary, compact-support, or Weil-positivity premise. -/
theorem factorialMuntzSmoothedTail_weil_log_rate :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ k : ℕ in atTop,
      Real.log ((n+1 : ℕ) : ℝ)/(2048*((n+1 : ℕ) : ℝ)) ≤
      (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
        (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re := by
  filter_upwards [log_index_tendsto.eventually
    (eventually_ge_atTop (4*factorialMuntzTailWeilLoss))] with n hn
  filter_upwards [factorialMuntzSmoothedTail_weil_log_lower n,
    factorialMuntzSmoothedTail_sq_integral_eventually_lower n] with k hk hm
  have hlog : 0 ≤ Real.log ((n+1 : ℕ) : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ n+1 by omega))
  have hm0 : 0 ≤ ∫ x : ℝ, factorialMuntzSmoothedTail n k x^2 :=
    integral_nonneg fun x => sq_nonneg _
  calc
    _ = (Real.log ((n+1 : ℕ) : ℝ)/4)*(1/(512*((n+1 : ℕ) : ℝ))) := by ring
    _ ≤ (Real.log ((n+1 : ℕ) : ℝ)/4)*(∫ x : ℝ, factorialMuntzSmoothedTail n k x^2) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ (Real.log ((n+1 : ℕ) : ℝ)/2-factorialMuntzTailWeilLoss)*
        (∫ x : ℝ, factorialMuntzSmoothedTail n k x^2) :=
      mul_le_mul_of_nonneg_right (by linarith) hm0
    _ ≤ _ := hk

theorem factorialMuntzSmoothedTail_weil_eventually_pos :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ k : ℕ in atTop,
      0 < (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
        (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re := by
  filter_upwards [factorialMuntzSmoothedTail_weil_coercive 1] with n hn
  filter_upwards [hn, factorialMuntzSmoothedTail_sq_integral_eventually_lower n] with k hk hm
  have hp : 0 < ∫ x : ℝ, factorialMuntzSmoothedTail n k x^2 := lt_of_lt_of_le (by positivity) hm
  exact hp.trans_le (by simpa only [one_mul] using hk)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
