import GaloisForLFunctions.BiScaleUncertainty.LinearKreinSmoothingAndInverseLinearGridTail
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinHoheiselEveryBase

/-!
# Short gaps between nodes control blind correlation tails

The linear logarithmic modulus `log(1/|x - y|) |h(x) - h(y)| ≤ 32√e 𝒥(f) + 2h(0)` turns any
supply of nodes in short multiplicative windows into an inverse-linear tail law for the
correlations that vanish on those nodes. If every window `(e^T, e^T + e^{θT}]` contains a node
`n`, the node `log n` lies within `e^{-(1-θ)T}` of `T`, hence

`(1 - θ) T |h(T)| ≤ 32√e 𝒥(f) + 2h(0)`.

For the primes the corpus supplies `θ = 71/100` unconditionally (a Hoheisel-type theorem from the
zero-density tower). Consequently every compact `C²` source whose correlation vanishes at all
logarithms of primes — in particular every source blind on the prime powers, which is the cone
on which the von Mangoldt term of the Weil form disappears — has `|h(T)| = O((𝒥 + h(0))/T)`
beyond an absolute threshold, uniformly in the support, and square-integrable tails
`∫_{T}^∞ h² = O((𝒥 + h(0))²/T)`. Only the density of the blind set in short windows enters;
the gap exponent appears as the factor `1 - θ`.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

variable {f : ℝ → ℝ}

/-- **Gap-to-tail transfer.** A node of the blind set in the window `(e^T, e^T + e^{θT}]`
forces `(1 - θ) T |h(T)| ≤ 32√e 𝒥(f) + 2h(0)`. -/
theorem mul_abs_autocorr_le_of_window_node (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {θ : ℝ} (hθ : θ < 1) {T : ℝ} (hT : 0 < T) {n : ℕ}
    (hn0 : autocorr f (Real.log n) = 0) (hlo : Real.exp T < n)
    (hhi : (n : ℝ) ≤ Real.exp T + Real.exp T ^ θ) :
    (1 - θ) * T * |autocorr f T| ≤
      32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0 := by
  have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos T) hlo
  set d : ℝ := Real.log n - T with hd
  have hd0 : 0 < d := by
    have := Real.log_lt_log (Real.exp_pos T) hlo
    rw [Real.log_exp] at this
    linarith
  have hθT : Real.exp T ^ θ = Real.exp (θ * T) := by
    rw [← Real.exp_mul, mul_comm]
  have hd1 : d ≤ Real.exp (-((1 - θ) * T)) := by
    have hratio : (n : ℝ) / Real.exp T ≤ 1 + Real.exp (-((1 - θ) * T)) := by
      rw [div_le_iff₀ (Real.exp_pos T), add_mul, one_mul, ← Real.exp_add]
      rw [hθT] at hhi
      have he : -((1 - θ) * T) + T = θ * T := by ring
      rw [he]
      exact hhi
    have hlog := Real.log_le_sub_one_of_pos (div_pos hnpos (Real.exp_pos T))
    rw [Real.log_div hnpos.ne' (Real.exp_pos T).ne', Real.log_exp] at hlog
    linarith
  have hneg : -((1 - θ) * T) < 0 := by
    have : 0 < (1 - θ) * T := mul_pos (by linarith) hT
    linarith
  have hdlt : d < 1 := lt_of_le_of_lt hd1 (Real.exp_lt_one_iff.mpr hneg)
  have hlog : (1 - θ) * T ≤ -Real.log d := by
    have := Real.log_le_log hd0 hd1
    rw [Real.log_exp] at this
    linarith
  have habs : |T - Real.log n| = d := by
    rw [abs_sub_comm, abs_of_pos hd0]
  have hmod := neg_log_mul_abs_autocorr_sub_le hf hfc (x := T) (y := Real.log n)
    (by rw [habs]; exact hd0) (by rw [habs]; exact hdlt)
  rw [habs, hn0, sub_zero] at hmod
  calc
    _ ≤ (-Real.log d) * |autocorr f T| := mul_le_mul_of_nonneg_right hlog (abs_nonneg _)
    _ ≤ _ := hmod

/-- **Prime-blind inverse-linear tail law.** There is an absolute threshold `T₀` such that every
compact `C²` source whose correlation vanishes at `log p` for every prime `p` satisfies
`(29/100) T |h(T)| ≤ 32√e 𝒥(f) + 2h(0)` for all `T ≥ T₀`. -/
theorem exists_prime_blind_inverse_linear_tail :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ p : ℕ, p.Prime → autocorr f (Real.log p) = 0) → ∀ T : ℝ, T₀ ≤ T →
        (29 / 100) * T * |autocorr f T| ≤
          32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0 := by
  obtain ⟨Z, hZ⟩ := eventually_atTop.1 RHTower.Sieve.exists_eventually_routeT_prime_in_every_base_window
  refine ⟨max 1 (Real.log (max Z 1)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro f hf hfc hblind T hT
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTZ : Z ≤ Real.exp T := by
    have h1 : Real.log (max Z 1) ≤ T := le_trans (le_max_right _ _) hT
    have h2 : max Z 1 ≤ Real.exp T := by
      rw [← Real.exp_log (lt_of_lt_of_le one_pos (le_max_right Z 1))]
      exact Real.exp_le_exp.mpr h1
    exact le_trans (le_max_left _ _) h2
  obtain ⟨p, hp, hlo, hhi⟩ := hZ (Real.exp T) hTZ
  have hθ : RHTower.Sieve.routeTHoheiselEveryBaseExponent = 71 / 100 := rfl
  rw [hθ] at hhi
  have h := mul_abs_autocorr_le_of_window_node hf hfc (θ := 71 / 100) (by norm_num)
    (by linarith) (hblind p hp) hlo hhi
  calc
    _ = (1 - 71 / 100) * T * |autocorr f T| := by norm_num
    _ ≤ _ := h

/-- **Uniform square-integrable prime-blind tails.** Beyond the same absolute threshold,
`∫_{T}^∞ h² ≤ (100/29)² (32√e 𝒥(f) + 2h(0))² / T` on the prime-blind cone. -/
theorem exists_prime_blind_square_tail :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ p : ℕ, p.Prime → autocorr f (Real.log p) = 0) → ∀ T : ℝ, T₀ ≤ T →
        ∫ x in Ioi T, autocorr f x ^ 2 ≤
          (100 / 29 * (32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0)) ^ 2 / T := by
  obtain ⟨T₀, hT₀, hlaw⟩ := exists_prime_blind_inverse_linear_tail
  refine ⟨T₀, hT₀, fun f hf hfc hblind T hT => ?_⟩
  set C : ℝ := 100 / 29 * (32 * Real.exp (1 / 2) * biScaleLevyEnergy f + 2 * autocorr f 0)
    with hC
  have hTpos : 0 < T := lt_of_lt_of_le hT₀ hT
  have hcont : Continuous (fun x => autocorr f x ^ 2) := (continuous_autocorr hf hfc).pow 2
  have hcs : HasCompactSupport (fun x => autocorr f x ^ 2) :=
    (hasCompactSupport_autocorr hfc).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  have hint : IntegrableOn (fun x => autocorr f x ^ 2) (Ioi T) :=
    (hcont.integrable_of_hasCompactSupport hcs).integrableOn
  have hrint : IntegrableOn (fun x : ℝ => C ^ 2 * x ^ (-2 : ℝ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hTpos).const_mul _
  have hpt : ∀ x ∈ Ioi T, autocorr f x ^ 2 ≤ C ^ 2 * x ^ (-2 : ℝ) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hTpos hx
    have hb := hlaw f hf hfc hblind x (le_trans hT (le_of_lt hx))
    have hb' : x * |autocorr f x| ≤ C := by
      rw [hC]
      have : x * |autocorr f x| = 100 / 29 * ((29 / 100) * x * |autocorr f x|) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hb (by norm_num)
    have hrp : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
      rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hrp, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have habs : (x * |autocorr f x|) ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hx0.le (abs_nonneg _)) hb' 2
    calc
      autocorr f x ^ 2 * x ^ 2 = (x * |autocorr f x|) ^ 2 := by rw [mul_pow, sq_abs]; ring
      _ ≤ _ := habs
  calc
    _ ≤ ∫ x in Ioi T, C ^ 2 * x ^ (-2 : ℝ) :=
      setIntegral_mono_on hint hrint measurableSet_Ioi hpt
    _ = C ^ 2 * (-T ^ ((-2 : ℝ) + 1) / ((-2 : ℝ) + 1)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hTpos]
    _ = C ^ 2 / T := by
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      field_simp

end

end GaloisForLFunctions.BiScaleUncertainty
