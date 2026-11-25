import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.Intensity
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # Asymptotics of a continuously marked band Euler product -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks

open Filter Topology Set _root_.RHTower

/-- Unnormalized squarefree product for an arbitrary complex mark. -/
def euler (c d : ℝ) (h : Ioi (0:ℝ)) (f : ℝ → ℂ) :=
  ∏ p ∈ added c d h, (1+f (location h p)/(p.val:ℂ))

private theorem log_error {u : ℂ} (hu : ‖u‖ ≤ 1/2) : ‖Complex.log (1+u)-u‖ ≤ ‖u‖^2 := by
  have hpos : 0 < 1-‖u‖ := by linarith only [hu]
  have hinv : (1-‖u‖)⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hpos).mpr (by linarith only [hu])
  exact (Complex.norm_log_one_add_sub_self_le (by linarith only [hu])).trans
    (by nlinarith only [mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖u‖)])

/-- Quadratic logarithm errors vanish because every prime in the band escapes to infinity. -/
theorem euler_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (f : ℝ → ℂ) (hf : Continuous f) :
    Tendsto (fun h => euler c d h f) criticalApproach
      (𝓝 (Complex.exp (∫ v in c..d, f v/(v:ℂ)))) := by
  let u (h : Ioi (0:ℝ)) (p : Nat.Primes) := f (location h p)/(p.val:ℂ)
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := c) (b := d)).exists_bound_of_continuousOn hf.continuousOn
  let δ (h : Ioi (0:ℝ)) := B/((primeCut c h:ℝ)+1)
  have hδ : Tendsto δ criticalApproach (𝓝 0) := by
    have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (primeCut_atTop hc)
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_mono' criticalApproach
      (Eventually.of_forall fun _ => le_add_of_nonneg_right zero_le_one) hN
  have hu (h : Ioi (0:ℝ)) (p : Nat.Primes) (hp : p ∈ added c d h) : ‖u h p‖ ≤ δ h := by
    have hv := (mem_added c d h p).mp hp
    have hlo : primeCut c h < p.val :=
      lt_of_not_ge (fun hle => (Finset.mem_sdiff.mp hp).2 (Sieve.mem_primeSubtypeLE.mpr hle))
    rw [show ‖u h p‖ = ‖f (location h p)‖/(p.val:ℝ) by simp [u]]
    exact div_le_div₀ (norm_nonneg _) (hB _ ⟨hv.1.le,hv.2⟩) (by positivity : (0:ℝ) < (primeCut c h:ℝ)+1)
      (by exact_mod_cast Nat.succ_le_of_lt hlo)
  let A (h : Ioi (0:ℝ)) := ∑ p ∈ added c d h, ‖u h p‖
  have hA := (Complex.continuous_re.tendsto _).comp
    (intensity_limit hc hcd (fun v => (‖f v‖:ℂ)) (Complex.continuous_ofReal.comp hf.norm))
  have hA' : Tendsto A criticalApproach (𝓝 (∫ v in c..d, (‖f v‖:ℂ)/(v:ℂ)).re) := by
    apply hA.congr
    intro h
    change (∑ p ∈ added c d h, (‖f (location h p)‖:ℂ)/(p.val:ℂ)).re = _
    simp only [A,u,norm_div,Complex.norm_natCast,← Complex.ofReal_natCast,← Complex.ofReal_div,
      ← Complex.ofReal_sum,Complex.ofReal_re]
  let S (h : Ioi (0:ℝ)) := ∑ p ∈ added c d h, u h p
  let L (h : Ioi (0:ℝ)) := ∑ p ∈ added c d h, Complex.log (1+u h p)
  have hE : Tendsto (fun h => ‖L h-S h‖) criticalApproach (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (show Tendsto (fun h => δ h*A h) _ (𝓝 0) by simpa only [zero_mul] using hδ.mul hA')
    filter_upwards [hδ.eventually_le_const (by norm_num : (0:ℝ) < 1/2)] with h hh
    change ‖(∑ p ∈ added c d h, _)-(∑ p ∈ added c d h, _)‖ ≤ _
    rw [← Finset.sum_sub_distrib,show δ h*A h = ∑ p ∈ added c d h, δ h*‖u h p‖ by rw [← Finset.mul_sum]]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    exact (log_error ((hu h p hp).trans hh)).trans
      (by rw [pow_two]; exact mul_le_mul_of_nonneg_right (hu h p hp) (norm_nonneg _))
  have hL := (tendsto_zero_iff_norm_tendsto_zero.mpr hE).add (intensity_limit hc hcd f hf)
  have hL' : Tendsto L criticalApproach (𝓝 (∫ v in c..d, f v/(v:ℂ))) := by
    simpa only [S,zero_add,sub_add_cancel] using hL
  apply ((Complex.continuous_exp.tendsto _).comp hL').congr'
  filter_upwards [hδ.eventually_le_const (by norm_num : (0:ℝ) < 1/2)] with h hh
  change Complex.exp (∑ p ∈ added c d h, _) = _
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  apply Complex.exp_log
  intro H
  have hh' := (hu h p hp).trans hh
  have hneg : u h p = -1 := by linear_combination H
  rw [hneg,norm_neg,norm_one] at hh'
  norm_num at hh'

#print axioms euler_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks
