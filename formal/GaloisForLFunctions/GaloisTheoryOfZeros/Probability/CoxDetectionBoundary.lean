import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.GammaCoxDetection
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Sharp boundaries of Gamma–Cox detection

Finite candidate consistency does not extend uniformly over residuals approaching
zero. Binary detection also forgets root multiplicity. At zero concentration its
initial derivative is the same positive constant for every residual.
-/

open Filter Topology Set
open scoped Classical
namespace GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
noncomputable section

/-- At every fixed concentration, detection is continuous in the residual. -/
theorem continuous_detection_residual (K : ℝ) : Continuous (detection K) := by
  have hw : Continuous (weight K) := by unfold weight; fun_prop
  have hp (r : ℝ) : 1 + weight K r ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one (Real.exp_pos _))
  exact continuous_const.sub
    (Real.continuous_exp.comp (continuous_const.mul ((continuous_const.add hw).log hp)))

/-- Detection also depends continuously on the concentration parameter. -/
theorem continuous_detection_concentration (r : ℝ) : Continuous (fun K => detection K r) := by
  have hw : Continuous (fun K => weight K r) := by unfold weight; fun_prop
  have hp (K : ℝ) : 1 + weight K r ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one (Real.exp_pos _))
  exact continuous_const.sub
    (Real.continuous_exp.comp (continuous_id.neg.mul ((continuous_const.add hw).log hp)))

/-- Detection is never decreasing on the whole positive concentration axis,
even for a fixed nonzero residual. Its value starts at zero and is positive at one. -/
theorem detection_not_antitone (r : ℝ) :
    ¬ AntitoneOn (fun K => detection K r) (Ioi 0) := by
  intro hanti
  have hp : 0 < detection 1 r := detection_pos 1 r zero_lt_one
  have hlim : Tendsto (fun K => detection K r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun K => detection K r) (𝓝[>] (0 : ℝ)) (𝓝 (detection 0 r)) :=
      (continuous_detection_concentration r).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [detection, neg_zero, zero_mul, Real.exp_zero, sub_self] using h
  have hk : ∀ᶠ K : ℝ in 𝓝[>] 0, K < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ K : ℝ in 𝓝[>] 0, 0 < K := self_mem_nhdsWithin
  obtain ⟨K, hK, hlt, hd⟩ :=
    (hpos.and (hk.and (hlim.eventually (eventually_lt_nhds hp)))).exists
  have h1 : (1 : ℝ) ∈ Ioi 0 := by norm_num
  exact (not_lt_of_ge (hanti hK h1 hlt.le)) hd

/-- Every positive concentration admits nonzero residuals with detection probability
arbitrarily close to the true-zero detection probability. -/
theorem exists_nonzero_detection_gt_half (K : ℝ) (hK : 0 < K) :
    ∃ r : ℝ, 0 < r ∧ detection K 0 / 2 < detection K r := by
  have hp := detection_pos K 0 hK
  have hlim : Tendsto (detection K) (𝓝[>] (0 : ℝ)) (𝓝 (detection K 0)) :=
    (continuous_detection_residual K).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have he := hlim.eventually (eventually_gt_nhds (show detection K 0 / 2 < detection K 0 by linarith))
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hd⟩ := (hpos.and he).exists
  exact ⟨r, hr, hd⟩

/-- No uniform zero classification is possible over all nonzero real residuals:
even arbitrarily large concentration retains false positives above one quarter. -/
theorem nonuniform_detection (K : ℝ) (hK : 1 ≤ K) :
    ∃ r : ℝ, 0 < r ∧ (1 / 4 : ℝ) < detection K r := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.exp (-K * Real.log 2) ≤ (1 / 2 : ℝ) := by
    calc
      Real.exp (-K * Real.log 2) ≤ Real.exp (-Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hK, hlog]
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  obtain ⟨r, hr, hd⟩ := exists_nonzero_detection_gt_half K (lt_of_lt_of_le zero_lt_one hK)
  refine ⟨r, hr, ?_⟩
  rw [detection_zero] at hd
  linarith only [he, hd]

/-- Raising a residual to any positive integer power leaves its limiting binary
classification unchanged, so the binary detector cannot recover multiplicity. -/
theorem tendsto_power_detection_gap (r : ℝ) (n : ℕ) :
    Tendsto (fun K => detection K (r ^ (n + 1)) - detection K r) atTop (𝓝 0) := by
  have h : Tendsto (fun K => detection K (r ^ (n + 1))) atTop
      (𝓝 (if r = 0 then 1 else 0)) := by
    simpa only [pow_eq_zero_iff (Nat.succ_ne_zero n)] using tendsto_detection (r ^ (n + 1))
  simpa only [sub_self] using h.sub (tendsto_detection r)

/-- Initial concentration increases detection at every residual, including nonzeros. -/
theorem hasDerivAt_detection_zero (r : ℝ) :
    HasDerivAt (fun K => detection K r) (Real.log 2) 0 := by
  have hw := (((hasDerivAt_id (0 : ℝ)).neg).mul_const (r ^ 2)).exp
  have hl := (hw.const_add 1).log (by norm_num : (1 : ℝ) + Real.exp (-(0 : ℝ) * r ^ 2) ≠ 0)
  have hd := (((hasDerivAt_id (0 : ℝ)).neg).mul hl).exp.const_sub 1
  simpa [detection, weight, show (1 : ℝ) + 1 = 2 by norm_num] using hd

end
end GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.continuous_detection_residual
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.continuous_detection_concentration
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.detection_not_antitone
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.exists_nonzero_detection_gt_half
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.nonuniform_detection
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_power_detection_gap
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.hasDerivAt_detection_zero
