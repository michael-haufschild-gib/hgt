import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.ClockReadout

/-! # Probability retained at zeros whose times approach zero -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

private theorem phase_tendsto {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) (n : ℕ+) :
    Tendsto (fun j => splitPhase (t j) n) atTop (𝓝 1) := by
  simpa only [Function.comp_def,splitPhase_zero] using ((splitPhase_continuous n).continuousAt (x := 0)).tendsto.comp ht

/-- On any fixed finite energy window the amplitude tends to its instantaneous mass, uniformly over the preparations. -/
theorem window_error_tendsto (v : ℕ → MissingWave) {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) (F : Finset ℕ+) :
    Tendsto (fun j => windowAmplitude (v j) (t j) F-(windowMass (v j) F:ℂ)) atTop (𝓝 0) := by
  have hterm (n : ℕ+) : Tendsto (fun j => (occupationProbability (v j) n:ℂ)*(splitPhase (t j) n-1)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun j => ‖splitPhase (t j) n-1‖)
    · intro j
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (occupationLaw_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (occupationLaw_le_one _ _)
    · simpa only [sub_self,norm_zero] using ((phase_tendsto ht n).sub_const (1:ℂ)).norm
  have h := tendsto_finsetSum F (fun n _ => hterm n)
  simpa only [mul_sub,mul_one,Finset.sum_sub_distrib,Finset.sum_const_zero,
    windowAmplitude,windowMass,Complex.ofReal_sum] using h

/-- Every fixed window eventually contains at most half the probability, up to arbitrary precision, at exact zeros tending to time zero. -/
theorem fast_zero_window (v : ℕ → MissingWave) {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0))
    (hz : ∀ j, compositionResponse (v j) (criticalTime (t j)) = 0) (F : Finset ℕ+) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, windowMass (v j) F < 1/2+ε := by
  have hlim := (window_error_tendsto v ht F).norm
  rw [norm_zero] at hlim
  filter_upwards [hlim.eventually_lt_const (show 0 < 2*ε by positivity)] with j hj
  have hd := window_response_disk (v j) (t j) F
  rw [hz j,zero_sub,norm_neg] at hd
  have h := norm_le_norm_add_norm_sub (windowAmplitude (v j) (t j) F) (windowMass (v j) F:ℂ)
  rw [Complex.norm_real,Real.norm_of_nonneg (windowMass_nonneg _ _)] at h
  linarith only [h,hd,hj]

private theorem windowMass_limit {v : ℕ → MissingWave} {m : ℕ+ → ℝ}
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) (F : Finset ℕ+) :
    Tendsto (fun j => windowMass (v j) F) atTop (𝓝 (∑ n ∈ F, m n)) :=
  tendsto_finsetSum F (fun n _ => hm n)

/-- For a limiting complex response b, the escaped mass bounds the distance from b to the mass remaining on finite labels. -/
theorem response_limit_disk {v : ℕ → MissingWave} {t : ℕ → ℝ} {m : ℕ+ → ℝ} {b : ℂ}
    (ht : Tendsto t atTop (𝓝 0))
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n)))
    (hb : Tendsto (fun j => compositionResponse (v j) (criticalTime (t j))) atTop (𝓝 b)) :
    (∀ n, 0 ≤ m n) ∧ Summable m ∧ ‖b-((∑' n, m n:ℝ):ℂ)‖ ≤ 1-∑' n, m n := by
  have hpos (n : ℕ+) : 0 ≤ m n := ge_of_tendsto (hm n) (Eventually.of_forall (fun j => occupationLaw_nonneg (v j) n))
  have hsum : Summable m := summable_of_sum_le hpos (fun F => le_of_tendsto' (windowMass_limit hm F) (fun j => windowMass_le_one (v j) F))
  refine ⟨hpos,hsum,?_⟩
  have hpartial (F : Finset ℕ+) : ‖b-((∑ n ∈ F, m n:ℝ):ℂ)‖ ≤ 1-∑ n ∈ F, m n := by
    have hA : Tendsto (fun j => windowAmplitude (v j) (t j) F) atTop (𝓝 ((∑ n ∈ F, m n:ℝ):ℂ)) := by
      have h := (window_error_tendsto v ht F).add (windowMass_limit hm F).ofReal
      simpa only [sub_add_cancel,zero_add] using h
    exact le_of_tendsto_of_tendsto' (hb.sub hA).norm (tendsto_const_nhds.sub (windowMass_limit hm F))
      (fun j => window_response_disk (v j) (t j) F)
  have hnet : Tendsto (fun F : Finset ℕ+ => ∑ n ∈ F, m n) atTop (𝓝 (∑' n, m n)) := hsum.hasSum
  exact le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub hnet.ofReal).norm (tendsto_const_nhds.sub hnet) hpartial

/-- A nonnegative summable array with at most half of a unit of occupation probability. -/
def halfLaw (m : ℕ+ → ℝ) : Prop := (∀ n, 0 ≤ m n) ∧ Summable m ∧ ∑' n, m n ≤ 1/2

theorem fast_zero_limit_halfLaw {v : ℕ → MissingWave} {t : ℕ → ℝ} {m : ℕ+ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hz : ∀ j, compositionResponse (v j) (criticalTime (t j)) = 0)
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) : halfLaw m := by
  have hb : Tendsto (fun j => compositionResponse (v j) (criticalTime (t j))) atTop (𝓝 0) :=
    Filter.EventuallyEq.tendsto (Eventually.of_forall hz)
  obtain ⟨hp,hs,hd⟩ := response_limit_disk ht hm hb
  rw [zero_sub,norm_neg,Complex.norm_real,Real.norm_of_nonneg (tsum_nonneg hp)] at hd
  exact ⟨hp,hs,by linarith only [hd]⟩

#print axioms window_error_tendsto
#print axioms fast_zero_window
#print axioms response_limit_disk
#print axioms fast_zero_limit_halfLaw

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
