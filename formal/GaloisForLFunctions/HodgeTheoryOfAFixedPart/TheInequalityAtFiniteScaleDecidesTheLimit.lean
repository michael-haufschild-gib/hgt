import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheNormalFormOfThePairingOfTheDegreePoints

/-!
# The inequality at finite scale decides the limit

The normal form states the inequality of Castelnuovo and Severi at one scale and on all real
divisors of a window. The Riemann hypothesis is the same inequality in the limit, on the samples
of a packet. This file relates the two.

* **From finite scale to the limit** (`riemannHypothesis_of_frequently_combForm_ge`): if for
  every window ratio and every `η > 0` there are arbitrarily large scales `N` at which
  `2 d₁ d₂ − D·D ≥ −η Σ c_n²` for every real divisor of the window, the Riemann hypothesis
  holds. The lower bound may fail at the other scales and may be negative: only the bottom of
  Weil's form on the comb, relative to `Σ c_n²`, is asked not to stay below a negative constant.
* **A zero off the line is seen at every large scale**
  (`exists_window_combForm_neg_of_not_riemannHypothesis`): if the Riemann hypothesis fails,
  there are a window ratio, `ε > 0` and `C` such that at every large scale some real divisor of
  the window has `Σ c_n² ≤ C` and `2 d₁ d₂ − D·D ≤ −ε`.

The squares of the coordinates of a sampled packet sum to `∫ f²`
(`tendsto_sum_sq_sampleCoord`): the norm `Σ c_n²` of the normal form is the norm of the packet.
-/

open Finset Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

variable {f : ℝ → ℝ}

/-- **The norm of the normal form is the norm of the packet**: `Σ c_n² → ∫ f²`. -/
theorem tendsto_sum_sq_sampleCoord (hcont : Continuous f) {K : ℕ} (hK : 1 ≤ K) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N), sampleCoord f N n ^ 2) atTop
      (𝓝 (∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2)) := by
  have hG : Continuous fun u : ℝ => f u ^ 2 := by fun_prop
  refine (tendsto_degreeSum hG (by omega : 1 ≤ 3 * K)).congr' ?_
  filter_upwards with N
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  show f (Real.log ((n : ℝ) / N)) ^ 2 / n = sampleCoord f N n ^ 2
  rw [sampleCoord, div_pow, Real.sq_sqrt hn', degreeSample]

/-- If Weil's form on the comb is bounded below by `−η Σ c_n²` on the samples of a packet at
arbitrarily large scales, for every `η > 0`, the sum over the zeros of the packet is
nonnegative. -/
theorem zeroSum_nonneg_of_frequently (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ}
    (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0)
    (h : ∀ η : ℝ, 0 < η → ∃ᶠ N : ℕ in atTop,
      -η * ∑ n ∈ Ioc N (N + 3 * K * N), sampleCoord f N n ^ 2 ≤
        combForm (Ioc N (N + 3 * K * N)) (sampleCoord f N)) :
    0 ≤ zeroSum f := by
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2 :=
    ⟨_, rfl⟩
  have hI := tendsto_sum_sq_sampleCoord hf.continuous hK
  rw [← hIdef] at hI
  have hZ := tendsto_combForm_sample hf hfc hK hsupp
  have hI0 : 0 ≤ I := by
    rw [hIdef]
    refine intervalIntegral.integral_nonneg (Real.log_nonneg ?_) fun u _ => sq_nonneg _
    have : (0 : ℝ) ≤ ((3 * K : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have key : ∀ η : ℝ, 0 < η → 0 ≤ zeroSum f + η * I := by
    intro η hη
    exact ge_of_tendsto_of_frequently (hZ.add (hI.const_mul η))
      ((h η hη).mono fun N hN => by linarith)
  by_contra hneg
  have hz : zeroSum f < 0 := not_le.mp hneg
  have hpos : 0 < -zeroSum f / (2 * (I + 1)) := div_pos (by linarith) (by linarith)
  have h1 := key _ hpos
  have e : zeroSum f + -zeroSum f / (2 * (I + 1)) * I = zeroSum f * (I + 2) / (2 * (I + 1)) := by
    field_simp
    ring
  rw [e] at h1
  have hlt : zeroSum f * (I + 2) / (2 * (I + 1)) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hz (by linarith)) (by linarith)
  linarith

/-- **The inequality at finite scale gives the Riemann hypothesis.** If for every window ratio
and every `η > 0` there are arbitrarily large scales at which `2 d₁ d₂ − D·D ≥ −η Σ c_n²` for
every real divisor of the window, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_frequently_combForm_ge
    (h : ∀ K : ℕ, 1 ≤ K → ∀ η : ℝ, 0 < η → ∃ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      -η * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 ≤ combForm (Ioc N (N + 3 * K * N)) c) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_degreePairing_le_degrees]
  intro f hf hfc K hK hsupp l hl
  have hz := zeroSum_nonneg_of_frequently hf hfc hK hsupp fun η hη =>
    (h K hK η hη).mono fun N hN => hN _
  rw [tendsto_nhds_unique hl (tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp)]
  linarith

/-- **A zero off the line is seen at every large scale.** If the Riemann hypothesis fails there
are a window ratio, `ε > 0` and `C` such that at every large scale some real divisor of the
window has `Σ c_n² ≤ C` and `2 d₁ d₂ − D·D ≤ −ε`. -/
theorem exists_window_combForm_neg_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ (K : ℕ) (ε C : ℝ), 1 ≤ K ∧ 0 < ε ∧ ∀ᶠ N : ℕ in atTop, ∃ c : ℕ → ℝ,
      ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 ≤ C ∧
        combForm (Ioc N (N + 3 * K * N)) c ≤ -ε := by
  rw [riemannHypothesis_iff_degreePairing_le_degrees] at hRH
  push Not at hRH
  obtain ⟨f, hf, hfc, K, hK, hsupp, l, hl, hlt⟩ := hRH
  have hl' := tendsto_nhds_unique hl (tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp)
  have hz : zeroSum f < 0 := by
    rw [hl'] at hlt
    linarith
  have hZ := tendsto_combForm_sample hf hfc hK hsupp
  have hI := tendsto_sum_sq_sampleCoord hf.continuous hK
  refine ⟨K, -zeroSum f / 2,
    (∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2) + 1, hK, by linarith, ?_⟩
  filter_upwards [hZ.eventually (gt_mem_nhds (show zeroSum f < zeroSum f / 2 by linarith)),
    hI.eventually (gt_mem_nhds (lt_add_one _))] with N h1 h2
  exact ⟨sampleCoord f N, h2.le, by linarith⟩

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
