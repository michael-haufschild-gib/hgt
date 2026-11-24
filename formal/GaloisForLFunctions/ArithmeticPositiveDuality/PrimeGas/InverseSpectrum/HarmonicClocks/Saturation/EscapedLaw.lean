import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.WeakConvergence

/-! # Distribution of phase carried by escaping occupation labels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

/-- Continuous phase observable restricted to occupied labels outside a fixed window. -/
def escapedObservable (v : MissingWave) (t : ℝ) (F : Finset ℕ+) (f : C(Circle,ℂ)) :=
  ∑' n : (Fᶜ : Set ℕ+), (occupationProbability v n:ℂ)*f (occupationPhase t n)

private theorem escaped_eq_sub (v : MissingWave) (t : ℝ) (F : Finset ℕ+) (f : C(Circle,ℂ)) :
    escapedObservable v t F f = (∫ z, f z ∂(occupationPhaseLaw v t : Measure Circle))-
      ∑ n ∈ F, (occupationProbability v n:ℂ)*f (occupationPhase t n) := by
  have h := phaseObservable_hasSum v t f
  exact eq_sub_iff_add_eq'.mpr ((h.summable.sum_add_tsum_compl (s := F)).trans h.tsum_eq)

/-- The finite-energy limit exhausts exactly the atom at one. -/
theorem cyclicPhaseLaw_remove_retained (r : ℕ+) {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) (f : Circle → ℂ) :
    (∫ z, f z ∂(cyclicPhaseLaw r δ h₀ h₁ : Measure Circle))-(retentionCeiling r δ:ℂ)*f 1 =
      (rootShare r δ:ℂ)*∑ k ∈ (Finset.range r.val).erase 0, f (clockRoot r^k) := by
  rw [cyclicPhaseLaw_integral,← Finset.add_sum_erase (Finset.range r.val) (fun k => f (clockRoot r^k))
    (Finset.mem_range.mpr r.pos),pow_zero]
  change _-((δ+rootShare r δ:ℝ):ℂ)*f 1 = _
  rw [Complex.ofReal_add]
  ring

/-- First taking the preparation limit and then exhausting finite windows isolates the nontrivial roots. -/
theorem saturated_escaped_phase_law {r : ℕ+} {t d : ℕ → ℝ} {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1)
    {v : ℕ → MissingWave} {m : ℕ+ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hd : Tendsto d atTop (𝓝 δ))
    (hc : ∀ j, harmonicTest r (d j) (v j) (t j))
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n)))
    (hs : HasSum m (retentionCeiling r δ)) (f : C(Circle,ℂ)) :
    ∃ L : Finset ℕ+ → ℂ, (∀ F, Tendsto (fun j => escapedObservable (v j) (t j) F f) atTop (𝓝 (L F))) ∧
      Tendsto L atTop (𝓝 ((rootShare r δ:ℂ)*∑ k ∈ (Finset.range r.val).erase 0, f (clockRoot r^k))) := by
  let C := ∫ z, f z ∂(cyclicPhaseLaw r δ h₀ h₁ : Measure Circle)
  refine ⟨fun F => C-((∑ n ∈ F, m n:ℝ):ℂ)*f 1,fun F => ?_,?_⟩
  · have hfull := (continuous_integral_complex_continuousMap f).continuousAt.tendsto.comp
      (saturated_phase_law h₀ h₁ ht hd hc hm hs)
    have hwin := tendsto_finsetSum F (fun n _ => (hm n).ofReal.mul
      (f.continuous.continuousAt.tendsto.comp (occupationPhase_limit ht n)))
    simpa only [Function.comp_def,escaped_eq_sub,← Finset.sum_mul,← Complex.ofReal_sum,C] using hfull.sub hwin
  · have net : Tendsto (fun F : Finset ℕ+ => ∑ n ∈ F, m n) atTop (𝓝 (retentionCeiling r δ)) := hs
    rw [← cyclicPhaseLaw_remove_retained r h₀ h₁]
    exact (net.ofReal.mul_const (f 1)).const_sub C

#print axioms cyclicPhaseLaw_remove_retained
#print axioms saturated_escaped_phase_law

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
