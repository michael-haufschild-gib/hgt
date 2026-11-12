import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ArithmeticPowerRiemannProfiles

/-!
# Power cancellation between an arithmetic staircase and a continuous trace

Above every positive cutoff the staircase is a finite sum of interval
indicators and the trace is continuous. The existing power-envelope
criterion then extends their Riemann sums through the singular endpoint.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- A continuous profile on the closed unit interval has convergent right meshes. -/
theorem riemannOn_of_continuousOn_Icc {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc 0 1)) : RiemannOn g := by
  have hi : IntervalIntegrable g volume 0 1 := hg.intervalIntegrable_of_Icc zero_le_one
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi, ?_⟩
  have hh := GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tendsto_riemannSum_of_continuousOn hg
  rw [intervalIntegral.integral_of_le zero_le_one] at hh
  refine hh.congr fun N => ?_
  have he := RHTower.sum_range_succ_eq_sourcePartialSum (fun n => g ((n : ℝ) / N)) N
  simpa only [RHTower.sourcePartialSum, tailRiemannSum, div_eq_inv_mul,
    Nat.cast_add, Nat.cast_one] using congrArg (fun z : ℝ => (N : ℝ)⁻¹ * z) he

/-- A positive cutoff of a continuous profile has convergent meshes even
though the cutoff itself may be a jump. -/
theorem riemannOn_cut_of_continuousOn {g : ℝ → ℝ} {δ : ℝ}
    (hg : ContinuousOn g (Set.Ioc 0 1)) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    RiemannOn ((Set.Ioi δ).indicator g) := by
  have hc := riemannOn_of_continuousOn_Icc (continuousOn_powerTailClip hg hδ hδ1)
  have hconst := (riemannOn_indicator_Iic (h := fun _ : ℝ => (1 : ℝ))
    (fun _ _ _ _ _ => le_rfl) (fun _ _ => zero_le_one)
    (integrableOn_const (by simp)) δ).const_mul (g δ)
  apply (hc.sub hconst).congr
  intro t _
  by_cases ht : t ≤ δ
  · rw [Set.indicator_of_mem (show t ∈ Set.Iic δ from ht),
      Set.indicator_of_notMem (show t ∉ Set.Ioi δ from not_lt.mpr ht),
      powerTailClip, max_eq_left ht, mul_one, sub_self]
  · rw [Set.indicator_of_notMem (show t ∉ Set.Iic δ from ht),
      Set.indicator_of_mem (show t ∈ Set.Ioi δ from lt_of_not_ge ht),
      powerTailClip, max_eq_right (le_of_not_ge ht), mul_zero, sub_zero]

/-- Cancellation between an arithmetic staircase and a continuous trace
pays the endpoint whenever their difference has an integrable power bound.
Neither summand needs to be integrable near zero separately. -/
theorem riemannOn_arithmeticPowerProfile_sub_continuous
    {p a C : ℝ} {f : ℕ → ℝ} {g : ℝ → ℝ}
    (hp : 0 ≤ p) (ha : 0 < a) (ha1 : a < 1)
    (hgm : Measurable g) (hgc : ContinuousOn g (Set.Ioc 0 1))
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      |arithmeticPowerProfile p f t - g t| ≤ C * t ^ (-a)) :
    RiemannOn (fun t => arithmeticPowerProfile p f t - g t) := by
  apply riemannOn_of_powerBound_and_cuts ha ha1
    ((measurable_arithmeticPowerProfile p f).sub hgm) hB
  intro δ hδ hδ1
  apply ((riemannOn_cut_arithmeticPowerProfile hp hδ f).sub
    (riemannOn_cut_of_continuousOn hgc hδ hδ1)).congr
  intro t _
  by_cases ht : δ < t
  · simp only [Set.indicator_of_mem (show t ∈ Set.Ioi δ from ht), Pi.sub_apply]
  · simp only [Set.indicator_of_notMem (show t ∉ Set.Ioi δ from ht), sub_self]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
