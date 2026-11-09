import GaloisForLFunctions.InfiniteRankWeilTheory.FiniteJetSublevelMeasure
import GaloisForLFunctions.InfiniteRankWeilTheory.UniformOscillatoryJets

/-!+# Uniform sublevel measure for finite oscillatory sums

Distinct frequencies give a uniformly nonzero finite jet. On each fixed-radius interval,
the derivative sublevel estimate for one real component bounds small values of the whole sum.
The resulting power and constant are independent of the center of the interval.
-/

open Set MeasureTheory Finset
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- A nonzero finite sum of distinct real frequencies has a uniform power-law sublevel bound
on translates of one fixed interval. -/
theorem exists_uniform_oscillatory_sublevel_bound {k : ℕ} (γ : Fin k → ℝ)
    (hγ : Function.Injective γ) (c : Fin k → ℂ) (hc : c ≠ 0) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧ ∀ x ε : ℝ, 0 < ε →
      volume {y ∈ Ioo (x - r) (x + r) | ‖oscillatoryJet γ c 0 y‖ < ε} ≤
        ENNReal.ofReal (K * ε ^ ((k : ℝ)⁻¹)) := by
  classical
  obtain ⟨r, A, hr, hA, hwindow⟩ := exists_uniform_oscillatoryJet_window γ hγ c hc
  have hk : 0 < k := by
    obtain ⟨m, _⟩ := hwindow 0
    exact Nat.zero_lt_of_lt m.isLt
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  let D : ℝ := ∑ m ∈ range k, derivativeSublevelConstant m A
  have hD : 0 ≤ D := sum_nonneg fun m _ => derivativeSublevelConstant_nonneg m hA
  let K : ℝ := D + 2 * r + 2 * r / A + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKr : 2 * r ≤ K := by
    dsimp [K]
    linarith only [hD, div_nonneg (by positivity : 0 ≤ 2 * r) hA.le]
  have hKA : 2 * r / A ≤ K := by dsimp [K]; linarith only [hD, hr]
  have hKD (m : ℕ) (hm : m < k) : derivativeSublevelConstant m A ≤ K := by
    have hmD : derivativeSublevelConstant m A ≤ D :=
      single_le_sum (fun j _ => derivativeSublevelConstant_nonneg j hA) (mem_range.mpr hm)
    dsimp [K]
    linarith [div_nonneg (by positivity : 0 ≤ 2 * r) hA.le]
  refine ⟨r, K, hr, hK, fun x ε hε => ?_⟩
  have htrivial : volume {y ∈ Ioo (x - r) (x + r) |
      ‖oscillatoryJet γ c 0 y‖ < ε} ≤ ENNReal.ofReal (2 * r) := by
    calc _ ≤ volume (Ioo (x - r) (x + r)) := measure_mono fun _ hy => hy.1
      _ = _ := by rw [Real.volume_Ioo]; congr 1; ring
  by_cases hε1 : 1 ≤ ε
  · refine htrivial.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp : 1 ≤ ε ^ ((k : ℝ)⁻¹) := Real.one_le_rpow hε1 (by positivity)
    exact hKr.trans (by nlinarith only [hp, hK])
  have hεsmall : ε ≤ 1 := (lt_of_not_ge hε1).le
  obtain ⟨m, b, hlow⟩ := hwindow x
  have hsub : {y ∈ Ioo (x - r) (x + r) | ‖oscillatoryJet γ c 0 y‖ < ε} ⊆
      {y ∈ Ioo (x - r) (x + r) |
        |traceComponent b (oscillatoryJet γ c 0 y)| < ε} := by
    intro y hy
    exact ⟨hy.1, (abs_traceComponent_le b _).trans_lt hy.2⟩
  by_cases hm : (m : ℕ) = 0
  · by_cases hεA : ε ≤ A
    · have hempty : {y ∈ Ioo (x - r) (x + r) |
          |traceComponent b (oscillatoryJet γ c 0 y)| < ε} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hl := hlow y hy.1
        rw [hm] at hl
        exact (not_lt_of_ge (hεA.trans hl)) hy.2
      exact (measure_mono hsub).trans (by rw [hempty, measure_empty]; exact bot_le)
    · have hAε : A ≤ ε := (lt_of_not_ge hεA).le
      have hp : ε ≤ ε ^ ((k : ℝ)⁻¹) := by
        have hki : (k : ℝ)⁻¹ ≤ 1 := by
          apply inv_le_one_of_one_le₀
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_ge hε hεsmall hki
      refine htrivial.trans (ENNReal.ofReal_le_ofReal ?_)
      calc 2 * r = (2 * r / A) * A := by field_simp
        _ ≤ (2 * r / A) * ε := mul_le_mul_of_nonneg_left hAε (by positivity)
        _ ≤ K * ε ^ ((k : ℝ)⁻¹) := mul_le_mul hKA hp hε.le hK.le
  · have hmpos : 1 ≤ (m : ℕ) := Nat.one_le_iff_ne_zero.mpr hm
    have hmreal : 0 < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    have hchain : HTGeometry.KleinbockMargulis.IsDerivChain (m : ℕ)
        (fun j y => traceComponent b (oscillatoryJet γ c j y)) (Ioo (x - r) (x + r)) :=
      fun j _ y _ => hasDerivAt_traceComponent_jet γ c b j y
    have hbound := volume_sublevel_le_of_derivative_lower hmpos hA hchain hlow hε
    have hexp : ε ^ ((m : ℝ)⁻¹) ≤ ε ^ ((k : ℝ)⁻¹) := by
      apply Real.rpow_le_rpow_of_exponent_ge hε hεsmall
      exact inv_anti₀ hmreal (by exact_mod_cast m.isLt.le)
    exact (measure_mono hsub).trans (hbound.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul (hKD m m.isLt) hexp (by positivity) hK.le)))

#print axioms exists_uniform_oscillatory_sublevel_bound

end GaloisForLFunctions.InfiniteRankWeilTheory
