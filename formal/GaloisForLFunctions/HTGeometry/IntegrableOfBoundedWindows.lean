import Mathlib

/-!
# Integrability from bounded window masses

A nonnegative continuous function whose masses over the symmetric windows `[-n, n]` are bounded by
one constant is integrable on the line.  The windows exhaust the line and the integrand is
nonnegative, so monotone convergence identifies the total lower integral with the supremum of the
window masses, which the bound keeps finite.

This is the criterion that turns an exact windowed identity into a global integrability statement.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Integrability from bounded window masses.** -/
theorem integrable_of_bounded_windows {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x)
    {C : ℝ} (hb : ∀ n : ℕ, (∫ x in Icc (-(n : ℝ)) (n : ℝ), f x) ≤ C) :
    Integrable f := by
  classical
  set g : ℝ → ENNReal := fun x => ENNReal.ofReal (f x) with hg
  have hgmeas : Measurable g := (ENNReal.measurable_ofReal.comp hf.measurable)
  set s : ℕ → Set ℝ := fun n => Icc (-(n : ℝ)) (n : ℝ) with hs
  have hsmeas : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Icc
  have hsmono : Monotone s := by
    intro m n hmn
    have hmn' : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
    exact Icc_subset_Icc (by linarith) hmn'
  -- the indicators increase to `g`
  set F : ℕ → ℝ → ENNReal := fun n => (s n).indicator g with hF
  have hFmeas : ∀ n, Measurable (F n) := fun n => hgmeas.indicator (hsmeas n)
  have hFmono : Monotone F := by
    intro m n hmn x
    exact Set.indicator_le_indicator_of_subset (hsmono hmn) (fun _ => bot_le) x
  have hFsup : ∀ x : ℝ, ⨆ n, F n x = g x := by
    intro x
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · exact Set.indicator_le (fun _ _ => le_rfl) x
    · refine le_iSup_of_le n ?_
      have hmem : x ∈ s n := by
        rw [hs]
        exact mem_Icc.2 ⟨by linarith [neg_abs_le x, hn], by linarith [le_abs_self x, hn]⟩
      rw [hF]
      simp only
      rw [Set.indicator_of_mem hmem]
  -- monotone convergence
  have hlint : ∫⁻ x, g x = ⨆ n, ∫⁻ x, F n x := by
    rw [← lintegral_iSup hFmeas hFmono]
    exact lintegral_congr fun x => (hFsup x).symm
  -- each window mass is at most `ofReal C`
  have hwin : ∀ n : ℕ, (∫⁻ x, F n x) ≤ ENNReal.ofReal C := by
    intro n
    have hindic : (∫⁻ x, F n x) = ∫⁻ x in s n, g x := lintegral_indicator (hsmeas n) g
    have hintOn : IntegrableOn f (s n) volume :=
      (hf.continuousOn).integrableOn_compact isCompact_Icc
    have hofreal : ENNReal.ofReal (∫ x in s n, f x) = ∫⁻ x in s n, ENNReal.ofReal (f x) :=
      ofReal_integral_eq_lintegral_ofReal hintOn
        (Filter.Eventually.of_forall fun x => hnn x)
    rw [hindic, hg, ← hofreal]
    exact ENNReal.ofReal_le_ofReal (hb n)
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  rw [show (∫⁻ a, ENNReal.ofReal (f a)) = ∫⁻ a, g a from rfl, hlint]
  exact lt_of_le_of_lt (iSup_le hwin) ENNReal.ofReal_lt_top

end GaloisForLFunctions.HTGeometry
