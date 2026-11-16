import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.BregmanDissipation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoTerminalSupportGap
import GaloisForLFunctions.HTGeometry.HalfPlanePolePhase

/-!
# Strict nonlinear dissipation at the half-line boundary

Every terminal interval carries positive square mass of a critical state.
Jumps crossing the endpoint therefore compare a nonzero value with zero.
The strict scalar inequalities for arctangent make both Bregman energy
comparisons strict, at each positive jump length and after integration.
Consequently the signed arithmetic balance lies strictly between the
arctangent jump energy and the original jump energy.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower HilbertMetric.Probability

private theorem arctan_zero_jump_strict {a : ℝ} (ha : a ≠ 0) :
    0 < Real.arctan a ^ 2 ∧
      Real.arctan a ^ 2 < a * Real.arctan a ∧ a * Real.arctan a < a ^ 2 := by
  have hp (x : ℝ) (hx : 0 < x) :
      0 < Real.arctan x ^ 2 ∧
        Real.arctan x ^ 2 < x * Real.arctan x ∧ x * Real.arctan x < x ^ 2 := by
    have ht := Real.arctan_pos.mpr hx
    have hl := HTGeometry.arctan_lt_self hx
    exact ⟨sq_pos_of_pos ht,
      by simpa only [pow_two] using mul_lt_mul_of_pos_right hl ht,
      by simpa only [pow_two] using mul_lt_mul_of_pos_left hl hx⟩
  rcases lt_or_gt_of_ne ha with hn | hp'
  · simpa only [Real.arctan_neg, neg_sq, neg_mul_neg] using hp (-a) (neg_pos.mpr hn)
  · exact hp a hp'

/-- Equality of ordered integrals would erase all mass where the comparison is strict. -/
private theorem integral_lt_of_endpoint_comparison {F f g : ℝ → ℝ} {d : ℝ}
    (hmass : 0 < ∫ u in Ioo (-d) 0, F u ^ 2)
    (hf : Integrable f) (hg : Integrable g) (hle : ∀ u, f u ≤ g u)
    (hlt : ∀ u ∈ Ioo (-d) 0, F u ≠ 0 → f u < g u) :
    (∫ u, f u) < ∫ u, g u := by
  by_contra hbad
  have he : (∫ u, f u) = ∫ u, g u :=
    le_antisymm (integral_mono hf hg hle) (le_of_not_gt hbad)
  have hae := (integral_eq_iff_of_ae_le hf hg (Eventually.of_forall hle)).mp he
  have hz : (fun u => F u ^ 2) =ᵐ[volume.restrict (Ioo (-d) 0)] 0 := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo] with u hu hus
    by_cases hF : F u = 0
    · simp only [hF, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Pi.zero_apply]
    · exact False.elim ((ne_of_lt (hlt u hus hF)) hu)
  have hezero : (∫ u in Ioo (-d) 0, F u ^ 2) = 0 := by
    rw [integral_congr_ae hz]
    simp only [Pi.zero_apply, integral_zero]
  exact (ne_of_gt hmass) hezero

/-- Positive jump lengths all see strict contraction on a positive-mass terminal interval. -/
theorem criticalState_arctan_jump_strict {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {h : ℝ} (hh : 0 < h) :
    0 < (∫ u, (Real.arctan (F u) - Real.arctan (F (u + h))) ^ 2) ∧
      (∫ u, (Real.arctan (F u) - Real.arctan (F (u + h))) ^ 2) <
        (∫ u, (F u - F (u + h)) * (Real.arctan (F u) - Real.arctan (F (u + h)))) ∧
      (∫ u, (F u - F (u + h)) * (Real.arctan (F u) - Real.arctan (F (u + h)))) <
        ∫ u, (F u - F (u + h)) ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := (domain_arctan hd).memLp_real
  have hdf := hd.memLp_real.sub (memLp_two_shift hd.memLp_real h)
  have hda := ha.sub (memLp_two_shift ha h)
  have hfa := integrable_mul_of_memLp hdf hda
  have hff := integrable_sq_of_memLp hdf
  have haa := integrable_sq_of_memLp hda
  simp only [Pi.sub_apply, Function.comp_apply] at hfa hff haa
  have hm := criticalHalfLineGroundState_endpoint_mass_pos hW ht hF hh
  have hb (u : ℝ) (hu : u ∈ Ioo (-h) 0) : F (u + h) = 0 :=
    hd.support _ (by linarith only [hu.1])
  constructor
  · have hp := integral_lt_of_endpoint_comparison hm (integrable_zero ℝ ℝ volume)
      haa (fun u => sq_nonneg (Real.arctan (F u) - Real.arctan (F (u + h))))
      (fun u hu hne => by
        simpa only [Pi.zero_apply, hb u hu, Real.arctan_zero, sub_zero] using
          (arctan_zero_jump_strict hne).1)
    simpa only [Pi.zero_apply, integral_zero] using hp
  constructor
  · apply integral_lt_of_endpoint_comparison hm haa hfa
      (fun u => (arctan_jump_bounds (F u) (F (u + h))).1)
    intro u hu hne
    simpa only [hb u hu, Real.arctan_zero, sub_zero] using (arctan_zero_jump_strict hne).2.1
  · apply integral_lt_of_endpoint_comparison hm hfa hff
      (fun u => (arctan_jump_bounds (F u) (F (u + h))).2)
    intro u hu hne
    simpa only [hb u hu, Real.arctan_zero, sub_zero] using (arctan_zero_jump_strict hne).2.2

private theorem integral_Ioi_strict {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0))
    (hlt : ∀ x, 0 < x → f x < g x) :
    (∫ x in Ioi (0 : ℝ), f x) < ∫ x in Ioi (0 : ℝ), g x := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun x => g x - f x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (sub_pos.mpr (hlt x hx)).le
  have hs : Ioi (0 : ℝ) ⊆ (Function.support fun x => g x - f x) ∩ Ioi 0 := by
    intro x hx
    exact ⟨ne_of_gt (sub_pos.mpr (hlt x hx)), hx⟩
  have hpos : (0 : ENNReal) < volume (Ioi (0 : ℝ)) := by
    simp only [Real.volume_Ioi, ENNReal.zero_lt_top]
  have hp : 0 < ∫ x in Ioi (0 : ℝ), g x - f x :=
    (setIntegral_pos_iff_support_of_nonneg_ae hn (hg.sub hf)).mpr
      (lt_of_lt_of_le hpos (measure_mono hs))
  rwa [integral_sub hg hf, sub_pos] at hp

/-- Boundary mass makes all three integrated energy inequalities strict. -/
theorem criticalState_arctan_dissipation_strict {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    0 < levyEnergy (Real.arctan ∘ F) ∧
      levyEnergy (Real.arctan ∘ F) < arctanLevyDissipation F ∧
      arctanLevyDissipation F < levyEnergy F := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := (domain_arctan hd).integrableOn_levyIntegrand
  have hm := integrableOn_arctanDissipation hd
  have hf := hd.integrableOn_levyIntegrand
  constructor
  · have hp := integral_Ioi_strict (integrable_zero ℝ ℝ (volume.restrict (Ioi (0 : ℝ))))
      ha (fun h hh => mul_pos (archLevyDensity_pos hh)
        (criticalState_arctan_jump_strict hW ht hF hh).1)
    simpa only [Pi.zero_apply, integral_zero, levyEnergy, Function.comp_apply] using hp
  constructor
  · exact integral_Ioi_strict ha hm fun h hh =>
      mul_lt_mul_of_pos_left (criticalState_arctan_jump_strict hW ht hF hh).2.1
        (archLevyDensity_pos hh)
  · exact integral_Ioi_strict hm hf fun h hh =>
      mul_lt_mul_of_pos_left (criticalState_arctan_jump_strict hW ht hF hh).2.2
        (archLevyDensity_pos hh)

/-- The actual arithmetic balance has a positive gap from both bounding jump energies. -/
theorem criticalState_arctan_balance_strict {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    0 < levyEnergy (Real.arctan ∘ F) ∧
      levyEnergy (Real.arctan ∘ F) < arctanArithmeticBalance W₀ F ∧
      arctanArithmeticBalance W₀ F < levyEnergy F := by
  rw [← criticalState_arctan_balance hW ht hF]
  exact criticalState_arctan_dissipation_strict hW ht hF

/-- The unconditional critical-state alternative carries the strict nonlinear constraint. -/
theorem riemannHypothesis_or_criticalState_strict_bregman_balance :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      0 < levyEnergy (Real.arctan ∘ F) ∧
      levyEnergy (Real.arctan ∘ F) < arctanArithmeticBalance W₀ F ∧
      arctanArithmeticBalance W₀ F < levyEnergy F := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀, F, hW, ht, hF, criticalState_arctan_balance_strict hW ht hF⟩

#print axioms criticalState_arctan_jump_strict
#print axioms criticalState_arctan_dissipation_strict
#print axioms riemannHypothesis_or_criticalState_strict_bregman_balance

end GaloisForLFunctions.ExclusionOfTheCriticalState
end
