import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.StrictBregmanBalance
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.PositiveJumpBoundaryControl

/-!
# Explicit terminal bounds for all three Bregman energy gaps

The three nonnegative jump kernels are the arctangent square, the gap
between the mixed dissipation and that square, and the gap between the
original square and the mixed dissipation. Their terminal moments are
respectively the integrals of `atan(F)^2`, `atan(F) * (F - atan(F))`, and
`F * (F - atan(F))` over `(-d, 0)`.

Multiplying each moment by `2 exp(-d/2)` gives a lower bound for its full
jump energy. Every terminal moment is positive for an actual critical
state, so these are explicit positive lower bounds without an amplitude
bound on the state.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower HilbertMetric.Probability

/-- Arctangent square, mixed-minus-arctangent gap, and original-minus-mixed gap. -/
def arctanGapKernel (i : Fin 3) (a b : ℝ) : ℝ :=
  ![(Real.arctan a - Real.arctan b) ^ 2,
    (a - b) * (Real.arctan a - Real.arctan b) - (Real.arctan a - Real.arctan b) ^ 2,
    (a - b) ^ 2 - (a - b) * (Real.arctan a - Real.arctan b)] i

theorem arctanGapKernel_nonneg (i : Fin 3) (a b : ℝ) : 0 ≤ arctanGapKernel i a b := by
  fin_cases i
  · exact sq_nonneg _
  · exact sub_nonneg.mpr (arctan_jump_bounds a b).1
  · exact sub_nonneg.mpr (arctan_jump_bounds a b).2

theorem arctanGapKernel_boundary_pos (i : Fin 3) {a : ℝ} (ha : a ≠ 0) :
    0 < arctanGapKernel i a 0 := by
  have h := arctan_zero_jump_strict ha
  fin_cases i
  · simpa only [arctanGapKernel, Real.arctan_zero, sub_zero] using h.1
  · simpa only [arctanGapKernel, Real.arctan_zero, sub_zero] using sub_pos.mpr h.2.1
  · simpa only [arctanGapKernel, Real.arctan_zero, sub_zero] using sub_pos.mpr h.2.2

/-- The three terminal moments, with the same ordering as the jump kernels. -/
def arctanBoundaryMoment (i : Fin 3) (d : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∫ u in Ioo (-d) 0, arctanGapKernel i (F u) 0

/-- The terminal densities are the arctangent square and the two factored contraction defects. -/
theorem arctanGapKernel_boundary (i : Fin 3) (a : ℝ) :
    arctanGapKernel i a 0 =
      ![Real.arctan a ^ 2, Real.arctan a * (a - Real.arctan a),
        a * (a - Real.arctan a)] i := by
  fin_cases i <;> simp only [arctanGapKernel, Real.arctan_zero, sub_zero] <;> ring

/-- The three consecutive gaps in the nonlinear energy chain. -/
def arctanGapEnergy (i : Fin 3) (F : ℝ → ℝ) : ℝ :=
  ![levyEnergy (Real.arctan ∘ F),
    arctanLevyDissipation F - levyEnergy (Real.arctan ∘ F),
    levyEnergy F - arctanLevyDissipation F] i

private theorem integrable_arctanJump_parts {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) :
    Integrable (fun u => (Real.arctan (F u) - Real.arctan (F (u + x))) ^ 2) ∧
      Integrable (fun u => (F u - F (u + x)) *
        (Real.arctan (F u) - Real.arctan (F (u + x)))) ∧
      Integrable (fun u => (F u - F (u + x)) ^ 2) := by
  have ha := (domain_arctan hF).memLp_real
  have hdF := hF.memLp_real.sub (memLp_two_shift hF.memLp_real x)
  have hdA := ha.sub (memLp_two_shift ha x)
  exact ⟨integrable_sq_of_memLp hdA, integrable_mul_of_memLp hdF hdA,
    integrable_sq_of_memLp hdF⟩

theorem integrable_arctanGapKernel {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (i : Fin 3) (x : ℝ) :
    Integrable fun u => arctanGapKernel i (F u) (F (u + x)) := by
  obtain ⟨ha, hm, hf⟩ := integrable_arctanJump_parts hF x
  fin_cases i
  · exact ha
  · exact hm.sub ha
  · exact hf.sub hm

theorem integrableOn_arctanGapKernel {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (i : Fin 3) :
    IntegrableOn (fun x : ℝ => archLevyDensity x *
      ∫ u, arctanGapKernel i (F u) (F (u + x))) (Ioi 0) := by
  have ha := (domain_arctan hF).integrableOn_levyIntegrand
  have hm := integrableOn_arctanDissipation hF
  have hf := hF.integrableOn_levyIntegrand
  fin_cases i
  · exact ha
  · refine (hm.sub ha).congr (Eventually.of_forall fun x => ?_)
    obtain ⟨ha', hm', _⟩ := integrable_arctanJump_parts hF x
    change archLevyDensity x * (∫ u, (F u - F (u + x)) *
        (Real.arctan (F u) - Real.arctan (F (u + x)))) -
      archLevyDensity x * (∫ u, (Real.arctan (F u) - Real.arctan (F (u + x))) ^ 2) =
      archLevyDensity x * ∫ u, ((F u - F (u + x)) *
        (Real.arctan (F u) - Real.arctan (F (u + x))) -
          (Real.arctan (F u) - Real.arctan (F (u + x))) ^ 2)
    rw [integral_sub hm' ha', mul_sub]
  · refine (hf.sub hm).congr (Eventually.of_forall fun x => ?_)
    obtain ⟨_, hm', hf'⟩ := integrable_arctanJump_parts hF x
    change archLevyDensity x * (∫ u, (F u - F (u + x)) ^ 2) -
      archLevyDensity x * (∫ u, (F u - F (u + x)) *
        (Real.arctan (F u) - Real.arctan (F (u + x)))) =
      archLevyDensity x * ∫ u, ((F u - F (u + x)) ^ 2 -
        (F u - F (u + x)) * (Real.arctan (F u) - Real.arctan (F (u + x))))
    rw [integral_sub hf' hm', mul_sub]

/-- Each energy gap is the integral of its nonnegative jump kernel. -/
theorem arctanGapEnergy_eq_integral {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (i : Fin 3) :
    arctanGapEnergy i F =
      ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u, arctanGapKernel i (F u) (F (u + x)) := by
  have ha := (domain_arctan hF).integrableOn_levyIntegrand
  have hm := integrableOn_arctanDissipation hF
  have hf := hF.integrableOn_levyIntegrand
  fin_cases i
  · rfl
  · change arctanLevyDissipation F - levyEnergy (Real.arctan ∘ F) = _
    unfold arctanLevyDissipation levyMixed levyEnergy
    rw [← integral_sub hm ha]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only [Function.comp_apply]
    obtain ⟨ha', hm', _⟩ := integrable_arctanJump_parts hF x
    rw [← mul_sub, ← integral_sub hm' ha']
    rfl
  · change levyEnergy F - arctanLevyDissipation F = _
    unfold arctanLevyDissipation levyMixed levyEnergy
    rw [← integral_sub hf hm]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only [Function.comp_apply]
    obtain ⟨_, hm', hf'⟩ := integrable_arctanJump_parts hF x
    rw [← mul_sub, ← integral_sub hf' hm']
    rfl

/-- The terminal moment is finite because the jump of length `d` crosses the endpoint. -/
theorem integrableOn_arctanBoundaryMoment {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (i : Fin 3) (d : ℝ) :
    IntegrableOn (fun u => arctanGapKernel i (F u) 0) (Ioo (-d) 0) := by
  refine (integrable_arctanGapKernel hF i d).integrableOn.congr_fun ?_ measurableSet_Ioo
  intro u hu
  change arctanGapKernel i (F u) (F (u + d)) = arctanGapKernel i (F u) 0
  rw [hF.support (u + d) (by linarith only [hu.1])]

/-- An explicit exponential coefficient turns each terminal moment into a full-energy floor. -/
theorem arctanBoundaryMoment_lower {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (i : Fin 3) {d : ℝ} (hd : 0 < d) :
    (2 * Real.exp (-d / 2)) * arctanBoundaryMoment i d F ≤ arctanGapEnergy i F := by
  rw [arctanGapEnergy_eq_integral hF i]
  exact hF.jump_boundary_lower (arctanGapKernel_nonneg i)
    (fun x _ => integrable_arctanGapKernel hF i x) (integrableOn_arctanGapKernel hF i) hd

/-- Every terminal moment is positive for a critical state, regardless of its sign changes. -/
theorem criticalState_arctanBoundaryMoment_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (i : Fin 3) {d : ℝ} (hd : 0 < d) : 0 < arctanBoundaryMoment i d F := by
  have hD := criticalHalfLineEnergyDomain_of_groundState hF
  have hn : 0 ≤ arctanBoundaryMoment i d F :=
    integral_nonneg fun u => arctanGapKernel_nonneg i (F u) 0
  by_contra hbad
  have hz : arctanBoundaryMoment i d F = 0 := le_antisymm (le_of_not_gt hbad) hn
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun u => arctanGapKernel_nonneg i (F u) 0)
    (integrableOn_arctanBoundaryMoment hD i d)).mp hz
  have hsq : (fun u => F u ^ 2) =ᵐ[volume.restrict (Ioo (-d) 0)] 0 := by
    filter_upwards [hae] with u hu
    change arctanGapKernel i (F u) 0 = 0 at hu
    by_cases hzero : F u = 0
    · simp only [hzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Pi.zero_apply]
    · exact False.elim ((ne_of_gt (arctanGapKernel_boundary_pos i hzero)) hu)
  have hezero : (∫ u in Ioo (-d) 0, F u ^ 2) = 0 := by
    rw [integral_congr_ae hsq]
    simp only [Pi.zero_apply, integral_zero]
  exact (ne_of_gt (criticalHalfLineGroundState_endpoint_mass_pos hW ht hF hd)) hezero

/-- The signed balance and its two neighboring energies have explicit positive terminal floors. -/
theorem criticalState_arctan_quantitative_balance {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (i : Fin 3)
    {d : ℝ} (hd : 0 < d) :
    0 < arctanBoundaryMoment i d F ∧
      (2 * Real.exp (-d / 2)) * arctanBoundaryMoment i d F ≤
        ![levyEnergy (Real.arctan ∘ F),
          arctanArithmeticBalance W₀ F - levyEnergy (Real.arctan ∘ F),
          levyEnergy F - arctanArithmeticBalance W₀ F] i := by
  refine ⟨criticalState_arctanBoundaryMoment_pos hW ht hF i hd, ?_⟩
  have h := arctanBoundaryMoment_lower (criticalHalfLineEnergyDomain_of_groundState hF) i hd
  simpa only [arctanGapEnergy, criticalState_arctan_balance hW ht hF] using h

/-- Explicit margins on both sides of the signed arithmetic balance. -/
theorem criticalState_arctan_quantitative_interval {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {d : ℝ} (hd : 0 < d) :
    (2 * Real.exp (-d / 2)) * arctanBoundaryMoment 0 d F ≤ levyEnergy (Real.arctan ∘ F) ∧
      levyEnergy (Real.arctan ∘ F) + (2 * Real.exp (-d / 2)) * arctanBoundaryMoment 1 d F ≤
        arctanArithmeticBalance W₀ F ∧
      arctanArithmeticBalance W₀ F + (2 * Real.exp (-d / 2)) * arctanBoundaryMoment 2 d F ≤
        levyEnergy F := by
  have h0 := (criticalState_arctan_quantitative_balance hW ht hF 0 hd).2
  have h1 := (criticalState_arctan_quantitative_balance hW ht hF 1 hd).2
  have h2 := (criticalState_arctan_quantitative_balance hW ht hF 2 hd).2
  change (2 * Real.exp (-d / 2)) * arctanBoundaryMoment 1 d F ≤
    arctanArithmeticBalance W₀ F - levyEnergy (Real.arctan ∘ F) at h1
  change (2 * Real.exp (-d / 2)) * arctanBoundaryMoment 2 d F ≤
    levyEnergy F - arctanArithmeticBalance W₀ F at h2
  exact ⟨h0, by linarith only [h1], by linarith only [h2]⟩

/-- The signed arithmetic side must pay an explicit positive nonlinear boundary moment. -/
theorem criticalState_arctan_balance_terminal_lower {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {d : ℝ} (hd : 0 < d) :
    0 < (2 * Real.exp (-d / 2)) * (∫ u in Ioo (-d) 0, F u * Real.arctan (F u)) ∧
      (2 * Real.exp (-d / 2)) * (∫ u in Ioo (-d) 0, F u * Real.arctan (F u)) ≤
        arctanArithmeticBalance W₀ F := by
  have hD := criticalHalfLineEnergyDomain_of_groundState hF
  have hA := domain_arctan hD
  have hi := integrable_mul_of_memLp hD.memLp_real hA.memLp_real
  have hm : arctanBoundaryMoment 0 d F ≤ ∫ u in Ioo (-d) 0, F u * Real.arctan (F u) := by
    simp only [arctanBoundaryMoment, arctanGapKernel, Real.arctan_zero, sub_zero]
    apply integral_mono hA.sq.integrableOn hi.integrableOn
    intro u
    simpa only [Real.arctan_zero, sub_zero] using (arctan_jump_bounds (F u) 0).1
  have hp := lt_of_lt_of_le (criticalState_arctanBoundaryMoment_pos hW ht hF 0 hd) hm
  refine ⟨mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hp, ?_⟩
  rw [← criticalState_arctan_balance hW ht hF]
  have hb := hD.jump_boundary_lower
    (K := fun a b => (a - b) * (Real.arctan a - Real.arctan b))
    (fun a b => (sq_nonneg _).trans (arctan_jump_bounds a b).1)
    (fun x _ => (integrable_arctanJump_parts hD x).2.1)
    (integrableOn_arctanDissipation hD) hd
  simpa only [Real.arctan_zero, sub_zero, arctanLevyDissipation, levyMixed, Function.comp_apply] using hb

/-- Every state in the unconditional alternative satisfies all three terminal bounds at every scale. -/
theorem riemannHypothesis_or_criticalState_quantitative_bregman_balance :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ d : ℝ, 0 < d → ∀ i : Fin 3,
        0 < arctanBoundaryMoment i d F ∧
        (2 * Real.exp (-d / 2)) * arctanBoundaryMoment i d F ≤
          ![levyEnergy (Real.arctan ∘ F),
            arctanArithmeticBalance W₀ F - levyEnergy (Real.arctan ∘ F),
            levyEnergy F - arctanArithmeticBalance W₀ F] i := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀, F, hW, ht, hF,
      fun d hd i => criticalState_arctan_quantitative_balance hW ht hF i hd⟩

#print axioms arctanGapEnergy_eq_integral
#print axioms arctanBoundaryMoment_lower
#print axioms criticalState_arctan_balance_terminal_lower
#print axioms riemannHypothesis_or_criticalState_quantitative_bregman_balance

end GaloisForLFunctions.ExclusionOfTheCriticalState
end
