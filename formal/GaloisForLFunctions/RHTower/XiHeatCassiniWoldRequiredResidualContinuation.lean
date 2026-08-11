import GaloisForLFunctions.RHTower.XiHeatCassiniWoldRelativeOrbitLeakage

/-!
# The required continuation of the Route-T physical residual

The preceding relative-orbit module constructs the canonical continued
Wold-minus-mesh-minus-holonomy residual and proves that every zeta zero right of the critical line
survives in it with exact multiplicity. This module extracts the genuinely new consequences:
forced discontinuity, a sharp conditional RH endpoint, and the coupling of that analytic pole to
the formal anti-reflected orbit compensator with the same multiplicity.

This isolates the only remaining Route-T compensator. It does not assert the critical prime-gap
energy or regularity of the required residual continuation.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The forced off-line residue prevents continuity of the required residual continuation at the
physical Wold pole. -/
theorem not_continuousAt_xiHeatCassiniWoldResidualLaplaceContinuation
    {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (hzeta : riemannZeta rho = 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    ¬ContinuousAt xiHeatCassiniWoldResidualLaplaceContinuation (rho - 1) := by
  intro hcontinuous
  obtain ⟨m, hm, hpole⟩ :=
    xiHeatCassiniWoldResidualLaplaceContinuation_nonzero_residue_of_criticalEnergy
      hrho hzeta hcritical
  have hlin := tendsto_sub_self_punctured_zero (rho - 1)
  have hvalue :
      Tendsto xiHeatCassiniWoldResidualLaplaceContinuation
        (𝓝[≠] (rho - 1))
        (𝓝 (xiHeatCassiniWoldResidualLaplaceContinuation (rho - 1))) :=
    hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hzero :
      Tendsto (fun s : ℂ =>
        (s - (rho - 1)) *
          xiHeatCassiniWoldResidualLaplaceContinuation s)
        (𝓝[≠] (rho - 1)) (𝓝 0) := by
    simpa using hlin.mul hvalue
  have hunique : -(m : ℂ) = 0 := tendsto_nhds_unique hpole hzero
  have hm0 : (m : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_lt hm
  exact hm0 (neg_eq_zero.mp hunique)

/-- **Exact Route-T endpoint.** Once critical mesh energy is available, RH is equivalent to
regularity of the one forced residual continuation at every possible right-half zeta pole. Mesh
and holonomy no longer occur in the open condition. -/
theorem riemannHypothesis_iff_requiredResidualContinuation_continuousAt
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    RiemannHypothesis ↔
      ∀ rho : ℂ, 1 / 2 < rho.re → riemannZeta rho = 0 →
        ContinuousAt xiHeatCassiniWoldResidualLaplaceContinuation (rho - 1) := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  constructor
  · intro hzeroFree rho hrho hzeta
    exact (hzeroFree rho hrho hzeta).elim
  · intro hregular rho hrho hzeta
    exact (not_continuousAt_xiHeatCassiniWoldResidualLaplaceContinuation
      hrho hzeta hcritical) (hregular rho hrho hzeta)

/-- **Analytic/formal cofinal-compensator capstone.** At an off-line zeta zero, one and the same
exact multiplicity appears in the nonzero analytic residual pole and in the anti-reflected formal
head. Every shift-two completion of that head therefore needs a nonzero compensator. -/
theorem xiHeatCassiniWoldRequiredResidual_cofinalCompensator
    {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (hzeta : riemannZeta rho = 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ =>
        (s - (rho - 1)) *
          xiHeatCassiniWoldResidualLaplaceContinuation s)
        (𝓝[≠] (rho - 1)) (𝓝 (-(m : ℂ))) ∧
      ∀ R E : ℂ →₀ (ℕ →₀ ℂ),
        xiHeatCassiniReflectedWoldPhysicalPoleHead rho m + R =
            GaloisForLFunctions.finiteOrbitCoboundary (2 : ℂ) E →
          R ≠ 0 := by
  obtain ⟨m, hm, hpole⟩ :=
    xiHeatCassiniWoldResidualLaplaceContinuation_nonzero_residue_of_criticalEnergy
      hrho hzeta hcritical
  refine ⟨m, hm, hpole, ?_⟩
  intro R E hcompletion
  apply xiHeatCassiniReflectedWoldPhysicalPoleHead_compensator_ne_zero
    (rho := rho) ⟨by linarith, riemannZeta_zero_re_lt_one hzeta⟩
    (by linarith) hm R E hcompletion

end

end RHTower
