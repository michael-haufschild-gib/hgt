import GaloisForLFunctions.RHTower.SourceHorizontalAbelianClassLawInformationEvacuation
import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherCofinalContiguitySelection
import GaloisForLFunctions.RHTower.XiMassCriticalPrimeTailDiagonalEscape

/-!
# Xi information escape is prime-tail diagonal escape

The canonical abelian source realizes the two reflected horizontal occupations conditionally on
a shrinking two-class aperture.  At nonzero horizontal grade, conditional Jeffreys information
diverges along the aperture scale even though both literal mass-weighted information currents
vanish.  This file proves that this joint rare-event phenomenon occurs exactly off the critical
line.

Globally, existence of one such Xi copy is equivalent both to failure of RH and to adversarial
escape from every moving finite prime-tail approximation.  It is also equivalent to a nonzero
canonical reflection self-intersection charge.  Thus probabilistic postselection escape and
analytic prime-tail escape are two presentations of one obstruction, not merely reporters with a
common zero set.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- At every positive horizontal grade, conditional adaptive information diverges along the
linear aperture scale. -/
theorem tendsto_sourceHorizontalPrimeAdaptiveJeffreysWork_linearScale
    (p : Nat.Primes) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => sourceHorizontalPrimeAdaptiveJeffreysWork p
      (((N + 1 : ℕ) : ℝ) * a)) atTop atTop := by
  have hsucc : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hscale : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) * a) atTop atTop := by
    simpa only [mul_comm] using Tendsto.const_mul_atTop ha hsucc
  have hcoef : 0 < (3 / 5 : ℝ) * Real.log (p : ℝ) := by
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    positivity
  have hlower : Tendsto (fun N : ℕ =>
      ((3 / 5 : ℝ) * Real.log (p : ℝ)) * (((N + 1 : ℕ) : ℝ) * a))
      atTop atTop := Tendsto.const_mul_atTop hcoef hscale
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [hscale.eventually_ge_atTop 1] with N hN
  exact sourceHorizontalPrimeAdaptiveJeffreysWork_linear_lower hN

/-- A multiplicity-labelled Xi zero carries information escape when its conditional reflected
information diverges while both literal abelian source-mass-weighted currents vanish. -/
def SourceHorizontalXiAbelianInformationEscape
    (q : XiZeroCopy) (p : Nat.Primes) : Prop :=
  let a := |primeDepthBVWoldXiCenteredRate q.1|
  Tendsto (fun N : ℕ => sourceHorizontalPrimeAdaptiveJeffreysWork p
      (((N + 1 : ℕ) : ℝ) * a)) atTop atTop ∧
    Tendsto (fun N : ℕ =>
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianForwardParameters a (abs_nonneg _)
            (sourceHorizontalXiCenteredRate_abs_lt_one q)) p (N + 1) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((N + 1 : ℕ) : ℝ) * a))
      atTop (nhds 0) ∧
    Tendsto (fun N : ℕ =>
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianReverseParameters a (abs_nonneg _)) p (N + 1) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((N + 1 : ℕ) : ℝ) * a))
      atTop (nhds 0)

/-- Local classification: information escape occurs exactly for an off-critical Xi copy. -/
theorem sourceHorizontalXiAbelianInformationEscape_iff_re_ne_half
    (q : XiZeroCopy) (p : Nat.Primes) :
    SourceHorizontalXiAbelianInformationEscape q p ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  let a := |primeDepthBVWoldXiCenteredRate q.1|
  constructor
  · intro hescape hline
    have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    have htop := hescape.1
    have hone := (Filter.tendsto_atTop.1 htop) 1
    obtain ⟨N, hN⟩ := hone.exists
    simp [hrate, sourceHorizontalPrimeAdaptiveJeffreysWork] at hN
    norm_num at hN
  · intro hline
    have hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
      intro hzero
      exact hline ((primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hzero)
    have ha : 0 < a := abs_pos.mpr hrate
    exact ⟨
      tendsto_sourceHorizontalPrimeAdaptiveJeffreysWork_linearScale p ha,
      sourceHorizontalXiAbelianMassWeightedAdaptiveWork_evacuates q p⟩

/-- Failure of RH is exactly existence of a divisor copy whose unbounded conditional information
is hidden in asymptotically vanishing literal source mass. -/
theorem not_riemannHypothesis_iff_exists_sourceHorizontalXiAbelianInformationEscape
    (p : Nat.Primes) :
    ¬ RiemannHypothesis ↔
      ∃ q : XiZeroCopy, SourceHorizontalXiAbelianInformationEscape q p := by
  constructor
  · intro hnot
    have hexists : ∃ rho : XiDivisorSupport, (rho : ℂ).re ≠ 1 / 2 := by
      by_contra hnone
      push Not at hnone
      exact hnot (riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half hnone)
    obtain ⟨rho, hrho⟩ := hexists
    let q : XiZeroCopy := ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
    exact ⟨q,
      (sourceHorizontalXiAbelianInformationEscape_iff_re_ne_half q p).2 hrho⟩
  · rintro ⟨q, hescape⟩ hRH
    exact (sourceHorizontalXiAbelianInformationEscape_iff_re_ne_half q p).1 hescape
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)

/-- Cross-route synthesis: rare-event information escape and adversarial escape from every moving
finite prime-tail approximation are the same global obstruction. -/
theorem exists_sourceHorizontalXiAbelianInformationEscape_iff_primeTailDiagonalEscape
    (p : Nat.Primes) {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    (∃ q : XiZeroCopy, SourceHorizontalXiAbelianInformationEscape q p) ↔
      XiMassCriticalPrimeTailFiniteStageDiagonalEscape a sigma := by
  calc
    (∃ q : XiZeroCopy, SourceHorizontalXiAbelianInformationEscape q p) ↔
        ¬ RiemannHypothesis :=
      (not_riemannHypothesis_iff_exists_sourceHorizontalXiAbelianInformationEscape p).symm
    _ ↔ XiMassCriticalPrimeTailFiniteStageDiagonalEscape a sigma :=
      not_riemannHypothesis_iff_xiMassCriticalPrimeTailFiniteStageDiagonalEscape ha hsigma

/-- The same escape is exactly a nonzero canonical reflection self-intersection charge. -/
theorem exists_sourceHorizontalXiAbelianInformationEscape_iff_exists_reflectionCharge_ne_zero
    (p : Nat.Primes) :
    (∃ q : XiZeroCopy, SourceHorizontalXiAbelianInformationEscape q p) ↔
      ∃ T : ℝ, xiReflectionSelfIntersectionCharge T ≠ 0 := by
  calc
    (∃ q : XiZeroCopy, SourceHorizontalXiAbelianInformationEscape q p) ↔
        ¬ RiemannHypothesis :=
      (not_riemannHypothesis_iff_exists_sourceHorizontalXiAbelianInformationEscape p).symm
    _ ↔ (∃ T : ℝ, xiReflectionSelfIntersectionCharge T ≠ 0) := by
      rw [riemannHypothesis_iff_forall_reflectionSelfIntersectionCharge_eq_zero]
      push Not
      rfl

end

end RHTower
