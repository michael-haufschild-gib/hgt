import GaloisForLFunctions.RHTower.XiMassCriticalPrimeTailFiniteExtinction
import GaloisForLFunctions.RHTower.XiMassTruePrimeCoboundaryBridge
import GaloisForLFunctions.RHTower.XiMassCriticalSafeEulerGreenWeld
import GaloisForLFunctions.RHTower.XiFirstTraceKreinDeterminantUniversality

/-!
# Reflection charge defeats every finite true-prime counterterm

The complete Green tail and moving true-prime cone represent opposite orientations of the same
unbounded source class.  Adding an arbitrary finite prime-power Green packet to the moving cone
and subtracting it from the complete Green current cancels the packet exactly.  What remains is
the sum of the already bounded true-prime/outgoing coboundary and the bounded archimedean face.

Consequently, if one reflection self-intersection charge survives, then the moving true-prime cone
escapes every finite stationary prime-power counterterm.  This strengthens finite-tail extinction:
the obstruction persists after transport from the complete prime-power Green current to the
physical true-prime light cone and is independent of cone depth.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Finite-counterterm conservation law.**  A finite Green packet cancels exactly between the
complete tail and the moving true-prime cone.  The surviving expression is packet-independent and
is the difference of two uniformly bounded coboundary faces. -/
theorem xiMassCriticalTruePrimeFiniteCounterterm_conservation
    {a sigma d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma)
    (u : ℝ) (S : Finset DeningerPrimePowerIndex) :
    (xiMassCriticalTruePrimeCone a sigma d u +
        xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S) +
      (xiMassCriticalPrimeTailGreenCurrent a sigma u -
        xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S) =
      (xiMassCriticalTruePrimeCone a sigma d u -
          xiMassCriticalOutgoingFlux a sigma u) -
        xiMassCriticalOutgoingExplicitFace a sigma u := by
  have hgreen : xiMassCriticalPrimeTailGreenCurrent a sigma u =
      -xiMassCriticalOutgoingExplicitFace a sigma u -
        xiMassCriticalOutgoingFlux a sigma u := by
    calc
      xiMassCriticalPrimeTailGreenCurrent a sigma u =
          -xiMassBottomPrimeIntegral a d ((sigma : ℂ) + (u : ℂ) * I) := by
        rw [xiMassBottomPrimeIntegral_eq_neg_primeTailGreenCurrent
          hdhalf hda hsigma]
        simp
      _ = -(xiMassCriticalOutgoingExplicitFace a sigma u +
          xiMassCriticalOutgoingFlux a sigma u) := by
        rw [xiMassBottomPrimeIntegral_eq_explicitFace_add_outgoingFlux
          hdhalf hda hsigma]
      _ = -xiMassCriticalOutgoingExplicitFace a sigma u -
          xiMassCriticalOutgoingFlux a sigma u := by ring
  rw [hgreen]
  ring

/-- The conserved finite-counterterm sum has one uniform bound, independent of the packet and of
future vertical time. -/
theorem exists_norm_xiMassCriticalTruePrimeFiniteCounterterm_conservation_bound
    {a sigma d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) :
    ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → ∀ S : Finset DeningerPrimePowerIndex,
      ‖(xiMassCriticalTruePrimeCone a sigma d u +
            xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S) +
          (xiMassCriticalPrimeTailGreenCurrent a sigma u -
            xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S)‖ ≤ B := by
  obtain ⟨D, hD⟩ :=
    exists_norm_truePrimeCone_sub_outgoingFlux_bound hdhalf hda hsigma
  let F : ℝ :=
    2 * Real.pi * Real.exp (-sigma * xiMassArchPoleFrequency a) +
      3 * (∫ x : ℝ, Real.exp (-(sigma * |x|)))
  refine ⟨D + F, fun u hu S => ?_⟩
  rw [xiMassCriticalTruePrimeFiniteCounterterm_conservation
    hdhalf hda hsigma u S]
  exact (norm_sub_le _ _).trans
    (add_le_add (hD u hu) (by
      simpa only [F] using
        norm_xiMassCriticalOutgoingExplicitFace_le
          (lt_trans hdhalf hda) hsigma u))

/-- **Reflection-charge finite-counterterm no-go.**  If any canonical reflection charge survives,
then every finite stationary prime-power Green counterterm leaves the moving true-prime cone
unbounded on future vertical time. -/
theorem xiMassCriticalTruePrimeCone_add_finiteGreen_unbounded_of_reflectionCharge_ne_zero
    {a sigma d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma)
    {T : ℝ} (hcharge : xiReflectionSelfIntersectionCharge T ≠ 0)
    (S : Finset DeningerPrimePowerIndex) (C : ℝ) :
    ∃ u : ℝ, 0 ≤ u ∧ C <
      ‖xiMassCriticalTruePrimeCone a sigma d u +
        xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S‖ := by
  obtain ⟨B, hB⟩ :=
    exists_norm_xiMassCriticalTruePrimeFiniteCounterterm_conservation_bound
      hdhalf hda hsigma
  obtain ⟨u, hu, htail⟩ :=
    xiMassCriticalPrimeTailGreenRemainder_unbounded_of_reflectionCharge_ne_zero
      (lt_trans hdhalf hda) hsigma hcharge S (C + B)
  refine ⟨u, hu, ?_⟩
  let X : ℂ := xiMassCriticalTruePrimeCone a sigma d u +
    xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S
  let R : ℂ := xiMassCriticalPrimeTailGreenCurrent a sigma u -
    xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S
  have hconserved : ‖X + R‖ ≤ B := by
    simpa only [X, R] using hB u hu S
  have htriangle : ‖R‖ ≤ ‖X + R‖ + ‖X‖ := by
    calc
      ‖R‖ = ‖(X + R) - X‖ := by ring_nf
      _ ≤ ‖X + R‖ + ‖X‖ := norm_sub_le _ _
  have htail' : C + B < ‖R‖ := by
    simpa only [R] using htail
  have hupper : ‖R‖ ≤ B + ‖X‖ :=
    htriangle.trans (add_le_add hconserved le_rfl)
  dsimp only [X] at hupper ⊢
  linarith

/-- The same escape law read entirely in the first-trace/Krein chart: nonzero normalized
transverse determinant charge cannot be absorbed by any finite stationary prime counterterm. -/
theorem xiMassCriticalTruePrimeCone_add_finiteGreen_unbounded_of_firstTraceKreinCharge_ne_zero
    {a sigma d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma)
    {T : ℝ} (hcharge :
      hedenmalmSquarefreeFirstTraceKreinDeterminantCharge T ≠ 0)
    (S : Finset DeningerPrimePowerIndex) (C : ℝ) :
    ∃ u : ℝ, 0 ≤ u ∧ C <
      ‖xiMassCriticalTruePrimeCone a sigma d u +
        xiMassCriticalPrimeTailGreenCurrentFinite a sigma u S‖ := by
  have hreflection : xiReflectionSelfIntersectionCharge T ≠ 0 := by
    intro hzero
    apply hcharge
    rw [hedenmalmSquarefreeFirstTraceKreinDeterminantCharge_eq_reflectionCharge,
      hzero]
    norm_num
  exact
    xiMassCriticalTruePrimeCone_add_finiteGreen_unbounded_of_reflectionCharge_ne_zero
      hdhalf hda hsigma hreflection S C

end

end RHTower
