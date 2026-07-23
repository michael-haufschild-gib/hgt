import GaloisForLFunctions.RHTower.SoninSemilocalCyclicWeylDescent
import GaloisForLFunctions.RHTower.SoninSemilocalWeylSourceReplacementLaw

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-! The finite source test separating the projection-correction trace from Weyl generators is
independent of the Hilbert--Schmidt probe used to perform cyclic descent. -/

/-- **Probe-universal semilocal source-separation law.** One finite prime-power test separates the
failed projection-correction trace from the cyclic tangent trace produced by every nonzero
Hilbert--Schmidt probe on every complex Hilbert space. -/
theorem exists_finiteSoninSemilocalRelativeTrace_ne_everyHilbertSchmidtCyclicSourceGenerator :
    ∃ f : SoninPrimePowerTest,
      ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (C : H →L[ℂ] H), IsHilbertSchmidt C → C ≠ 0 →
        canonicalFiniteSoninSemilocalRelativeTrace f ≠
          f.sum (fun pk w =>
            w * opTrace
              (normalizedHilbertSchmidtCentralTangentCarrier C
                soninSemilocalPrimeFluxCoefficient pk)) := by
  obtain ⟨f, hweyl, _hwigner⟩ :=
    exists_finiteSoninSemilocalRelativeTrace_ne_allWeylSourceGenerators
  refine ⟨f, ?_⟩
  intro H _ _ _ C hC hCne
  have hself : hsInner C C ≠ 0 := by
    rw [GaloisForLFunctions.HTGeometry.hsInner_self_eq_ofReal_hsNormSq hC]
    exact Complex.ofReal_ne_zero.mpr
      (fun hzero => hCne ((hsNormSq_eq_zero_iff hC).mp hzero))
  intro heq
  apply hweyl
  calc
    canonicalFiniteSoninSemilocalRelativeTrace f =
        f.sum (fun pk w =>
          w * opTrace
            (normalizedHilbertSchmidtCentralTangentCarrier C
              soninSemilocalPrimeFluxCoefficient pk)) := heq
    _ = f.sum (fun pk w =>
        w * (Complex.I * deriv (soninSemilocalWeylFluxOrbit pk) 0)) := by
      apply Finsupp.sum_congr
      intro pk _hpk
      rw [opTrace_normalizedHilbertSchmidtCentralTangentCarrier hself,
        I_mul_deriv_soninSemilocalWeylFluxOrbit_zero]

end

end RHTower
