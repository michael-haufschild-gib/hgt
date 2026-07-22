import GaloisForLFunctions.RHTower.SoninSemilocalTraceObstruction
import GaloisForLFunctions.RHTower.SoninSemilocalWeylGenerator

/-!
# Sonin semilocal Weyl-source replacement law

The bounded projection-correction pairing cannot reproduce the von Mangoldt source on every
finite prime-power test.  On one separating test, both phase constructions remain exact: the
identity tangent of each bounded Weyl flux orbit and every real-parameter Wigner--Smith charge
sum reproduce the source and therefore differ from the failed geometric scalarization.
-/

namespace RHTower

noncomputable section

/-- **Semilocal source replacement law.**  One finite test simultaneously separates the failed
projection-correction relative trace from the exact Weyl tangent generator and from every
Wigner--Smith phase-charge generator. -/
theorem exists_finiteSoninSemilocalRelativeTrace_ne_allWeylSourceGenerators :
    ∃ f : SoninPrimePowerTest,
      canonicalFiniteSoninSemilocalRelativeTrace f ≠
        f.sum (fun pk w =>
          w * (Complex.I * deriv (soninSemilocalWeylFluxOrbit pk) 0)) ∧
      ∀ t : ℝ,
        canonicalFiniteSoninSemilocalRelativeTrace f ≠
          f.sum (fun pk w =>
            w * (soninSemilocalLogPrimePowerCoefficient pk *
              soninSemilocalWignerSmithCharge pk t)) := by
  obtain ⟨f, hf⟩ := exists_finiteSoninSemilocalRelativeTrace_ne_vonMangoldt
  refine ⟨f, ?_, ?_⟩
  · rw [← finiteVonMangoldtCentralTrace_eq_sum_weylGenerators]
    exact hf
  · intro t
    rw [← finiteVonMangoldtCentralTrace_eq_sum_wignerSmithCharges f t]
    exact hf

end

end RHTower
