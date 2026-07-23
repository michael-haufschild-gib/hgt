import GaloisForLFunctions.RHTower.VonMangoldtGammaBetaReflectionPositivityGapUniversalityLaw
import GaloisForLFunctions.RHTower.VonMangoldtGammaBoundaryDisplacementUniversalityLaw

/-!
# Von Mangoldt--Gamma boundary/Beta-reflection fracture universality

At every sufficiently large displacement, the raw von Mangoldt--Gamma source lies in its complete
finite-energy, all-moment, all-packet-positive universal boundary phase.  Nevertheless its
canonical factorial/Beta reflection is already non-positive-semidefinite on the first separated
even-order packet.  Hence the reflection cannot preserve positivity on the universal raw phase.
-/

open Filter

namespace RHTower

noncomputable section

/-- **Von Mangoldt--Gamma boundary/Beta-reflection fracture universality law.**  Eventually the
entire positive-displacement boundary certificate holds, its first separated even-order raw Gram
is positive definite, and the canonical factorial/Beta reflection of that same packet is not
positive semidefinite. -/
theorem vonMangoldtGammaBoundary_betaReflectionFractureUniversality :
    ∀ᶠ x : ℝ in atTop,
      VonMangoldtGammaBoundaryDisplacementUniversalCertificate x ∧
        (vonMangoldtGammaCofinalBianchiGram x ![0, 2]).PosDef ∧
        0 < (vonMangoldtGammaCofinalBianchiGram x ![0, 2]).det ∧
        ¬ (infiniteVonMangoldtGammaFactorialTraceGram x ![0, 2]).PosSemidef := by
  filter_upwards
    [eventually_gt_atTop (0 : ℝ),
      vonMangoldtGamma_betaReflectionPositivityGapUniversality]
      with x hx hfracture
  exact
    ⟨(positiveDisplacement_iff_vonMangoldtGammaBoundaryUniversalCertificate x).mp hx,
      hfracture⟩

/-- Factorial/Beta reflection does not preserve positive semidefiniteness on the complete
von Mangoldt--Gamma positive-displacement boundary phase. -/
theorem not_forall_vonMangoldtGammaBoundaryCertificate_implies_betaReflectionPosSemidef :
    ¬ ∀ x : ℝ,
      VonMangoldtGammaBoundaryDisplacementUniversalCertificate x →
        (infiniteVonMangoldtGammaFactorialTraceGram x ![0, 2]).PosSemidef := by
  intro hpreserve
  obtain ⟨x, hcertificate, _hraw, _hdet, hreflection⟩ :=
    vonMangoldtGammaBoundary_betaReflectionFractureUniversality.exists
  exact hreflection (hpreserve x hcertificate)

end

end RHTower
