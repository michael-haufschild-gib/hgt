import GaloisForLFunctions.RHTower.AnchoredCalkinCriticalLineUniversalityLaw
import GaloisForLFunctions.RHTower.XiPrimeSeamEulerOrientationReflection

/-!
# Anchored Calkin FE--Schwarz orbit universality

The anchored two-prime commutator inherits the exact adjoint/negation table of every finite Euler
packet.  Combining this with the anchored critical-line classifier makes cofinal Calkin decay,
all-partner compactness, and the calibrated Hurwitz seam invariant on the full four-point
functional-equation/Schwarz orbit.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The three anchored critical-line diagnostics are invariant under all nontrivial
functional-equation/Schwarz orbit moves. -/
def AnchoredCalkinFESchwarzOrbitInvariantAt (a : ℝ) (rho : ℂ) : Prop :=
  (CofinalAnchoredEulerCompressionEssentialNormDecayAt a rho ↔
    CofinalAnchoredEulerCompressionEssentialNormDecayAt a ((starRingEnd ℂ) rho)) ∧
  (CofinalAnchoredEulerCompressionEssentialNormDecayAt a rho ↔
    CofinalAnchoredEulerCompressionEssentialNormDecayAt a (1 - rho)) ∧
  (CofinalAnchoredEulerCompressionEssentialNormDecayAt a rho ↔
    CofinalAnchoredEulerCompressionEssentialNormDecayAt a
      (1 - (starRingEnd ℂ) rho)) ∧
  (AllAnchoredEulerCompressionCommutatorsCompactAt a rho ↔
    AllAnchoredEulerCompressionCommutatorsCompactAt a ((starRingEnd ℂ) rho)) ∧
  (AllAnchoredEulerCompressionCommutatorsCompactAt a rho ↔
    AllAnchoredEulerCompressionCommutatorsCompactAt a (1 - rho)) ∧
  (AllAnchoredEulerCompressionCommutatorsCompactAt a rho ↔
    AllAnchoredEulerCompressionCommutatorsCompactAt a
      (1 - (starRingEnd ℂ) rho)) ∧
  (xiHurwitzPrimeTwoEulerBoundarySeam rho = 0 ↔
    xiHurwitzPrimeTwoEulerBoundarySeam ((starRingEnd ℂ) rho) = 0) ∧
  (xiHurwitzPrimeTwoEulerBoundarySeam rho = 0 ↔
    xiHurwitzPrimeTwoEulerBoundarySeam (1 - rho) = 0) ∧
  (xiHurwitzPrimeTwoEulerBoundarySeam rho = 0 ↔
    xiHurwitzPrimeTwoEulerBoundarySeam (1 - (starRingEnd ℂ) rho) = 0)

/-- **Anchored Calkin FE--Schwarz orbit universality law.**  At every open-strip point, the
pointwise anchored Calkin/Hurwitz classifier extends to the full four-point reflection orbit.
Every anchored prime-pair commutator transforms by the exact adjoint/negation table, and all three
critical-line diagnostics are orbit invariant. -/
theorem anchoredCalkin_feSchwarzOrbitUniversality
    {a : ℝ} (ha : 0 < a) {rho : ℂ}
    (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ((CofinalAnchoredEulerCompressionEssentialNormDecayAt a rho ↔
        rho.re = 1 / 2) ∧
      (AllAnchoredEulerCompressionCommutatorsCompactAt a rho ↔
        rho.re = 1 / 2) ∧
      (xiHurwitzPrimeTwoEulerBoundarySeam rho = 0 ↔
        rho.re = 1 / 2)) ∧
    (∀ q : ℕ, q.Prime →
      firstPrimeAnchoredEulerCompressionCommutator a
          (1 - (starRingEnd ℂ) rho) q =
          -firstPrimeAnchoredEulerCompressionCommutator a rho q ∧
      firstPrimeAnchoredEulerCompressionCommutator a
          ((starRingEnd ℂ) rho) q =
          -ContinuousLinearMap.adjoint
            (firstPrimeAnchoredEulerCompressionCommutator a rho q) ∧
      firstPrimeAnchoredEulerCompressionCommutator a (1 - rho) q =
          ContinuousLinearMap.adjoint
            (firstPrimeAnchoredEulerCompressionCommutator a rho q)) ∧
    AnchoredCalkinFESchwarzOrbitInvariantAt a rho := by
  have hbase := anchoredCalkin_criticalLineUniversality ha hstrip
  have hconjStrip :
      0 < ((starRingEnd ℂ) rho).re ∧ ((starRingEnd ℂ) rho).re < 1 := by
    simpa using hstrip
  have hfeStrip : 0 < (1 - rho).re ∧ (1 - rho).re < 1 := by
    constructor <;> simp only [sub_re, one_re] <;> linarith [hstrip.1, hstrip.2]
  have hlineReflectStrip :
      0 < (1 - (starRingEnd ℂ) rho).re ∧
        (1 - (starRingEnd ℂ) rho).re < 1 := by
    constructor <;> simp only [sub_re, one_re, Complex.conj_re] <;>
      linarith [hstrip.1, hstrip.2]
  have hconj :=
    anchoredCalkin_criticalLineUniversality ha hconjStrip
  have hfe :=
    anchoredCalkin_criticalLineUniversality ha hfeStrip
  have hlineReflect :=
    anchoredCalkin_criticalLineUniversality ha hlineReflectStrip
  have hconjLine :
      ((starRingEnd ℂ) rho).re = 1 / 2 ↔ rho.re = 1 / 2 := by
    simp
  have hfeLine : (1 - rho).re = 1 / 2 ↔ rho.re = 1 / 2 := by
    simp only [sub_re, one_re]
    constructor <;> intro h <;> linarith
  have hlineReflectLine :
      (1 - (starRingEnd ℂ) rho).re = 1 / 2 ↔ rho.re = 1 / 2 := by
    simp only [sub_re, one_re, Complex.conj_re]
    constructor <;> intro h <;> linarith
  refine ⟨hbase, ?_, ?_⟩
  · intro q hq
    have hp : ∀ i, (firstPrimeAnchoredPacket q i).Prime :=
      firstPrimeAnchoredPacket_prime hq
    constructor
    · change orbitwiseFinitePrimeEulerCompressionCommutator a
          (firstPrimeAnchoredPacket q) (1 - (starRingEnd ℂ) rho) =
        -orbitwiseFinitePrimeEulerCompressionCommutator a
          (firstPrimeAnchoredPacket q) rho
      exact orbitwiseFinitePrimeEulerCompressionCommutator_lineReflect
        a (firstPrimeAnchoredPacket q) hp rho
    constructor
    · change orbitwiseFinitePrimeEulerCompressionCommutator a
          (firstPrimeAnchoredPacket q) ((starRingEnd ℂ) rho) =
        -ContinuousLinearMap.adjoint
          (orbitwiseFinitePrimeEulerCompressionCommutator a
            (firstPrimeAnchoredPacket q) rho)
      have hadjoint :=
        adjoint_orbitwiseFinitePrimeEulerCompressionCommutator
          a (firstPrimeAnchoredPacket q) hp rho
      have h := congrArg Neg.neg hadjoint
      simpa only [neg_neg] using h.symm
    · change orbitwiseFinitePrimeEulerCompressionCommutator a
          (firstPrimeAnchoredPacket q) (1 - rho) =
        ContinuousLinearMap.adjoint
          (orbitwiseFinitePrimeEulerCompressionCommutator a
            (firstPrimeAnchoredPacket q) rho)
      exact orbitwiseFinitePrimeEulerCompressionCommutator_one_sub
        a (firstPrimeAnchoredPacket q) hp rho
  · unfold AnchoredCalkinFESchwarzOrbitInvariantAt
    have hconjDecay := hconj.1.trans hconjLine
    have hfeDecay := hfe.1.trans hfeLine
    have hlineDecay := hlineReflect.1.trans hlineReflectLine
    have hconjCompact := hconj.2.1.trans hconjLine
    have hfeCompact := hfe.2.1.trans hfeLine
    have hlineCompact := hlineReflect.2.1.trans hlineReflectLine
    have hconjSeam := hconj.2.2.trans hconjLine
    have hfeSeam := hfe.2.2.trans hfeLine
    have hlineSeam := hlineReflect.2.2.trans hlineReflectLine
    exact ⟨hbase.1.trans hconjDecay.symm,
      hbase.1.trans hfeDecay.symm,
      hbase.1.trans hlineDecay.symm,
      hbase.2.1.trans hconjCompact.symm,
      hbase.2.1.trans hfeCompact.symm,
      hbase.2.1.trans hlineCompact.symm,
      hbase.2.2.trans hconjSeam.symm,
      hbase.2.2.trans hfeSeam.symm,
      hbase.2.2.trans hlineSeam.symm⟩

end

end RHTower
