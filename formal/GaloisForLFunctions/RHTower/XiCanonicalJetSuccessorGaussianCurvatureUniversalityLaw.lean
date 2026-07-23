import GaloisForLFunctions.RHTower.XiArbitraryJetSuccessorGaussianCurvatureUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeLaplaceGramStrict
import GaloisForLFunctions.RHTower.VonMangoldtHardyEventualStrictLaw
import GaloisForLFunctions.RHTower.XiEvenShiftRawDefectCofiniteHilbertReconstruction

/-!
# Canonical completed-Xi jets with unconditional successor-aperture curvature

The initial derivative dictionary `0, ..., d - 1` is collision-free.  Relabeling it by successor
apertures gives `1, ..., d`, so the transverse nonzero-aperture condition also disappears.
Choosing packet size `N + 2` discharges the sharp rank-two condition.  The existing
HTGeometry/HilbertMetric connector then supplies the complete complex and real cofinite
reconstruction, Möbius exact-Hilbert, Gaussian strict-curvature, concavity, and nonnormality
package at every depth, prime pair, and nonnegative metric scale.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open Filter Set
open scoped ComplexOrder

/-- Canonical initial completed-Xi derivative dictionary. -/
def xiCanonicalDerivativeOrder (d : ℕ) : Fin d → ℕ :=
  fun j => j

/-- Canonical derivative orders have no collisions. -/
theorem xiCanonicalDerivativeOrder_injective (d : ℕ) :
    Function.Injective (xiCanonicalDerivativeOrder d) := by
  intro i j hij
  exact Fin.ext hij

/-- The associated successor aperture is the positive label `j + 1`. -/
theorem xiCanonicalDerivativeOrder_successorAperture_apply
    {d : ℕ} (j : Fin d) :
    xiDerivativeOrderSuccessorAperture
        (xiCanonicalDerivativeOrder d) j = j + 1 :=
  rfl

/-- Positive integral aperture packet canonically attached to the initial Xi jet dictionary. -/
def xiCanonicalPositiveAperture (d : ℕ) : Fin d → ℕ :=
  xiDerivativeOrderSuccessorAperture (xiCanonicalDerivativeOrder d)

/-- Canonical positive apertures have no collisions. -/
theorem xiCanonicalPositiveAperture_injective (d : ℕ) :
    Function.Injective (xiCanonicalPositiveAperture d) :=
  (xiDerivativeOrderSuccessorAperture_injective_iff
    (xiCanonicalDerivativeOrder d)).2
      (xiCanonicalDerivativeOrder_injective d)

/-- Canonical successor apertures exclude the zero boundary. -/
theorem xiCanonicalPositiveAperture_ne_zero
    {d : ℕ} (j : Fin d) :
    xiCanonicalPositiveAperture d j ≠ 0 :=
  xiDerivativeOrderSuccessorAperture_ne_zero
    (xiCanonicalDerivativeOrder d) j

/-- Canonical successor apertures lie in the strict positive chamber. -/
theorem xiCanonicalPositiveAperture_pos
    {d : ℕ} (j : Fin d) :
    0 < xiCanonicalPositiveAperture d j :=
  Nat.pos_of_ne_zero (xiCanonicalPositiveAperture_ne_zero j)

/-- Canonical arbitrary Xi jets admit exact complex cofinite Hilbert reconstruction with no
collision hypothesis. -/
theorem xiCanonicalDerivativeOrder_cofiniteHilbertReconstruction (d : ℕ) :
    CofiniteEvaluationHilbertReconstruction
      (xiDerivativeOrderFamily (xiCanonicalDerivativeOrder d)) :=
  (xiDerivativeOrderCofiniteHilbertReconstruction_iff_injective
    (xiCanonicalDerivativeOrder d)).2
      (xiCanonicalDerivativeOrder_injective d)

/-- Canonical Xi jets satisfy the complete finite evaluation/dual-recovery/strict-Gram
interface. -/
theorem xiCanonicalDerivativeOrder_finiteEvaluationHilbertReconstruction
    (d : ℕ) :
    FiniteEvaluationHilbertReconstruction
      (xiDerivativeOrderFamily (xiCanonicalDerivativeOrder d)) :=
  (exists_injective_xiDerivativeOrderEvaluationHilbertReconstruction_iff
    (xiCanonicalDerivativeOrder d)).2
      (xiCanonicalDerivativeOrder_injective d)

/-- Canonical Xi derivative functions are algebraically independent at every finite depth. -/
theorem xiCanonicalDerivativeOrder_algebraicIndependent (d : ℕ) :
    AlgebraicIndependent ℂ
      (xiDerivativeOrderFamily (xiCanonicalDerivativeOrder d)) :=
  (algebraicIndependent_xiDerivativeOrderFamily_iff_injective
    (xiCanonicalDerivativeOrder d)).2
      (xiCanonicalDerivativeOrder_injective d)

/-- Canonical Xi derivative functions are linearly independent at every finite depth. -/
theorem xiCanonicalDerivativeOrder_linearIndependent (d : ℕ) :
    LinearIndependent ℂ
      (xiDerivativeOrderFamily (xiCanonicalDerivativeOrder d)) :=
  (linearIndependent_xiDerivativeOrderFamily_iff_injective
    (xiCanonicalDerivativeOrder d)).2
      (xiCanonicalDerivativeOrder_injective d)

/-- Canonical Xi jets also satisfy the real-channel cofinite reconstruction interface. -/
theorem xiCanonicalDerivativeOrder_realChannelCofiniteHilbertReconstruction
    (d : ℕ) :
    XiDerivativeOrderRealChannelCofiniteHilbertReconstruction
      (xiCanonicalDerivativeOrder d) :=
  (xiDerivativeOrderRealChannelCofiniteHilbertReconstruction_iff_injective
    (xiCanonicalDerivativeOrder d)).2
      (xiCanonicalDerivativeOrder_injective d)

/-- Canonical Xi jets satisfy the full complex-coefficient real-channel reconstruction
interface. -/
theorem
    xiCanonicalDerivativeOrder_complexCoefficientRealChannelCofiniteHilbertReconstruction
    (d : ℕ) :
    XiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction
      (xiCanonicalDerivativeOrder d) :=
  (xiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction_iff_injective
    (xiCanonicalDerivativeOrder d)).2
      (xiCanonicalDerivativeOrder_injective d)

/-- Their positive successor apertures admit deletion-robust transverse reconstruction at every
jet depth. -/
theorem xiCanonicalDerivativeOrder_successorApertureCofiniteHilbertReconstruction
    (d m : ℕ) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction
      (xiDerivativeOrderSuccessorAperture
        (xiCanonicalDerivativeOrder d)) m :=
  (xiDerivativeOrderCofiniteHilbertReconstruction_iff_successorApertureCofiniteHilbertReconstruction
    (xiCanonicalDerivativeOrder d) m).1
      (xiCanonicalDerivativeOrder_cofiniteHilbertReconstruction d)

/-- The same canonical positive grades discharge the raw even-shift Xi log-derivative defect
reconstruction interface. -/
theorem
    xiCanonicalPositiveAperture_evenShiftRawLogDerivDefectCofiniteHilbertReconstruction
    (d : ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction
      (xiCanonicalPositiveAperture d) :=
  (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff
    (xiCanonicalPositiveAperture d)).2
      ⟨xiCanonicalPositiveAperture_injective d,
        xiCanonicalPositiveAperture_ne_zero⟩

/-- At every prime, canonical positive apertures satisfy finite continuous Möbius coefficient
reconstruction. -/
theorem xiCanonicalPositiveAperture_mobiusCanonicalReconstruction
    (d : ℕ) (p : Nat.Primes) :
    XiMobiusPrimeIntegralApertureCanonicalReconstruction
      (xiCanonicalPositiveAperture d) p :=
  (xiMobiusPrimeIntegralApertureCanonicalReconstruction_iff_injective_ne_zero
    (xiCanonicalPositiveAperture d) p).2
      ⟨xiCanonicalPositiveAperture_injective d,
        xiCanonicalPositiveAperture_ne_zero⟩

/-- At every prime, the continuous Möbius--Szegő Gram of canonical positive apertures is strictly
positive definite. -/
theorem xiCanonicalPositiveAperture_mobiusSzegoGram_posDef
    (d : ℕ) (p : Nat.Primes) :
    (xiMobiusPrimeIntegralApertureSzegoGramMatrix
      (xiCanonicalPositiveAperture d) p).PosDef :=
  (xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_injective_ne_zero
    (xiCanonicalPositiveAperture d) p).2
      ⟨xiCanonicalPositiveAperture_injective d,
        xiCanonicalPositiveAperture_ne_zero⟩

/-- The actual von Mangoldt Laplace Gram is strictly positive on the same canonical successor
packet. -/
theorem xiCanonicalPositiveAperture_vonMangoldtPrimeLaplaceGram_posDef
    (d : ℕ) :
    (vonMangoldtPrimeLaplaceGram
      (fun j => (xiCanonicalPositiveAperture d j : ℝ))).PosDef := by
  apply vonMangoldtPrimeLaplaceGram_posDef
  · intro j
    exact_mod_cast xiCanonicalPositiveAperture_pos j
  · intro i j hij
    apply xiCanonicalPositiveAperture_injective d
    exact Nat.cast_injective hij

/-- Hence every canonical successor packet has strictly positive resolved Euler volume. -/
theorem det_xiCanonicalPositiveAperture_vonMangoldtPrimeLaplaceGram_pos
    (d : ℕ) :
    0 < (vonMangoldtPrimeLaplaceGram
      (fun j => (xiCanonicalPositiveAperture d j : ℝ))).det :=
  (xiCanonicalPositiveAperture_vonMangoldtPrimeLaplaceGram_posDef d).det_pos

/-- On canonical successor nodes, the scaled von Mangoldt Hardy Gram is eventually strictly
positive at the Hardy boundary without node hypotheses. -/
theorem
    eventually_xiCanonicalPositiveAperture_scaledVonMangoldtPrimeRightHalfPlaneGram_posDef
    (d : ℕ) :
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      (scaledVonMangoldtPrimeRightHalfPlaneGram t
        (fun j => (xiCanonicalPositiveAperture d j : ℂ))).PosDef := by
  apply eventually_scaledVonMangoldtPrimeRightHalfPlaneGram_posDef
  · intro j
    change 0 < ((xiCanonicalPositiveAperture d j : ℕ) : ℝ)
    exact_mod_cast xiCanonicalPositiveAperture_pos j
  · intro i j hij
    apply xiCanonicalPositiveAperture_injective d
    exact Nat.cast_injective hij

/-- **Unconditional canonical successor-curvature universality.**  For the first `N + 2`
completed-Xi derivatives, the full exact-Hilbert Gaussian-curvature certificate exists
simultaneously at every source prime, metric prime, jet depth, and nonnegative scale. -/
theorem xiCanonicalDerivativeOrder_every_successorGaussianCurvatureCertificate
    (N : ℕ) :
    ∀ (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
      XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        (xiCanonicalDerivativeOrder (N + 2))
        sourcePrime metricPrime m t :=
  (xiDerivativeOrder_injective_and_two_le_iff_every_successorGaussianCurvatureCertificate
    (xiCanonicalDerivativeOrder (N + 2))).1
      ⟨xiCanonicalDerivativeOrder_injective (N + 2), by omega⟩

end

end RHTower
