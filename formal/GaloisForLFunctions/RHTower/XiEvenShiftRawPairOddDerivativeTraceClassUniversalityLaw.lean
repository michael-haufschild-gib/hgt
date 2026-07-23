import GaloisForLFunctions.RHTower.XiEvenShiftRawPairGaussianCurvatureUniversalityLaw
import GaloisForLFunctions.RHTower.XiPositiveDerivativeOrderTraceClassIntrinsicDimensionUniversalityLaw

/-!
# Raw even-shift edges and the odd predecessor derivative dictionary

For a raw completed-Xi grade `g`, the canonical odd derivative order `2g - 1` has successor
aperture `2g` on the nonzero-grade phase.  This identifies the doubled aperture used by the raw
edge/vertex curvature law with the positive successor aperture used by the derivative-order
trace-class/intrinsic-dimension law.
-/

namespace RHTower

noncomputable section

/-- Canonical derivative-order dictionary whose successor is the doubled raw aperture. -/
def xiEvenShiftOddPredecessorDerivativeOrder
    {N : ℕ} (grade : Fin N → ℕ) : Fin N → ℕ :=
  fun v => 2 * grade v - 1

/-- On the nonzero-grade stratum, the successor of the odd predecessor is exactly the doubled
raw aperture. -/
theorem xiEvenShiftOddPredecessorDerivativeOrder_successorAperture
    {N : ℕ} (grade : Fin N → ℕ) (hgrade : ∀ v, grade v ≠ 0) :
    xiDerivativeOrderSuccessorAperture
        (xiEvenShiftOddPredecessorDerivativeOrder grade) =
      fun v => 2 * grade v := by
  funext v
  simp only [xiDerivativeOrderSuccessorAperture,
    xiEvenShiftOddPredecessorDerivativeOrder]
  have hpositive : 0 < grade v := Nat.pos_of_ne_zero (hgrade v)
  omega

/-- Odd-predecessor relabeling preserves exactly the grade collision relation. -/
theorem xiEvenShiftOddPredecessorDerivativeOrder_injective_iff
    {N : ℕ} (grade : Fin N → ℕ) :
    Function.Injective (xiEvenShiftOddPredecessorDerivativeOrder grade) ↔
      Function.Injective grade := by
  constructor
  · intro horder i j hij
    apply horder
    simp [xiEvenShiftOddPredecessorDerivativeOrder, hij]
  · intro hgrade i j hij
    apply hgrade
    simp only [xiEvenShiftOddPredecessorDerivativeOrder] at hij
    omega

/-- Odd-predecessor positivity is exactly raw-grade nonvanishing. -/
theorem xiEvenShiftOddPredecessorDerivativeOrder_ne_zero_iff
    {N : ℕ} (grade : Fin N → ℕ) (v : Fin N) :
    xiEvenShiftOddPredecessorDerivativeOrder grade v ≠ 0 ↔
      grade v ≠ 0 := by
  simp only [xiEvenShiftOddPredecessorDerivativeOrder]
  omega

/-- **Raw-edge/odd-derivative trace-class universality law.**  At independent stored primes,
depths, and nonnegative scales, a complete raw arbitrary-edge/full-vertex Gaussian certificate
is exactly the positive trace-class/intrinsic certificate on its canonical odd derivative-order
dictionary plus independence of the selected raw edge family.  The successor aperture on the
right is literally the doubled raw aperture on the certificate phase. -/
theorem
    xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_oddDerivativeTraceClassIntrinsic_and_incidence
    {N e : ℕ} (grade : Fin N → ℕ) (tail head : Fin e → Fin N)
    (rawSourcePrime rawMetricPrime : Nat.Primes) (rawDepth : ℕ)
    (rawScale : ℝ) (hrawScale : 0 ≤ rawScale)
    (traceSourcePrime traceCurvaturePrime traceIntrinsicPrime : Nat.Primes)
    (traceDepth : ℕ) (traceScale : ℝ) (htraceScale : 0 ≤ traceScale) :
    XiEvenShiftRawPairGaussianCurvatureCertificate
        grade tail head rawSourcePrime rawMetricPrime rawDepth rawScale ↔
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
          (xiEvenShiftOddPredecessorDerivativeOrder grade)
          traceSourcePrime traceCurvaturePrime traceIntrinsicPrime
          traceDepth traceScale ∧
        XiEvenShiftRawPairIncidenceIndependent grade tail head := by
  constructor
  · intro hraw
    have hstratum :=
      (xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_vertex_and_incidence_and_two_le
        grade tail head rawSourcePrime rawMetricPrime rawDepth rawScale hrawScale).2 hraw
    have horder :
        (Function.Injective (xiEvenShiftOddPredecessorDerivativeOrder grade) ∧
            ∀ v, xiEvenShiftOddPredecessorDerivativeOrder grade v ≠ 0) ∧
          2 ≤ N := by
      exact
        ⟨⟨(xiEvenShiftOddPredecessorDerivativeOrder_injective_iff grade).2
              hstratum.1.1.1,
            fun v =>
              (xiEvenShiftOddPredecessorDerivativeOrder_ne_zero_iff grade v).2
                (hstratum.1.1.2 v)⟩,
          hstratum.2⟩
    exact
      ⟨(xiPositiveDerivativeOrder_traceClassIntrinsicDimensionCertificate_iff
          (xiEvenShiftOddPredecessorDerivativeOrder grade)
          traceSourcePrime traceCurvaturePrime traceIntrinsicPrime
          traceDepth traceScale htraceScale).1 horder,
        hstratum.1.2⟩
  · rintro ⟨htrace, hincidence⟩
    have horder :=
      (xiPositiveDerivativeOrder_traceClassIntrinsicDimensionCertificate_iff
        (xiEvenShiftOddPredecessorDerivativeOrder grade)
        traceSourcePrime traceCurvaturePrime traceIntrinsicPrime
        traceDepth traceScale htraceScale).2 htrace
    have hstratum :
        ((Function.Injective grade ∧ ∀ v, grade v ≠ 0) ∧
            XiEvenShiftRawPairIncidenceIndependent grade tail head) ∧
          2 ≤ N := by
      exact
        ⟨⟨⟨(xiEvenShiftOddPredecessorDerivativeOrder_injective_iff grade).1
                horder.1.1,
              fun v =>
                (xiEvenShiftOddPredecessorDerivativeOrder_ne_zero_iff grade v).1
                  (horder.1.2 v)⟩,
            hincidence⟩,
          horder.2⟩
    exact
      (xiEvenShiftRawPair_gaussianCurvatureCertificate_iff_vertex_and_incidence_and_two_le
        grade tail head rawSourcePrime rawMetricPrime rawDepth rawScale hrawScale).1 hstratum

end

end RHTower
