import GaloisForLFunctions.RHTower.XiCofiniteEvaluationReporterUniversalityLaw
import GaloisForLFunctions.RHTower.XiLogDerivReporterIsometricRecovery

/-!
# Cofinite Xi exact-blind data-processing law

The cofinite Xi reporter theorem retains complete decoder data processing after every isometric
encoding, but records logarithmic-source blindness only through conditional information.  Exact
blind-packet recovery normalizes a nonzero source packet and identifies the full original and
encoded kernels.  Choosing both on the same cofinite evaluation packet gives the joint law below.
-/

open scoped ComplexOrder InnerProductSpace

namespace RHTower

open GaloisForLFunctions HTGeometry Module

noncomputable section

universe u v

/-- **Cofinite exact-blind data-processing universality law.**  Outside every finite forbidden set,
one Xi evaluation packet is faithful before and after every isometric encoding; the encoding has
an exact normalized nonzero `logDeriv xi` blind packet with unchanged kernel and rank; its adjoint
recovers the reporter; and every downstream decoder obeys exact and strict packet-erasure laws. -/
theorem xiCofiniteEvaluationReporter_exactBlindDataProcessingUniversality (N : ℕ) :
    ∀ F : Set ℂ, F.Finite →
      ∃ points : Fin N → {z : ℂ // z ∉ F},
        Function.Injective points ∧
        let report := finiteEvaluationReporter (fun i => (points i : ℂ))
        (finiteDerivativeReporterGram N xi report).PosDef ∧
        ∀ (Z : Type u) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
            [CompleteSpace Z]
            (encode : EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ] Z),
          (finiteDerivativeReporterGram N xi
            (encode.toLinearMap.comp report)).PosDef ∧
          (∃ (k : ℕ) (c : Fin (k + 1) → ℂ),
            k ≤ N ∧
            finiteDerivativeReporterConditionalInformation k (logDeriv xi) report = 0 ∧
            finiteDerivativeReporterConditionalInformation k (logDeriv xi)
                (encode.toLinearMap.comp report) = 0 ∧
            c (Fin.last k) = -1 ∧
            c ∈ LinearMap.ker
              (finiteDerivativeReporterMap (k + 1) (logDeriv xi) report) ∧
            c ∈ LinearMap.ker (finiteDerivativeReporterMap (k + 1) (logDeriv xi)
              (encode.toLinearMap.comp report)) ∧
            LinearMap.ker (finiteDerivativeReporterMap (k + 1) (logDeriv xi)
                (encode.toLinearMap.comp report)) =
              LinearMap.ker
                (finiteDerivativeReporterMap (k + 1) (logDeriv xi) report) ∧
            finrank ℂ (LinearMap.range (finiteDerivativeReporterMap (k + 1)
                (logDeriv xi) (encode.toLinearMap.comp report))) =
              finrank ℂ (LinearMap.range
                (finiteDerivativeReporterMap (k + 1) (logDeriv xi) report)) ∧
            finiteDerivativeReporterPacket c (logDeriv xi) ≠ 0 ∧
            report (finiteDerivativeReporterPacket c (logDeriv xi)) = 0 ∧
            encode (report (finiteDerivativeReporterPacket c (logDeriv xi))) = 0 ∧
            iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
              (Set.range fun i : Fin k =>
                iteratedDeriv (i : ℕ) (logDeriv xi))) ∧
          encode.toContinuousLinearMap.adjoint.toLinearMap.comp
              (encode.toLinearMap.comp report) = report ∧
          (∀ (Y : Type v) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
              (decode : Z →ₗ[ℂ] Y),
            (finiteDerivativeReporterGram N xi
              (decode.comp (encode.toLinearMap.comp report))).det = 0 ↔
            ∃ c : Fin N → ℂ,
              c ≠ 0 ∧
              finiteDerivativeReporterPacket c xi ≠ 0 ∧
              report (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
              encode (report (finiteDerivativeReporterPacket c xi)) ≠ 0 ∧
              decode (encode (report (finiteDerivativeReporterPacket c xi))) = 0) ∧
          ∀ (Y : Type v) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
              [FiniteDimensional ℂ Y] (decode : Z →ₗ[ℂ] Y),
            finrank ℂ Y < N →
            ∃ c : Fin N → ℂ,
              c ≠ 0 ∧
              finiteDerivativeReporterPacket c xi ≠ 0 ∧
              report (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
              encode (report (finiteDerivativeReporterPacket c xi)) ≠ 0 ∧
              decode (encode (report (finiteDerivativeReporterPacket c xi))) = 0 := by
  intro F hF
  obtain ⟨points, hinjective, hXi, hisometric⟩ :=
    xiCofiniteEvaluationReporter_isometricDataProcessingUniversality.{u, v} N F hF
  refine ⟨points, hinjective, ?_⟩
  dsimp only
  let report := finiteEvaluationReporter (fun i => (points i : ℂ))
  have hXi' : (finiteDerivativeReporterGram N xi report).PosDef := by
    simpa only [report] using hXi
  refine ⟨hXi', ?_⟩
  intro Z _ _ _ encode
  obtain ⟨hencodedXi, _hcollapse, hrecover, hexact, hstrict⟩ :=
    hisometric Z encode
  obtain ⟨k, c, hk, hzero, hencodedZero, hlast, hker, hencodedKer,
      hkernels, hranks, hpacket, hreport, hencoded, _hrecoverExact, hsource⟩ :=
    exists_xiLogDeriv_isometricReporterRecovery_exactBlindPacket_collapse report encode
  refine ⟨?_, ⟨k, c, ?_, hzero, hencodedZero, hlast, hker, hencodedKer,
      hkernels, hranks, hpacket, hreport, hencoded, hsource⟩, ?_, ?_, ?_⟩
  · simpa only [report] using hencodedXi
  · simpa [report] using hk
  · simpa only [report] using hrecover
  · simpa only [report] using hexact
  · simpa only [report] using hstrict

end

end RHTower
