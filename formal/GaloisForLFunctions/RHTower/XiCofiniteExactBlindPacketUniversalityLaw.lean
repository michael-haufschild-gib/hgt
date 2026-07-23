import GaloisForLFunctions.RHTower.XiCofiniteEvaluationReporterUniversalityLaw
import GaloisForLFunctions.RHTower.XiLogDerivReporterIsometricRecovery

/-!
# Cofinite Xi reporters with an exact blind packet

The cofinite evaluation-reporter law supplies faithful completed-Xi geometry outside an arbitrary
finite forbidden set.  The isometric recovery law supplies more than a vanishing conditional
information number: it normalizes a genuinely nonzero logarithmic-derivative source packet whose
original and encoded reports both vanish.  Choosing the same evaluation reporter joins these two
scales into one certificate.
-/

open scoped ComplexOrder InnerProductSpace

namespace RHTower

open GaloisForLFunctions
open HTGeometry
open Module

noncomputable section

universe u

/-- **Cofinite exact-blind-packet universality law.**  Outside every finite forbidden set, one
injective evaluation packet is faithful to the first `N` Xi jets under every isometric recoding,
yet carries a normalized, genuinely nonzero `logDeriv xi` source packet annihilated both before and
after that perfectly recoverable recoding. -/
theorem xiCofiniteEvaluationReporter_exactBlindPacketUniversality (N : ℕ) :
    ∀ F : Set ℂ, F.Finite →
      ∃ points : Fin N → {z : ℂ // z ∉ F},
        Function.Injective points ∧
        (finiteDerivativeReporterGram N xi
          (finiteEvaluationReporter (fun i => (points i : ℂ)))).PosDef ∧
        ∀ (Z : Type u) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
            [CompleteSpace Z]
            (encode : EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ] Z),
          (finiteDerivativeReporterGram N xi
            (encode.toLinearMap.comp
              (finiteEvaluationReporter (fun i => (points i : ℂ))))).PosDef ∧
          ∃ (k : ℕ) (c : Fin (k + 1) → ℂ),
            k ≤ N ∧
            c (Fin.last k) = -1 ∧
            finiteDerivativeReporterPacket c (logDeriv xi) ≠ 0 ∧
            finiteEvaluationReporter (fun i => (points i : ℂ))
              (finiteDerivativeReporterPacket c (logDeriv xi)) = 0 ∧
            encode (finiteEvaluationReporter (fun i => (points i : ℂ))
              (finiteDerivativeReporterPacket c (logDeriv xi))) = 0 ∧
            encode.toContinuousLinearMap.adjoint.toLinearMap.comp
                (encode.toLinearMap.comp
                  (finiteEvaluationReporter (fun i => (points i : ℂ)))) =
              finiteEvaluationReporter (fun i => (points i : ℂ)) ∧
            iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
              (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) (logDeriv xi)) := by
  intro F hF
  obtain ⟨points, hinjective, hXi, hisometric⟩ :=
    xiCofiniteEvaluationReporter_isometricDataProcessingUniversality.{u, 0} N F hF
  refine ⟨points, hinjective, hXi, ?_⟩
  intro Z _ _ _ encode
  let report := finiteEvaluationReporter (fun i => (points i : ℂ))
  have hencodedXi := (hisometric Z encode).1
  obtain ⟨k, c, hk, _hzero, _hencodedZero, hlast, _hker, _hencodedKer,
      _hkernels, _hranks, hpacket, hreport, hencoded, hrecover, hsource⟩ :=
    exists_xiLogDeriv_isometricReporterRecovery_exactBlindPacket_collapse report encode
  refine ⟨hencodedXi, k, c, ?_, hlast, hpacket, ?_, ?_, ?_, hsource⟩
  · simpa [report] using hk
  · simpa only [report] using hreport
  · simpa only [report] using hencoded
  · simpa only [report] using hrecover

end

end RHTower
