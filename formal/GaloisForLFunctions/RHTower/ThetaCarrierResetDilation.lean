import GaloisForLFunctions.RHTower.ThetaCarrierHassePacket
import GaloisForLFunctions.HTGeometry.ResetBilateralDilation

/-!
# The theta/Hasse natural extension

Let `ν_a` be the tilted theta law on the logarithmic scale coordinate, with reflection
`x ↦ -x` carrying `ν_a` to `ν_{-a}`, and let `Q̂_a = E_κ(ν_a)` be the theta-carrier packet with
Hasse recovery.  Put `Q̄_a = ν_a ⊗ λ^ℤ` on `ℝ × [0, 1)^ℤ`.

**Corollary 7.3, `(RFDM.33)`**: the bilateral reset dilation `𝒯(x, ω) = (-x, Sω)` satisfies
`𝒯_* Q̄_a = Q̄_{-a}`, `𝒯²_* Q̄_a = Q̄_a` and `Π_* Q̄_a = Q̂_a`, executes the Hasse reset process,
preserves the reflected information `D(Q̄_a ‖ Q̄_{-a}) = D(ν_a ‖ ν_{-a})`, and almost every lifted
state has infinite period: the observed law closes after two steps while the lifted history stays
open.
-/

open MeasureTheory InformationTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ResetDilation
open scoped ENNReal

noncomputable section

namespace RHTower

/-- The lifted theta law `Q̄_a = ν_a ⊗ λ^ℤ`. -/
def thetaLiftedLaw (a : ℝ) : Measure (ℝ × SeedHistory) := (thetaTiltProb a).prod historyLaw

/-- **Corollary 7.3, `(RFDM.33)`**: the theta/Hasse natural extension. -/
theorem thetaCarrier_natural_extension {a : ℝ} (ha : |a| ≤ 1) :
    (thetaLiftedLaw a).map (dilationMap fun x : ℝ => -x) = thetaLiftedLaw (-a) ∧
      (thetaLiftedLaw a).map ((dilationMap fun x : ℝ => -x)^[2]) = thetaLiftedLaw a ∧
      (thetaLiftedLaw a).map (dilationPacket thetaHasseProfile.kernel) = thetaCarrierPacket a ∧
      (∀ x k, (dilationSource x).map (fun z (j : Fin (k + 1)) =>
          dilationPacket thetaHasseProfile.kernel ((dilationMap fun x : ℝ => -x)^[j] z)) =
        markovPath (splitFormation (Measure.dirac x) thetaHasseProfile.kernel)
          (formationLiftKernel thetaHasseProfile.kernel (fun x : ℝ => -x) measurable_neg) k) ∧
      klDiv (thetaLiftedLaw a) (thetaLiftedLaw (-a)) =
        klDiv (thetaTiltProb a) (thetaTiltProb (-a)) ∧
      ∀ N, 0 < N → thetaLiftedLaw a {z | (dilationMap (fun x : ℝ => -x))^[N] z = z} = 0 := by
  have habs : |(-a)| ≤ 1 := by rwa [abs_neg]
  haveI := thetaTiltProb_isProbabilityMeasure ha
  haveI := thetaTiltProb_isProbabilityMeasure habs
  have hinv : ∀ x : ℝ, - -x = x := neg_neg
  have hstep : ∀ b, |b| ≤ 1 →
      (thetaLiftedLaw b).map (dilationMap fun x : ℝ => -x) = thetaLiftedLaw (-b) := fun b hb => by
    haveI := thetaTiltProb_isProbabilityMeasure hb
    rw [thetaLiftedLaw, map_dilationMap_prod _ measurable_neg, map_neg_thetaTiltProb hb,
      thetaLiftedLaw]
  have hmeas := measurable_dilationMap (fun x : ℝ => -x) measurable_neg
  refine ⟨hstep a ha, ?_, ?_, fun x k => (resetDilation thetaHasseProfile.kernel _ measurable_neg
    hinv).fdd x k, klDiv_prod_historyLaw _ _, fun N hN => prod_historyLaw_periodic_null _ _ hN⟩
  · rw [Function.iterate_succ, Function.iterate_one, ← Measure.map_map hmeas hmeas, hstep a ha,
      hstep (-a) habs, neg_neg]
  · rw [thetaLiftedLaw, map_dilationPacket, thetaCarrierPacket]

end RHTower
