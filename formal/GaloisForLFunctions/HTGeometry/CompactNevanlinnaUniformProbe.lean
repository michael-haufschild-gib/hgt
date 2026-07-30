import GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaKernelContinuity
import GaloisForLFunctions.HTGeometry.CompactUniformFiniteProbe

/-!
# Compact uniform probes inside a frozen Nevanlinna tangent

Fix a finite frozen genuine-jet packet.  On a compact family of disjoint regular target packets,
the direct projective Nevanlinna control varies continuously in operator norm and remains
surjective after restriction to the exact frozen tangent.  Compact uniformization therefore
produces one finitely generated subspace of that tangent which controls every target packet in the
family.  This is the finite-dimensional perturbation manifold required before classical
parametric transversality can be applied.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Topology
open scoped ENNReal OnePoint

noncomputable section

/-- **Compact frozen-tangent uniform-probe law.** A compact regular family of genuine
Nevanlinna-jet target packets admits one common finitely generated perturbation subspace inside
the exact tangent which annihilates the frozen packet. -/
theorem compact_regularNevanlinnaTargetFamily_has_uniform_finiteProbe
    {ιf ιt : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt]
    (a q : ℂ → ℂ) (haCont : ContDiff ℂ ⊤ a) (hqCont : ContDiff ℂ ⊤ q)
    (η : ℝ) (hη : 0 < η)
    (zf : ιf → ℂ) (hqf_inj : Function.Injective (fun i => q (zf i)))
    (hupperf : ∀ i, 0 < (q (zf i)).im)
    (nf : ιf → ℕ) (haf : ∀ i, a (zf i) ≠ 0)
    (hqdf : ∀ i, deriv q (zf i) ≠ 0)
    (nt : ιt → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (K : Set (ιt → NevanlinnaUpperNodeAtLeast q η)) (hK : IsCompact K)
    (hqt_inj : ∀ z ∈ K, Function.Injective (fun i => q (z i).1))
    (hcross : ∀ z ∈ K, ∀ i j, q (zf i) ≠ q (z j).1)
    (hat : ∀ z ∈ K, ∀ i, a (z i).1 ≠ 0)
    (hqdt : ∀ z ∈ K, ∀ i, deriv q (z i).1 ≠ 0) :
    let frozen := projectiveNevanlinnaJetLinftyContinuousControl
      a q zf nf haf hqdf mu hupperf
    let S := LinearMap.ker frozen.toLinearMap
    let target := fun z : ιt → NevanlinnaUpperNodeAtLeast q η =>
      linftyBochnerControl mu
        (projectiveNevanlinnaJetExpansionColumn a q (fun i => (z i).1) nt)
        (memLp_projectiveNevanlinnaJetExpansionColumn η hη nt mu z)
    ∃ V : Submodule ℝ S, V.FG ∧
      ∀ z ∈ K, Function.Surjective (((target z).domRestrict S).domRestrict V) := by
  dsimp only
  let frozen := projectiveNevanlinnaJetLinftyContinuousControl
    a q zf nf haf hqdf mu hupperf
  let S := LinearMap.ker frozen.toLinearMap
  let target := fun z : ιt → NevanlinnaUpperNodeAtLeast q η =>
    linftyBochnerControl mu
      (projectiveNevanlinnaJetExpansionColumn a q (fun i => (z i).1) nt)
      (memLp_projectiveNevanlinnaJetExpansionColumn η hη nt mu z)
  let L := fun z : ιt → NevanlinnaUpperNodeAtLeast q η =>
    (target z).domRestrict S
  have htarget : Continuous target := by
    exact continuous_projectiveNevanlinnaJetExpansionLinftyBochnerControl
      haCont hqCont η hη nt mu
  have hL : Continuous L := continuous_clm_domRestrict target htarget S
  have hsurj : ∀ z ∈ K, Function.Surjective (L z) := by
    intro z hz
    have heq := projectiveNevanlinnaJetExpansionLinftyControl_eq_existing
      a q η hη nt mu z (hat z hz) (hqdt z hz)
    have hexisting : Function.Surjective
        ((projectiveNevanlinnaJetLinftyContinuousControl
          a q (fun i => (z i).1) nt (hat z hz) (hqdt z hz) mu
            (fun i => hη.trans_le (z i).2)).domRestrict S) := by
      simpa [frozen, S,
        projectiveNevanlinnaJetLinftyContinuousControl_toLinearMap] using!
        (constrainedProjectiveNevanlinnaJet_linftyControl_surjective
          a q zf (fun i => (z i).1) hqf_inj (hqt_inj z hz)
          (hcross z hz) hupperf (fun i => hη.trans_le (z i).2)
          nf nt haf (hat z hz) hqdf (hqdt z hz) mu hmu)
    simpa [L, target, heq] using hexisting
  exact compact_surjectiveControls_have_uniform_finiteProbe L hL K hK hsurj

end

end GaloisForLFunctions.HTGeometry
