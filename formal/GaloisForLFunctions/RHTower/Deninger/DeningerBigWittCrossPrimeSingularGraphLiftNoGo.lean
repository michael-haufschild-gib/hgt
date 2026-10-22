import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCrossPrimeHarmonicSingularGraphSource

/-!
# No bounded lift from the all-cross-prime ambient completion to the singular graph

The prime-harmonic Big-Witt source rows expose a topology-changing boundary.
After normalization by their divergent one-leg trace, their literal finite
packet admissions converge to zero in the all-cross-prime Calderón--Witt
`ℓ²` completion.  The same literal packets converge in the one-leg graph
completion to its nonzero vertical trace generator.

Consequently no map continuous at the ambient origin can reconstruct finite
one-leg graph admission from ambient packet admission.  Linearity and a global
operator bound are unnecessary.  In particular, no bounded linear
all-cross-prime coupling can perform the reconstruction.

This kills the bounded irreducible cross-prime lift proposed after
channel-resolved Gamma naturality failed.  Such a lift was the first arrow in
the candidate chain

`bounded cross-prime source lift`
`→ singular one-leg Gamma reporter`
`→ joint source/Gamma naturality`
`→ HB/FZZ-P/PW-B/RBH shared Ward endpoint`.

The sharp positive survivor is topological: every exact reconstruction is
discontinuous already at the zero source.  Thus any viable common Ward
producer must change the source topology before completion and must be
genuinely singular/unbounded there, rather than adding a bounded coupling
after the existing `ℓ²` completion.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/-- Exact reconstruction on literal finite source packets forces convergence
to the nonzero singular vertical generator along the canonical source-normalized
prime-harmonic row. -/
theorem tendsto_crossPrime_oneLegGraph_of_finitePacket_reconstruction
    (F : DeningerCalderonWittCrossPrimePacketHilbert →
      DeningerBigWittCrossPairSingularOneLegGraph)
    (hfinite :
      ∀ c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ,
        F (deningerBigWittCrossPairFinitePacketAdmission c) =
          deningerBigWittCrossPairFiniteOneLegGraphAdmission c) :
    Tendsto
      (fun n => F (deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n)))
      atTop (nhds deningerBigWittCrossPairOneLegGraphSingularVector) := by
  convert
    tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_primeTwoRightEdgeNormalizedPacket
      using 1
  ext n
  exact hfinite _

/-- No map continuous at the ambient origin can reconstruct literal finite
one-leg graph admission from all-cross-prime `ℓ²` packet admission.  The
obstruction is source-native: the witness sequence consists of actual
prime-harmonic Big-Witt rows. -/
theorem no_continuousAt_zero_crossPrimeAmbient_to_oneLegGraph_reconstruction :
    ¬ ∃ F : DeningerCalderonWittCrossPrimePacketHilbert →
        DeningerBigWittCrossPairSingularOneLegGraph,
      ContinuousAt F 0 ∧
      ∀ c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ,
        F (deningerBigWittCrossPairFinitePacketAdmission c) =
          deningerBigWittCrossPairFiniteOneLegGraphAdmission c := by
  rintro ⟨F, hF, hfinite⟩
  have hzero : F 0 = 0 := by
    simpa using
      (hfinite
        (0 : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ))
  have hambient : Tendsto
      (fun n => F (deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n)))
      atTop (nhds 0) := by
    have hcomp := hF.tendsto.comp
      tendsto_deningerBigWittCrossPairFinitePacketAdmission_primeTwoRightEdgeNormalizedPacket
    rw [hzero] at hcomp
    change Tendsto
      (F ∘ fun n => deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittPrimeTwoRightEdgeNormalizedPacket n))
      atTop (nhds 0)
    exact hcomp
  have hgraph :=
    tendsto_crossPrime_oneLegGraph_of_finitePacket_reconstruction F hfinite
  have hcollapse :
      (0 : DeningerBigWittCrossPairSingularOneLegGraph) =
        deningerBigWittCrossPairOneLegGraphSingularVector :=
    tendsto_nhds_unique hambient hgraph
  exact deningerBigWittCrossPairOneLegGraphSingularVector_ne_zero
    hcollapse.symm

/-- Sharp survivor: every exact graph reconstruction is discontinuous at the
zero source of the existing all-cross-prime `ℓ²` completion. -/
theorem crossPrime_oneLegGraph_reconstruction_not_continuousAt_zero
    (F : DeningerCalderonWittCrossPrimePacketHilbert →
      DeningerBigWittCrossPairSingularOneLegGraph)
    (hfinite :
      ∀ c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ,
        F (deningerBigWittCrossPairFinitePacketAdmission c) =
          deningerBigWittCrossPairFiniteOneLegGraphAdmission c) :
    ¬ ContinuousAt F 0 := by
  intro hF
  exact no_continuousAt_zero_crossPrimeAmbient_to_oneLegGraph_reconstruction
    ⟨F, hF, hfinite⟩

/-- In particular, no bounded linear all-cross-prime coupling reconstructs
the source-faithful singular graph admission. -/
theorem not_exists_continuousLinearMap_crossPrimeAmbient_to_oneLegGraph_reconstruction :
    ¬ ∃ L : DeningerCalderonWittCrossPrimePacketHilbert →L[ℂ]
        DeningerBigWittCrossPairSingularOneLegGraph,
      ∀ c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ,
        L (deningerBigWittCrossPairFinitePacketAdmission c) =
          deningerBigWittCrossPairFiniteOneLegGraphAdmission c := by
  rintro ⟨L, hL⟩
  exact no_continuousAt_zero_crossPrimeAmbient_to_oneLegGraph_reconstruction
    ⟨L, L.continuous.continuousAt, hL⟩

/-- **Bounded cross-prime source-lift route kill.**  Exact finite-packet
reconstruction is necessarily singular at the source origin, and therefore
cannot be supplied by any bounded linear coupling on the existing ambient
completion.  A surviving HB/FZZ-P/PW-B/RBH common Ward producer must change
topology before completion. -/
theorem boundedCrossPrimeSingularGraphLiftRouteKilled :
    (∀ F : DeningerCalderonWittCrossPrimePacketHilbert →
        DeningerBigWittCrossPairSingularOneLegGraph,
      (∀ c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ,
        F (deningerBigWittCrossPairFinitePacketAdmission c) =
          deningerBigWittCrossPairFiniteOneLegGraphAdmission c) →
        ¬ ContinuousAt F 0) ∧
    ¬ ∃ L : DeningerCalderonWittCrossPrimePacketHilbert →L[ℂ]
        DeningerBigWittCrossPairSingularOneLegGraph,
      ∀ c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ,
        L (deningerBigWittCrossPairFinitePacketAdmission c) =
          deningerBigWittCrossPairFiniteOneLegGraphAdmission c := by
  exact
    ⟨crossPrime_oneLegGraph_reconstruction_not_continuousAt_zero,
      not_exists_continuousLinearMap_crossPrimeAmbient_to_oneLegGraph_reconstruction⟩

end

end RHTower
