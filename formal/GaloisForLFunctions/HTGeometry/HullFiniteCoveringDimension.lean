import GaloisForLFunctions.HTGeometry.HullJetEmbedding
import GaloisForLFunctions.HTGeometry.EuclideanCompactCoveringDimension
import GaloisForLFunctions.HTGeometry.BohrHullDimension

/-!
# A jet-separated compact hull has finite covering dimension

A compact space that injects continuously into `ℂ^N` is homeomorphic to a compact subset of a
`2N`-dimensional real normed space, and compact subsets of Euclidean space have finite covering
dimension.  Hence the compact translation hull of an almost periodic function whose finite jets
separate its hull points has finite covering dimension.

This is the topological half of the singular Kolchin frequency budget: the jet tower of a
differentially algebraic almost periodic function embeds its hull into a fixed finite-dimensional
space, so the hull cannot carry infinite topological dimension.  The remaining half — the identity
between covering dimension and the rational rank of the character group — is Pontryagin–Takahashi
duality.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped BoundedContinuousFunction

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- A compact space with a continuous injection into `ℂ^N` has finite covering dimension. -/
theorem exists_hasCoverDimLE_of_continuous_injective {K : Type*} [TopologicalSpace K]
    [CompactSpace K] {N : ℕ} {J : K → (Fin N → ℂ)} (hJcont : Continuous J)
    (hJinj : Function.Injective J) : ∃ d : ℕ, HasCoverDimLE K d := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- no jets to separate: the hull is a single point
    haveI : Subsingleton K := by
      constructor
      intro x y
      refine hJinj ?_
      funext i
      exact absurd i.2 (by omega)
    exact ⟨0, HasCoverDimLE.of_subsingleton⟩
  · have hfrC : Module.finrank ℝ (Fin N → ℂ) = 2 * N := by
      rw [Module.finrank_pi_fintype ℝ]
      simp [Complex.finrank_real_complex, mul_comm]
    have hfrE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * N))) = 2 * N := by
      simp
    obtain ⟨e⟩ : Nonempty ((Fin N → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * N))) :=
      FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by rw [hfrC, hfrE])
    haveI : Nonempty (Fin (2 * N)) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (EuclideanSpace ℝ (Fin (2 * N))) := inferInstance
    set Φ : K → EuclideanSpace ℝ (Fin (2 * N)) := fun x => e (J x) with hΦ
    have hΦcont : Continuous Φ := e.continuous.comp hJcont
    have hΦinj : Function.Injective Φ := e.injective.comp hJinj
    have hcomp : IsCompact (Set.range Φ) := isCompact_range hΦcont
    have hdim : HasCoverDimLE (↥(Set.range Φ)) (5 ^ (2 * N) - 1) :=
      HTGeometry.hasCoverDimLE_of_isCompact hcomp
    -- `K` is homeomorphic to the image
    have hEquiv : K ≃ₜ ↥(Set.range Φ) := by
      refine Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective Φ hΦinj) ?_
      exact Continuous.subtype_mk hΦcont _
    exact ⟨5 ^ (2 * N) - 1, HasCoverDimLE.of_homeomorph hEquiv.symm hdim⟩

/-- **Finite hull dimension.**  If the finite jets separate the points of the compact translation
hull of an almost periodic function, that hull has finite covering dimension. -/
theorem exists_hasCoverDimLE_bohrHull {f : ℝ →ᵇ ℂ}
    (htb : GaloisForLFunctions.HasTotallyBoundedOrbit (fun x => f x))
    {N : ℕ} {φ : GaloisForLFunctions.BohrHull f → (Fin N → ℂ)}
    (hcont : Continuous φ) (hinj : Function.Injective φ) :
    ∃ d : ℕ, HasCoverDimLE (GaloisForLFunctions.BohrHull f) d := by
  haveI : CompactSpace (GaloisForLFunctions.BohrHull f) :=
    GaloisForLFunctions.compactSpace_bohrHull htb
  exact exists_hasCoverDimLE_of_continuous_injective hcont hinj

end GaloisForLFunctions.HTGeometry
