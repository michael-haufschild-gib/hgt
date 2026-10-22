import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMEPerturbativeGradeSeparation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingCubicPhaseCovarianceOpticalNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence
import GaloisForLFunctions.RHTower.XiOrdinateEndpointObstruction

/-!
# Finite-rank global AIME source-response no-go

The strongest surviving HB threshold proposal is source-adapted and carries the odd cubic AIME
phase charge.  This file therefore feeds an arbitrary complex-linear global Xi-packet response the
literal cubic AIME source packet itself.  The response may mix every Xi fibre; no diagonal,
locality, passivity, Schwarz, boundedness, or finite-band condition is imposed.

Finite algebraic rank alone is fatal.  A finite-dimensional subspace of a `Finsupp` space has one
common finite coordinate support: take finitely many module generators and unite their supports.
Since `XiZeroCopy` is infinite, some Xi fibre lies outside that support.  Every response-range
vector vanishes in its coordinate, while the cubic AIME numerator there is nonzero for every
nonzero seed.  Universal cancellation is impossible.

The phase and scale laws are retained exactly: the source packet and its full response are odd
under the seed half-turn and homogeneous of real degree three.  Thus this is not the weaker
seed-linear or phase-blind obstruction.  It kills every finite-rank globally mixed realization of
the source-adapted HB radiative threshold.  The sharp positive survivor is that any universal
cancelling response must have infinite algebraic rank before divisor selection.

The exact intended RH chain is

`source-adapted radiative cancellation` -> `full causal-cut extinction` ->
`source-FE clock covariance` -> the existing FZZ-P/PW-B/RBH Ward transductions -> RH.

`[PROVED HERE] [LEAN-PROVED] [HB ROUTE KILL] [INFINITE-RANK NECESSITY]`
`[NOVELTY AUDITED 2026-08-31] [NOVELTY UNVERIFIED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Every finite-dimensional subspace of a finite-support coordinate space has one common finite
coordinate support. -/
theorem exists_common_finset_support_of_finiteDimensional_finsupp
    {ι : Type*} [DecidableEq ι]
    (W : Submodule ℂ (ι →₀ ℂ)) [FiniteDimensional ℂ W] :
    ∃ S : Finset ι, ∀ x : W, x.1.support ⊆ S := by
  obtain ⟨n, generators, hspan⟩ := Module.Finite.exists_fin (R := ℂ) (M := W)
  let S : Finset ι := Finset.univ.biUnion fun i => (generators i).1.support
  refine ⟨S, ?_⟩
  intro x q hqx
  by_contra hqS
  have hxspan : x ∈ Submodule.span ℂ (Set.range generators) := by
    rw [hspan]
    exact Submodule.mem_top
  have hxq : x.1 q = 0 := by
    refine Submodule.span_induction
      (p := fun y _ => y.1 q = 0) ?_ ?_ ?_ ?_ hxspan
    · rintro y ⟨i, rfl⟩
      have hqgen : q ∉ (generators i).1.support := by
        intro hmem
        exact hqS (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩)
      simpa [Finsupp.mem_support_iff] using hqgen
    · rfl
    · intro y z _ _ hy hz
      simp [hy, hz]
    · intro c y _ hy
      simp [hy]
  exact (Finsupp.mem_support_iff.mp hqx) hxq

/-- An infinite index type always has a coordinate outside a prescribed finite packet. -/
theorem exists_not_mem_finset_of_infinite
    {ι : Type*} [Infinite ι] (S : Finset ι) :
    ∃ q : ι, q ∉ S := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hunivFinite : (Set.univ : Set ι).Finite :=
    S.finite_toSet.subset fun q _ => h q
  exact Set.infinite_univ hunivFinite

/-- Literal cubic AIME source packet localized at one Xi fibre. -/
def d4HBGlobalAIMESourcePacket (amplitude : ℂ) (q : XiZeroCopy) :
    HBXiPeierlsPacket :=
  Finsupp.single q
    (d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q))

/-- The literal AIME packet retains the physical half-turn odd charge. -/
theorem d4HBGlobalAIMESourcePacket_neg (amplitude : ℂ) (q : XiZeroCopy) :
    d4HBGlobalAIMESourcePacket (-amplitude) q =
      -d4HBGlobalAIMESourcePacket amplitude q := by
  classical
  simp [d4HBGlobalAIMESourcePacket,
    d4FundamentalQNMCrossBranchAIMENumerator_neg]

/-- The literal AIME packet is cubic under real seed rescaling. -/
theorem d4HBGlobalAIMESourcePacket_realScale
    (scale : ℝ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4HBGlobalAIMESourcePacket ((scale : ℂ) * amplitude) q =
      ((scale ^ (3 : ℕ) : ℝ) : ℂ) • d4HBGlobalAIMESourcePacket amplitude q := by
  classical
  simp [d4HBGlobalAIMESourcePacket,
    d4FundamentalQNMCrossBranchAIMENumerator_realScale]

/-- Full projected pole numerator after an arbitrary complex-linear global response acts on the
literal cubic AIME source packet. -/
def d4HBGlobalAIMESourceResponseFullPoleNumerator
    (Delta : HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket)
    (amplitude : ℂ) (q : XiZeroCopy) : ℂ :=
  d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) +
    Delta (d4HBGlobalAIMESourcePacket amplitude q) q

/-- Every complex-linear response to the literal source preserves its half-turn oddness. -/
theorem d4HBGlobalAIMESourceResponseFullPoleNumerator_neg
    (Delta : HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket)
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4HBGlobalAIMESourceResponseFullPoleNumerator Delta (-amplitude) q =
      -d4HBGlobalAIMESourceResponseFullPoleNumerator Delta amplitude q := by
  unfold d4HBGlobalAIMESourceResponseFullPoleNumerator
  rw [d4FundamentalQNMCrossBranchAIMENumerator_neg,
    d4HBGlobalAIMESourcePacket_neg, map_neg]
  simp
  ring

/-- Every complex-linear response to the literal source preserves cubic real homogeneity. -/
theorem d4HBGlobalAIMESourceResponseFullPoleNumerator_realScale
    (Delta : HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket)
    (scale : ℝ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4HBGlobalAIMESourceResponseFullPoleNumerator Delta
        ((scale : ℂ) * amplitude) q =
      ((scale ^ (3 : ℕ) : ℝ) : ℂ) *
        d4HBGlobalAIMESourceResponseFullPoleNumerator Delta amplitude q := by
  unfold d4HBGlobalAIMESourceResponseFullPoleNumerator
  rw [d4FundamentalQNMCrossBranchAIMENumerator_realScale,
    d4HBGlobalAIMESourcePacket_realScale, map_smul]
  simp [smul_eq_mul]
  ring

/-- No finite-algebraic-rank global response can cancel cubic AIME on every Xi fibre, even with
arbitrary cross-fibre mixing. -/
theorem not_d4HBFiniteRankGlobalAIMESourceResponse_universalCancellation
    (Delta : HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket)
    (hfinite : FiniteDimensional ℂ (LinearMap.range Delta))
    (amplitude : ℂ) (ha : amplitude ≠ 0) :
    ¬ (∀ q : XiZeroCopy,
      d4HBGlobalAIMESourceResponseFullPoleNumerator Delta amplitude q = 0) := by
  intro hcancel
  letI : FiniteDimensional ℂ (LinearMap.range Delta) := hfinite
  obtain ⟨S, hS⟩ :=
    exists_common_finset_support_of_finiteDimensional_finsupp (LinearMap.range Delta)
  obtain ⟨q, hq⟩ := exists_not_mem_finset_of_infinite S
  let source := d4HBGlobalAIMESourcePacket amplitude q
  let response : LinearMap.range Delta := ⟨Delta source, ⟨source, rfl⟩⟩
  have hresponseSupport := hS response
  have hresponseZero : Delta source q = 0 := by
    by_contra hne
    exact hq (hresponseSupport (Finsupp.mem_support_iff.mpr hne))
  have hzero := hcancel q
  have hresponseZero' :
      Delta (d4HBGlobalAIMESourcePacket amplitude q) q = 0 := by
    simpa [source] using hresponseZero
  rw [d4HBGlobalAIMESourceResponseFullPoleNumerator, hresponseZero', add_zero] at hzero
  exact ((d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr ha) hzero

/-- Sharp positive survivor: universal source-adapted AIME cancellation forces the global response
to have infinite algebraic rank. -/
theorem d4HBGlobalAIMESourceResponse_universalCancellation_forces_infiniteRank
    (Delta : HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket)
    (amplitude : ℂ) (ha : amplitude ≠ 0)
    (hcancel : ∀ q : XiZeroCopy,
      d4HBGlobalAIMESourceResponseFullPoleNumerator Delta amplitude q = 0) :
    ¬ FiniteDimensional ℂ (LinearMap.range Delta) := by
  intro hfinite
  exact not_d4HBFiniteRankGlobalAIMESourceResponse_universalCancellation
    Delta hfinite amplitude ha hcancel

/-- Closed route class: no finite-algebraic-rank complex-linear global response to the literal
cubic, phase-odd AIME source packet supplies universal HB pole cancellation. -/
def D4HBFiniteRankGlobalAIMESourceResponseCancellationRouteKilled : Prop :=
  ∀ (Delta : HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket),
    FiniteDimensional ℂ (LinearMap.range Delta) →
    ∀ amplitude : ℂ, amplitude ≠ 0 →
      ¬ (∀ q : XiZeroCopy,
        d4HBGlobalAIMESourceResponseFullPoleNumerator Delta amplitude q = 0)

/-- Premise-free certificate killing the finite-rank global source-adapted HB response class. -/
theorem d4HBFiniteRankGlobalAIMESourceResponseCancellationRouteKilled :
    D4HBFiniteRankGlobalAIMESourceResponseCancellationRouteKilled := by
  intro Delta hfinite amplitude ha
  exact not_d4HBFiniteRankGlobalAIMESourceResponse_universalCancellation
    Delta hfinite amplitude ha

end

end RHTower
