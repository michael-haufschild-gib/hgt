import GaloisForLFunctions.RHTower.HighExponentShellLeastAtomAsymptotic
import GaloisForLFunctions.RHTower.XiSourceBoundaryOrientationConservation

/-!
# Riemann centered-flow capacity intertwining

The complete derivative-order capacity of an actual Xi residue is an exact
one-dimensional modular character.  The canonical prime-tail entropy is its
inverse character, so their product is exactly conserved and equals the
squared divisor multiplicity.

This constructs the source-derived covariant capacity without assuming RH.
It also separates covariant conservation from static positive conservation:
the raw capacity is time-independent exactly when the boundary character is
neutral, hence globally exactly under RH.
-/

open Complex Filter Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Factorially normalized order-`r` capacity of the Cayley-transported
residue at one actual Xi divisor point. -/
def xiCenteredFlowOrderCapacity
    (rho : XiDivisorSupport) (tau : ℝ) (r : ℕ) : ℝ :=
  let x := sourceCayleyObservationTime 1 (rho : ℂ) tau
  x ^ r / r.factorial *
    ‖iteratedDeriv r
      (cayleyPoleResidueMode
        ((analyticOrderAt xi (rho : ℂ)).toNat : ℂ) 1 (rho : ℂ))
      (x : ℂ)‖ ^ (2 : ℕ)

/-- Complete derivative-order capacity of one transported Xi residue. -/
def xiCenteredFlowRawCapacity
    (rho : XiDivisorSupport) (tau : ℝ) : ℝ :=
  ∑' r : ℕ, xiCenteredFlowOrderCapacity rho tau r

/-- Squared multiplicity mass retained by the complete order packet. -/
def xiCenteredFlowMultiplicityMass (rho : XiDivisorSupport) : ℝ :=
  ‖((analyticOrderAt xi (rho : ℂ)).toNat : ℂ)‖ ^ (2 : ℕ)

/-- Prime-tail entropy countercharacter of the raw centered-flow capacity. -/
def xiCenteredFlowSourceCountercharacter
    (rho : XiDivisorSupport) (tau : ℝ) : ℝ :=
  Real.exp (riemannReflectedSourceEntropy (rho : ℂ) * tau)

/-- Source-trivialized centered-flow capacity. -/
def xiCenteredFlowConservedCapacity
    (rho : XiDivisorSupport) (tau : ℝ) : ℝ :=
  xiCenteredFlowSourceCountercharacter rho tau *
    xiCenteredFlowRawCapacity rho tau

/-- Static raw capacity at one actual divisor point. -/
def XiCenteredFlowStaticCapacityAt (rho : XiDivisorSupport) : Prop :=
  ∀ tau : ℝ,
    xiCenteredFlowRawCapacity rho tau =
      xiCenteredFlowRawCapacity rho 0

/-- Static raw capacity on every actual Xi divisor fibre. -/
def XiCenteredFlowStaticCapacity : Prop :=
  ∀ rho : XiDivisorSupport, XiCenteredFlowStaticCapacityAt rho

/-- Triviality of the source-derived modular countercharacter on every
actual Xi divisor fibre. -/
def XiCenteredFlowSourceCountercharacterTrivial : Prop :=
  ∀ (rho : XiDivisorSupport) (tau : ℝ),
    xiCenteredFlowSourceCountercharacter rho tau = 1

private theorem xiCenteredFlow_rho_ne_one (rho : XiDivisorSupport) :
    (rho : ℂ) ≠ 1 := by
  intro h
  have hrange := xi_divisor_support_re_mem_open_unit rho
  rw [h] at hrange
  norm_num at hrange

/-- Orderwise capacity is the multiplicity mass times the arithmetic
modular character and the Poisson order weight. -/
theorem xiCenteredFlowOrderCapacity_eq
    (rho : XiDivisorSupport) (tau : ℝ) (r : ℕ) :
    xiCenteredFlowOrderCapacity rho tau r =
      xiCenteredFlowMultiplicityMass rho *
        Real.exp
          (sourceCayleyTransverseRate 1 (rho : ℂ) * tau) *
        poissonOrderWeight tau r := by
  rw [xiCenteredFlowOrderCapacity, xiCenteredFlowMultiplicityMass]
  exact sourceCayleyResidueMode_horizon_conservation
    ((analyticOrderAt xi (rho : ℂ)).toNat : ℂ)
    1 (rho : ℂ) tau r (xiCenteredFlow_rho_ne_one rho)

/-- **Exact capacity character.**  Summing every derivative order removes
only the Poisson profile.  The signed transverse character survives. -/
theorem xiCenteredFlowRawCapacity_eq
    (rho : XiDivisorSupport) (tau : ℝ) :
    xiCenteredFlowRawCapacity rho tau =
      xiCenteredFlowMultiplicityMass rho *
        Real.exp
          (sourceCayleyTransverseRate 1 (rho : ℂ) * tau) := by
  let C : ℝ :=
    xiCenteredFlowMultiplicityMass rho *
      Real.exp (sourceCayleyTransverseRate 1 (rho : ℂ) * tau)
  have hterm : ∀ r : ℕ,
      xiCenteredFlowOrderCapacity rho tau r =
        C * poissonOrderWeight tau r := by
    intro r
    rw [xiCenteredFlowOrderCapacity_eq]
  rw [xiCenteredFlowRawCapacity, tsum_congr hterm, tsum_mul_left,
    tsum_poissonOrderWeight, mul_one]

/-- The multiplicity mass is strictly positive on every divisor support
point. -/
theorem xiCenteredFlowMultiplicityMass_pos (rho : XiDivisorSupport) :
    0 < xiCenteredFlowMultiplicityMass rho := by
  have hm : (analyticOrderAt xi (rho : ℂ)).toNat ≠ 0 :=
    xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support rho)
  rw [xiCenteredFlowMultiplicityMass]
  exact sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr (Nat.cast_ne_zero.mpr hm))

/-- **Centered-flow capacity intertwining.**  Time translation acts on the
complete order capacity by the exact transverse character. -/
theorem xiCenteredFlowRawCapacity_add
    (rho : XiDivisorSupport) (tau u : ℝ) :
    xiCenteredFlowRawCapacity rho (tau + u) =
      Real.exp
          (sourceCayleyTransverseRate 1 (rho : ℂ) * u) *
        xiCenteredFlowRawCapacity rho tau := by
  rw [xiCenteredFlowRawCapacity_eq, xiCenteredFlowRawCapacity_eq]
  rw [mul_add, Real.exp_add]
  ring

/-- The source countercharacter is a multiplicative flow cocycle. -/
theorem xiCenteredFlowSourceCountercharacter_add
    (rho : XiDivisorSupport) (tau u : ℝ) :
    xiCenteredFlowSourceCountercharacter rho (tau + u) =
      xiCenteredFlowSourceCountercharacter rho tau *
        xiCenteredFlowSourceCountercharacter rho u := by
  rw [xiCenteredFlowSourceCountercharacter,
    xiCenteredFlowSourceCountercharacter,
    xiCenteredFlowSourceCountercharacter, mul_add, Real.exp_add]

/-- **Source-derived capacity conservation.**  Prime-tail entropy
trivializes the complete centered-flow capacity exactly, leaving only
squared divisor multiplicity. -/
theorem xiCenteredFlowConservedCapacity_eq_multiplicityMass
    (rho : XiDivisorSupport) (tau : ℝ) :
    xiCenteredFlowConservedCapacity rho tau =
      xiCenteredFlowMultiplicityMass rho := by
  rw [xiCenteredFlowConservedCapacity,
    xiCenteredFlowSourceCountercharacter,
    xiCenteredFlowRawCapacity_eq,
    riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  have hcancel :
      Real.exp
          (-sourceCayleyTransverseRate 1 (rho : ℂ) * tau) *
        Real.exp
          (sourceCayleyTransverseRate 1 (rho : ℂ) * tau) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [show
      Real.exp
            (-sourceCayleyTransverseRate 1 (rho : ℂ) * tau) *
          (xiCenteredFlowMultiplicityMass rho *
            Real.exp
              (sourceCayleyTransverseRate 1 (rho : ℂ) * tau)) =
        xiCenteredFlowMultiplicityMass rho *
          (Real.exp
              (-sourceCayleyTransverseRate 1 (rho : ℂ) * tau) *
            Real.exp
              (sourceCayleyTransverseRate 1 (rho : ℂ) * tau)) by ring,
    hcancel, mul_one]

/-- The conserved capacity is genuinely time invariant. -/
theorem xiCenteredFlowConservedCapacity_add
    (rho : XiDivisorSupport) (tau u : ℝ) :
    xiCenteredFlowConservedCapacity rho (tau + u) =
      xiCenteredFlowConservedCapacity rho tau := by
  rw [xiCenteredFlowConservedCapacity_eq_multiplicityMass,
    xiCenteredFlowConservedCapacity_eq_multiplicityMass]

/-- Static positive capacity at one divisor fibre is exactly vanishing of
the unsquared boundary fracture.  The moving source countercharacter is not
mistaken for a fixed invariant norm. -/
theorem xiCenteredFlowStaticCapacityAt_iff_boundaryFracture_zero
    (rho : XiDivisorSupport) :
    XiCenteredFlowStaticCapacityAt rho ↔
      xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) = 0 := by
  constructor
  · intro hstatic
    have h := hstatic 1
    rw [xiCenteredFlowRawCapacity_eq,
      xiCenteredFlowRawCapacity_eq] at h
    simp only [mul_one, mul_zero, Real.exp_zero] at h
    have hexp :
        Real.exp (sourceCayleyTransverseRate 1 (rho : ℂ)) = 1 := by
      nlinarith [xiCenteredFlowMultiplicityMass_pos rho]
    have hrate : sourceCayleyTransverseRate 1 (rho : ℂ) = 0 :=
      (Real.exp_eq_one_iff
        (sourceCayleyTransverseRate 1 (rho : ℂ))).mp hexp
    have hre : (rho : ℂ).re = 1 / 2 := by
      have hneutral :=
        (sourceCayleyTransverseRate_eq_zero_iff 1 (rho : ℂ)).1 hrate
      norm_num at hneutral ⊢
      exact hneutral
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).2 hre
  · intro hfracture tau
    have hre : (rho : ℂ).re = 1 / 2 :=
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).1 hfracture
    have hrate : sourceCayleyTransverseRate 1 (rho : ℂ) = 0 :=
      (sourceCayleyTransverseRate_eq_zero_iff 1 (rho : ℂ)).2 (by
        norm_num at hre ⊢
        exact hre)
    rw [xiCenteredFlowRawCapacity_eq,
      xiCenteredFlowRawCapacity_eq, hrate]
    simp

/-- The source countercharacter is trivial at one divisor fibre exactly
when its unsquared boundary fracture vanishes. -/
theorem xiCenteredFlowSourceCountercharacter_trivial_iff_boundaryFracture_zero
    (rho : XiDivisorSupport) :
    (∀ tau : ℝ,
      xiCenteredFlowSourceCountercharacter rho tau = 1) ↔
      xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) = 0 := by
  constructor
  · intro htrivial
    have h := htrivial 1
    rw [xiCenteredFlowSourceCountercharacter,
      riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate,
      mul_one] at h
    have hnegRate :
        -sourceCayleyTransverseRate 1 (rho : ℂ) = 0 :=
      (Real.exp_eq_one_iff
        (-sourceCayleyTransverseRate 1 (rho : ℂ))).mp h
    have hrate : sourceCayleyTransverseRate 1 (rho : ℂ) = 0 := by
      linarith
    have hre : (rho : ℂ).re = 1 / 2 := by
      have hneutral :=
        (sourceCayleyTransverseRate_eq_zero_iff 1 (rho : ℂ)).1 hrate
      norm_num at hneutral ⊢
      exact hneutral
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).2 hre
  · intro hfracture tau
    have hre : (rho : ℂ).re = 1 / 2 :=
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).1 hfracture
    have hrate : sourceCayleyTransverseRate 1 (rho : ℂ) = 0 :=
      (sourceCayleyTransverseRate_eq_zero_iff 1 (rho : ℂ)).2 (by
        norm_num at hre ⊢
        exact hre)
    rw [xiCenteredFlowSourceCountercharacter,
      riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate, hrate]
    simp

/-- **Global static-capacity gate.**  Covariant capacity conservation is
unconditional; triviality of its modular character on every divisor fibre
is exactly RH. -/
theorem xiCenteredFlowStaticCapacity_iff_riemannHypothesis :
    XiCenteredFlowStaticCapacity ↔ RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  constructor
  · intro hstatic rho
    exact
      (xiCenteredFlowStaticCapacityAt_iff_boundaryFracture_zero rho).1
        (hstatic rho)
  · intro hneutral rho
    exact
      (xiCenteredFlowStaticCapacityAt_iff_boundaryFracture_zero rho).2
        (hneutral rho)

/-- **Exact remaining source law.**  The prime-tail modular
countercharacter is globally trivial exactly under RH.  Covariant
conservation above is unconditional; this statement identifies, without
renaming it as boundedness, the sole additional arithmetic obligation. -/
theorem xiCenteredFlowSourceCountercharacterTrivial_iff_riemannHypothesis :
    XiCenteredFlowSourceCountercharacterTrivial ↔ RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  constructor
  · intro htrivial rho
    exact
      (xiCenteredFlowSourceCountercharacter_trivial_iff_boundaryFracture_zero
        rho).1 (htrivial rho)
  · intro hneutral rho
    exact
      (xiCenteredFlowSourceCountercharacter_trivial_iff_boundaryFracture_zero
        rho).2 (hneutral rho)

end

end RHTower
