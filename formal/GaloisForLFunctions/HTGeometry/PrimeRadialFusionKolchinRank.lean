import GaloisForLFunctions.HTGeometry.PrimeRadialFusionConductorLaw
import GaloisForLFunctions.HTGeometry.PrimeValuationProfileFieldClassification

/-!
# Exact relative Kolchin rank of radial fusion channels

At a valuation cutoff `N`, the observable directions of a profile subspace form the range of its
first-`N` coefficient map.  A basis of this finite-dimensional range lifts to actual
prime-supported sources.  Those sources are jointly differentially independent over the complete
high-valuation tail field.  Hence every finite channel-by-jet rectangle has exactly the expected
product rank.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Set
open scoped Differential

noncomputable section

set_option maxHeartbeats 1200000

/-! ## Observable prefix channels and the complete tail -/

/-- The first `N` positive coefficients of an ambient radial profile. -/
def primeRadialPrefixMap (N : Nat) :
    PrimeRadialProfile →ₗ[ℂ] (Fin N → ℂ) where
  toFun u j := PowerSeries.coeff (j.1 + 1) (u : PowerSeries ℂ)
  map_add' u v := by
    funext j
    simp
  map_smul' z u := by
    funext j
    simp

/-- Profiles in `W` invisible through valuation cutoff `N`, retained as an ambient profile
subspace. -/
def primeRadialTailSubmodule
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    Submodule ℂ PrimeRadialProfile :=
  W ⊓ LinearMap.ker (primeRadialPrefixMap N)

/-- The finite observable prefix space of `W` at cutoff `N`. -/
abbrev PrimeRadialPrefixRange
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :=
  LinearMap.range ((primeRadialPrefixMap N).domRestrict W)

noncomputable instance primeRadialPrefixRange_finiteDimensional
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    FiniteDimensional ℂ (PrimeRadialPrefixRange W N) := by
  exact FiniteDimensional.of_injective
    (PrimeRadialPrefixRange W N).subtype
    (Submodule.subtype_injective (PrimeRadialPrefixRange W N))

/-! ## A canonical basis of observable channels and chosen source lifts -/

/-- Index of the observable valuation channels through cutoff `N`. -/
abbrev PrimeRadialPrefixChannelIndex
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :=
  Module.Basis.ofVectorSpaceIndex ℂ (PrimeRadialPrefixRange W N)

/-- A chosen lift in `W` of one basis vector of the observable prefix range. -/
def primeRadialPrefixChannelLiftInW
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat)
    (i : PrimeRadialPrefixChannelIndex W N) : W :=
  Function.surjInv
    ((primeRadialPrefixMap N).domRestrict W).surjective_rangeRestrict
    (Module.Basis.ofVectorSpace ℂ (PrimeRadialPrefixRange W N) i)

@[simp]
theorem primeRadialPrefixMap_channelLiftInW
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat)
    (i : PrimeRadialPrefixChannelIndex W N) :
    primeRadialPrefixMap N (primeRadialPrefixChannelLiftInW W N i : W) =
      ((Module.Basis.ofVectorSpace ℂ (PrimeRadialPrefixRange W N) i :
        PrimeRadialPrefixRange W N) : Fin N → ℂ) := by
  exact congrArg Subtype.val
    (Function.rightInverse_surjInv
      ((primeRadialPrefixMap N).domRestrict W).surjective_rangeRestrict _)

/-- Observable prefix channel, embedded in the full formal profile algebra. -/
def primeRadialPrefixChannelProfile
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat)
    (i : PrimeRadialPrefixChannelIndex W N) : PrimeRadialProfile :=
  (primeRadialPrefixChannelLiftInW W N i : W).1

theorem linearIndependent_prefixMap_channelProfiles
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    LinearIndependent ℂ
      (primeRadialPrefixMap N ∘ primeRadialPrefixChannelProfile W N) := by
  let R := PrimeRadialPrefixRange W N
  let b := Module.Basis.ofVectorSpace ℂ R
  have hb : LinearIndependent ℂ (fun i => ((b i : R) : Fin N → ℂ)) :=
    b.linearIndependent.map' R.subtype R.ker_subtype
  have hfamily :
      (primeRadialPrefixMap N ∘ primeRadialPrefixChannelProfile W N) =
        fun i => ((b i : R) : Fin N → ℂ) := by
    funext i
    exact primeRadialPrefixMap_channelLiftInW W N i
  rw [hfamily]
  exact hb

theorem linearIndependent_primeRadialPrefixChannelProfile
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    LinearIndependent ℂ (primeRadialPrefixChannelProfile W N) :=
  LinearIndependent.of_comp (primeRadialPrefixMap N)
    (linearIndependent_prefixMap_channelProfiles W N)

/-- Tail basis plus lifted prefix basis is a linearly independent family of full profiles. -/
theorem linearIndependent_sum_tail_prefixProfiles
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    LinearIndependent ℂ
      (Sum.elim (primeRadialBasisProfile (primeRadialTailSubmodule W N))
        (primeRadialPrefixChannelProfile W N)) := by
  have htail_le :
      Submodule.span ℂ
          (Set.range (primeRadialBasisProfile (primeRadialTailSubmodule W N))) ≤
        LinearMap.ker (primeRadialPrefixMap N) := by
    rw [span_primeRadialBasisProfile]
    exact inf_le_right
  have hprefix_disjoint : Disjoint
      (Submodule.span ℂ (Set.range (primeRadialPrefixChannelProfile W N)))
      (LinearMap.ker (primeRadialPrefixMap N)) :=
    Submodule.range_ker_disjoint
      (linearIndependent_prefixMap_channelProfiles W N)
  have hdisjoint : Disjoint
      (Submodule.span ℂ
        (Set.range (primeRadialBasisProfile (primeRadialTailSubmodule W N))))
      (Submodule.span ℂ (Set.range (primeRadialPrefixChannelProfile W N))) :=
    hprefix_disjoint.symm.mono htail_le le_rfl
  exact linearIndependent_sum.mpr
    ⟨linearIndependent_primeRadialBasisProfile _,
      linearIndependent_primeRadialPrefixChannelProfile W N, hdisjoint⟩

/-! ## Exact relative differential rank -/

/-- The complete differential field generated by every high-valuation tail profile. -/
def primeRadialTailDifferentialField
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    IntermediateField finitePrimeCoefficientField arithmeticFunctionFractionField :=
  primeRadialDifferentialField (primeRadialTailSubmodule W N)

/-- **Exact relative channel law.**  A basis of all observable prefix directions is jointly
differentially independent over the complete high-valuation tail field. -/
theorem differentialIndependent_primeRadialPrefixChannels_over_tailField
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    GaloisForLFunctions.DifferentialIndependent
      (primeRadialTailDifferentialField W N)
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
          (primeRadialSource (primeRadialPrefixChannelProfile W N i))) := by
  let x : PrimeRadialBasisIndex (primeRadialTailSubmodule W N) →
      arithmeticFunctionFractionField := fun i =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (primeRadialSource
        (primeRadialBasisProfile (primeRadialTailSubmodule W N) i))
  let y : PrimeRadialPrefixChannelIndex W N → arithmeticFunctionFractionField := fun i =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (primeRadialSource (primeRadialPrefixChannelProfile W N i))
  have hcombined := differentialIndependent_primeRadialSource_of_linearIndependent
    (Sum.elim (primeRadialBasisProfile (primeRadialTailSubmodule W N))
      (primeRadialPrefixChannelProfile W N))
    (linearIndependent_sum_tail_prefixProfiles W N)
  have hfamily :
      (fun q => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primeRadialSource
          (Sum.elim (primeRadialBasisProfile (primeRadialTailSubmodule W N))
            (primeRadialPrefixChannelProfile W N) q))) = Sum.elim x y := by
    funext q
    rcases q with i | j <;> rfl
  rw [hfamily] at hcombined
  have hrelative :=
    GaloisForLFunctions.differentialIndependent_sum_right_over_left_differentialAdjoin
      x y hcombined
  change GaloisForLFunctions.DifferentialIndependent
    (GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
      (Set.range x)) y
  exact hrelative

/-- Every finite channel-by-jet rectangle has the exact product algebraic rank. -/
theorem algebraicIndependent_primeRadialPrefixChannelJetRectangle
    (W : Submodule ℂ PrimeRadialProfile) (N r : Nat) :
    AlgebraicIndependent (primeRadialTailDifferentialField W N)
      (fun q : PrimeRadialPrefixChannelIndex W N × Fin (r + 1) =>
        GaloisForLFunctions.differentialJet q.2
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (primeRadialSource (primeRadialPrefixChannelProfile W N q.1)))) := by
  have h := differentialIndependent_primeRadialPrefixChannels_over_tailField W N
  unfold GaloisForLFunctions.DifferentialIndependent at h
  exact h.comp (fun q => (q.1, (q.2 : Nat))) (by
    intro q z hqz
    apply Prod.ext
    · exact congrArg Prod.fst hqz
    · exact Fin.ext (congrArg Prod.snd hqz))

/-- The number of observable channels is exactly the dimension of the prefix range. -/
theorem primeRadialPrefixChannelIndex_natCard
    (W : Submodule ℂ PrimeRadialProfile) (N : Nat) :
    Nat.card (PrimeRadialPrefixChannelIndex W N) =
      Module.finrank ℂ (PrimeRadialPrefixRange W N) := by
  exact (Module.finrank_eq_nat_card_basis
    (Module.Basis.ofVectorSpace ℂ (PrimeRadialPrefixRange W N))).symm

/-- The exact two-cutoff Kolchin rank. -/
def primeRadialKolchinRank
    (W : Submodule ℂ PrimeRadialProfile) (N r : Nat) : Nat :=
  (r + 1) * Module.finrank ℂ (PrimeRadialPrefixRange W N)

/-- The channel-by-jet rectangle has exactly the declared two-cutoff rank. -/
theorem primeRadialPrefixChannelJetRectangle_natCard
    (W : Submodule ℂ PrimeRadialProfile) (N r : Nat) :
    Nat.card (PrimeRadialPrefixChannelIndex W N × Fin (r + 1)) =
      primeRadialKolchinRank W N r := by
  rw [Nat.card_prod, Nat.card_fin, primeRadialPrefixChannelIndex_natCard]
  simp [primeRadialKolchinRank, Nat.mul_comm]

end

end GaloisForLFunctions.HTGeometry
