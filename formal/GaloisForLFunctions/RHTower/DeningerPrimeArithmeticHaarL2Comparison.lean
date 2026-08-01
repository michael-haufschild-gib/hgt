import GaloisForLFunctions.RHTower.DeningerPrimeFibreComparison
import GaloisForLFunctions.RHTower.DeningerPrimePacketHaarL2Green
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Normalized Haar-L² on the literal arithmetic prime quotient

The packet quotient is already identified with the full multiplicative-automorphism quotient by
the pointwise Frobenius closure.  This module proves that the identification preserves normalized
Haar measure, not merely topology.  Pullback therefore gives a canonical real Hilbert isometry
between the packet Haar-`L²` fibre and Haar-`L²` on the literal arithmetic quotient.

The comparison is constructed from the natural pointwise topology and uniqueness of probability
Haar measure.  No measure or Hilbert structure is transported by declaration.
-/

namespace RHTower

open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

noncomputable section

/-- Borel measurable structure on the literal arithmetic Frobenius quotient. -/
noncomputable instance
    deningerPrimeArithmeticMulAutFrobeniusQuotientMeasurableSpace
    (p : Nat.Primes) :
    MeasurableSpace (DeningerPrimeArithmeticMulAutFrobeniusQuotient p) :=
  borel (DeningerPrimeArithmeticMulAutFrobeniusQuotient p)

noncomputable instance
    deningerPrimeArithmeticMulAutFrobeniusQuotientBorelSpace
    (p : Nat.Primes) :
    BorelSpace (DeningerPrimeArithmeticMulAutFrobeniusQuotient p) :=
  ⟨rfl⟩

/-- Whole arithmetic quotient, bundled as a positive compact for Haar normalization. -/
def deningerPrimeArithmeticPositiveCompact (p : Nat.Primes) :
    PositiveCompacts (DeningerPrimeArithmeticMulAutFrobeniusQuotient p) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Haar measure on the literal arithmetic quotient, normalized to total mass one. -/
def deningerPrimeArithmeticHaarMeasure (p : Nat.Primes) :
    Measure (DeningerPrimeArithmeticMulAutFrobeniusQuotient p) :=
  Measure.haarMeasure (deningerPrimeArithmeticPositiveCompact p)

theorem deningerPrimeArithmeticHaarMeasure_univ (p : Nat.Primes) :
    deningerPrimeArithmeticHaarMeasure p Set.univ = 1 := by
  exact Measure.haarMeasure_self

noncomputable instance deningerPrimeArithmeticHaarMeasureProbability
    (p : Nat.Primes) :
    IsProbabilityMeasure (deningerPrimeArithmeticHaarMeasure p) :=
  ⟨deningerPrimeArithmeticHaarMeasure_univ p⟩

noncomputable instance deningerPrimeArithmeticHaarMeasureIsOpenPos
    (p : Nat.Primes) :
    (deningerPrimeArithmeticHaarMeasure p).IsOpenPosMeasure := by
  unfold deningerPrimeArithmeticHaarMeasure
  infer_instance

/-- The packet/arithmetic quotient equivalence sends normalized Haar measure exactly to normalized
Haar measure. -/
theorem
    deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv_map_haar
    (p : Nat.Primes) :
    Measure.map
        (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p)
        (deningerPrimePacketHaarMeasure p) =
      deningerPrimeArithmeticHaarMeasure p := by
  let E :=
    deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p
  let μ := deningerPrimePacketHaarMeasure p
  let ν := deningerPrimeArithmeticHaarMeasure p
  haveI hμhaar : μ.IsHaarMeasure := by
    dsimp [μ, deningerPrimePacketHaarMeasure]
    infer_instance
  haveI hνhaar : ν.IsHaarMeasure := by
    dsimp [ν, deningerPrimeArithmeticHaarMeasure]
    infer_instance
  haveI hmapHaar : (Measure.map E μ).IsHaarMeasure :=
    E.isHaarMeasure_map μ
  haveI hmapProbability : IsProbabilityMeasure (Measure.map E μ) :=
    Measure.isProbabilityMeasure_map E.continuous.measurable.aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure (Measure.map E μ) ν

/-- Packet-to-arithmetic quotient comparison as a measure-preserving map. -/
theorem deningerPrimePacketArithmeticFrobeniusQuotientMeasurePreserving
    (p : Nat.Primes) :
    MeasurePreserving
      (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p)
      (deningerPrimePacketHaarMeasure p)
      (deningerPrimeArithmeticHaarMeasure p) where
  measurable :=
    (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p).continuous.measurable
  map_eq :=
    deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv_map_haar p

/-- Arithmetic-to-packet inverse comparison is measure-preserving as well. -/
theorem deningerPrimePacketArithmeticFrobeniusQuotientSymmMeasurePreserving
    (p : Nat.Primes) :
    MeasurePreserving
      (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p).symm
      (deningerPrimeArithmeticHaarMeasure p)
      (deningerPrimePacketHaarMeasure p) := by
  exact MeasurePreserving.symm
    (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p).toHomeomorph.toMeasurableEquiv
    (deningerPrimePacketArithmeticFrobeniusQuotientMeasurePreserving p)

/-- Real Haar-`L²` on the literal arithmetic multiplicative quotient. -/
abbrev DeningerPrimeArithmeticHaarL2 (p : Nat.Primes) : Type :=
  Lp ℝ 2 (deningerPrimeArithmeticHaarMeasure p)

/-- Pull packet functions to the arithmetic quotient along the inverse quotient equivalence. -/
def deningerPrimePacketArithmeticHaarL2Forward (p : Nat.Primes) :
    DeningerPrimePacketHaarL2 p →ₗᵢ[ℝ] DeningerPrimeArithmeticHaarL2 p :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p).symm
    (deningerPrimePacketArithmeticFrobeniusQuotientSymmMeasurePreserving p)

/-- Pull arithmetic quotient functions back to the packet quotient. -/
def deningerPrimePacketArithmeticHaarL2Backward (p : Nat.Primes) :
    DeningerPrimeArithmeticHaarL2 p →ₗᵢ[ℝ] DeningerPrimePacketHaarL2 p :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p)
    (deningerPrimePacketArithmeticFrobeniusQuotientMeasurePreserving p)

theorem deningerPrimePacketArithmeticHaarL2Forward_surjective
    (p : Nat.Primes) :
    Function.Surjective (deningerPrimePacketArithmeticHaarL2Forward p) := by
  intro g
  refine ⟨deningerPrimePacketArithmeticHaarL2Backward p g, ?_⟩
  change
    Lp.compMeasurePreserving
      (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p).symm
      (deningerPrimePacketArithmeticFrobeniusQuotientSymmMeasurePreserving p)
      (Lp.compMeasurePreserving
        (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p)
        (deningerPrimePacketArithmeticFrobeniusQuotientMeasurePreserving p) g) = g
  apply Lp.ext
  let E :=
    deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p
  let hE :=
    deningerPrimePacketArithmeticFrobeniusQuotientMeasurePreserving p
  let hEsymm :=
    deningerPrimePacketArithmeticFrobeniusQuotientSymmMeasurePreserving p
  have houter :=
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving E hE g) hEsymm
  have hinner :=
    Lp.coeFn_compMeasurePreserving g hE
  have hinnerComp :=
    hEsymm.quasiMeasurePreserving.ae_eq_comp hinner
  exact houter.trans <| hinnerComp.trans <| Filter.Eventually.of_forall fun x => by
    exact congrArg g (ContinuousMulEquiv.apply_symm_apply E x)

/-- **Arithmetic Haar-L² comparison.**  Packet Haar-`L²` and literal arithmetic quotient
Haar-`L²` are canonically linearly isometric. -/
noncomputable def deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv
    (p : Nat.Primes) :
    DeningerPrimePacketHaarL2 p ≃ₗᵢ[ℝ]
      DeningerPrimeArithmeticHaarL2 p :=
  LinearIsometryEquiv.ofSurjective
    (deningerPrimePacketArithmeticHaarL2Forward p)
    (deningerPrimePacketArithmeticHaarL2Forward_surjective p)

/-- Pointwise meaning of the Haar-`L²` comparison: compose with the inverse arithmetic quotient
map, modulo almost-everywhere equality. -/
theorem deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv_coeFn_ae
    (p : Nat.Primes) (f : DeningerPrimePacketHaarL2 p) :
    deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p f =ᵐ[
        deningerPrimeArithmeticHaarMeasure p]
      f ∘
        (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p).symm := by
  change
    deningerPrimePacketArithmeticHaarL2Forward p f =ᵐ[
        deningerPrimeArithmeticHaarMeasure p]
      f ∘
        (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p).symm
  exact Lp.coeFn_compMeasurePreserving f
    (deningerPrimePacketArithmeticFrobeniusQuotientSymmMeasurePreserving p)

/-- Continuous packet data transported to the literal arithmetic quotient. -/
def deningerPrimePacketContinuousToArithmetic
    (p : Nat.Primes)
    (f : C(DeningerPacketFrobeniusQuotient p, ℝ)) :
    C(DeningerPrimeArithmeticMulAutFrobeniusQuotient p, ℝ) :=
  f.comp
    ⟨(deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p).symm,
      (deningerPrimePacketArithmeticFrobeniusQuotientContinuousMulEquiv p).symm.continuous⟩

/-- Canonical inclusion of continuous arithmetic-quotient data into arithmetic Haar-`L²`. -/
def deningerPrimeArithmeticContinuousToHaarL2 (p : Nat.Primes) :
    C(DeningerPrimeArithmeticMulAutFrobeniusQuotient p, ℝ) →L[ℝ]
      DeningerPrimeArithmeticHaarL2 p :=
  ContinuousMap.toLp 2 (deningerPrimeArithmeticHaarMeasure p) ℝ

/-- The Hilbert comparison intertwines continuous inclusions exactly. -/
theorem deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv_continuous
    (p : Nat.Primes)
    (f : C(DeningerPacketFrobeniusQuotient p, ℝ)) :
    deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p
        (deningerPrimePacketContinuousToHaarL2 p f) =
      deningerPrimeArithmeticContinuousToHaarL2 p
        (deningerPrimePacketContinuousToArithmetic p f) := by
  apply Lp.ext
  refine
    (deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv_coeFn_ae p
      (deningerPrimePacketContinuousToHaarL2 p f)).trans ?_
  have hf :=
    ContinuousMap.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := deningerPrimePacketHaarMeasure p)
      (𝕜 := ℝ) f
  have hfComp :=
    (deningerPrimePacketArithmeticFrobeniusQuotientSymmMeasurePreserving p).quasiMeasurePreserving
      |>.ae_eq_comp hf
  refine hfComp.trans ?_
  exact
    (ContinuousMap.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := deningerPrimeArithmeticHaarMeasure p)
      (𝕜 := ℝ)
      (deningerPrimePacketContinuousToArithmetic p f)).symm

end

end RHTower
