import GaloisForLFunctions.HTGeometry.DifferentialAdjoinMobiusGenerator
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.KolchinSlopeDichotomy

/-!
# The wedge four-point exchange carrier

The connected four-point function of a wedge-local polarization-free generator has the exact
two-rapidity coefficient `K₄ = S₂ − 1`.  This file records the differential-algebraic content of
that identity: the coefficient and the exchange function generate the same differential field, so
they have the same differential-algebraic class, the same hypertranscendence class, and the same
normalized Kolchin slope.  The hypertranscendence of a factorizing scattering function is therefore
visible already in the first connected vacuum correlator sector.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exact two-rapidity connected four-point coefficient of a wedge-local polarization-free
generator with exchange function `S`. -/
def wedgeFourPointCoefficient {K : Type*} [Field K] (S : K) : K := S - 1

/-- **The coefficient is a differential generator.**  The exchange function and its connected
four-point coefficient generate the same differential field over the kinematic base. -/
theorem differentialAdjoin_wedgeFourPointCoefficient
    {C K : Type*} [Field C] [Field K] [Differential C] [Differential K]
    [Algebra C K] [DifferentialAlgebra C K] (S : K) :
    differentialAdjoin C ({wedgeFourPointCoefficient S} : Set K)
      = differentialAdjoin C ({S} : Set K) := by
  unfold wedgeFourPointCoefficient
  have hS : S ∈ differentialAdjoin C ({S} : Set K) := subset_differentialAdjoin C _ rfl
  have hcoeff : S - 1 ∈ differentialAdjoin C ({S} : Set K) := sub_mem hS (one_mem _)
  have hc : S - 1 ∈ differentialAdjoin C ({S - 1} : Set K) :=
    subset_differentialAdjoin C _ rfl
  have hback : S ∈ differentialAdjoin C ({S - 1} : Set K) := by
    have h2 : S - 1 + 1 ∈ differentialAdjoin C ({S - 1} : Set K) := add_mem hc (one_mem _)
    simpa using h2
  exact differentialAdjoin_singleton_eq_of_mem_mem hcoeff hback

/-- **Hypertranscendence transfer.**  The exchange function is hypertranscendental exactly when its
connected four-point coefficient is. -/
theorem hypertranscendentalOver_wedgeFourPointCoefficient_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {S : E} :
    HypertranscendentalOver F (wedgeFourPointCoefficient S) ↔ HypertranscendentalOver F S := by
  have hnegOne : DifferentialAlgebraicOver F (-(1 : E)) := by
    have h1 : DifferentialAlgebraicOver F ((1 : E)) := by
      simpa using differentialAlgebraicOver_algebraMap (F := F) (E := E) 1
    simpa using differentialAlgebraicOver_sub
      (differentialAlgebraicOver_algebraMap (F := F) (E := E) 0) h1
  have h := hypertranscendentalOver_add_differentialAlgebraic_iff (x := S) hnegOne
  simpa [wedgeFourPointCoefficient, sub_eq_add_neg] using h

/-- **Differential-algebraic transfer.**  The exchange function is differentially algebraic exactly
when its connected four-point coefficient is. -/
theorem differentialAlgebraicOver_wedgeFourPointCoefficient_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {S : E} :
    DifferentialAlgebraicOver F (wedgeFourPointCoefficient S)
      ↔ DifferentialAlgebraicOver F S := by
  have h := hypertranscendentalOver_wedgeFourPointCoefficient_iff (F := F) (S := S)
  unfold HypertranscendentalOver at h
  constructor
  · intro hda
    by_contra hS
    exact (h.mpr hS) hda
  · intro hda
    by_contra hc
    exact (h.mp hc) hda

/-- **The connected sector carries the full Kolchin slope.**  If the exchange function is
hypertranscendental, the normalized jet-rank slope of the connected four-point coefficient is `1`. -/
theorem tendsto_kolchinSlope_one_wedgeFourPointCoefficient
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {S : E} (hS : HypertranscendentalOver F S) :
    Filter.Tendsto
      (normalizedRankSequence (kolchinJetRank F (wedgeFourPointCoefficient S)))
      Filter.atTop (nhds 1) :=
  tendsto_kolchinSlope_one_of_hypertranscendentalOver
    (hypertranscendentalOver_wedgeFourPointCoefficient_iff.mpr hS)

/-- The differentially algebraic branch: the connected coefficient then has slope `0`. -/
theorem tendsto_kolchinSlope_zero_wedgeFourPointCoefficient
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {S : E} (hS : DifferentialAlgebraicOver F S) :
    Filter.Tendsto
      (normalizedRankSequence (kolchinJetRank F (wedgeFourPointCoefficient S)))
      Filter.atTop (nhds 0) :=
  tendsto_kolchinSlope_zero_of_differentialAlgebraicOver
    (differentialAlgebraicOver_wedgeFourPointCoefficient_iff.mpr hS)

end

end GaloisForLFunctions.HTGeometry
