import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAllRankQSystem
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCriticalMultiplicity
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPageTransition
import Mathlib.LinearAlgebra.Dimension.Finrank

open GaloisForLFunctions
open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- The finite coefficient matrix of the reciprocal tangent law `δY = -Y² δX`. -/
noncomputable def truncatedReciprocalTangentMatrix
    {K : Type*} [Field K] (Y : Polynomial K) (N : ℕ) :
    Matrix (Fin N) (Fin N) K :=
  fun r i => if (i : ℕ) ≤ (r : ℕ) then -(Y * Y).coeff ((r : ℕ) - (i : ℕ)) else 0

/-- The reciprocal tangent law on the `N`-coefficient truncated jet space. -/
noncomputable def truncatedReciprocalTangentMap
    {K : Type*} [Field K] (Y : Polynomial K) (N : ℕ) :
    (Fin N → K) →ₗ[K] (Fin N → K) :=
  Matrix.toLin' (truncatedReciprocalTangentMatrix Y N)

theorem linearMap_graph_finrank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (f : V →ₗ[K] V) :
    Module.finrank K f.graph = Module.finrank K V := by
  rw [LinearMap.graph_eq_range_prod]
  apply LinearMap.finrank_range_of_inj
  intro x y h
  have hp := congrArg Prod.fst h
  simpa using hp

/-- The reciprocal tangent graph has exactly half the dimension of the ambient truncated
raw/cotangent space.  Together with `criticalReciprocalGraph_isotropic`, this is the finite
Lagrangian dimension statement. -/
theorem truncatedReciprocalTangentGraph_half_dimension
    {K : Type*} [Field K] (Y : Polynomial K) (N : ℕ) :
    2 * Module.finrank K (truncatedReciprocalTangentMap Y N).graph =
      Module.finrank K ((Fin N → K) × (Fin N → K)) := by
  rw [linearMap_graph_finrank]
  simp
  omega

/-- One source together with the hypothesis that makes every finite polarization algebraically
generic.  Its methods expose the single reciprocal-series tower and its full Q-system. -/
structure HypertranscendentalPolarizationTower
    (F E : Type*) [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E] where
  source : E
  sourceHT : HypertranscendentalOver F source

namespace HypertranscendentalPolarizationTower

noncomputable def rawSeries
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) : PowerSeries E :=
  normalizedDifferentialJetSeries T.source

noncomputable def reciprocalSeries
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) : PowerSeries E :=
  T.rawSeries⁻¹

noncomputable def coefficient
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) (k : ℕ) : E :=
  PowerSeries.coeff k (T.reciprocalSeries ^ 2)

noncomputable def amplitude
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) (m n : ℕ) : E :=
  horizonAmplitude T.coefficient m n

theorem source_ne_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) : T.source ≠ 0 := by
  intro hz
  exact (hypertranscendentalOver_jet_transcendental T.sourceHT 0) (by
    simpa [hz, differentialJet_zero] using (isAlgebraic_zero : IsAlgebraic F (0 : E)))

theorem rawSeries_constantCoeff
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) :
    PowerSeries.constantCoeff T.rawSeries = 1 :=
  normalizedDifferentialJetSeries_constantCoeff T.source T.source_ne_zero

theorem raw_mul_reciprocal
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) :
    T.rawSeries * T.reciprocalSeries = 1 :=
  PowerSeries.mul_inv_cancel T.rawSeries (by rw [T.rawSeries_constantCoeff]; exact one_ne_zero)

theorem coefficient_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) : T.coefficient 0 = 1 :=
  hypertranscendentalHorizonCoefficient_zero T.source T.source_ne_zero

theorem coefficient_eq_horizonCoefficient
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) (k : ℕ) :
    T.coefficient k = hypertranscendentalHorizonCoefficient T.source k := rfl

theorem amplitude_eq_horizonAmplitude
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) (m n : ℕ) :
    T.amplitude m n = hypertranscendentalHorizonAmplitude T.source m n := rfl

theorem noncaustic
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) : T.amplitude m n ≠ 0 :=
  hypertranscendentalHorizonAmplitude_ne_zero T.sourceHT m n hm hn

@[simp]
theorem zero_rank
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) (n : ℕ) : T.amplitude 0 n = 1 :=
  hypertranscendentalHorizonAmplitude_zero_rank T.source n

theorem zero_depth
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) (m : ℕ) : T.amplitude m 0 = 1 :=
  hypertranscendentalHorizonAmplitude_zero_depth T.source T.source_ne_zero m

theorem qSystem
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) (c n : ℕ) (hn : 0 < n) :
    T.amplitude (c + 1) n ^ 2 =
      T.amplitude (c + 1) (n - 1) * T.amplitude (c + 1) (n + 1) +
        T.amplitude c n * T.amplitude (c + 2) n :=
  hypertranscendentalHorizonAmplitude_qSystem T.sourceHT c n hn

theorem zeroPropagation
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    (T : HypertranscendentalPolarizationTower F E) (c n : ℕ) (hn : 0 < n)
    (hcenter : T.amplitude (c + 1) n = 0)
    (hleft : T.amplitude (c + 1) (n - 1) = 0) :
    T.amplitude c n = 0 ∨ T.amplitude (c + 2) n = 0 :=
  hypertranscendentalHorizonCaustic_zero_propagation T.sourceHT c n hn hcenter hleft

end HypertranscendentalPolarizationTower

end GaloisForLFunctions.HTGeometry

