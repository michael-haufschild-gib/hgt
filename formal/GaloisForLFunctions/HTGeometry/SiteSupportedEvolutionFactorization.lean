import GaloisForLFunctions.HTGeometry.DecoupledEvolutionFactorization
import GaloisForLFunctions.HTGeometry.HypergraphComponentWitness
import GaloisForLFunctions.HTGeometry.SiteSupportedLocalHamiltonian

/-!
# Exact evolution factorization across disjoint site packets

Site support is stable under the exponential defining Schrödinger evolution.  Generators on
disjoint packets commute, and the evolution of their sum is exactly the ordered product of their
individual evolutions.  No approximation, time-ordering assumption, or commutativity premise is
left to the caller: disjoint physical support discharges commutativity.
-/

open scoped Kronecker Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- Evolution commutes exactly with lifting a packet matrix to the full product carrier. -/
theorem unitaryEvolution_liftLocalMatrix (S : Finset V)
    (B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ) (t : ℝ) :
    unitaryEvolution (liftLocalMatrix S B) t =
      liftLocalMatrix S (unitaryEvolution B t) := by
  letI : NormedAlgebra ℚ (Matrix ((v : V) → A v) ((v : V) → A v) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  letI : NormedAlgebra ℚ
      (Matrix (LocalConfiguration A S × OutsideConfiguration A S)
        (LocalConfiguration A S × OutsideConfiguration A S) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let e := configurationSplitEquiv A S
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ e
  apply Φ.injective
  have hcont : Continuous Φ := Φ.toLinearEquiv.continuous_of_finiteDimensional
  have hmap := NormedSpace.map_exp Φ.toRingEquiv.toRingHom hcont
      (t • ((-Complex.I) • liftLocalMatrix S B))
  rw [unitaryEvolution, unitaryEvolution]
  rw [show Φ (NormedSpace.exp (t • ((-Complex.I) • liftLocalMatrix S B))) =
      NormedSpace.exp (Φ (t • ((-Complex.I) • liftLocalMatrix S B))) by exact hmap]
  have hgen : Φ (t • ((-Complex.I) • liftLocalMatrix S B)) =
      t • ((-Complex.I) • Φ (liftLocalMatrix S B)) := by
    calc
      Φ (t • ((-Complex.I) • liftLocalMatrix S B)) =
          t • Φ ((-Complex.I) • liftLocalMatrix S B) :=
        Φ.toLinearMap.map_smul_of_tower t _
      _ = t • ((-Complex.I) • Φ (liftLocalMatrix S B)) := by
        rw [map_smul]
  rw [hgen]
  have hLift : Φ (liftLocalMatrix S B) =
      B ⊗ₖ (1 : Matrix (OutsideConfiguration A S) (OutsideConfiguration A S) ℂ) :=
    reindex_liftLocalMatrix_eq_kronecker_one S B
  rw [hLift]
  rw [← Matrix.smul_kronecker, ← Matrix.smul_kronecker]
  rw [exp_kronecker_one]
  exact reindex_liftLocalMatrix_eq_kronecker_one S _ |>.symm

/-- Evolution preserves intrinsic site support. -/
theorem isSiteSupported_unitaryEvolution [∀ v, Nonempty (A v)]
    {S : Finset V} {H : Matrix ((v : V) → A v) ((v : V) → A v) ℂ}
    (hH : IsSiteSupported S H) (t : ℝ) :
    IsSiteSupported S (unitaryEvolution H t) := by
  obtain ⟨B, rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hH
  rw [unitaryEvolution_liftLocalMatrix]
  exact isSiteSupported_liftLocalMatrix S _

/-- Operators supported on disjoint site packets commute. -/
theorem commute_of_isSiteSupported_disjoint [∀ v, Nonempty (A v)]
    {S T : Finset V}
    {H K : Matrix ((v : V) → A v) ((v : V) → A v) ℂ}
    (hST : Disjoint S T) (hH : IsSiteSupported S H) (hK : IsSiteSupported T K) :
    Commute H K := by
  obtain ⟨B, rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hH
  obtain ⟨C, rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hK
  let e := configurationSplitEquiv A S
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ e
  apply Φ.injective
  rw [show Φ (liftLocalMatrix S B * liftLocalMatrix T C) =
      Φ (liftLocalMatrix S B) * Φ (liftLocalMatrix T C) by exact map_mul Φ _ _]
  rw [show Φ (liftLocalMatrix T C * liftLocalMatrix S B) =
      Φ (liftLocalMatrix T C) * Φ (liftLocalMatrix S B) by exact map_mul Φ _ _]
  rw [show Φ (liftLocalMatrix S B) =
      B ⊗ₖ (1 : Matrix (OutsideConfiguration A S) (OutsideConfiguration A S) ℂ) by
        exact reindex_liftLocalMatrix_eq_kronecker_one S B]
  rw [show Φ (liftLocalMatrix T C) =
      (1 : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ) ⊗ₖ
        liftLocalMatrixOutsideDisjoint hST C by
        exact reindex_liftLocalMatrix_disjoint_eq_one_kronecker hST C]
  exact (commute_kronecker_one_one_kronecker B
    (liftLocalMatrixOutsideDisjoint hST C)).eq

/-- Evolution of a sum on disjoint packets factorizes exactly. -/
theorem unitaryEvolution_add_of_isSiteSupported_disjoint [∀ v, Nonempty (A v)]
    {S T : Finset V}
    {H K : Matrix ((v : V) → A v) ((v : V) → A v) ℂ}
    (hST : Disjoint S T) (hH : IsSiteSupported S H) (hK : IsSiteSupported T K)
    (t : ℝ) :
    unitaryEvolution (H + K) t = unitaryEvolution H t * unitaryEvolution K t := by
  letI : NormedAlgebra ℚ (Matrix ((v : V) → A v) ((v : V) → A v) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hbase : Commute H K := commute_of_isSiteSupported_disjoint hST hH hK
  have hleftI : Commute ((-Complex.I) • H) K := hbase.smul_left (-Complex.I)
  have hleftT : Commute (t • ((-Complex.I) • H)) K := hleftI.smul_left t
  have hrightI : Commute (t • ((-Complex.I) • H)) ((-Complex.I) • K) :=
    hleftT.smul_right (-Complex.I)
  have hcomm : Commute (t • ((-Complex.I) • H)) (t • ((-Complex.I) • K)) :=
    hrightI.smul_right t
  rw [unitaryEvolution, unitaryEvolution, unitaryEvolution, smul_add, smul_add,
    NormedSpace.exp_add_of_commute hcomm]

end

end GaloisForLFunctions.HTGeometry
