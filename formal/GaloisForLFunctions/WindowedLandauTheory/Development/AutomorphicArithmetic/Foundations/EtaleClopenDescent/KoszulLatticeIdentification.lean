import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulLatticeExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulLatticeBoundaryValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorLatticeDiagonalKernel

/-! Compare the integral and ambient descriptions of the same Koszul
column using equality of the coefficient lattice and of the actions. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD

namespace GlobalTheory.WH

variable {k R V ι : Type} [Field k] [CommRing R] [Algebra k R] [LinearOrder ι]
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]

/-- Exactness is unchanged under identifying the ambient action with
the intrinsic lattice action. -/
theorem acx_exact_of_lattice_identification
    (P : Submodule R V) (r : ι → R) (M : Submodule k V) (w : ι → Module.End k V)
    (hM : P.restrictScalars k = M)
    (hw : (fun i => Algebra.lsmul k k V (r i)) = w)
    (n : ℤ) (hex : ∀ a : Finset ι → P, (∀ t : Finset ι, (t.card : ℤ) ≠ n → a t = 0) →
      koszulDifferential r a = 0 → ∃ b : Finset ι → P,
        (∀ t : Finset ι, (t.card : ℤ) ≠ n - 1 → b t = 0) ∧ koszulDifferential r b = a) :
    let C := acx (fun _ => M) w
    C.Z n ≤ C.B n := by
  subst M w
  exact acx_lattice_exact P r n hex

/-- The intrinsic ideal multiple gives selected boundary values after
identifying the actions on the coefficient lattice. -/
theorem mem_selectedBoundaryValues_of_lattice_identification {d : ℕ}
    (P : Submodule R V) (r : ι → R) (M : Submodule k V) (w : ι → Module.End k V)
    (hM : P.restrictScalars k = M)
    (hw : (fun i => Algebra.lsmul k k V (r i)) = w)
    (e : Fin d ↪o ι) (v : P)
    (hv : v ∈ idealMultiple (M := P) (Ideal.span (Set.range (fun j => r (e j))))) :
    (v : V) ∈ selectedBoundaryValues M w e := by
  subst M w
  rw [selectedBoundaryValues_eq_ideal_smul]
  exact ⟨v, hv, rfl⟩

end GlobalTheory.WH
