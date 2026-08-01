import GaloisForLFunctions.HTGeometry.ComplexPolynomialComplementPathConnected
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# Common-base transport in polynomial matrix families

For a polynomial matrix family, the fixed-size resultant of the
characteristic polynomial and its derivative is itself a polynomial in the
parameters.  A complete injective root packet makes this obstruction
nonzero.  Consequently any two such parameter points can be joined while
the obstruction remains nonzero.

This is the common-base transport mechanism needed to compare local
spectral transposition loops inside one polynomial Hamiltonian family.
-/

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

/-- Fixed-size characteristic resultant of a polynomial square matrix. -/
noncomputable def matrixCharacteristicResultantPolynomial
    {θ J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J (MvPolynomial θ ℂ)) :
    MvPolynomial θ ℂ :=
  Polynomial.resultant M.charpoly M.charpoly.derivative
    (Fintype.card J) (Fintype.card J - 1)

/-- Evaluating parameters commutes with the fixed-size characteristic
resultant. -/
theorem eval_matrixCharacteristicResultantPolynomial
    {θ J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J (MvPolynomial θ ℂ))
    (f : MvPolynomial θ ℂ →+* ℂ) :
    f (matrixCharacteristicResultantPolynomial M) =
      Polynomial.resultant (M.map f).charpoly
        (M.map f).charpoly.derivative
        (Fintype.card J) (Fintype.card J - 1) := by
  rw [matrixCharacteristicResultantPolynomial,
    ← Polynomial.resultant_map_map]
  rw [← Polynomial.derivative_map]
  rw [← Matrix.charpoly_map]

/-- A complete injective packet of characteristic roots forces the
fixed-size characteristic resultant to be nonzero. -/
theorem matrixCharacteristicResultant_ne_zero_of_complete_injective_roots
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : Matrix J J ℂ)
    (root : J → ℂ)
    (hinjective : Function.Injective root)
    (hroot : ∀ i, H.charpoly.eval (root i) = 0) :
    Polynomial.resultant H.charpoly H.charpoly.derivative
      (Fintype.card J) (Fintype.card J - 1) ≠ 0 := by
  let packet : Multiset ℂ :=
    Finset.univ.val.map root
  have hpacketNodup : packet.Nodup :=
    Finset.univ.nodup.map hinjective
  have hcharpolyNe : H.charpoly ≠ 0 :=
    H.charpoly_monic.ne_zero
  have hpacketLe : packet ≤ H.charpoly.roots := by
    rw [Multiset.le_iff_subset hpacketNodup]
    intro z hz
    simp only [packet, Multiset.mem_map] at hz
    obtain ⟨i, _hi, rfl⟩ := hz
    rw [Polynomial.mem_roots hcharpolyNe]
    exact hroot i
  have hrootsCard :
      H.charpoly.roots.card = Fintype.card J := by
    rw [Polynomial.splits_iff_card_roots.mp
      (IsAlgClosed.splits H.charpoly)]
    exact H.charpoly_natDegree_eq_dim
  have hpacketCard :
      packet.card = Fintype.card J := by
    simp [packet]
  have hpacketEq :
      packet = H.charpoly.roots := by
    apply Multiset.eq_of_le_of_card_le hpacketLe
    rw [hrootsCard, hpacketCard]
  have hrootsNodup : H.charpoly.roots.Nodup := by
    rw [← hpacketEq]
    exact hpacketNodup
  have hseparable : H.charpoly.Separable :=
    (Polynomial.nodup_roots_iff_of_splits
      hcharpolyNe (IsAlgClosed.splits H.charpoly)).mp
      hrootsNodup
  have hcoprime :
      IsCoprime H.charpoly H.charpoly.derivative :=
    (Polynomial.separable_def H.charpoly).mp
      hseparable
  have hresultant :
      Polynomial.resultant H.charpoly
        H.charpoly.derivative ≠ 0 := by
    intro hzero
    exact
      (Polynomial.resultant_eq_zero_iff.mp hzero).2
        hcoprime
  simpa [H.charpoly_natDegree_eq_dim,
    Polynomial.natDegree_derivative] using
    hresultant

/-- Any two parameter points with nonzero characteristic resultant can be
joined through the same nonzero-resultant locus. -/
theorem exists_parameterPath_avoiding_matrixCharacteristicResultant
    {θ J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J (MvPolynomial θ ℂ))
    {x y : θ → ℂ}
    (hx :
      MvPolynomial.eval x
        (matrixCharacteristicResultantPolynomial M) ≠ 0)
    (hy :
      MvPolynomial.eval y
        (matrixCharacteristicResultantPolynomial M) ≠ 0) :
    ∃ path : Path x y,
      ∀ s : I,
        MvPolynomial.eval (path s)
          (matrixCharacteristicResultantPolynomial M) ≠ 0 :=
  exists_path_avoiding_complexMvPolynomial_zero
    (matrixCharacteristicResultantPolynomial M) hx hy

/-- Complete distinct root packets at two parameter values provide the
endpoint certificates for a common nonzero-resultant transport path. -/
theorem exists_parameterPath_of_complete_injective_rootPackets
    {θ J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J (MvPolynomial θ ℂ))
    (x y : θ → ℂ)
    (rootX rootY : J → ℂ)
    (hinjectiveX : Function.Injective rootX)
    (hinjectiveY : Function.Injective rootY)
    (hrootX :
      ∀ i,
        (M.map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) x)).charpoly.eval
            (rootX i) = 0)
    (hrootY :
      ∀ i,
        (M.map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) y)).charpoly.eval
            (rootY i) = 0) :
    ∃ path : Path x y,
      ∀ s : I,
        MvPolynomial.eval (path s)
          (matrixCharacteristicResultantPolynomial M) ≠ 0 := by
  let evalX :=
    MvPolynomial.eval₂Hom (RingHom.id ℂ) x
  let evalY :=
    MvPolynomial.eval₂Hom (RingHom.id ℂ) y
  have hx :
      MvPolynomial.eval x
        (matrixCharacteristicResultantPolynomial M) ≠ 0 := by
    change
      evalX
        (matrixCharacteristicResultantPolynomial M) ≠ 0
    rw [eval_matrixCharacteristicResultantPolynomial]
    exact
      matrixCharacteristicResultant_ne_zero_of_complete_injective_roots
        (M.map evalX) rootX hinjectiveX hrootX
  have hy :
      MvPolynomial.eval y
        (matrixCharacteristicResultantPolynomial M) ≠ 0 := by
    change
      evalY
        (matrixCharacteristicResultantPolynomial M) ≠ 0
    rw [eval_matrixCharacteristicResultantPolynomial]
    exact
      matrixCharacteristicResultant_ne_zero_of_complete_injective_roots
        (M.map evalY) rootY hinjectiveY hrootY
  exact
    exists_parameterPath_avoiding_matrixCharacteristicResultant
      M hx hy

end GaloisForLFunctions.HTGeometry
