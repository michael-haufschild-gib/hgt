import GaloisForLFunctions.HTGeometry.ActivePauliShellRateLaw
import GaloisForLFunctions.HTGeometry.ProductCliffordLabelAction
import GaloisForLFunctions.HTGeometry.ShellProbabilityMeasure

/-!
# Product-Clifford covariance of the active Pauli shell

Product Clifford conjugation preserves Pauli support exactly.  It therefore restricts to a signed
permutation of the active nonidentity weight-at-most-`q` dictionary, conjugates the corrected
Hamiltonian by that signed coefficient permutation, and preserves the corrected shell law.
-/

open Matrix MeasureTheory
open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem pauliWeight_productCliffordRelabel {n : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (P : Fin n → Option (Fin 3)) :
    pauliWeight (productCliffordRelabel g P) = pauliWeight P := by
  classical
  simp only [pauliWeight]
  congr 1
  ext s
  simp [productCliffordRelabel_none_iff]

theorem productCliffordRelabel_ne_identity_iff {n : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (P : Fin n → Option (Fin 3)) :
    productCliffordRelabel g P ≠ pauliIdentityLabel n ↔ P ≠ pauliIdentityLabel n := by
  constructor
  · contrapose!
    intro h
    subst P
    funext s
    exact (productCliffordRelabel_none_iff g (pauliIdentityLabel n) s).mpr rfl
  · contrapose!
    intro h
    funext s
    apply (productCliffordRelabel_none_iff g P s).mp
    exact congrFun h s

/-- Product-Clifford relabelling restricted to the active dictionary. -/
def productCliffordActiveRelabel {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    PauliTracelessLabel n q → PauliTracelessLabel n q :=
  fun P => ⟨productCliffordRelabel g P.1,
    (pauliWeight_productCliffordRelabel g P.1).trans_le P.2.1,
    (productCliffordRelabel_ne_identity_iff g P.1).mpr P.2.2⟩

theorem productCliffordActiveRelabel_injective {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    Function.Injective (productCliffordActiveRelabel (q := q) g) := by
  intro P Q hPQ
  apply Subtype.ext
  apply productCliffordRelabel_injective g
  exact congrArg Subtype.val hPQ

/-- Product-Clifford relabelling is a permutation of the active dictionary. -/
def productCliffordActiveRelabelEquiv {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    Equiv.Perm (PauliTracelessLabel n q) :=
  Equiv.ofBijective (productCliffordActiveRelabel (q := q) g)
    (Finite.injective_iff_bijective.mp (productCliffordActiveRelabel_injective (q := q) g))

@[simp] theorem productCliffordActiveRelabelEquiv_apply {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral) (P : PauliTracelessLabel n q) :
    productCliffordActiveRelabelEquiv (q := q) g P = productCliffordActiveRelabel g P := rfl

/-- Signed coefficient permutation induced by product-Clifford conjugation on the active shell. -/
def activeCliffordCoefficientMap {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (J : PauliTracelessLabel n q → ℝ) : PauliTracelessLabel n q → ℝ :=
  fun Q => productCliffordSign g
      ((productCliffordActiveRelabelEquiv (q := q) g).symm Q).1 *
    J ((productCliffordActiveRelabelEquiv (q := q) g).symm Q)

/-- Product-Clifford conjugation acts on active coefficients by the signed permutation above. -/
theorem activePauliHamiltonian_conj {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (J : PauliTracelessLabel n q → ℝ) :
    finiteProductCliffordGate g *
        activePauliHamiltonian (fun P => (J P : ℂ)) *
        (finiteProductCliffordGate g)ᴴ =
      activePauliHamiltonian (fun Q => (activeCliffordCoefficientMap g J Q : ℂ)) := by
  classical
  rw [activePauliHamiltonian, Finset.mul_sum, Finset.sum_mul]
  have hterm : ∀ P : PauliTracelessLabel n q,
      finiteProductCliffordGate g * ((J P : ℂ) • finitePauliMatrix P.1) *
          (finiteProductCliffordGate g)ᴴ =
        ((activeCliffordCoefficientMap g J
          (productCliffordActiveRelabelEquiv (q := q) g P) : ℝ) : ℂ) •
          finitePauliMatrix (productCliffordActiveRelabelEquiv (q := q) g P).1 := by
    intro P
    rw [Matrix.mul_smul, Matrix.smul_mul,
      finiteProductCliffordGate_conj_finitePauliMatrix_relabel g P.1]
    rw [activeCliffordCoefficientMap, Equiv.symm_apply_apply]
    simp only [productCliffordActiveRelabelEquiv_apply, productCliffordActiveRelabel]
    rw [smul_smul, ← ofReal_productCliffordSign g P.1]
    push_cast
    congr 1
    ring
  rw [Finset.sum_congr rfl fun P (_ : P ∈ Finset.univ) => hterm P,
    activePauliHamiltonian]
  exact Fintype.sum_equiv (productCliffordActiveRelabelEquiv (q := q) g) _ _ fun P => rfl

/-- The corrected active-shell law is product-Clifford invariant. -/
theorem measurePreserving_activeCliffordCoefficientMap_shell {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    MeasurePreserving (activeCliffordCoefficientMap (q := q) g)
      (shellProbability (PauliTracelessLabel n q))
      (shellProbability (PauliTracelessLabel n q)) := by
  exact measurePreserving_signedPerm_shellProbability
    (productCliffordActiveRelabelEquiv (q := q) g).symm
    (ε := fun Q => productCliffordSign g
      ((productCliffordActiveRelabelEquiv (q := q) g).symm Q).1)
    (fun _ => productCliffordSign_eq_one_or_neg_one g _)

end GaloisForLFunctions.HTGeometry
