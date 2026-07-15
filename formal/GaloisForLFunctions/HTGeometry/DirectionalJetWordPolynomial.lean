import GaloisForLFunctions.HTGeometry.DirectionalDerivationLawSpace
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Noncommutative directional jets as homogeneous law-coordinate polynomials

Iterating a constant linear combination of derivations expands over ordered derivation words; no
commutativity is used.  The resulting universal polynomial is homogeneous in the direction
coordinates and specializes exactly to the genuine directional jet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {k L ι : Type*} [Field k] [Field L] [Algebra k L]
  [Fintype ι]

/-- The ordered composition attached to a noncommutative derivation word. -/
def directionalWordDerivative (δ : ι → Derivation k L L) (x : L) :
    {n : ℕ} → (Fin n → ι) → L
  | 0, _ => x
  | _ + 1, w => δ (w 0) (directionalWordDerivative δ x (fun j => w j.succ))

omit [Fintype ι] in
@[simp]
theorem directionalWordDerivative_zero
    (δ : ι → Derivation k L L) (x : L) (w : Fin 0 → ι) :
    directionalWordDerivative δ x w = x := rfl

omit [Fintype ι] in
@[simp]
theorem directionalWordDerivative_cons
    (δ : ι → Derivation k L L) (x : L) (i : ι) {n : ℕ} (w : Fin n → ι) :
    directionalWordDerivative δ x (Fin.cons i w) =
      δ i (directionalWordDerivative δ x w) := by
  rfl

/-- Expansion of a directional jet over all ordered derivation words. -/
theorem directionalJet_eq_sum_words
    (δ : ι → Derivation k L L) (c : ι → k) (x : L) : ∀ n : ℕ,
    directionalJet δ c n x =
      ∑ w : Fin n → ι,
        (∏ r, c (w r)) • directionalWordDerivative δ x w := by
  intro n
  induction n with
  | zero => simp [directionalJet]
  | succ n ih =>
      rw [directionalJet_succ, ih, map_sum]
      simp_rw [Derivation.map_smul, directionalDerivation_apply, Finset.smul_sum]
      rw [Finset.sum_comm]
      calc
        (∑ i, ∑ w : Fin n → ι,
            (∏ r, c (w r)) • c i • δ i (directionalWordDerivative δ x w)) =
            ∑ iw : ι × (Fin n → ι),
              (∏ r, c (iw.2 r)) • c iw.1 •
                δ iw.1 (directionalWordDerivative δ x iw.2) := by
                  exact (Fintype.sum_prod_type
                    (γ := L) (fun iw : ι × (Fin n → ι) =>
                      (∏ r, c (iw.2 r)) • c iw.1 •
                        δ iw.1 (directionalWordDerivative δ x iw.2))).symm
        _ = ∑ w : Fin (n + 1) → ι,
            (∏ r, c (w r)) • directionalWordDerivative δ x w := by
          refine Fintype.sum_equiv
            (M := L) (Fin.consEquiv (fun _ : Fin (n + 1) => ι))
            (fun iw => (∏ r, c (iw.2 r)) • c iw.1 •
              δ iw.1 (directionalWordDerivative δ x iw.2))
            (fun w => (∏ r, c (w r)) • directionalWordDerivative δ x w) ?_
          rintro ⟨i, w⟩
          dsimp
          rw [show (Fin.consEquiv (fun _ : Fin (n + 1) => ι)) (i, w) =
            Fin.cons i w by rfl, directionalWordDerivative_cons]
          simp [Fin.prod_univ_succ, smul_smul, mul_comm]

/-- The universal word polynomial whose specialization is the `n`-th directional jet. -/
def directionalJetWordPolynomial
    (δ : ι → Derivation k L L) (x : L) (n : ℕ) : MvPolynomial ι L :=
  ∑ w : Fin n → ι,
    MvPolynomial.C (directionalWordDerivative δ x w) *
      ∏ r, MvPolynomial.X (w r)

/-- Evaluating the universal word polynomial at a direction gives the genuine jet. -/
theorem eval_directionalJetWordPolynomial
    (δ : ι → Derivation k L L) (c : ι → k) (x : L) (n : ℕ) :
    MvPolynomial.eval (fun i => algebraMap k L (c i))
        (directionalJetWordPolynomial δ x n) =
      directionalJet δ c n x := by
  rw [directionalJet_eq_sum_words δ c x n]
  simp [directionalJetWordPolynomial, Algebra.smul_def, mul_comm]

/-- Every term in the universal word polynomial has total degree `n`. -/
theorem directionalJetWordPolynomial_isHomogeneous
    (δ : ι → Derivation k L L) (x : L) (n : ℕ) :
    IsHomogeneous (directionalJetWordPolynomial δ x n) n := by
  apply IsHomogeneous.sum Finset.univ
  intro w hw
  have hp : IsHomogeneous (∏ r, X (w r) : MvPolynomial ι L)
      (∑ _ : Fin n, 1) :=
    IsHomogeneous.prod Finset.univ (fun r => X (w r)) (fun _ => 1)
      (fun r _ => isHomogeneous_X L (w r))
  simpa using (isHomogeneous_C ι (directionalWordDerivative δ x w)).mul hp

end

end GaloisForLFunctions.HTGeometry
