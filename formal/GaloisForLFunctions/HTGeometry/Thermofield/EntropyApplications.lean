import GaloisForLFunctions.HTGeometry.Thermofield.FinitePurification
import GaloisForLFunctions.HTGeometry.Thermofield.ThermalReturnPlateau
import GaloisForLFunctions.HTGeometry.GibbsSizeBiasEntropy

/-!
# Entanglement entropy and persistent thermal return

The spectral entropy of the thermofield marginal is its Gibbs Shannon entropy.
Comparing the Gibbs law with twice its inverse temperature identifies the gap
between Shannon entropy and collision entropy as a relative entropy. Hence
the long-time return plateau is bounded below by the exponential of minus the
actual entanglement entropy.

These identities connect the entangled-state and finite-entropy mechanisms of
Maldacena, *Eternal black holes in Anti-de-Sitter*, arXiv:hep-th/0106112, to the
corpus spectral, Gibbs, and relative-entropy constructions.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry.Thermofield

open _root_.HTGeometry

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- A real diagonal spectrum gives a Hermitian complex matrix. -/
theorem realDiagonal_isHermitian (p : α → ℝ) :
    (Matrix.diagonal fun a => (p a : ℂ)).IsHermitian := by
  change (Matrix.diagonal fun a => (p a : ℂ))ᴴ = Matrix.diagonal fun a => (p a : ℂ)
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  exact Complex.conj_ofReal _

/-- Spectral entropy of a real diagonal matrix is the entropy of its entries.
Characteristic-polynomial roots retain every eigenvalue multiplicity. -/
theorem vonNeumannEntropy_real_diagonal (p : α → ℝ) :
    finiteMatrixVonNeumannEntropy (Matrix.diagonal fun a => (p a : ℂ))
      (realDiagonal_isHermitian p) = entropy p := by
  classical
  have hdiag : (Matrix.diagonal fun a => (p a : ℂ)).charpoly.roots =
      (Finset.univ : Finset α).val.map (fun a => (p a : ℂ)) := by
    rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod]
    simpa only [Multiset.map_map, Function.comp_def] using
      Polynomial.roots_multiset_prod_X_sub_C
        ((Finset.univ : Finset α).val.map (fun a => (p a : ℂ)))
  have hroots := (realDiagonal_isHermitian p).roots_charpoly_eq_eigenvalues
  rw [hdiag] at hroots
  have hsum := congrArg
    (fun s : Multiset ℂ => (s.map fun z => -(z.re * Real.log z.re)).sum) hroots
  simpa [finiteMatrixVonNeumannEntropy, entropy, tsum_fintype, Function.comp_def]
    using hsum.symm

/-- Actual spectral entropy after tracing out the right partner. -/
def entanglementEntropy (β : ℝ) (E : α → ℝ) : ℝ :=
  finiteMatrixVonNeumannEntropy
    (pureStateReducedLeft (fun p => amplitude β E p.1 p.2))
    (pureStateReducedLeft_isHermitian (fun p => amplitude β E p.1 p.2))

variable [Nonempty α]

omit [DecidableEq α] in
private theorem thermal_relativeEntropy_nonneg (β γ : ℝ) (E : α → ℝ) :
    0 ≤ relEntropy (finiteGibbsStateWeight β E) (finiteGibbsStateWeight γ E) := by
  apply relEntropy_nonneg (fun a => (finiteGibbsStateWeight_pos β E a).le)
    (finiteGibbsStateWeight_pos γ E)
  · simpa only [sum_finiteGibbsStateWeight_eq_one] using
      hasSum_fintype (finiteGibbsStateWeight β E)
  · simpa only [sum_finiteGibbsStateWeight_eq_one] using
      hasSum_fintype (finiteGibbsStateWeight γ E)
  · exact (hasSum_fintype _).summable

/-- Entanglement entropy is exactly the Shannon entropy of the Gibbs law. -/
theorem entanglementEntropy_eq_gibbs (β : ℝ) (E : α → ℝ) :
    entanglementEntropy β E = entropy (finiteGibbsStateWeight β E) := by
  simpa only [entanglementEntropy, reduced_left, density] using
    vonNeumannEntropy_real_diagonal (finiteGibbsStateWeight β E)

/-- The other boundary has the same actual spectral thermal entropy. -/
theorem right_entropy_eq_gibbs (β : ℝ) (E : α → ℝ) :
    finiteMatrixVonNeumannEntropy
        (pureStateReducedRight (fun p => amplitude β E p.1 p.2))
        (pureStateReducedRight_isHermitian (fun p => amplitude β E p.1 p.2)) =
      entropy (finiteGibbsStateWeight β E) := by
  rw [← pureStateReduced_entropies_eq (fun p : α × α => amplitude β E p.1 p.2)]
  exact entanglementEntropy_eq_gibbs β E

/-- The deficit from maximal entanglement is relative entropy from infinite temperature. -/
theorem entanglementEntropy_capacity_split (β : ℝ) (E : α → ℝ) :
    entanglementEntropy β E +
        relEntropy (finiteGibbsStateWeight β E) (finiteGibbsStateWeight 0 E) =
      Real.log (Fintype.card α : ℝ) := by
  have hzero (a : α) :
      Real.log (finiteGibbsStateWeight 0 E a) = -Real.log (Fintype.card α : ℝ) := by
    simp [finiteGibbsStateWeight, finiteGibbsPartition]
  have hc : crossEntropy (finiteGibbsStateWeight β E) (finiteGibbsStateWeight 0 E) =
      Real.log (Fintype.card α : ℝ) := by
    simp only [crossEntropy, tsum_fintype, hzero, mul_neg, neg_neg,
      ← Finset.sum_mul, sum_finiteGibbsStateWeight_eq_one, one_mul]
  have h := entropy_add_relEntropy (fun a => (finiteGibbsStateWeight_pos β E a).le)
    (finiteGibbsStateWeight_pos 0 E) (hasSum_fintype _).summable (hasSum_fintype _).summable
  rw [hc] at h
  rw [entanglementEntropy_eq_gibbs]
  exact h

/-- Hilbert-space dimension bounds the thermofield entanglement entropy. -/
theorem entanglementEntropy_le_log_card (β : ℝ) (E : α → ℝ) :
    entanglementEntropy β E ≤ Real.log (Fintype.card α : ℝ) := by
  have h := entanglementEntropy_capacity_split β E
  have hk := thermal_relativeEntropy_nonneg β 0 E
  linarith only [h, hk]

/-- The spectral entanglement entropy obeys the canonical partition identity. -/
theorem entanglementEntropy_partition {n : ℕ} (β : ℝ) (E : Fin (n + 1) → ℝ) :
    entanglementEntropy β E =
      Real.log (finiteGibbsPartition β E) + β * finiteGibbsEnergyMean β E := by
  have h := entanglementEntropy_capacity_split β E
  have hZ0 : finiteGibbsPartition 0 E = (Fintype.card (Fin (n + 1)) : ℝ) := by
    simp [finiteGibbsPartition]
  rw [finiteGibbs_relativeEntropy, hZ0] at h
  simp only [zero_sub, neg_mul] at h
  linarith only [h]

/-- The Shannon-versus-collision entropy gap is relative entropy between the
Gibbs states at inverse temperatures β and 2β. -/
theorem purity_entropy_gap {n : ℕ} (β : ℝ) (E : Fin (n + 1) → ℝ) :
    entanglementEntropy β E + Real.log (finiteGibbsPurity β E) =
      relEntropy (finiteGibbsStateWeight β E) (finiteGibbsStateWeight (2 * β) E) := by
  rw [entanglementEntropy_partition, finiteGibbsPurity_eq_partitionRatio,
    Real.log_div (finiteGibbsPartition_pos (2 * β) E).ne'
      (pow_ne_zero 2 (finiteGibbsPartition_pos β E).ne'),
    Real.log_pow, finiteGibbs_relativeEntropy]
  ring

/-- Gibbs purity is at least the exponential of minus entanglement entropy. -/
theorem exp_neg_entanglementEntropy_le_purity {n : ℕ}
    (β : ℝ) (E : Fin (n + 1) → ℝ) :
    Real.exp (-entanglementEntropy β E) ≤ finiteGibbsPurity β E := by
  have h := thermal_relativeEntropy_nonneg β (2 * β) E
  rw [← purity_entropy_gap] at h
  calc
    Real.exp (-entanglementEntropy β E) ≤ Real.exp (Real.log (finiteGibbsPurity β E)) :=
      Real.exp_le_exp.mpr (by linarith only [h])
    _ = finiteGibbsPurity β E := Real.exp_log (finiteGibbsPurity_pos β E)

/-- Finite thermal mean return has a positive floor set by actual entanglement entropy. -/
theorem exp_neg_entanglementEntropy_le_returnPlateau {n : ℕ}
    (β : ℝ) (E : Fin (n + 1) → ℝ) :
    Real.exp (-entanglementEntropy β E) ≤ returnPlateau β E :=
  (exp_neg_entanglementEntropy_le_purity β E).trans (purity_le_returnPlateau β E)

end

end GaloisForLFunctions.HTGeometry.Thermofield
