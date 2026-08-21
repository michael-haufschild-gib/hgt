/-
# The collision second moment on the nearest-neighbour Pauli shell

A product Clifford relabels a Pauli string without changing its support, so it acts on the
nearest-neighbour family by a signed permutation of coefficients, which the shell law preserves.
With almost-sure simple spectrum -- supplied by the nonvanishing of the family's spectral
discriminant -- the covariance argument gives the product-input mean collision bound `(2/3)^n` and
its Markov tail on the chain shell.

Main results:
* `chainEnsemble`, `reindex_chainEnsemble` — the chain Hamiltonian on the qubit register.
* `chainEnsemble_conj`, `measurePreserving_chainCliffordCoefficientMap` — the Clifford covariance.
* `integral_spectralCollision_chainShell_le` — **the mean collision bound `(2/3)^n`**.
* `measureReal_spectralCollision_chainShell_ge_le` — **its Markov tail**.
-/
import GaloisForLFunctions.HTGeometry.ChainPauliFinFamily
import GaloisForLFunctions.HTGeometry.ShellFamilySimpleSpectrum
import GaloisForLFunctions.HTGeometry.ActivePauliShellSecondMomentLaw

open Matrix MeasureTheory
open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- The Pauli label of a numbered chain index. -/
def chainLabelOf (n : ℕ) (a : Fin (Fintype.card (ChainLabel n))) : Fin n → Option (Fin 3) :=
  ((Fintype.equivFin (ChainLabel n)).symm a).1

theorem chainPauliFin_eq (n : ℕ) (a : Fin (Fintype.card (ChainLabel n))) :
    chainPauliFin n a = Matrix.reindex (qubitConfigFin n) (qubitConfigFin n)
      (finitePauliMatrix (chainLabelOf n a)) := rfl

/-- The nearest-neighbour Hamiltonian on the qubit register. -/
def chainEnsemble (n : ℕ) (θ : Fin (Fintype.card (ChainLabel n)) → ℝ) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ :=
  ∑ a, ((θ a : ℝ) : ℂ) • finitePauliMatrix (chainLabelOf n a)

theorem reindex_chainEnsemble (n : ℕ) (θ : Fin (Fintype.card (ChainLabel n)) → ℝ) :
    Matrix.reindex (qubitConfigFin n) (qubitConfigFin n) (chainEnsemble n θ)
      = spectralEnsembleMatrix (chainPauliFin n) θ := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, chainEnsemble,
    spectralEnsembleMatrix, Matrix.sum_apply, Matrix.smul_apply, chainPauliFin_eq]

theorem isHermitian_chainEnsemble (n : ℕ) (θ : Fin (Fintype.card (ChainLabel n)) → ℝ) :
    (chainEnsemble n θ).IsHermitian := by
  show (chainEnsemble n θ)ᴴ = chainEnsemble n θ
  rw [chainEnsemble, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_smul,
    show (finitePauliMatrix (chainLabelOf n a))ᴴ = finitePauliMatrix (chainLabelOf n a) from
      finitePauliMatrix_isHermitian _]
  congr 1
  exact Complex.conj_ofReal _

theorem measurable_chainEnsemble_entry (n : ℕ) (x y : FiniteQubitConfiguration (Fin n)) :
    Measurable fun θ : Fin (Fintype.card (ChainLabel n)) → ℝ => chainEnsemble n θ x y := by
  simp only [chainEnsemble, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun a _ => ?_
  exact (Complex.measurable_ofReal.comp (measurable_pi_apply a)).mul measurable_const

/-! ## The Clifford action on chain labels -/

theorem isChainLabel_productCliffordRelabel (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    {P : Fin n → Option (Fin 3)} (hP : IsChainLabel P) :
    IsChainLabel (productCliffordRelabel g P) := by
  intro i j hi hj
  exact hP i j (fun h => hi ((productCliffordRelabel_none_iff g P i).mpr h))
    (fun h => hj ((productCliffordRelabel_none_iff g P j).mpr h))

theorem productCliffordRelabel_ne_identity (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    {P : Fin n → Option (Fin 3)} (hP : P ≠ pauliIdentityLabel n) :
    productCliffordRelabel g P ≠ pauliIdentityLabel n := by
  intro hcon
  refine hP ?_
  funext s
  have := congrFun hcon s
  exact (productCliffordRelabel_none_iff g P s).mp this

/-- The Clifford relabelling as a permutation of the nearest-neighbour labels. -/
def chainRelabelEquiv (n : ℕ) (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    Equiv.Perm (ChainLabel n) :=
  Equiv.ofBijective
    (fun P => ⟨productCliffordRelabel g P.1,
      isChainLabel_productCliffordRelabel g P.2.1, productCliffordRelabel_ne_identity g P.2.2⟩)
    (Finite.injective_iff_bijective.mp (by
      intro P Q hPQ
      exact Subtype.ext (productCliffordRelabel_injective g (congrArg Subtype.val hPQ))))

@[simp] theorem chainRelabelEquiv_val (n : ℕ) (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (P : ChainLabel n) : ((chainRelabelEquiv n g) P).1 = productCliffordRelabel g P.1 := rfl

/-- The Clifford relabelling in numbered coordinates. -/
def chainFinRelabel (n : ℕ) (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    Equiv.Perm (Fin (Fintype.card (ChainLabel n))) :=
  (Fintype.equivFin (ChainLabel n)).symm.trans
    ((chainRelabelEquiv n g).trans (Fintype.equivFin (ChainLabel n)))

theorem chainLabelOf_chainFinRelabel (n : ℕ) (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (a : Fin (Fintype.card (ChainLabel n))) :
    chainLabelOf n (chainFinRelabel n g a) = productCliffordRelabel g (chainLabelOf n a) := by
  rw [chainLabelOf, chainFinRelabel]
  simp [chainLabelOf]

/-- The induced signed permutation of chain coefficients. -/
def chainCliffordCoefficientMap (n : ℕ) (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (θ : Fin (Fintype.card (ChainLabel n)) → ℝ) : Fin (Fintype.card (ChainLabel n)) → ℝ :=
  fun b => productCliffordSign g (chainLabelOf n ((chainFinRelabel n g).symm b)) *
    θ ((chainFinRelabel n g).symm b)

theorem measurePreserving_chainCliffordCoefficientMap (n : ℕ)
    (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    MeasurePreserving (chainCliffordCoefficientMap n g)
      (shellProbability (Fin (Fintype.card (ChainLabel n))))
      (shellProbability (Fin (Fintype.card (ChainLabel n)))) :=
  measurePreserving_signedPerm_shellProbability (chainFinRelabel n g).symm
    (fun _ => productCliffordSign_eq_one_or_neg_one g _)

/-- **Product-Clifford covariance of the nearest-neighbour ensemble.** -/
theorem chainEnsemble_conj (n : ℕ) (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (θ : Fin (Fintype.card (ChainLabel n)) → ℝ) :
    finiteProductCliffordGate g * chainEnsemble n θ * (finiteProductCliffordGate g)ᴴ
      = chainEnsemble n (chainCliffordCoefficientMap n g θ) := by
  classical
  rw [chainEnsemble, Finset.mul_sum, Finset.sum_mul]
  have hterm : ∀ a : Fin (Fintype.card (ChainLabel n)),
      finiteProductCliffordGate g * (((θ a : ℝ) : ℂ) • finitePauliMatrix (chainLabelOf n a)) *
          (finiteProductCliffordGate g)ᴴ
        = ((chainCliffordCoefficientMap n g θ (chainFinRelabel n g a) : ℝ) : ℂ) •
          finitePauliMatrix (chainLabelOf n (chainFinRelabel n g a)) := by
    intro a
    rw [Matrix.mul_smul, Matrix.smul_mul,
      finiteProductCliffordGate_conj_finitePauliMatrix_relabel g (chainLabelOf n a), smul_smul,
      chainLabelOf_chainFinRelabel]
    congr 1
    rw [chainCliffordCoefficientMap, Equiv.symm_apply_apply, ← ofReal_productCliffordSign]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hterm a, chainEnsemble]
  exact Fintype.sum_equiv (chainFinRelabel n g) _ _ fun a => rfl

/-! ## The collision bound -/

/-- Transporting an orthonormal eigenbasis back along a reindexing. -/
theorem IsOrthoEigenBasis.ofReindex {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {A : Matrix α α ℂ} (σ : α ≃ β)
    {f : β → β → ℂ} {mu : β → ℝ}
    (h : IsOrthoEigenBasis (Matrix.reindex σ σ A) f mu) :
    IsOrthoEigenBasis A (fun j x => f (σ j) (σ x)) (fun j => mu (σ j)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro j k
    have hinner : finiteComplexInner (fun x => f (σ j) (σ x)) (fun x => f (σ k) (σ x))
        = finiteComplexInner (f (σ j)) (f (σ k)) := by
      rw [finiteComplexInner, finiteComplexInner]
      exact Equiv.sum_comp σ (fun y => (starRingEnd ℂ) (f (σ j) y) * f (σ k) y)
    rw [hinner, h.orth (σ j) (σ k)]
    by_cases hjk : j = k
    · simp [hjk]
    · simp [hjk, σ.injective.ne hjk]
  · intro j
    funext i
    have hrow : (A *ᵥ fun x => f (σ j) (σ x)) i
        = (Matrix.reindex σ σ A *ᵥ f (σ j)) (σ i) := by
      show (∑ x, A i x * f (σ j) (σ x)) = ∑ y, (Matrix.reindex σ σ A) (σ i) y * f (σ j) y
      rw [← Equiv.sum_comp σ (fun y => (Matrix.reindex σ σ A) (σ i) y * f (σ j) y)]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp
    rw [hrow, h.eigen (σ j)]
    rfl
  · intro ψ
    funext i
    have hinner : ∀ j, finiteComplexInner (fun x => f (σ j) (σ x)) ψ
        = finiteComplexInner (f (σ j)) (fun y => ψ (σ.symm y)) := by
      intro j
      rw [finiteComplexInner, finiteComplexInner]
      refine Eq.trans ?_ (Equiv.sum_comp σ
        (fun y => (starRingEnd ℂ) (f (σ j) y) * ψ (σ.symm y)))
      exact Finset.sum_congr rfl fun x _ => by rw [Equiv.symm_apply_apply]
    have hcomp := congrFun (h.complete (fun y => ψ (σ.symm y))) (σ i)
    show (∑ j, finiteComplexInner (fun x => f (σ j) (σ x)) ψ • (fun x => f (σ j) (σ x))) i = ψ i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hinner]
    rw [Equiv.sum_comp σ (fun b => finiteComplexInner (f b) (fun y => ψ (σ.symm y)) *
      f b (σ i))]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcomp
    rw [hcomp, Equiv.symm_apply_apply]

theorem isOrthoEigenBasis_injective_chainEnsemble_shell_ae (n : ℕ)
    (hdisc : spectralDiscriminantPoly (chainPauliFin n) ≠ 0) :
    ∀ᵐ θ ∂(shellProbability (Fin (Fintype.card (ChainLabel n)))),
      IsOrthoEigenBasis (chainEnsemble n θ)
          (fun j x => hermitianEigenBasis (spectralEnsembleMatrix (chainPauliFin n) θ)
            (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ)
            (qubitConfigFin n j) (qubitConfigFin n x))
          (fun j => (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ).eigenvalues
            (qubitConfigFin n j)) ∧
        Function.Injective (fun j =>
          (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ).eigenvalues
            (qubitConfigFin n j)) := by
  filter_upwards [injective_eigenvalues_spectralEnsemble_shell_ae
    (chainPauliFin_isHermitian n) hdisc] with θ hθ
  refine ⟨?_, hθ.comp (qubitConfigFin n).injective⟩
  refine IsOrthoEigenBasis.ofReindex (qubitConfigFin n) ?_
  rw [reindex_chainEnsemble n θ]
  exact isOrthoEigenBasis_hermitian _ (isHermitian_spectralEnsembleMatrix
    (chainPauliFin_isHermitian n) θ)

/-! ## Nonemptiness of the chain family -/

instance instNonemptyChainLabel (m : ℕ) : Nonempty (ChainLabel (m + 1)) := by
  refine ⟨⟨pauliZLabel ⟨0, by omega⟩, ?_, pauliZLabel_ne_identity _⟩⟩
  refine isChainLabel_of_isSiteLabel (s := ⟨0, by omega⟩) ?_
  intro i hi
  by_contra hne
  exact hi (by simp only [pauliZLabel, if_neg hne])

instance instNonemptyChainCoordinate (m : ℕ) :
    Nonempty (Fin (Fintype.card (ChainLabel (m + 1)))) :=
  Fin.pos_iff_nonempty.mp (Fintype.card_pos_iff.mpr (instNonemptyChainLabel m))

/-! ## The mean collision bound and its Markov tail -/

/-- **The mean collision bound on the nearest-neighbour shell.** -/
theorem integral_spectralCollision_chainShell_le (m : ℕ)
    (hdisc : spectralDiscriminantPoly (chainPauliFin (m + 1)) ≠ 0) :
    (∫ θ, spectralCollision
        (fun j x => hermitianEigenBasis
          (spectralEnsembleMatrix (chainPauliFin (m + 1)) θ)
          (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (m + 1)) θ)
          (qubitConfigFin (m + 1) j) (qubitConfigFin (m + 1) x))
        (zeroProductState (Fin (m + 1)))
      ∂(shellProbability (Fin (Fintype.card (ChainLabel (m + 1)))))) ≤ (2 / 3 : ℝ) ^ (m + 1) := by
  refine integral_spectralCollision_zeroProductState_le_of_covariant
    (H := chainEnsemble (m + 1)) (T := fun g => chainCliffordCoefficientMap (m + 1) g)
    (measurable_chainEnsemble_entry (m + 1))
    (fun g => measurePreserving_chainCliffordCoefficientMap (m + 1) g)
    (fun g θ => chainEnsemble_conj (m + 1) g θ)
    (isOrthoEigenBasis_injective_chainEnsemble_shell_ae (m + 1) hdisc)

/-- **The Markov tail of the collision on the nearest-neighbour shell.** -/
theorem measureReal_spectralCollision_chainShell_ge_le (m : ℕ)
    (hdisc : spectralDiscriminantPoly (chainPauliFin (m + 1)) ≠ 0) {L : ℝ} (hL : 0 < L) :
    (shellProbability (Fin (Fintype.card (ChainLabel (m + 1))))).real
        {θ | L * (2 / 3 : ℝ) ^ (m + 1) ≤ spectralCollision
          (fun j x => hermitianEigenBasis
            (spectralEnsembleMatrix (chainPauliFin (m + 1)) θ)
            (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (m + 1)) θ)
            (qubitConfigFin (m + 1) j) (qubitConfigFin (m + 1) x))
          (zeroProductState (Fin (m + 1)))} ≤ 1 / L :=
  measureReal_spectralCollision_ge_le
    (measurable_chainEnsemble_entry (m + 1))
    (sum_normSq_zeroProductState (Fin (m + 1)))
    (isOrthoEigenBasis_injective_chainEnsemble_shell_ae (m + 1) hdisc)
    (by positivity)
    (integral_spectralCollision_chainShell_le m hdisc) hL

end GaloisForLFunctions.HTGeometry

end
