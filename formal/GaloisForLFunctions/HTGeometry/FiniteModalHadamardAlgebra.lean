import GaloisForLFunctions.HTGeometry.FiniteModalHankelRank

/-!
# Hadamard algebra of finite modal observations

The pointwise product of a width-`d` modal sequence and a width-`e` modal sequence is a
width-`d*e` modal sequence.  Its nodes are all pairwise products of the input nodes.  Thus a
quadratic observation creates combination modes, and the only obstruction to the full `d*e`
noiseless mode count is collision of those product nodes.

For sampled complex exponentials this is the algebraic law behind summed complex frequencies in
nonlinear spectroscopy: `exp(w n) * exp(v n) = exp((w+v)n)`.  The theorem itself is about sampled
values and does not require a temporal interpretation.
-/

open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

/-- Amplitude of the pair mode indexed through `Fin d × Fin e ≃ Fin (d*e)`. -/
def finiteModalProductWeight {K : Type*} [Mul K] {d e : ℕ}
    (weight₁ : Fin d → K) (weight₂ : Fin e → K) (k : Fin (d * e)) : K :=
  weight₁ (finProdFinEquiv.symm k).1 * weight₂ (finProdFinEquiv.symm k).2

/-- Node of the pair mode indexed through `Fin d × Fin e ≃ Fin (d*e)`. -/
def finiteModalProductNode {K : Type*} [Mul K] {d e : ℕ}
    (node₁ : Fin d → K) (node₂ : Fin e → K) (k : Fin (d * e)) : K :=
  node₁ (finProdFinEquiv.symm k).1 * node₂ (finProdFinEquiv.symm k).2

/-- **Finite modal Hadamard product law.**  Pointwise multiplication forms all pairwise product
nodes and no others. -/
theorem finiteModalSequence_mul
    {K : Type*} [CommSemiring K] {d e : ℕ}
    (weight₁ node₁ : Fin d → K) (weight₂ node₂ : Fin e → K) (n : ℕ) :
    finiteModalSequence weight₁ node₁ n * finiteModalSequence weight₂ node₂ n =
      finiteModalSequence
        (finiteModalProductWeight weight₁ weight₂)
        (finiteModalProductNode node₁ node₂) n := by
  rw [finiteModalSequence, finiteModalSequence, finiteModalSequence,
    Fintype.sum_mul_sum]
  conv_rhs => rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro i
  apply Fintype.sum_congr
  intro j
  simp [finiteModalProductWeight, finiteModalProductNode, mul_pow]
  ring

/-- The width-bounded finite modal class is closed under pointwise multiplication, with
multiplicative width bound. -/
theorem FiniteModalWidthAtMost.mul
    {K : Type*} [CommSemiring K] {d e : ℕ} {m₁ m₂ : ℕ → K}
    (hm₁ : FiniteModalWidthAtMost d m₁) (hm₂ : FiniteModalWidthAtMost e m₂) :
    FiniteModalWidthAtMost (d * e) (fun n ↦ m₁ n * m₂ n) := by
  obtain ⟨weight₁, node₁, rfl⟩ := hm₁
  obtain ⟨weight₂, node₂, rfl⟩ := hm₂
  refine ⟨finiteModalProductWeight weight₁ weight₂,
    finiteModalProductNode node₁ node₂, ?_⟩
  funext n
  exact finiteModalSequence_mul weight₁ node₁ weight₂ node₂ n

/-- A pointwise product of width-`d` and width-`e` modal observations has singular Hankel block
in size `d*e+1`. -/
theorem det_algebraicHankelMatrix_mul_eq_zero_of_finiteModalWidthAtMost
    {K : Type*} [Field K] {d e : ℕ} {m₁ m₂ : ℕ → K}
    (hm₁ : FiniteModalWidthAtMost d m₁) (hm₂ : FiniteModalWidthAtMost e m₂) :
    (algebraicHankelMatrix (fun n ↦ m₁ n * m₂ n) (d * e + 1)).det = 0 :=
  det_algebraicHankelMatrix_succ_eq_zero_of_finiteModalWidthAtMost (hm₁.mul hm₂)

/-- Nonzero input amplitudes give a nonsingular maximal product block exactly when no two
combination nodes collide. -/
theorem det_algebraicHankelMatrix_finiteModalSequence_mul_ne_zero_iff
    {K : Type*} [Field K] {d e : ℕ}
    {weight₁ node₁ : Fin d → K} {weight₂ node₂ : Fin e → K}
    (hweight₁ : ∀ i, weight₁ i ≠ 0) (hweight₂ : ∀ j, weight₂ j ≠ 0) :
    (algebraicHankelMatrix
        (fun n ↦ finiteModalSequence weight₁ node₁ n *
          finiteModalSequence weight₂ node₂ n) (d * e)).det ≠ 0 ↔
      Function.Injective (fun p : Fin d × Fin e ↦ node₁ p.1 * node₂ p.2) := by
  have hsequence :
      (fun n ↦ finiteModalSequence weight₁ node₁ n *
        finiteModalSequence weight₂ node₂ n) =
        finiteModalSequence
          (finiteModalProductWeight weight₁ weight₂)
          (finiteModalProductNode node₁ node₂) := by
    funext n
    exact finiteModalSequence_mul weight₁ node₁ weight₂ node₂ n
  rw [hsequence]
  constructor
  · intro hdet
    have hvandermonde :
        (Matrix.vandermonde (finiteModalProductNode node₁ node₂)).det ≠ 0 := by
      intro hzero
      apply hdet
      rw [det_algebraicHankelMatrix_finiteModalSequence, hzero]
      simp
    have hindexed : Function.Injective (finiteModalProductNode node₁ node₂) :=
      Matrix.det_vandermonde_ne_zero_iff.mp hvandermonde
    intro p q hpq
    apply finProdFinEquiv.injective
    apply hindexed
    simpa [finiteModalProductNode] using hpq
  · intro hpair
    apply det_algebraicHankelMatrix_finiteModalSequence_ne_zero
    · intro k l hkl
      apply finProdFinEquiv.symm.injective
      apply hpair
      simpa [finiteModalProductNode] using hkl
    · intro k
      exact mul_ne_zero
        (hweight₁ (finProdFinEquiv.symm k).1)
        (hweight₂ (finProdFinEquiv.symm k).2)

/-- **Exact quadratic combination-mode count.**  With nonzero amplitudes and no product-node
resonances, the product has exactly `d*e` noiseless Hankel modes. -/
theorem finiteModalSequence_mul_exact_hankel_mode_count
    {K : Type*} [Field K] {d e : ℕ}
    {weight₁ node₁ : Fin d → K} {weight₂ node₂ : Fin e → K}
    (hweight₁ : ∀ i, weight₁ i ≠ 0) (hweight₂ : ∀ j, weight₂ j ≠ 0)
    (hnode : Function.Injective (fun p : Fin d × Fin e ↦ node₁ p.1 * node₂ p.2)) :
    (algebraicHankelMatrix
        (fun n ↦ finiteModalSequence weight₁ node₁ n *
          finiteModalSequence weight₂ node₂ n) (d * e)).det ≠ 0 ∧
      (algebraicHankelMatrix
        (fun n ↦ finiteModalSequence weight₁ node₁ n *
          finiteModalSequence weight₂ node₂ n) (d * e + 1)).det = 0 := by
  have hsequence :
      (fun n ↦ finiteModalSequence weight₁ node₁ n *
        finiteModalSequence weight₂ node₂ n) =
        finiteModalSequence
          (finiteModalProductWeight weight₁ weight₂)
          (finiteModalProductNode node₁ node₂) := by
    funext n
    exact finiteModalSequence_mul weight₁ node₁ weight₂ node₂ n
  rw [hsequence]
  apply finiteModalSequence_exact_hankel_mode_count
  · intro k l hkl
    apply finProdFinEquiv.symm.injective
    apply hnode
    simpa [finiteModalProductNode] using hkl
  · intro k
    exact mul_ne_zero
      (hweight₁ (finProdFinEquiv.symm k).1)
      (hweight₂ (finProdFinEquiv.symm k).2)

end

end HTGeometry
