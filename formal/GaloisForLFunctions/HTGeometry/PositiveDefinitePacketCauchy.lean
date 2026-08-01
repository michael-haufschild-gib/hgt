import GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite

/-!
# Cauchy law for positive-definite kernel packets

A positive-definite translation kernel controls correlations between any two finite packets, not
only correlations with one distinguished anchor.  The mixed packet correlation squared is at most
the product of the two coherent Gram energies.  The result is proved directly from finite kernel
positivity, so it applies without a Hilbert-space realization or a representing measure.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Coherent energy of a finite real packet for a translation kernel. -/
def realKernelPacketEnergy (K : ℝ → ℝ) {N : ℕ}
    (t b : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, b i * K (t j - t i) * b j

/-- Mixed correlation of two finite real packets for a translation kernel. -/
def realKernelPacketCross (K : ℝ → ℝ) {N M : ℕ}
    (s a : Fin N → ℝ) (t b : Fin M → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * K (t j - s i) * b j

/-- Every finite packet has nonnegative coherent energy under a positive-definite kernel. -/
theorem realKernelPacketEnergy_nonneg_of_positiveDefinite
    (K : ℝ → ℝ)
    (hPD : PositiveDefiniteOnReal (fun y => (K y : ℂ)))
    {N : ℕ} (t b : Fin N → ℝ) :
    0 ≤ realKernelPacketEnergy K t b := by
  obtain ⟨r, hr, hq⟩ := hPD N t (fun i => (b i : ℂ))
  have hre := congrArg Complex.re hq
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_re] at hre
  exact hr.trans_eq (by simpa [realKernelPacketEnergy] using hre.symm)

/-- **Universal two-packet Cauchy law.**  For an even real positive-definite translation kernel,
the square of every mixed finite-packet correlation is bounded by the product of the two coherent
packet energies. -/
theorem realKernelPacketCross_sq_le_energy_mul_energy_of_positiveDefinite
    (K : ℝ → ℝ)
    (hPD : PositiveDefiniteOnReal (fun y => (K y : ℂ)))
    (hEven : ∀ y, K (-y) = K y)
    {N M : ℕ} (s a : Fin N → ℝ) (t b : Fin M → ℝ) :
    realKernelPacketCross K s a t b ^ 2 ≤
      realKernelPacketEnergy K s a * realKernelPacketEnergy K t b := by
  let A := realKernelPacketEnergy K s a
  let B := realKernelPacketEnergy K t b
  let C := realKernelPacketCross K s a t b
  have hA : 0 ≤ A := realKernelPacketEnergy_nonneg_of_positiveDefinite K hPD s a
  have hB : 0 ≤ B := realKernelPacketEnergy_nonneg_of_positiveDefinite K hPD t b
  have hquad : ∀ z : ℝ, 0 ≤ A * z ^ 2 + 2 * C * z + B := by
    intro z
    let T : Fin (N + M) → ℝ := Fin.append s t
    let D : Fin (N + M) → ℂ :=
      Fin.append (fun i => ((z * a i : ℝ) : ℂ)) (fun j => (b j : ℂ))
    obtain ⟨r, hr, hq⟩ := hPD (N + M) T D
    have hre := congrArg Complex.re hq
    have hform :
        (∑ i, ∑ j, star (D i) * (K (T j - T i) : ℂ) * D j) =
          ((A * z ^ 2 + 2 * C * z + B : ℝ) : ℂ) := by
      simp only [Fin.sum_univ_add, T, D, Fin.append_left, Fin.append_right,
        Complex.star_def, Complex.conj_ofReal, Finset.sum_add_distrib]
      dsimp only [A, B, C, realKernelPacketEnergy, realKernelPacketCross]
      rw [show (∑ i : Fin N, ∑ j : Fin N,
            ((z * a i : ℝ) : ℂ) * (K (s j - s i) : ℂ) * ((z * a j : ℝ) : ℂ)) =
          (((∑ i : Fin N, ∑ j : Fin N, a i * K (s j - s i) * a j) * z ^ 2 : ℝ) : ℂ) by
        push_cast
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring]
      rw [show (∑ i : Fin N, ∑ j : Fin M,
            ((z * a i : ℝ) : ℂ) * (K (t j - s i) : ℂ) * (b j : ℂ)) =
          (((∑ i : Fin N, ∑ j : Fin M, a i * K (t j - s i) * b j) * z : ℝ) : ℂ) by
        push_cast
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring]
      rw [show (∑ i : Fin M, ∑ j : Fin N,
            (b i : ℂ) * (K (s j - t i) : ℂ) * ((z * a j : ℝ) : ℂ)) =
          (((∑ i : Fin N, ∑ j : Fin M, a i * K (t j - s i) * b j) * z : ℝ) : ℂ) by
        push_cast
        rw [Finset.sum_comm, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [show s i - t j = -(t j - s i) by ring, hEven]
        ring]
      push_cast
      ring
    rw [hform] at hre
    simp only [Complex.ofReal_re] at hre
    nlinarith
  change C ^ 2 ≤ A * B
  by_cases hA0 : A = 0
  · have hC0 : C = 0 := by
      by_contra hC
      have hneg := hquad (-B / (2 * C) - 1)
      rw [hA0, zero_mul, zero_add] at hneg
      have hnegEq : 2 * C * (-B / (2 * C) - 1) + B = -2 * C := by
        field_simp [hC]
        ring
      rw [hnegEq] at hneg
      have hpos := hquad (-B / (2 * C) + 1)
      rw [hA0, zero_mul, zero_add] at hpos
      have hposEq : 2 * C * (-B / (2 * C) + 1) + B = 2 * C := by
        field_simp [hC]
        ring
      rw [hposEq] at hpos
      exact hC (le_antisymm (by linarith) (by linarith))
    simp [hA0, hC0]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have h := hquad (-C / A)
    field_simp [hA0] at h
    nlinarith

/-- Channel Gram matrix formed from finitely many coherent packets of a common size. -/
def realKernelPacketChannelGram (K : ℝ → ℝ) {M N : ℕ}
    (t b : Fin M → Fin N → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun r s => realKernelPacketCross K (t r) (b r) (t s) (b s)

/-- Channel Gram matrix for packets sharing one node family but carrying different masses. -/
def realKernelSharedNodePacketChannelGram (K : ℝ → ℝ) {M N : ℕ}
    (t : Fin N → ℝ) (b : Fin M → Fin N → ℝ) :
    Matrix (Fin M) (Fin M) ℝ :=
  realKernelPacketChannelGram K (fun _ => t) b

/-- Node Gram matrix before packet channels are mixed. -/
def realKernelNodeGram (K : ℝ → ℝ) {N : ℕ}
    (t : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => K (t j - t i)

/-- **Exact packet-channel factorization.**  Every shared-node coherent Gram is the congruence
of its node Gram by the channel-mass matrix.  This identity uses no positivity assumption. -/
theorem realKernelSharedNodePacketChannelGram_eq_mass_mul_nodeGram_mul_transpose
    (K : ℝ → ℝ) {M N : ℕ} (t : Fin N → ℝ)
    (b : Fin M → Fin N → ℝ) :
    realKernelSharedNodePacketChannelGram K t b =
      Matrix.of b * realKernelNodeGram K t *
        Matrix.transpose (Matrix.of b) := by
  ext r s
  simp only [realKernelSharedNodePacketChannelGram,
    realKernelPacketChannelGram, realKernelPacketCross,
    realKernelNodeGram, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

/-- Channel rank cannot exceed arithmetic mass rank.  Kernel analysis can change the form on the
mass image, but cannot create a new coherent channel direction. -/
theorem realKernelSharedNodePacketChannelGram_rank_le_massRank
    (K : ℝ → ℝ) {M N : ℕ} (t : Fin N → ℝ)
    (b : Fin M → Fin N → ℝ) :
    (realKernelSharedNodePacketChannelGram K t b).rank ≤
      Matrix.rank (Matrix.of b) := by
  rw [realKernelSharedNodePacketChannelGram_eq_mass_mul_nodeGram_mul_transpose]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)

/-- In particular, at most one coherent channel dimension can be carried by each shared node. -/
theorem realKernelSharedNodePacketChannelGram_rank_le_nodeCount
    (K : ℝ → ℝ) {M N : ℕ} (t : Fin N → ℝ)
    (b : Fin M → Fin N → ℝ) :
    (realKernelSharedNodePacketChannelGram K t b).rank ≤ N := by
  exact (realKernelSharedNodePacketChannelGram_rank_le_massRank K t b).trans
    (by simpa using Matrix.rank_le_card_width (Matrix.of b))

/-- More channels than shared nodes force singularity for every kernel, without needing an
explicit mass relation. -/
theorem realKernelSharedNodePacketChannelGram_det_eq_zero_of_nodeCount_lt_channelCount
    (K : ℝ → ℝ) {M N : ℕ} (hNM : N < M) (t : Fin N → ℝ)
    (b : Fin M → Fin N → ℝ) :
    (realKernelSharedNodePacketChannelGram K t b).det = 0 := by
  by_contra hdet
  have hunitDet : IsUnit (realKernelSharedNodePacketChannelGram K t b).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit (realKernelSharedNodePacketChannelGram K t b) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hunitDet
  have hrank : (realKernelSharedNodePacketChannelGram K t b).rank = M := by
    simpa using Matrix.rank_of_isUnit _ hunit
  have hle := realKernelSharedNodePacketChannelGram_rank_le_nodeCount K t b
  omega

/-- **Universal coherent-channel law.**  Every finite family of packets for an even real
positive-definite translation kernel has a positive-semidefinite channel Gram matrix.  Thus all
channel principal minors and every coherent linear recombination are controlled simultaneously;
the scalar two-packet inequality is its two-channel shadow. -/
theorem realKernelPacketChannelGram_posSemidef_of_positiveDefinite
    (K : ℝ → ℝ)
    (hPD : PositiveDefiniteOnReal (fun y => (K y : ℂ)))
    (hEven : ∀ y, K (-y) = K y)
    {M N : ℕ} (t b : Fin M → Fin N → ℝ) :
    (realKernelPacketChannelGram K t b).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro r s
    simp only [realKernelPacketChannelGram, star_trivial]
    unfold realKernelPacketCross
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show t r i - t s j = -(t s j - t r i) by ring, hEven]
    ring
  · intro x
    let e : Fin M × Fin N ≃ Fin (M * N) := finProdFinEquiv
    let T : Fin (M * N) → ℝ := fun k => t (e.symm k).1 (e.symm k).2
    let c : Fin (M * N) → ℂ := fun k =>
      ((x (e.symm k).1 * b (e.symm k).1 (e.symm k).2 : ℝ) : ℂ)
    obtain ⟨q, hq, hform⟩ := hPD (M * N) T c
    have hflat :
        (∑ i, ∑ j, star (c i) * (K (T j - T i) : ℂ) * c j) =
          ((dotProduct (star x)
              ((realKernelPacketChannelGram K t b).mulVec x) : ℝ) : ℂ) := by
      have hsum (f : Fin (M * N) → ℂ) :
          (∑ k, f k) = ∑ r : Fin M, ∑ i : Fin N, f (e (r, i)) := by
        rw [← e.sum_comp, Fintype.sum_prod_type]
      rw [hsum]
      simp_rw [hsum]
      simp only [e, T, c, Equiv.symm_apply_apply, dotProduct, Matrix.mulVec,
        realKernelPacketChannelGram, realKernelPacketCross, star_trivial,
        Complex.star_def, Complex.conj_ofReal]
      push_cast
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have heq : dotProduct (star x)
        ((realKernelPacketChannelGram K t b).mulVec x) = q := by
      exact_mod_cast hflat.symm.trans hform
    exact hq.trans_eq heq.symm

/-- Every full coherent-channel determinant is nonnegative. -/
theorem realKernelPacketChannelGram_det_nonneg_of_positiveDefinite
    (K : ℝ → ℝ)
    (hPD : PositiveDefiniteOnReal (fun y => (K y : ℂ)))
    (hEven : ∀ y, K (-y) = K y)
    {M N : ℕ} (t b : Fin M → Fin N → ℝ) :
    0 ≤ (realKernelPacketChannelGram K t b).det :=
  (realKernelPacketChannelGram_posSemidef_of_positiveDefinite
    K hPD hEven t b).det_nonneg

/-- Every shared-node channel mass relation is an exact null vector of the coherent Gram.  This
is the universal linear-algebra law behind good/bad source decompositions: it requires neither
positivity nor a representing measure. -/
theorem realKernelSharedNodePacketChannelGram_mulVec_eq_zero_of_mass_relation
    (K : ℝ → ℝ) {M N : ℕ} (t : Fin N → ℝ)
    (b : Fin M → Fin N → ℝ) (c : Fin M → ℝ)
    (hrel : ∀ j, ∑ s, b s j * c s = 0) :
    (realKernelSharedNodePacketChannelGram K t b).mulVec c = 0 := by
  rw [realKernelSharedNodePacketChannelGram_eq_mass_mul_nodeGram_mul_transpose]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hb : (Matrix.transpose (Matrix.of b)).mulVec c = 0 := by
    funext j
    simpa [Matrix.mulVec, dotProduct] using hrel j
  rw [hb]
  simp

/-- A nontrivial shared-node mass relation forces the coherent channel determinant to vanish. -/
theorem realKernelSharedNodePacketChannelGram_det_eq_zero_of_mass_relation
    (K : ℝ → ℝ) {M N : ℕ} (t : Fin N → ℝ)
    (b : Fin M → Fin N → ℝ) (c : Fin M → ℝ)
    (hrel : ∀ j, ∑ s, b s j * c s = 0)
    (k : Fin M) (hk : c k ≠ 0) :
    (realKernelSharedNodePacketChannelGram K t b).det = 0 := by
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (realKernelSharedNodePacketChannelGram_mulVec_eq_zero_of_mass_relation
      K t b c hrel) (i := k)
  simpa [mem_nonZeroDivisors_iff_ne_zero] using hk

/-- **Shared-node coherent boundary law.**  Positive definiteness controls every channel
recombination, while any nontrivial pointwise relation places the channel Gram exactly on the
boundary of the positive-semidefinite cone. -/
theorem realKernelSharedNodePacketChannelGram_boundary_of_positiveDefinite_of_mass_relation
    (K : ℝ → ℝ)
    (hPD : PositiveDefiniteOnReal (fun y => (K y : ℂ)))
    (hEven : ∀ y, K (-y) = K y)
    {M N : ℕ} (t : Fin N → ℝ) (b : Fin M → Fin N → ℝ)
    (c : Fin M → ℝ) (hrel : ∀ j, ∑ s, b s j * c s = 0)
    (k : Fin M) (hk : c k ≠ 0) :
    (realKernelSharedNodePacketChannelGram K t b).PosSemidef ∧
      (realKernelSharedNodePacketChannelGram K t b).det = 0 := by
  exact ⟨realKernelPacketChannelGram_posSemidef_of_positiveDefinite
      K hPD hEven (fun _ => t) b,
    realKernelSharedNodePacketChannelGram_det_eq_zero_of_mass_relation
      K t b c hrel k hk⟩

end

end GaloisForLFunctions.HTGeometry
