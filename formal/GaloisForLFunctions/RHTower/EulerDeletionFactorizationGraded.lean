import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleCylinderSquareNoGo
import GaloisForLFunctions.RHTower.EulerDeletionCompositeInterference

/-!
# Factorization-graded Euler deletion

For coprime positive moduli, the literal inserted deletion channel splits into the old
single-modulus channel minus the squarefree interaction channel.  On one common product block,
these two grades are orthogonal for the uniform counting form.  Their exact Pythagorean splitting
gives the arithmetic replication factor `p` before any Mellin weight or zeta zero is introduced.

This is finite source algebra only.  It does not identify the uniform grade form with the
Dirichlet-weighted quasi-shuffle bracket.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

/-- Generic coefficient insertion along the cofactor clock. -/
def deletionCoefficientInsertion (p : ℕ) (x : ℕ → ℤ) (n : ℕ) : ℤ :=
  if p ∣ n then (p : ℤ) * x (n / p) else 0

/-- Cofactor insertion is an exact multiplicative action. -/
theorem deletionCoefficientInsertion_comp
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (x : ℕ → ℤ) (n : ℕ) :
    deletionCoefficientInsertion p (deletionCoefficientInsertion q x) n =
      deletionCoefficientInsertion (p * q) x n := by
  by_cases hpn : p ∣ n
  · obtain ⟨k, rfl⟩ := hpn
    by_cases hqk : q ∣ k
    · obtain ⟨m, rfl⟩ := hqk
      have hpqpos : 0 < p * q := Nat.mul_pos hp hq
      simp only [deletionCoefficientInsertion, dvd_mul_right, if_true,
        Nat.mul_div_cancel_left _ hp, Nat.mul_div_cancel_left _ hq]
      rw [← Nat.mul_assoc p q m]
      rw [if_pos (dvd_mul_right (p * q) m), Nat.mul_div_cancel_left m hpqpos]
      push_cast
      ring
    · have hpq : ¬p * q ∣ p * k := by
        intro h
        have : q ∣ k := (Nat.mul_dvd_mul_iff_left hp).mp h
        exact hqk this
      simp [deletionCoefficientInsertion, hp, hqk, hpq]
  · have hpq : ¬p * q ∣ n := fun h => hpn ((dvd_mul_right p q).trans h)
    simp [deletionCoefficientInsertion, hpn, hpq]

/-- Insertion order is flat before chronological summation. -/
theorem deletionCoefficientInsertion_comm
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (x : ℕ → ℤ) (n : ℕ) :
    deletionCoefficientInsertion p (deletionCoefficientInsertion q x) n =
      deletionCoefficientInsertion q (deletionCoefficientInsertion p x) n := by
  rw [deletionCoefficientInsertion_comp hp hq,
    deletionCoefficientInsertion_comp hq hp, mul_comm]

/-- Nested cofactor cutoffs are also independent of factorization order. -/
theorem deletionNestedCofactorCutoff_comm (N p q : ℕ) :
    (N / p) / q = (N / q) / p := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]

/-- Squarefree two-modulus interaction grade. -/
def deletionFactorizationInteraction (p q n : ℕ) : ℤ :=
  blockDeletionCoefficient p n * blockDeletionCoefficient q n

/-- The inserted `q`-channel expressed on the common physical clock. -/
def deletionFactorizationInsertion (p q n : ℕ) : ℤ :=
  blockDeletionCoefficient q n - deletionFactorizationInteraction p q n

/-- Mellin-weighted squarefree interaction grade on the original integer clock. -/
noncomputable def deletionFactorizationInteractionSource
    (p q : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  (deletionFactorizationInteraction p q n : ℂ) * (n : ℂ) ^ (-s)

/-- Insertion is supported on multiples of the outer modulus, with its literal amplitude. -/
theorem deletionFactorizationInsertion_eq_indicator (p q n : ℕ) :
    deletionFactorizationInsertion p q n =
      (p : ℤ) * if p ∣ n then blockDeletionCoefficient q n else 0 := by
  by_cases hp : p ∣ n
  · simp [deletionFactorizationInsertion, deletionFactorizationInteraction,
      blockDeletionCoefficient, hp]
    ring
  · simp [deletionFactorizationInsertion, deletionFactorizationInteraction,
      blockDeletionCoefficient, hp]

/-- Coprimality lets the common-clock insertion agree with the literal cofactor insertion. -/
theorem deletionFactorizationInsertion_eq_cofactor_of_coprime
    {p q n : ℕ} (hp : 0 < p) (hpq : Nat.Coprime p q) :
    deletionFactorizationInsertion p q n =
      (p : ℤ) * if p ∣ n then blockDeletionCoefficient q (n / p) else 0 := by
  by_cases hpn : p ∣ n
  · obtain ⟨k, rfl⟩ := hpn
    have hq : q ∣ p * k ↔ q ∣ k := by
      constructor
      · exact hpq.symm.dvd_of_dvd_mul_left
      · exact fun h => dvd_mul_of_dvd_right h p
    rw [deletionFactorizationInsertion_eq_indicator]
    simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hp]
    by_cases hqk : q ∣ k <;>
      simp [blockDeletionCoefficient, hq, hqk]
  · rw [deletionFactorizationInsertion_eq_indicator]
    simp [hpn]

/-- Literal inserted Mellin source is dense grade one minus squarefree grade two. -/
theorem deletionInsertedSource_eq_single_sub_interaction_of_coprime
    {p q : ℕ} (hp : 0 < p) (hpq : Nat.Coprime p q) (s : ℂ) (n : ℕ) :
    deletionInsertedSource p q s n =
      deletionMellinSource q s n - deletionFactorizationInteractionSource p q s n := by
  have hc := deletionFactorizationInsertion_eq_cofactor_of_coprime
    (p := p) (q := q) (n := n) hp hpq
  have hcC :
      (deletionFactorizationInsertion p q n : ℂ) =
        (p : ℂ) * if p ∣ n then (blockDeletionCoefficient q (n / p) : ℂ) else 0 := by
    exact_mod_cast hc
  unfold deletionFactorizationInsertion at hcC
  unfold deletionInsertedSource deletionMellinSource
    deletionFactorizationInteractionSource
  by_cases hpn : p ∣ n
  · simp only [hpn, if_true] at hcC ⊢
    push_cast at hcC ⊢
    rw [← hcC]
    ring
  · simp only [hpn, if_false, mul_zero] at hcC ⊢
    push_cast at hcC ⊢
    rw [← sub_mul, hcC, zero_mul]

/-- Composite Mellin deletion splits into both singleton grades and their interaction. -/
theorem deletionMellinSource_mul_eq_single_add_single_sub_interaction_of_coprime
    {p q : ℕ} (hp : 0 < p) (hpq : Nat.Coprime p q) (s : ℂ) (n : ℕ) :
    deletionMellinSource (p * q) s n =
      deletionMellinSource p s n + deletionMellinSource q s n -
        deletionFactorizationInteractionSource p q s n := by
  rw [deletionMellinSource_mul_eq_add_inserted hp,
    deletionInsertedSource_eq_single_sub_interaction_of_coprime hp hpq]
  ring

/-! ## Uniform grade orthogonality versus Mellin grade mixing -/

/-- Dirichlet-weighted pairing of grade one with its squarefree interaction grade. -/
noncomputable def deletionFactorizationGradeCross
    (α : ℝ) (p q : ℕ) : ℝ :=
  ∑' n, (blockDeletionCoefficient q n : ℝ) *
    (deletionFactorizationInteraction p q n : ℝ) * deletionDirichletWeight α n

/-- Exact Mellin deformation of the grade-one/grade-two cross term. -/
theorem deletionFactorizationGradeCross_eq_of_coprime
    {α : ℝ} (hα : 1 < α) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) :
    deletionFactorizationGradeCross α p q =
      deletionDirichletMass α * (1 - p * (p : ℝ) ^ (-α)) *
        (1 + (q : ℝ) * ((q : ℝ) - 2) * (q : ℝ) ^ (-α)) := by
  have hpoint (n : ℕ) :
      (blockDeletionCoefficient q n : ℝ) *
          (deletionFactorizationInteraction p q n : ℝ) * deletionDirichletWeight α n =
        ((q : ℝ) - 1) *
            ((blockDeletionCoefficient p n : ℝ) * deletionDirichletWeight α n) +
          (2 - (q : ℝ)) *
            ((blockDeletionCoefficient p n : ℝ) *
              (blockDeletionCoefficient q n : ℝ) * deletionDirichletWeight α n) := by
    have hsquare :
        (blockDeletionCoefficient q n : ℝ) ^ 2 =
          (q : ℝ) - 1 + (2 - (q : ℝ)) * (blockDeletionCoefficient q n : ℝ) := by
      exact_mod_cast blockDeletionCoefficient_sq_eq q n
    rw [deletionFactorizationInteraction]
    push_cast
    calc
      (blockDeletionCoefficient q n : ℝ) *
            ((blockDeletionCoefficient p n : ℝ) * blockDeletionCoefficient q n) *
            deletionDirichletWeight α n =
          (blockDeletionCoefficient p n : ℝ) *
            blockDeletionCoefficient q n ^ 2 * deletionDirichletWeight α n := by ring
      _ = _ := by rw [hsquare]; ring
  have hfirst :=
    (summable_deletionDirichlet_first hα p).mul_left ((q : ℝ) - 1)
  have hgram :=
    (summable_deletionDirichlet_gram hα p q).mul_left (2 - (q : ℝ))
  rw [deletionFactorizationGradeCross]
  simp_rw [hpoint]
  rw [hfirst.tsum_add hgram, tsum_mul_left, tsum_mul_left,
    tsum_deletionDirichlet_first hα hp,
    tsum_deletionDirichlet_gram_of_coprime hα hp hq hpq]
  ring

/-- In every absolutely convergent chamber, Mellin weighting mixes the two uniform grades
strictly positively. -/
theorem deletionFactorizationGradeCross_pos_of_coprime
    {α : ℝ} (hα : 1 < α) {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q) :
    0 < deletionFactorizationGradeCross α p q := by
  rw [deletionFactorizationGradeCross_eq_of_coprime hα
    (by omega : 0 < p) (by omega : 0 < q) hpq]
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpow : 0 ≤ (q : ℝ) ^ (-α) := Real.rpow_nonneg (by positivity) _
  have hfactor :
      0 < 1 + (q : ℝ) * ((q : ℝ) - 2) * (q : ℝ) ^ (-α) := by
    have : 0 ≤ (q : ℝ) * ((q : ℝ) - 2) * (q : ℝ) ^ (-α) := by positivity
    linarith
  exact mul_pos
    (mul_pos (deletionDirichletMass_pos hα) (deletionDirichletMean_pos hα hp))
    hfactor

/-- Every full modulus product block has zero single-channel sum. -/
theorem sum_blockDeletionCoefficient_product_block_eq_zero
    {p q : ℕ} :
    ∑ n ∈ Finset.range (p * q), blockDeletionCoefficient p (n + 1) = 0 := by
  change deletionCoeffPartialSum p (p * q) = 0
  rw [deletionCoeffPartialSum_eq_mod]
  norm_cast
  exact Nat.mod_eq_zero_of_dvd (dvd_mul_right p q)

/-- A squarefree interaction has zero uniform mean on its common product block. -/
theorem sum_deletionFactorizationInteraction_product_block_eq_zero
    {p q : ℕ} (hpq : Nat.Coprime p q) :
    ∑ n ∈ Finset.range (p * q), deletionFactorizationInteraction p q (n + 1) = 0 := by
  simp_rw [deletionFactorizationInteraction,
    blockDeletionCoefficient_mul_eq_add_sub_product_of_coprime hpq]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_blockDeletionCoefficient_product_block_eq_zero]
  have hqsum :
      ∑ n ∈ Finset.range (p * q), blockDeletionCoefficient q (n + 1) = 0 := by
    rw [mul_comm]
    exact sum_blockDeletionCoefficient_product_block_eq_zero
  rw [hqsum]
  have hpqsum :
      ∑ n ∈ Finset.range (p * q), blockDeletionCoefficient (p * q) (n + 1) = 0 := by
    simpa using
      (sum_blockDeletionCoefficient_product_block_eq_zero
        (p := p * q) (q := 1))
  rw [hpqsum]
  ring

/-- Exact square energy of one channel on a common product block. -/
theorem sum_blockDeletionCoefficient_sq_product_block
    {p q : ℕ} :
    ∑ n ∈ Finset.range (p * q), blockDeletionCoefficient p (n + 1) ^ 2 =
      (p * q : ℕ) * ((p : ℤ) - 1) := by
  simp_rw [blockDeletionCoefficient_sq_eq]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_blockDeletionCoefficient_product_block_eq_zero]
  ring

/-- Distinct squarefree grades are orthogonal for uniform counting on the product block. -/
theorem sum_single_mul_interaction_product_block_eq_zero
    {p q : ℕ} (hpq : Nat.Coprime p q) :
    ∑ n ∈ Finset.range (p * q),
      blockDeletionCoefficient q (n + 1) *
        deletionFactorizationInteraction p q (n + 1) = 0 := by
  have hpoint (n : ℕ) :
      blockDeletionCoefficient q n * deletionFactorizationInteraction p q n =
        blockDeletionCoefficient p n * blockDeletionCoefficient q n ^ 2 := by
    simp [deletionFactorizationInteraction]
    ring
  calc
    (∑ n ∈ Finset.range (p * q),
        blockDeletionCoefficient q (n + 1) *
          deletionFactorizationInteraction p q (n + 1)) =
        ((q : ℤ) - 1) *
            ∑ n ∈ Finset.range (p * q), blockDeletionCoefficient p (n + 1) +
          (2 - (q : ℤ)) *
            ∑ n ∈ Finset.range (p * q),
              deletionFactorizationInteraction p q (n + 1) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [hpoint, blockDeletionCoefficient_sq_eq]
      simp [deletionFactorizationInteraction]
      ring
    _ = 0 := by
      rw [sum_blockDeletionCoefficient_product_block_eq_zero,
        sum_deletionFactorizationInteraction_product_block_eq_zero hpq]
      ring

/-- Exact energy of the squarefree interaction grade. -/
theorem sum_deletionFactorizationInteraction_sq_product_block
    {p q : ℕ} (hpq : Nat.Coprime p q) :
    ∑ n ∈ Finset.range (p * q),
      deletionFactorizationInteraction p q (n + 1) ^ 2 =
      (p * q : ℕ) * ((p : ℤ) - 1) * ((q : ℤ) - 1) := by
  have hcross :
      ∑ n ∈ Finset.range (p * q),
        blockDeletionCoefficient p (n + 1) ^ 2 *
          blockDeletionCoefficient q (n + 1) = 0 := by
    have h := sum_single_mul_interaction_product_block_eq_zero
      (p := q) (q := p) hpq.symm
    rw [mul_comm q p] at h
    calc
      (∑ n ∈ Finset.range (p * q),
          blockDeletionCoefficient p (n + 1) ^ 2 *
            blockDeletionCoefficient q (n + 1)) =
          ∑ n ∈ Finset.range (p * q),
            blockDeletionCoefficient p (n + 1) *
              deletionFactorizationInteraction q p (n + 1) := by
        apply Finset.sum_congr rfl
        intro n _
        simp [deletionFactorizationInteraction, pow_two]
        ring
      _ = 0 := h
  calc
    (∑ n ∈ Finset.range (p * q),
        deletionFactorizationInteraction p q (n + 1) ^ 2) =
        ((q : ℤ) - 1) *
            ∑ n ∈ Finset.range (p * q),
              blockDeletionCoefficient p (n + 1) ^ 2 +
          (2 - (q : ℤ)) *
            ∑ n ∈ Finset.range (p * q),
              blockDeletionCoefficient p (n + 1) ^ 2 *
                blockDeletionCoefficient q (n + 1) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [deletionFactorizationInteraction, mul_pow,
        blockDeletionCoefficient_sq_eq q]
      ring
    _ = (p * q : ℕ) * ((p : ℤ) - 1) * ((q : ℤ) - 1) := by
      rw [sum_blockDeletionCoefficient_sq_product_block, hcross]
      ring

/-- Exact Pythagorean splitting of the inserted channel into degree one and degree two. -/
theorem sum_deletionFactorizationInsertion_sq_product_block
    {p q : ℕ} (hpq : Nat.Coprime p q) :
    ∑ n ∈ Finset.range (p * q),
      deletionFactorizationInsertion p q (n + 1) ^ 2 =
      (p * q : ℕ) * (p : ℤ) * ((q : ℤ) - 1) := by
  have hpoint (n : ℕ) :
      deletionFactorizationInsertion p q n ^ 2 =
        blockDeletionCoefficient q n ^ 2 +
          deletionFactorizationInteraction p q n ^ 2 -
            2 * (blockDeletionCoefficient q n *
              deletionFactorizationInteraction p q n) := by
    simp [deletionFactorizationInsertion]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hdense :
      ∑ n ∈ Finset.range (p * q), blockDeletionCoefficient q (n + 1) ^ 2 =
        (p * q : ℕ) * ((q : ℤ) - 1) := by
    rw [mul_comm p q]
    exact sum_blockDeletionCoefficient_sq_product_block
  rw [hdense]
  rw [sum_single_mul_interaction_product_block_eq_zero hpq]
  rw [sum_deletionFactorizationInteraction_sq_product_block hpq]
  ring

/-- On the same product block, uniform insertion energy is exactly `p` times dense energy. -/
theorem deletionFactorizationInsertion_uniform_replication_scale
    {p q : ℕ} (hpq : Nat.Coprime p q) :
    ∑ n ∈ Finset.range (p * q),
        deletionFactorizationInsertion p q (n + 1) ^ 2 =
      (p : ℤ) * ∑ n ∈ Finset.range (p * q),
        blockDeletionCoefficient q (n + 1) ^ 2 := by
  rw [sum_deletionFactorizationInsertion_sq_product_block hpq]
  have hdense :
      ∑ n ∈ Finset.range (p * q), blockDeletionCoefficient q (n + 1) ^ 2 =
        (p * q : ℕ) * ((q : ℤ) - 1) := by
    rw [mul_comm p q]
    exact sum_blockDeletionCoefficient_sq_product_block
  rw [hdense]
  ring

end RHTower
