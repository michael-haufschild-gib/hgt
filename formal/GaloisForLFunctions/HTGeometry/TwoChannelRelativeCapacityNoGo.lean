import GaloisForLFunctions.HTGeometry.NonnegativeKernelDiagonalCapacity

/-!
# Two-channel relative-capacity no-go

Moving a diagonal counterterm before good/bad projection does not by itself preserve coherent
capacity.  In the complete class of channel-linear quadratic currents, positivity and a null
pure-bad diagonal force the mixed coefficient to vanish.  More sharply, universal control of a
negative signed excursion forces the pure-bad diagonal weight to be at least one.

The file also records the exact one-node tradeoff for the canonical anchored Schur complement:
the residual can dominate the removed anchor correlation only when the squared anchor coefficient
is at most one half.  Thus a source-faithful coefficient tending to one cannot be oriented by that
residual.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-- A scalarization of a symmetric two-channel Gram on aggregate good and bad masses. -/
def twoChannelLinearCurrent
    (goodWeight mixedWeight badWeight good bad : ℝ) : ℝ :=
  goodWeight * good ^ (2 : ℕ) + 2 * mixedWeight * good * bad + badWeight * bad ^ (2 : ℕ)

/-- Signed good-minus-bad source coordinate. -/
def twoChannelSignedExcursion (good bad : ℝ) : ℝ := good - bad

@[simp] theorem twoChannelLinearCurrent_pureGood
    (goodWeight mixedWeight badWeight good : ℝ) :
    twoChannelLinearCurrent goodWeight mixedWeight badWeight good 0 =
      goodWeight * good ^ (2 : ℕ) := by
  simp [twoChannelLinearCurrent]

@[simp] theorem twoChannelLinearCurrent_pureBad
    (goodWeight mixedWeight badWeight bad : ℝ) :
    twoChannelLinearCurrent goodWeight mixedWeight badWeight 0 bad =
      badWeight * bad ^ (2 : ℕ) := by
  simp [twoChannelLinearCurrent]

/-- Positivity plus cancellation of the pure-bad self-current also kills every mixed good/bad
coefficient.  A positive two-channel current cannot retain cross-channel orientation after
annihilating one diagonal channel. -/
theorem twoChannelLinearCurrent_mixedWeight_eq_zero_of_nonnegative_of_badWeight_eq_zero
    {goodWeight mixedWeight badWeight : ℝ}
    (hnonneg : ∀ good bad : ℝ,
      0 ≤ twoChannelLinearCurrent goodWeight mixedWeight badWeight good bad)
    (hbad : badWeight = 0) :
    mixedWeight = 0 := by
  have hgood : 0 ≤ goodWeight := by
    simpa [twoChannelLinearCurrent] using hnonneg 1 0
  have htest := hnonneg mixedWeight (-(goodWeight + 1))
  rw [hbad] at htest
  simp only [twoChannelLinearCurrent, zero_mul, add_zero] at htest
  have hprod : (goodWeight + 2) * mixedWeight ^ (2 : ℕ) ≤ 0 := by
    nlinarith
  have hweight : 0 < goodWeight + 2 := by linarith
  have hmixedSq : mixedWeight ^ (2 : ℕ) = 0 := by
    nlinarith [mul_nonneg hweight.le (sq_nonneg mixedWeight)]
  nlinarith [sq_nonneg mixedWeight]

/-- After a positive two-channel current cancels the bad diagonal, it is exactly a multiple of the
good diagonal and is blind to the bad channel. -/
theorem twoChannelLinearCurrent_eq_goodDiagonal_of_nonnegative_of_badWeight_eq_zero
    {goodWeight mixedWeight badWeight : ℝ}
    (hnonneg : ∀ good bad : ℝ,
      0 ≤ twoChannelLinearCurrent goodWeight mixedWeight badWeight good bad)
    (hbad : badWeight = 0) (good bad : ℝ) :
    twoChannelLinearCurrent goodWeight mixedWeight badWeight good bad =
      goodWeight * good ^ (2 : ℕ) := by
  rw [hbad,
    twoChannelLinearCurrent_mixedWeight_eq_zero_of_nonnegative_of_badWeight_eq_zero
      hnonneg hbad]
  simp [twoChannelLinearCurrent]

/-- If both diagonal channels of a nonnegative channel-linear current are cancelled, the current
vanishes identically. -/
theorem twoChannelLinearCurrent_eq_zero_of_nonnegative_of_diagonalWeights_eq_zero
    {goodWeight mixedWeight badWeight : ℝ}
    (hnonneg : ∀ good bad : ℝ,
      0 ≤ twoChannelLinearCurrent goodWeight mixedWeight badWeight good bad)
    (hgood : goodWeight = 0) (hbad : badWeight = 0) (good bad : ℝ) :
    twoChannelLinearCurrent goodWeight mixedWeight badWeight good bad = 0 := by
  rw [twoChannelLinearCurrent_eq_goodDiagonal_of_nonnegative_of_badWeight_eq_zero
    hnonneg hbad, hgood, zero_mul]

/-- Universal dominance of every negative good-minus-bad excursion forces retention of the full
pure-bad diagonal coefficient. -/
theorem one_le_twoChannelLinearCurrent_badWeight_of_negativeExcursionDominance
    {goodWeight mixedWeight badWeight : ℝ}
    (hdominates : ∀ good bad : ℝ,
      twoChannelSignedExcursion good bad < 0 →
        twoChannelSignedExcursion good bad ^ (2 : ℕ) ≤
          twoChannelLinearCurrent goodWeight mixedWeight badWeight good bad) :
    1 ≤ badWeight := by
  have hneg : twoChannelSignedExcursion 0 1 < 0 := by
    norm_num [twoChannelSignedExcursion]
  simpa [twoChannelSignedExcursion, twoChannelLinearCurrent] using
    hdominates 0 1 hneg

/-- A channel-linear current with cancelled pure-bad diagonal cannot dominate all negative signed
excursions, regardless of whether the cancellation is described before or after projection. -/
theorem not_negativeExcursionDominance_of_twoChannelLinearCurrent_badWeight_eq_zero
    {goodWeight mixedWeight badWeight : ℝ} (hbad : badWeight = 0) :
    ¬ (∀ good bad : ℝ,
      twoChannelSignedExcursion good bad < 0 →
        twoChannelSignedExcursion good bad ^ (2 : ℕ) ≤
          twoChannelLinearCurrent goodWeight mixedWeight badWeight good bad) := by
  intro hdominates
  have hweight :=
    one_le_twoChannelLinearCurrent_badWeight_of_negativeExcursionDominance hdominates
  linarith

/-! ## Pairwise-positive kernel closure -/

/-- Pairwise positivity of a real kernel: every two-node compression is a nonnegative quadratic
current.  For a symmetric matrix this is forced by positive semidefiniteness. -/
def PairwiseNonnegativeKernel {ι : Type*} (kernel : ι → ι → ℝ) : Prop :=
  ∀ i j x y, 0 ≤
    twoChannelLinearCurrent (kernel i i) (kernel i j) (kernel j j) x y

/-- In a pairwise-positive kernel, a null diagonal entry kills every mixed coefficient pointing
into that entry. -/
theorem pairwiseNonnegativeKernel_entry_eq_zero_of_diagonal_eq_zero
    {ι : Type*} {kernel : ι → ι → ℝ}
    (hnonneg : PairwiseNonnegativeKernel kernel) {i j : ι}
    (hdiag : kernel j j = 0) :
    kernel i j = 0 := by
  exact
    twoChannelLinearCurrent_mixedWeight_eq_zero_of_nonnegative_of_badWeight_eq_zero
      (hnonneg i j) hdiag

/-- Any cross term coupled to a null diagonal forces ambient indefiniteness.  This is the exact
alternative left after a relative current cancels one self-current but still needs that channel
for orientation. -/
theorem not_pairwiseNonnegativeKernel_of_entry_ne_zero_of_diagonal_eq_zero
    {ι : Type*} {kernel : ι → ι → ℝ} {i j : ι}
    (hentry : kernel i j ≠ 0) (hdiag : kernel j j = 0) :
    ¬ PairwiseNonnegativeKernel kernel := by
  intro hnonneg
  exact hentry
    (pairwiseNonnegativeKernel_entry_eq_zero_of_diagonal_eq_zero hnonneg hdiag)

/-- For a symmetric pairwise-positive kernel, a zero diagonal annihilates the complete row.  Thus
no globally nonhereditary positive current can cancel one self-current yet recover it through
cross-block coupling. -/
theorem pairwiseNonnegativeKernel_row_eq_zero_of_symmetric_of_diagonal_eq_zero
    {ι : Type*} {kernel : ι → ι → ℝ}
    (hnonneg : PairwiseNonnegativeKernel kernel)
    (hsymmetric : ∀ i j, kernel i j = kernel j i) {j : ι}
    (hdiag : kernel j j = 0) :
    ∀ i, kernel j i = 0 := by
  intro i
  rw [hsymmetric j i]
  exact pairwiseNonnegativeKernel_entry_eq_zero_of_diagonal_eq_zero
    hnonneg hdiag

/-- A symmetric pairwise-positive kernel that cancels every diagonal in a set annihilates every
cross term from that set to the full carrier. -/
theorem pairwiseNonnegativeKernel_cross_eq_zero_of_symmetric_of_diagonal_eq_zero
    {ι : Type*} {kernel : ι → ι → ℝ} {bad : Set ι}
    (hnonneg : PairwiseNonnegativeKernel kernel)
    (hsymmetric : ∀ i j, kernel i j = kernel j i)
    (hdiag : ∀ j ∈ bad, kernel j j = 0) :
    ∀ j ∈ bad, ∀ i, kernel j i = 0 := by
  intro j hj
  exact pairwiseNonnegativeKernel_row_eq_zero_of_symmetric_of_diagonal_eq_zero
    hnonneg hsymmetric (hdiag j hj)

/-! ## Diagonal-null off-diagonal current -/

/-- Quadratic kernel energy with every self-current deleted.  This form need not be positive on the
ambient vector space, but it is nonnegative on the nonnegative cone when the off-diagonal kernel is
pointwise nonnegative. -/
def finsetOffDiagonalKernelEnergy {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (kernel : ι → ι → ℝ) (mass : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    if i = j then 0 else mass i * kernel i j * mass j

/-- With unit off-diagonal coupling, the diagonal-null current is exactly total mass squared minus
the diagonal square mass. -/
theorem finsetOffDiagonalKernelEnergy_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (mass : ι → ℝ) :
    finsetOffDiagonalKernelEnergy s (fun _ _ => 1) mass =
      (∑ i ∈ s, mass i) ^ (2 : ℕ) - ∑ i ∈ s, mass i ^ (2 : ℕ) := by
  classical
  rw [finsetOffDiagonalKernelEnergy]
  calc
    (∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else mass i * 1 * mass j) =
        ∑ i ∈ s, ((∑ j ∈ s, mass i * mass j) - mass i ^ (2 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j ∈ s, if i = j then 0 else mass i * 1 * mass j) =
            ∑ j ∈ s,
              (mass i * mass j - if i = j then mass i * mass j else 0) := by
          apply Finset.sum_congr rfl
          intro j _hj
          split_ifs
          · ring
          · ring
        _ = (∑ j ∈ s, mass i * mass j) -
            ∑ j ∈ s, (if i = j then mass i * mass j else 0) := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ j ∈ s, mass i * mass j) - mass i ^ (2 : ℕ) := by
          rw [Finset.sum_ite_eq]
          simp only [hi, if_true]
          ring
    _ = (∑ i ∈ s, mass i) ^ (2 : ℕ) - ∑ i ∈ s, mass i ^ (2 : ℕ) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul_sum]
      ring

/-- Constant off-diagonal coupling scales the exact pair-mass identity. -/
theorem finsetOffDiagonalKernelEnergy_const {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (kappa : ℝ) (mass : ι → ℝ) :
    finsetOffDiagonalKernelEnergy s (fun _ _ => kappa) mass =
      kappa * ((∑ i ∈ s, mass i) ^ (2 : ℕ) - ∑ i ∈ s, mass i ^ (2 : ℕ)) := by
  classical
  calc
    finsetOffDiagonalKernelEnergy s (fun _ _ => kappa) mass =
        kappa * finsetOffDiagonalKernelEnergy s (fun _ _ => 1) mass := by
      rw [finsetOffDiagonalKernelEnergy, finsetOffDiagonalKernelEnergy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      split_ifs
      · ring
      · ring
    _ = kappa * ((∑ i ∈ s, mass i) ^ (2 : ℕ) - ∑ i ∈ s, mass i ^ (2 : ℕ)) := by
      rw [finsetOffDiagonalKernelEnergy_one]

/-- A pointwise off-diagonal kernel floor controls the whole diagonal-null current by the exact
ordered pair mass. -/
theorem kappa_mul_pairMass_le_finsetOffDiagonalKernelEnergy
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (kernel : ι → ι → ℝ) (mass : ι → ℝ) {kappa : ℝ}
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hkernel : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → kappa ≤ kernel i j) :
    kappa * ((∑ i ∈ s, mass i) ^ (2 : ℕ) - ∑ i ∈ s, mass i ^ (2 : ℕ)) ≤
      finsetOffDiagonalKernelEnergy s kernel mass := by
  rw [← finsetOffDiagonalKernelEnergy_const]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  split_ifs with hij
  · exact le_rfl
  · calc
      mass i * kappa * mass j = mass i * (kappa * mass j) := by ring
      _ ≤ mass i * (kernel i j * mass j) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hkernel i hi j hj hij) (hmass j hj))
          (hmass i hi)
      _ = mass i * kernel i j * mass j := by ring

/-- Pointwise nonnegative off-diagonal coupling is copositive: its diagonal-null energy is
nonnegative on every nonnegative mass packet, even though a nonzero cross term makes the ambient
quadratic form indefinite. -/
theorem finsetOffDiagonalKernelEnergy_nonneg
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (kernel : ι → ι → ℝ) (mass : ι → ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hkernel : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 0 ≤ kernel i j) :
    0 ≤ finsetOffDiagonalKernelEnergy s kernel mass := by
  simpa using
    (kappa_mul_pairMass_le_finsetOffDiagonalKernelEnergy
      s kernel mass hmass hkernel :
        0 * ((∑ i ∈ s, mass i) ^ (2 : ℕ) - ∑ i ∈ s, mass i ^ (2 : ℕ)) ≤
          finsetOffDiagonalKernelEnergy s kernel mass)

/-- An antisymmetric exterior current has identically zero scalar quadratic energy.  It can retain
orientation as a two-form, but symmetric mass scalarization cannot turn it into capacity. -/
theorem finsetOffDiagonalKernelEnergy_eq_zero_of_antisymmetric
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (kernel : ι → ι → ℝ) (mass : ι → ℝ)
    (hantisymmetric : ∀ i j, kernel j i = -kernel i j) :
    finsetOffDiagonalKernelEnergy s kernel mass = 0 := by
  classical
  let term := fun i j : ι =>
    if i = j then 0 else mass i * kernel i j * mass j
  have hswap : ∀ i j, term j i = -term i j := by
    intro i j
    dsimp only [term]
    by_cases hij : i = j
    · subst j
      simp
    · have hji : j ≠ i := Ne.symm hij
      rw [if_neg hji, if_neg hij, hantisymmetric]
      ring
  rw [finsetOffDiagonalKernelEnergy]
  change ∑ i ∈ s, ∑ j ∈ s, term i j = 0
  have hneg : (∑ i ∈ s, ∑ j ∈ s, term i j) =
      -(∑ i ∈ s, ∑ j ∈ s, term i j) := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, term i j) =
          ∑ j ∈ s, ∑ i ∈ s, term i j := Finset.sum_comm
      _ = ∑ j ∈ s, ∑ i ∈ s, -term j i := by
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← hswap]
      _ = -(∑ j ∈ s, ∑ i ∈ s, term j i) := by simp
      _ = -(∑ i ∈ s, ∑ j ∈ s, term i j) := by rw [Finset.sum_comm]
  linarith

/-- Squared correlation carried by one normalized-kernel anchor coefficient. -/
def oneNodeAnchorSquare (anchorCoefficient mass : ℝ) : ℝ :=
  mass ^ (2 : ℕ) * anchorCoefficient ^ (2 : ℕ)

/-- One-node energy left by the canonical anchored Schur complement of a normalized kernel. -/
def oneNodeAnchoredSchurResidual (anchorCoefficient mass : ℝ) : ℝ :=
  mass ^ (2 : ℕ) * (1 - anchorCoefficient ^ (2 : ℕ))

/-- Anchor square and anchored Schur residual exactly partition the normalized one-node energy. -/
theorem oneNodeAnchorSquare_add_anchoredSchurResidual
    (anchorCoefficient mass : ℝ) :
    oneNodeAnchorSquare anchorCoefficient mass +
        oneNodeAnchoredSchurResidual anchorCoefficient mass = mass ^ (2 : ℕ) := by
  simp [oneNodeAnchorSquare, oneNodeAnchoredSchurResidual]
  ring

/-- Exact one-node Schur tradeoff: for nonzero mass, the anchored residual dominates the removed
anchor correlation exactly below the half-capacity threshold. -/
theorem oneNodeAnchorSquare_le_anchoredSchurResidual_iff
    {anchorCoefficient mass : ℝ} (hmass : mass ≠ 0) :
    oneNodeAnchorSquare anchorCoefficient mass ≤
        oneNodeAnchoredSchurResidual anchorCoefficient mass ↔
      anchorCoefficient ^ (2 : ℕ) ≤ 1 / 2 := by
  simp only [oneNodeAnchorSquare, oneNodeAnchoredSchurResidual]
  constructor
  · intro h
    have hmassSq : 0 < mass ^ (2 : ℕ) := sq_pos_of_ne_zero hmass
    nlinarith
  · intro h
    nlinarith [sq_nonneg mass]

/-- A source-faithful anchor coefficient above the half-capacity threshold cannot have its removed
correlation controlled by the canonical Schur residual. -/
theorem not_oneNodeAnchorSquare_le_anchoredSchurResidual_of_half_lt_sq
    {anchorCoefficient mass : ℝ} (hmass : mass ≠ 0)
    (hfaithful : 1 / 2 < anchorCoefficient ^ (2 : ℕ)) :
    ¬ oneNodeAnchorSquare anchorCoefficient mass ≤
        oneNodeAnchoredSchurResidual anchorCoefficient mass := by
  rw [oneNodeAnchorSquare_le_anchoredSchurResidual_iff hmass]
  exact not_le.mpr hfaithful

end

end GaloisForLFunctions.HTGeometry
