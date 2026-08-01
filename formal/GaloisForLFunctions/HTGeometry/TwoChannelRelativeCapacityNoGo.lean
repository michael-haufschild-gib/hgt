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

/-- A scalarization of a symmetric two-channel Gram on aggregate good and bad masses. -/
def twoChannelLinearCurrent
    (goodWeight mixedWeight badWeight good bad : ℝ) : ℝ :=
  goodWeight * good ^ 2 + 2 * mixedWeight * good * bad + badWeight * bad ^ 2

/-- Signed good-minus-bad source coordinate. -/
def twoChannelSignedExcursion (good bad : ℝ) : ℝ := good - bad

@[simp] theorem twoChannelLinearCurrent_pureGood
    (goodWeight mixedWeight badWeight good : ℝ) :
    twoChannelLinearCurrent goodWeight mixedWeight badWeight good 0 =
      goodWeight * good ^ 2 := by
  simp [twoChannelLinearCurrent]

@[simp] theorem twoChannelLinearCurrent_pureBad
    (goodWeight mixedWeight badWeight bad : ℝ) :
    twoChannelLinearCurrent goodWeight mixedWeight badWeight 0 bad =
      badWeight * bad ^ 2 := by
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
  have hprod : (goodWeight + 2) * mixedWeight ^ 2 ≤ 0 := by
    nlinarith
  have hweight : 0 < goodWeight + 2 := by linarith
  have hmixedSq : mixedWeight ^ 2 = 0 := by
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
      goodWeight * good ^ 2 := by
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
        twoChannelSignedExcursion good bad ^ 2 ≤
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
        twoChannelSignedExcursion good bad ^ 2 ≤
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

/-- Squared correlation carried by one normalized-kernel anchor coefficient. -/
def oneNodeAnchorSquare (anchorCoefficient mass : ℝ) : ℝ :=
  mass ^ 2 * anchorCoefficient ^ 2

/-- One-node energy left by the canonical anchored Schur complement of a normalized kernel. -/
def oneNodeAnchoredSchurResidual (anchorCoefficient mass : ℝ) : ℝ :=
  mass ^ 2 * (1 - anchorCoefficient ^ 2)

/-- Anchor square and anchored Schur residual exactly partition the normalized one-node energy. -/
theorem oneNodeAnchorSquare_add_anchoredSchurResidual
    (anchorCoefficient mass : ℝ) :
    oneNodeAnchorSquare anchorCoefficient mass +
        oneNodeAnchoredSchurResidual anchorCoefficient mass = mass ^ 2 := by
  simp [oneNodeAnchorSquare, oneNodeAnchoredSchurResidual]
  ring

/-- Exact one-node Schur tradeoff: for nonzero mass, the anchored residual dominates the removed
anchor correlation exactly below the half-capacity threshold. -/
theorem oneNodeAnchorSquare_le_anchoredSchurResidual_iff
    {anchorCoefficient mass : ℝ} (hmass : mass ≠ 0) :
    oneNodeAnchorSquare anchorCoefficient mass ≤
        oneNodeAnchoredSchurResidual anchorCoefficient mass ↔
      anchorCoefficient ^ 2 ≤ 1 / 2 := by
  simp only [oneNodeAnchorSquare, oneNodeAnchoredSchurResidual]
  constructor
  · intro h
    have hmassSq : 0 < mass ^ 2 := sq_pos_of_ne_zero hmass
    nlinarith
  · intro h
    nlinarith [sq_nonneg mass]

/-- A source-faithful anchor coefficient above the half-capacity threshold cannot have its removed
correlation controlled by the canonical Schur residual. -/
theorem not_oneNodeAnchorSquare_le_anchoredSchurResidual_of_half_lt_sq
    {anchorCoefficient mass : ℝ} (hmass : mass ≠ 0)
    (hfaithful : 1 / 2 < anchorCoefficient ^ 2) :
    ¬ oneNodeAnchorSquare anchorCoefficient mass ≤
        oneNodeAnchoredSchurResidual anchorCoefficient mass := by
  rw [oneNodeAnchorSquare_le_anchoredSchurResidual_iff hmass]
  exact not_le.mpr hfaithful

end

end GaloisForLFunctions.HTGeometry
