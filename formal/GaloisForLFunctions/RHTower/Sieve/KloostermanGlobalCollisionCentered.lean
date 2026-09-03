import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionInterval
import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumFourier

/-!
# Centered global Kloosterman collision receiver

The erased-diagonal global collision transform has zero common-period mean because every
off-diagonal global frequency is nonzero.  Its exact fourth-moment normal form is therefore a
centered variance, not an arbitrary fourth moment.

Combining this centering with the sharp pointwise and average single-modulus response bounds gives
an unconditional collective receiver with the exact factor `#Q + 1`, replacing the direct
`#Q * (#Q - 1)` multiplier by a product of two aggregate diagonal budgets.  At comparable
modulus/source weights this saves one full family-cardinality factor.  Every weight and source
residue energy remains visible, and the literal source-interval specialization inserts exact
residue occupancy.  The final theorems feed this bound back into the actual terminal Gram with
the zero-frequency orbit square deleted exactly.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- The erased-diagonal collision transform has exactly zero mean over its common period. -/
theorem sum_kloostermanGlobalCollisionTimeTransform_eq_zero
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ k : ZMod (kloostermanGlobalPeriod Q),
      kloostermanGlobalCollisionTimeTransform Q w B b k) = 0 := by
  letI : NeZero (kloostermanGlobalPeriod Q) :=
    ⟨(kloostermanGlobalPeriod_pos Q).ne'⟩
  unfold kloostermanGlobalCollisionTimeTransform
  simp_rw [ZMod.dft_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    rw [kloostermanGlobalFrequencyCoefficient_zero]
    simp
  · rw [← Finset.sum_mul]
    have hchar : (∑ k : ZMod (kloostermanGlobalPeriod Q),
        ZMod.stdAddChar (-(z * k))) = 0 := by
      convert sum_stdAddChar_mul (kloostermanGlobalPeriod Q) (-z) using 1
      · apply Fintype.sum_congr
        intro k
        congr 1
        ring
      · simp [hz0]
    rw [hchar, zero_mul]

/-- Pointwise diagonal response budget, with each complete transform charged at its sharp local
energy. -/
def kloostermanGlobalResponsePointwiseBudget
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, Complex.normSq (w q) *
    (((q + 1 : ℕ) : ℝ) ^ 2 *
      ∑ z : ZMod (q + 1),
        Complex.normSq (kloostermanSourceResidue (q + 1) B b z))

/-- Common-period average diagonal response budget. -/
def kloostermanGlobalResponseAverageBudget
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, Complex.normSq (w q) *
    (((q + 1 : ℕ) : ℝ) *
      ∑ z : ZMod (q + 1),
        Complex.normSq (kloostermanSourceResidue (q + 1) B b z))

private theorem normSq_sum_le_card_mul_sum_normSq_centered
    {iota : Type*} [DecidableEq iota]
    (S : Finset iota) (a : iota → ℂ) :
    Complex.normSq (∑ i ∈ S, a i) ≤
      (S.card : ℝ) * ∑ i ∈ S, Complex.normSq (a i) := by
  rw [← Complex.sq_norm]
  have htri : ‖∑ i ∈ S, a i‖ ≤ ∑ i ∈ S, ‖a i‖ := norm_sum_le _ _
  have hsum0 : 0 ≤ ∑ i ∈ S, ‖a i‖ := by positivity
  calc
    ‖∑ i ∈ S, a i‖ ^ 2 ≤ (∑ i ∈ S, ‖a i‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ i ∈ S, a i)]
    _ ≤ (S.card : ℝ) * ∑ i ∈ S, Complex.normSq (a i) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq S
        (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul,
        Complex.sq_norm, Nat.cast_ofNat, mul_one] using h

/-- Centered collective collision receiver.  Exact zero-frequency cancellation reduces the direct
ordered-pair finite-Cauchy loss to the single collective factor `#Q + 1`. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_centered
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      ((Q.card : ℝ) + 1) *
        kloostermanGlobalResponsePointwiseBudget Q w B b *
        kloostermanGlobalResponseAverageBudget Q w B b := by
  let P := kloostermanGlobalPeriod Q
  let response : ZMod P → ℕ → ℂ := fun k q =>
    w q * kloostermanGlobalModulusTimeResponse q B b k.val
  let diagonal : ZMod P → ℝ := fun k =>
    ∑ q ∈ Q, Complex.normSq (response k q)
  let total : ZMod P → ℝ := fun k =>
    Complex.normSq (∑ q ∈ Q, response k q)
  let U := kloostermanGlobalResponsePointwiseBudget Q w B b
  let V := kloostermanGlobalResponseAverageBudget Q w B b
  have hU : 0 ≤ U := by
    dsimp only [U, kloostermanGlobalResponsePointwiseBudget]
    exact Finset.sum_nonneg fun q hq =>
      mul_nonneg (Complex.normSq_nonneg _)
        (mul_nonneg (sq_nonneg _)
          (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _))
  have hV : 0 ≤ V := by
    dsimp only [V, kloostermanGlobalResponseAverageBudget]
    exact Finset.sum_nonneg fun q hq =>
      mul_nonneg (Complex.normSq_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _)
          (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _))
  have hdiagonal : ∀ k : ZMod P, 0 ≤ diagonal k := by
    intro k
    dsimp only [diagonal]
    exact Finset.sum_nonneg fun q hq => Complex.normSq_nonneg _
  have htotal : ∀ k : ZMod P, 0 ≤ total k := by
    intro k
    dsimp only [total]
    exact Complex.normSq_nonneg _
  have htotal_le : ∀ k : ZMod P,
      total k ≤ (Q.card : ℝ) * diagonal k := by
    intro k
    exact normSq_sum_le_card_mul_sum_normSq_centered Q (response k)
  have hdiagonal_le : ∀ k : ZMod P, diagonal k ≤ U := by
    intro k
    dsimp only [diagonal, response, U, kloostermanGlobalResponsePointwiseBudget]
    apply Finset.sum_le_sum
    intro q hq
    rw [Complex.normSq_mul]
    exact mul_le_mul_of_nonneg_left
      (normSq_kloostermanGlobalModulusTimeResponse_le q B b k.val)
      (Complex.normSq_nonneg _)
  have hcenter : (∑ k : ZMod P, total k) = ∑ k : ZMod P, diagonal k := by
    have hsum := sum_kloostermanGlobalCollisionTimeTransform_eq_zero Q w B b
    simp_rw [kloostermanGlobalCollisionTimeTransform_eq_normSq_sub_diagonal] at hsum
    have hreal : (∑ k : ZMod P, (total k - diagonal k)) = 0 := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_sum]
      simpa only [Complex.ofReal_zero, total, diagonal, response, P] using hsum
    rw [Finset.sum_sub_distrib] at hreal
    linarith
  have hpoint : ∀ k : ZMod P,
      (total k - diagonal k) ^ 2 ≤
        (Q.card : ℝ) * U * total k + U * diagonal k := by
    intro k
    have hd := hdiagonal k
    have ht := htotal k
    have htd := htotal_le k
    have hdU := hdiagonal_le k
    have htotalUpper : total k ≤ (Q.card : ℝ) * U := by
      calc
        total k ≤ (Q.card : ℝ) * diagonal k := htd
        _ ≤ (Q.card : ℝ) * U := by
          exact mul_le_mul_of_nonneg_left hdU (by positivity)
    have htotalSq : total k ^ 2 ≤ (Q.card : ℝ) * U * total k := by
      nlinarith [mul_nonneg (sub_nonneg.mpr htotalUpper) ht]
    have hdiagonalSq : diagonal k ^ 2 ≤ U * diagonal k := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hdU) hd]
    nlinarith [mul_nonneg ht hd]
  have hsumPoint :
      (∑ k : ZMod P, (total k - diagonal k) ^ 2) ≤
        ((Q.card : ℝ) + 1) * U * ∑ k : ZMod P, diagonal k := by
    calc
      (∑ k : ZMod P, (total k - diagonal k) ^ 2) ≤
          ∑ k : ZMod P,
            ((Q.card : ℝ) * U * total k + U * diagonal k) :=
        Finset.sum_le_sum fun k _ => hpoint k
      _ = (Q.card : ℝ) * U * (∑ k : ZMod P, total k) +
          U * ∑ k : ZMod P, diagonal k := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = ((Q.card : ℝ) + 1) * U * ∑ k : ZMod P, diagonal k := by
        rw [hcenter]
        ring
  have haverageDiagonal : (P : ℝ)⁻¹ * ∑ k : ZMod P, diagonal k ≤ V := by
    calc
      (P : ℝ)⁻¹ * ∑ k : ZMod P, diagonal k =
          ∑ q ∈ Q, Complex.normSq (w q) *
            ((P : ℝ)⁻¹ * ∑ k : ZMod P,
              Complex.normSq
                (kloostermanGlobalModulusTimeResponse q B b k.val)) := by
        dsimp only [diagonal, response]
        rw [Finset.sum_comm]
        simp_rw [Complex.normSq_mul]
        simp_rw [← Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ ∑ q ∈ Q, Complex.normSq (w q) *
          (((q + 1 : ℕ) : ℝ) *
            ∑ z : ZMod (q + 1),
              Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left
          (average_normSq_kloostermanGlobalModulusTimeResponse_le Q q hq B b)
          (Complex.normSq_nonneg _)
      _ = V := by
        rfl
  rw [kloostermanGlobalFrequencyCollisionEnergy_eq_average_responseMassDefect]
  change (P : ℝ)⁻¹ * ∑ k : ZMod P, (total k - diagonal k) ^ 2 ≤ _
  calc
    (P : ℝ)⁻¹ * ∑ k : ZMod P, (total k - diagonal k) ^ 2 ≤
        (P : ℝ)⁻¹ *
          (((Q.card : ℝ) + 1) * U * ∑ k : ZMod P, diagonal k) :=
      mul_le_mul_of_nonneg_left hsumPoint (by positivity)
    _ = ((Q.card : ℝ) + 1) * U *
        ((P : ℝ)⁻¹ * ∑ k : ZMod P, diagonal k) := by ring
    _ ≤ ((Q.card : ℝ) + 1) * U * V := by
      exact mul_le_mul_of_nonneg_left haverageDiagonal (by positivity)
    _ = ((Q.card : ℝ) + 1) *
        kloostermanGlobalResponsePointwiseBudget Q w B b *
        kloostermanGlobalResponseAverageBudget Q w B b := by
      rfl

/-- The actual terminal distinct-modulus Gram inherits the sharp centered collision receiver and
the exact nonzero-frequency orbit energy.  This closes the bridge from the collective collision
normal form back to the terminal quadratic appearing in the integer-kernel decomposition. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_centered
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ^ 2 ≤
      (((Q.card : ℝ) + 1) *
          kloostermanGlobalResponsePointwiseBudget Q w B b *
          kloostermanGlobalResponseAverageBudget Q w B b) *
        ((kloostermanGlobalPeriod Q : ℝ) *
            (M % kloostermanGlobalPeriod Q : ℕ) -
          ((M % kloostermanGlobalPeriod Q : ℕ) : ℝ) ^ 2) := by
  have horbit :
      0 ≤ (kloostermanGlobalPeriod Q : ℝ) *
          (M % kloostermanGlobalPeriod Q : ℕ) -
        ((M % kloostermanGlobalPeriod Q : ℕ) : ℝ) ^ 2 := by
    rw [← sum_normSq_kloostermanGlobalTerminalOrbit_erase_zero_eq M Q]
    exact Finset.sum_nonneg fun z hz => sq_nonneg _
  exact
    (norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_globalFrequencyCollisionEnergy_erase_zero
      M Q w B b).trans
      (mul_le_mul_of_nonneg_right
        (kloostermanGlobalFrequencyCollisionEnergy_le_centered Q w B b) horbit)

/-- Literal-interval pointwise diagonal response budget. -/
def kloostermanGlobalResponsePointwiseIntervalBudget
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, Complex.normSq (w q) *
    (((q + 1 : ℕ) : ℝ) ^ 2 *
      ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
        ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)))

/-- Literal-interval average diagonal response budget. -/
def kloostermanGlobalResponseAverageIntervalBudget
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, Complex.normSq (w q) *
    (((q + 1 : ℕ) : ℝ) *
      ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
        ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)))

/-- Literal-source centered receiver with exact residue occupancy on `Finset.Icc 1 N`. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_Icc_le_centered
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
      ((Q.card : ℝ) + 1) *
        kloostermanGlobalResponsePointwiseIntervalBudget Q w N b *
        kloostermanGlobalResponseAverageIntervalBudget Q w N b := by
  have hpointwise :
      kloostermanGlobalResponsePointwiseBudget Q w (Finset.Icc 1 N) b ≤
        kloostermanGlobalResponsePointwiseIntervalBudget Q w N b := by
    apply Finset.sum_le_sum
    intro q hq
    apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
    apply mul_le_mul_of_nonneg_left
      (sum_normSq_kloostermanSourceResidue_Icc_le_interval q N b)
      (sq_nonneg _)
  have haverage :
      kloostermanGlobalResponseAverageBudget Q w (Finset.Icc 1 N) b ≤
        kloostermanGlobalResponseAverageIntervalBudget Q w N b := by
    apply Finset.sum_le_sum
    intro q hq
    apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
    apply mul_le_mul_of_nonneg_left
      (sum_normSq_kloostermanSourceResidue_Icc_le_interval q N b)
      (Nat.cast_nonneg _)
  have haverage0 :
      0 ≤ kloostermanGlobalResponseAverageBudget Q w (Finset.Icc 1 N) b := by
    unfold kloostermanGlobalResponseAverageBudget
    exact Finset.sum_nonneg fun q hq =>
      mul_nonneg (Complex.normSq_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _)
          (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _))
  have hpointwiseInterval0 :
      0 ≤ kloostermanGlobalResponsePointwiseIntervalBudget Q w N b := by
    unfold kloostermanGlobalResponsePointwiseIntervalBudget
    exact Finset.sum_nonneg fun q hq =>
      mul_nonneg (Complex.normSq_nonneg _)
        (mul_nonneg (sq_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _)
            (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg _)))
  calc
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
        ((Q.card : ℝ) + 1) *
          kloostermanGlobalResponsePointwiseBudget Q w (Finset.Icc 1 N) b *
          kloostermanGlobalResponseAverageBudget Q w (Finset.Icc 1 N) b :=
      kloostermanGlobalFrequencyCollisionEnergy_le_centered Q w (Finset.Icc 1 N) b
    _ ≤ ((Q.card : ℝ) + 1) *
        kloostermanGlobalResponsePointwiseIntervalBudget Q w N b *
        kloostermanGlobalResponseAverageIntervalBudget Q w N b := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hpointwise (by positivity)) haverage
        haverage0
        (mul_nonneg (by positivity) hpointwiseInterval0)

/-- Literal-source terminal Gram receiver.  It retains the exact `Finset.Icc 1 N` residue
occupancies, the sharp centered family factor, and the zero-mode-subtracted orbit energy. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_Icc_sq_le_centered
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic
        M Q w (Finset.Icc 1 N) b‖ ^ 2 ≤
      (((Q.card : ℝ) + 1) *
          kloostermanGlobalResponsePointwiseIntervalBudget Q w N b *
          kloostermanGlobalResponseAverageIntervalBudget Q w N b) *
        ((kloostermanGlobalPeriod Q : ℝ) *
            (M % kloostermanGlobalPeriod Q : ℕ) -
          ((M % kloostermanGlobalPeriod Q : ℕ) : ℝ) ^ 2) := by
  have horbit :
      0 ≤ (kloostermanGlobalPeriod Q : ℝ) *
          (M % kloostermanGlobalPeriod Q : ℕ) -
        ((M % kloostermanGlobalPeriod Q : ℕ) : ℝ) ^ 2 := by
    rw [← sum_normSq_kloostermanGlobalTerminalOrbit_erase_zero_eq M Q]
    exact Finset.sum_nonneg fun z hz => sq_nonneg _
  exact
    (norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_globalFrequencyCollisionEnergy_erase_zero
      M Q w (Finset.Icc 1 N) b).trans
      (mul_le_mul_of_nonneg_right
        (kloostermanGlobalFrequencyCollisionEnergy_Icc_le_centered Q w N b) horbit)

end

end RHTower.Sieve
