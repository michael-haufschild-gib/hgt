import GaloisForLFunctions.RHTower.Sieve.DirichletFiniteSetLargeValues
import GaloisForLFunctions.RHTower.Sieve.MaynardGroupedFactor

/-!
# Literal Montgomery estimate for grouped Heath--Brown factors

The coefficient vector of a grouped factor is supported above its multiplicative lower edge.
Consequently inserting the Perron abscissa costs exactly that lower edge to the power `-sigma`.
Combining this fact with arbitrary-fibre Montgomery yields a count stated directly for the product
of the literal Möbius, zeta, and logarithmic factors selected from a Heath--Brown box.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

theorem two_le_groupedDyadicUpper {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) : 2 ≤ groupedDyadicUpper q := by
  rw [groupedDyadicUpper_eq_lower_mul_twoPow]
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
  have hlower : 1 ≤ groupedDyadicLower q := one_le_groupedDyadicLower q
  have htwo : 2 ≤ 2 ^ Fintype.card ι := by
    simpa using (Nat.pow_le_pow_right (n := 2) (by omega) hcard)
  calc
    2 = 1 * 2 := by omega
    _ ≤ groupedDyadicLower q * 2 ^ Fintype.card ι :=
      Nat.mul_le_mul hlower htwo

/-- The real-axis weight of a grouped factor is bounded by its lower edge. -/
theorem sum_normSq_sigmaWeighted_grouped_le
    {ι : Type*} [Fintype ι]
    (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ)
    {sigma G : ℝ} (hsigma : 0 ≤ sigma)
    (henergy : ∑ j : Fin (groupedDyadicUpper q),
      ‖groupedDyadicCoeffVector F q j‖ ^ 2 ≤ G) :
    ∑ j : Fin (groupedDyadicUpper q),
        ‖sigmaWeightedCoeff (groupedDyadicUpper q)
          (groupedDyadicCoeffVector F q) sigma j‖ ^ 2
      ≤ ((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G := by
  have hA : 0 < (groupedDyadicLower q : ℝ) := by
    exact_mod_cast (show 0 < groupedDyadicLower q by
      exact Nat.zero_lt_of_lt (one_le_groupedDyadicLower q))
  have hterm : ∀ j : Fin (groupedDyadicUpper q),
      ‖sigmaWeightedCoeff (groupedDyadicUpper q)
        (groupedDyadicCoeffVector F q) sigma j‖ ^ 2 ≤
      ((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
        ‖groupedDyadicCoeffVector F q j‖ ^ 2 := by
    intro j
    by_cases hj : groupedDyadicCoeffVector F q j = 0
    · simp [sigmaWeightedCoeff, hj]
    · have hsupp := groupedDyadicCoeffVector_support_fixedWidth F q j hj
      have hn : 0 < ((((j : ℕ) + 1 : ℕ) : ℝ)) := by positivity
      have hweight : ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ (-sigma) ≤
          (groupedDyadicLower q : ℝ) ^ (-sigma) := by
        rw [Real.rpow_neg hn.le, Real.rpow_neg hA.le]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos hn sigma)
          (Real.rpow_pos_of_pos hA sigma)).2
            (Real.rpow_le_rpow hA.le (by exact_mod_cast hsupp.1) hsigma)
      have hweight0 : 0 ≤ ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ (-sigma) :=
        Real.rpow_nonneg hn.le _
      rw [sigmaWeightedCoeff, norm_mul, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_nonneg hweight0]
      have hmul :
          ‖groupedDyadicCoeffVector F q j‖ *
              ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ (-sigma) ≤
            ‖groupedDyadicCoeffVector F q j‖ *
              (groupedDyadicLower q : ℝ) ^ (-sigma) :=
        mul_le_mul_of_nonneg_left hweight (norm_nonneg _)
      calc
        (‖groupedDyadicCoeffVector F q j‖ *
            ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ (-sigma)) ^ 2
          ≤ (‖groupedDyadicCoeffVector F q j‖ *
              (groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hweight0) hmul 2
        _ = ((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
            ‖groupedDyadicCoeffVector F q j‖ ^ 2 := by ring
  calc
    ∑ j : Fin (groupedDyadicUpper q),
        ‖sigmaWeightedCoeff (groupedDyadicUpper q)
          (groupedDyadicCoeffVector F q) sigma j‖ ^ 2
      ≤ ∑ j : Fin (groupedDyadicUpper q),
          ((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
            ‖groupedDyadicCoeffVector F q j‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = ((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
        ∑ j : Fin (groupedDyadicUpper q),
          ‖groupedDyadicCoeffVector F q j‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G :=
      mul_le_mul_of_nonneg_left henergy (by positivity)

/-- **Literal finite-fibre Montgomery count.** -/
theorem montgomery_heathBrown_grouped_large_values_finset
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {sigma G : ℝ} (hsigma : 0 ≤ sigma)
    (henergy : ∑ j : Fin (groupedDyadicUpper q),
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 ≤ G)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hlarge : ∀ r ∈ S, V ≤
      ‖∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖) :
    (S.card : ℝ) * V ^ 2 ≤
      (T + 4 * (groupedDyadicUpper q : ℝ) *
          (1 + Real.log (groupedDyadicUpper q))) *
        (1 / delta + 2 * Real.log (groupedDyadicUpper q)) *
        (((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 * G) := by
  let F : ι → ArithmeticFunction ℝ := fun i => heathBrownFactorBase L X (kind i)
  let b : Fin (groupedDyadicUpper q) → ℂ :=
    sigmaWeightedCoeff (groupedDyadicUpper q) (groupedDyadicCoeffVector F q) sigma
  let a : Fin (groupedDyadicUpper q) → ℂ := fun j => (starRingEnd ℂ) (b j)
  have hbig : ∀ r ∈ S, V ≤ ‖dirPoly (groupedDyadicUpper q) a (lam r)‖ := by
    intro r hr
    rw [show dirPoly (groupedDyadicUpper q) a (lam r) =
      (starRingEnd ℂ) (dirPoly (groupedDyadicUpper q) b (-lam r)) by
        exact dirPoly_conj_neg (groupedDyadicUpper q) b (lam r)]
    rw [RCLike.norm_conj]
    rw [show dirPoly (groupedDyadicUpper q) b (-lam r) =
      ∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I) by
        exact dirPoly_groupedDyadicCoeffVector_eq_product F q sigma (lam r)]
    exact hlarge r hr
  have hbase := card_largeValues_dirPoly_finset (groupedDyadicUpper q)
    (two_le_groupedDyadicUpper q) a hdelta hT hV hgap hband hbig
  have hnorm : ∑ j : Fin (groupedDyadicUpper q), ‖a j‖ ^ 2 =
      ∑ j : Fin (groupedDyadicUpper q), ‖b j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [RCLike.norm_conj]
  rw [hnorm] at hbase
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (sum_normSq_sigmaWeighted_grouped_le F q hsigma henergy) (by positivity))

end RHTower.Sieve
