import GaloisForLFunctions.RHTower.Sieve.DirichletFiniteSetLargeValues
import GaloisForLFunctions.RHTower.Sieve.MaynardMontgomeryFiniteSet
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedRaise
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectionFibreHuxley

/-!
# Montgomery mean value for a raised fixed-width factor

This module is the Montgomery analogue of the raised Huxley interface.  It applies the exact
finite-fibre mean square directly to a convolution power, retaining the lower support edge
`A^ell` in the Perron weight.  No Huxley square-scale absorption hypothesis occurs.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- A coefficient vector supported above `A` pays at most `A^(-sigma)` when the Perron abscissa
weight is inserted. -/
theorem sum_normSq_sigmaWeighted_le_of_lower_support
    {N A : ℕ} (b : Fin N → ℂ) {sigma G : ℝ}
    (hsigma : 0 ≤ sigma) (hA : 1 ≤ A)
    (hsupp : ∀ j : Fin N, b j ≠ 0 → A ≤ (j : ℕ) + 1)
    (henergy : ∑ j : Fin N, ‖b j‖ ^ 2 ≤ G) :
    ∑ j : Fin N, ‖sigmaWeightedCoeff N b sigma j‖ ^ 2 ≤
      (((A : ℝ) ^ (-sigma)) ^ 2) * G := by
  have hAR : 0 < (A : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hterm : ∀ j : Fin N,
      ‖sigmaWeightedCoeff N b sigma j‖ ^ 2 ≤
        (((A : ℝ) ^ (-sigma)) ^ 2) * ‖b j‖ ^ 2 := by
    intro j
    by_cases hj : b j = 0
    · simp [sigmaWeightedCoeff, hj]
    · have hsupport := hsupp j hj
      have hn : 0 < ((((j : ℕ) + 1 : ℕ) : ℝ)) := by positivity
      have hweight : ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ (-sigma) ≤
          (A : ℝ) ^ (-sigma) := by
        rw [Real.rpow_neg hn.le, Real.rpow_neg hAR.le]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos hn sigma)
          (Real.rpow_pos_of_pos hAR sigma)).2
            (Real.rpow_le_rpow hAR.le (by exact_mod_cast hsupport) hsigma)
      have hweight0 : 0 ≤ ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ (-sigma) :=
        Real.rpow_nonneg hn.le _
      rw [sigmaWeightedCoeff, norm_mul, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_nonneg hweight0]
      have hmul :
          ‖b j‖ * ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ (-sigma) ≤
            ‖b j‖ * (A : ℝ) ^ (-sigma) :=
        mul_le_mul_of_nonneg_left hweight (norm_nonneg _)
      calc
        (‖b j‖ * ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ (-sigma)) ^ 2 ≤
            (‖b j‖ * (A : ℝ) ^ (-sigma)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hweight0) hmul 2
        _ = (((A : ℝ) ^ (-sigma)) ^ 2) * ‖b j‖ ^ 2 := by ring
  calc
    ∑ j : Fin N, ‖sigmaWeightedCoeff N b sigma j‖ ^ 2 ≤
        ∑ j : Fin N, (((A : ℝ) ^ (-sigma)) ^ 2) * ‖b j‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = (((A : ℝ) ^ (-sigma)) ^ 2) * ∑ j : Fin N, ‖b j‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (((A : ℝ) ^ (-sigma)) ^ 2) * G :=
      mul_le_mul_of_nonneg_left henergy (by positivity)

/-- **Raised fixed-width Montgomery count on an arbitrary finite fibre.** -/
theorem montgomery_raised_fixedWidth_large_values_finset
    {N A w ell : ℕ} (hA : 1 ≤ A) (hNell : 2 ≤ N ^ ell)
    (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ A * 2 ^ w)
    {sigma G : ℝ} (hsigma : 0 ≤ sigma)
    (henergy : ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤ G)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hlarge : ∀ r ∈ S, V ≤ ‖raisedDirichletValue N ell a sigma (lam r)‖) :
    (S.card : ℝ) * V ^ 2 ≤
      (T + 4 * ((N ^ ell : ℕ) : ℝ) * (1 + Real.log (N ^ ell))) *
        (1 / delta + 2 * Real.log (N ^ ell)) *
        (((((A ^ ell : ℕ) : ℝ) ^ (-sigma)) ^ 2) * G) := by
  let b : Fin (N ^ ell) → ℂ := convPow N ell a
  let weighted : Fin (N ^ ell) → ℂ := sigmaWeightedCoeff (N ^ ell) b sigma
  let conjugate : Fin (N ^ ell) → ℂ := fun j => (starRingEnd ℂ) (weighted j)
  have hbig : ∀ r ∈ S, V ≤ ‖dirPoly (N ^ ell) conjugate (lam r)‖ := by
    intro r hr
    rw [show dirPoly (N ^ ell) conjugate (lam r) =
      (starRingEnd ℂ) (dirPoly (N ^ ell) weighted (-lam r)) by
        exact dirPoly_conj_neg (N ^ ell) weighted (lam r)]
    rw [RCLike.norm_conj]
    have hvalue : dirPoly (N ^ ell) weighted (-lam r) =
        raisedDirichletValue N ell a sigma (lam r) := by
      rw [raisedDirichletValue, sum_anchoredDirichletTerm_eq_dirPoly]
    rw [hvalue]
    exact hlarge r hr
  have hbase := card_largeValues_dirPoly_finset (N ^ ell) hNell conjugate
    hdelta hT hV hgap hband hbig
  have hnorm : ∑ j : Fin (N ^ ell), ‖conjugate j‖ ^ 2 =
      ∑ j : Fin (N ^ ell), ‖weighted j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [RCLike.norm_conj]
  rw [hnorm] at hbase
  have hsuppRaised : ∀ j : Fin (N ^ ell), b j ≠ 0 →
      A ^ ell ≤ (j : ℕ) + 1 := by
    intro j hj
    exact (convPow_support_fixedWidth a hsupp j hj).1
  let P : ℝ := ((N ^ ell : ℕ) : ℝ)
  let C : ℝ := (T + 4 * P * (1 + Real.log P)) *
    (1 / delta + 2 * Real.log P)
  have hbase' : (S.card : ℝ) * V ^ 2 ≤
      C * ∑ j : Fin (N ^ ell), ‖weighted j‖ ^ 2 := by
    simpa [C, P] using hbase
  have hweighted := sum_normSq_sigmaWeighted_le_of_lower_support b hsigma
    (Nat.one_le_pow ell A hA) hsuppRaised henergy
  have hP1 : (1 : ℝ) ≤ P := by
    dsimp [P]
    exact_mod_cast (le_trans (by omega) hNell)
  have hlog : 0 ≤ Real.log P := Real.log_nonneg hP1
  have hfirst : 0 ≤ T + 4 * P * (1 + Real.log P) := by positivity
  have hsecond : 0 ≤ 1 / delta + 2 * Real.log P := by
    exact add_nonneg (one_div_nonneg.mpr hdelta.le) (mul_nonneg (by norm_num) hlog)
  have hC0 : 0 ≤ C := mul_nonneg hfirst hsecond
  have hfinal := hbase'.trans (mul_le_mul_of_nonneg_left hweighted hC0)
  simpa [C, P] using hfinal

/-- Literal selected-factor specialization of the raised Montgomery theorem. -/
theorem montgomery_heathBrown_selected_raised_large_values_finset
    {L X : ℕ} (label : HeathBrownSelectionLabel L X 60)
    (ell : ℕ) (hell : 0 < ell) (hlabel : label.2.Nonempty)
    {sigma G : ℝ} (hsigma : 0 ≤ sigma)
    (henergy : heathBrownSelectedRaisedEnergy label ell ≤ G)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hlarge : ∀ r ∈ S, V ≤
      ‖(∏ i : HeathBrownSelectedFactor label, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (heathBrownSelectedKind label i))
          (heathBrownSelectedExponent label i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖) :
    (S.card : ℝ) * V ^ 2 ≤
      (T + 4 * (((groupedDyadicUpper
          (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) *
          (1 + Real.log ((groupedDyadicUpper
            (heathBrownSelectedExponent label)) ^ ell))) *
        (1 / delta + 2 * Real.log ((groupedDyadicUpper
          (heathBrownSelectedExponent label)) ^ ell)) *
        ((((((groupedDyadicLower
          (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^ (-sigma)) ^ 2) * G) := by
  let F : HeathBrownSelectedFactor label → ArithmeticFunction ℝ := fun i =>
    heathBrownFactorBase L X (heathBrownSelectedKind label i)
  let q : HeathBrownSelectedFactor label → ℕ := heathBrownSelectedExponent label
  let a : Fin (groupedDyadicUpper q) → ℂ := groupedDyadicCoeffVector F q
  have hnonempty : Nonempty (HeathBrownSelectedFactor label) := by
    exact Finset.nonempty_coe_sort.mpr hlabel
  letI : Nonempty (HeathBrownSelectedFactor label) := hnonempty
  have hN : 2 ≤ (groupedDyadicUpper q) ^ ell := by
    have hbase : 2 ≤ groupedDyadicUpper q := two_le_groupedDyadicUpper q
    have hell1 : 1 ≤ ell := hell
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ell := Nat.pow_le_pow_right (by norm_num) hell1
      _ ≤ (groupedDyadicUpper q) ^ ell := Nat.pow_le_pow_left hbase ell
  have hsupp : ∀ n : Fin (groupedDyadicUpper q), a n ≠ 0 →
      groupedDyadicLower q ≤ (n : ℕ) + 1 ∧
        (n : ℕ) + 1 ≤ groupedDyadicLower q * 2 ^ Fintype.card (HeathBrownSelectedFactor label) := by
    intro n hn
    exact groupedDyadicCoeffVector_support_fixedWidth F q n hn
  have hlarge' : ∀ r ∈ S,
      V ≤ ‖raisedDirichletValue (groupedDyadicUpper q) ell a sigma (lam r)‖ := by
    intro r hr
    rw [show raisedDirichletValue (groupedDyadicUpper q) ell a sigma (lam r) =
      (∏ i : HeathBrownSelectedFactor label, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (heathBrownSelectedKind label i))
          (heathBrownSelectedExponent label i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell by
        exact raised_groupedDyadicValue_eq_product_pow F q ell sigma (lam r)]
    exact hlarge r hr
  simpa [F, q, a, heathBrownSelectedRaisedEnergy] using
    (montgomery_raised_fixedWidth_large_values_finset
      (one_le_groupedDyadicLower q) hN a hsupp hsigma henergy
      hdelta hT hV hgap hband hlarge')

end RHTower.Sieve
