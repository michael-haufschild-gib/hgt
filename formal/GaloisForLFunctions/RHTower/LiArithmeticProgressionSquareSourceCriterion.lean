import GaloisForLFunctions.RHTower.LiPairedPrimeArchShiftedMomentLanding

/-!
# Arithmetic-progression Li criterion and even square-source landing

For every fixed positive step `k`, paired-Li nonnegativity only at degrees `k * n` is already
equivalent to RH.  The hard direction applies the corpus dominance theorem to the powered
reciprocal family `w ↦ w ^ k`; its negative degree pulls back to a multiple of `k`.

At step two, Chebyshev algebra factors the whole finite source polynomial:

`2 - 2 T_{2(n+1)}(1-u/2) = u(4-u) U_n(1-u/2)^2`.

Consequently Route LI reduces exactly to nonnegativity of one hard-edge weighted-square family in
the completed prime--Gamma quarter-shift moment functional.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- Abstract Li dominance remains true after restricting degrees to any fixed positive multiple. -/
theorem exists_re_tsum_liTerm_neg_on_multiples
    {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}
    (hm : ∀ i, 1 ≤ m i)
    (hv : ∀ i, 1 ≤ ‖v i‖)
    (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable (fun i => m i * ‖v i - 1‖ ^ 2))
    {i₀ : ι} (hlt : 1 < ‖v i₀‖)
    {k : ℕ} (hk : 0 < k) :
    ∃ n : ℕ, ∑' i, m i * (liTerm (v i) (k * n)).re < 0 := by
  have hM1 : 1 ≤ M := le_trans (hv i₀) (hM i₀)
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM1
  have hvPow : ∀ i, 1 ≤ ‖(v i) ^ k‖ := by
    intro i
    rw [norm_pow]
    exact one_le_pow₀ (hv i)
  have hMPow : ∀ i, ‖(v i) ^ k‖ ≤ M ^ k := by
    intro i
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM i) k
  let A : ℝ := (k : ℝ) * M ^ k
  have hA0 : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM0 _)
  have hsPow : Summable (fun i => m i * ‖(v i) ^ k - 1‖ ^ 2) := by
    refine Summable.of_nonneg_of_le
      (fun i => mul_nonneg (le_trans (by norm_num) (hm i)) (sq_nonneg _))
      (fun i => ?_) (hs.mul_left (A ^ 2))
    have hdef : ‖(v i) ^ k - 1‖ ≤ A * ‖v i - 1‖ := by
      calc
        ‖(v i) ^ k - 1‖
            ≤ (k : ℝ) * max 1 ‖v i‖ ^ k * ‖v i - 1‖ :=
          norm_pow_sub_one_le (v i) k
        _ = (k : ℝ) * ‖v i‖ ^ k * ‖v i - 1‖ := by
          rw [max_eq_right (hv i)]
        _ ≤ (k : ℝ) * M ^ k * ‖v i - 1‖ := by
          gcongr
          exact hM i
        _ = A * ‖v i - 1‖ := by rfl
    have hm0 : 0 ≤ m i := le_trans (by norm_num) (hm i)
    have hnorm0 : 0 ≤ ‖v i - 1‖ := norm_nonneg _
    have hpowNorm0 : 0 ≤ ‖(v i) ^ k - 1‖ := norm_nonneg _
    have hsq : ‖(v i) ^ k - 1‖ ^ 2 ≤ (A * ‖v i - 1‖) ^ 2 := by
      nlinarith
    calc
      m i * ‖(v i) ^ k - 1‖ ^ 2 ≤ m i * (A * ‖v i - 1‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hm0
      _ = A ^ 2 * (m i * ‖v i - 1‖ ^ 2) := by ring
  have hbadPow : 1 < ‖(v i₀) ^ k‖ := by
    rw [norm_pow]
    exact one_lt_pow₀ hlt (Nat.ne_of_gt hk)
  obtain ⟨n, hn⟩ := exists_re_tsum_liTerm_neg hm hvPow hMPow hsPow hbadPow
  refine ⟨n, ?_⟩
  have hid : ∀ i, liTerm ((v i) ^ k) n = liTerm (v i) (k * n) := by
    intro i
    rw [liTerm, liTerm, pow_mul, pow_mul]
    rw [← inv_pow]
  simpa only [hid] using hn

/-- Nonnegativity on any fixed positive arithmetic progression of paired Li degrees forces RH. -/
theorem riemannHypothesis_of_forall_re_xiLiPaired_mul_nonneg
    {k : ℕ} (hk : 0 < k)
    (h : ∀ n : ℕ, 0 ≤ (xiLiPaired (k * n)).re) : RiemannHypothesis := by
  by_contra hRH
  rw [riemannHypothesis_iff_xi_zero_re_eq_half] at hRH
  push Not at hRH
  obtain ⟨ρ₁, hρ₁zero, hρ₁re⟩ := hRH
  set ρ₀ : XiDivisorSupport := ⟨ρ₁, mem_xi_divisor_support_of_eq_zero hρ₁zero⟩ with hρ₀def
  obtain ⟨M, hM1, hMb⟩ := exists_bound_xiRootW
  have hne0 : ∀ ρ : XiDivisorSupport, (ρ : ℂ) ≠ 0 := by
    intro ρ hzero
    have him := xi_divisor_support_im_ne_zero ρ
    rw [hzero] at him
    simp at him
  have hne1 : ∀ ρ : XiDivisorSupport, (ρ : ℂ) ≠ 1 := by
    intro ρ hone
    have him := xi_divisor_support_im_ne_zero ρ
    rw [hone] at him
    simp at him
  have hmult : ∀ ρ : XiDivisorSupport,
      (1 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    intro ρ
    have hpos := xi_divisor_pos_on_support ρ
    exact_mod_cast hpos
  have hvnorm : ∀ ρ : XiDivisorSupport, 1 ≤ ‖xiRootV (ρ : ℂ)‖ :=
    fun ρ => one_le_norm_xiRootV (hne0 ρ) (hne1 ρ)
  have hvM : ∀ ρ : XiDivisorSupport, ‖xiRootV (ρ : ℂ)‖ ≤ M := by
    intro ρ
    rw [norm_xiRootV (hne0 ρ) (hne1 ρ)]
    exact hMb ρ
  have hsum : Summable fun ρ : XiDivisorSupport =>
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ 2 := by
    refine Summable.of_nonneg_of_le
      (fun ρ => by nlinarith [hmult ρ, sq_nonneg ‖xiRootV (ρ : ℂ) - 1‖])
      (fun ρ => ?_) (xi_zero_multiplicity_inv_sq_summable.mul_left (M ^ 2))
    have hb := norm_xiRootV_sub_one_le (hne0 ρ) (hne1 ρ) hM1 (hMb ρ)
    have hw1 : ‖xiRootW (ρ : ℂ) - 1‖ = 1 / ‖(ρ : ℂ)‖ := norm_xiRootW_sub_one _
    rw [hw1] at hb
    have hnn : (0 : ℝ) ≤ ‖xiRootV (ρ : ℂ) - 1‖ := norm_nonneg _
    have hsq : ‖xiRootV (ρ : ℂ) - 1‖ ^ 2 ≤ M ^ 2 * (1 / ‖(ρ : ℂ)‖ ^ 2) := by
      have hM0 : (0 : ℝ) ≤ M := by linarith
      have hmul : (M * (1 / ‖(ρ : ℂ)‖)) ^ 2 = M ^ 2 * (1 / ‖(ρ : ℂ)‖ ^ 2) := by
        rw [mul_pow, div_pow, one_pow]
      rw [← hmul]
      nlinarith [mul_nonneg hM0 (by positivity : (0 : ℝ) ≤ 1 / ‖(ρ : ℂ)‖)]
    calc
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          ‖xiRootV (ρ : ℂ) - 1‖ ^ 2
          ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
              (M ^ 2 * (1 / ‖(ρ : ℂ)‖ ^ 2)) := by
            have := hmult ρ
            nlinarith
      _ = M ^ 2 *
          (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
            ring
  have hbad : 1 < ‖xiRootV ((ρ₀ : XiDivisorSupport) : ℂ)‖ := by
    have hnorm : ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ ≠ 1 := by
      intro hEq
      exact hρ₁re ((norm_xiRootW_eq_one_iff (hne0 ρ₀)).mp hEq)
    have hposw : 0 < ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ :=
      norm_pos_iff.mpr (xiRootW_ne_zero (hne0 ρ₀) (hne1 ρ₀))
    rw [norm_xiRootV (hne0 ρ₀) (hne1 ρ₀)]
    rcases lt_trichotomy ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ 1 with hlt | heq | hgt
    · refine lt_of_lt_of_le ?_ (le_max_right _ _)
      rw [one_lt_inv₀ hposw]
      exact hlt
    · exact absurd heq hnorm
    · exact lt_of_lt_of_le hgt (le_max_left _ _)
  obtain ⟨n, hn⟩ :=
    exists_re_tsum_liTerm_neg_on_multiples hmult hvnorm hvM hsum hbad hk
  refine absurd (h n) (not_le.mpr ?_)
  have hre : (xiLiPaired (k * n)).re =
      ∑' ρ : XiDivisorSupport,
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          (liTerm (xiRootV (ρ : ℂ)) (k * n)).re := by
    rw [xiLiPaired, Complex.re_tsum (summable_xiLiPairedTerm (k * n))]
    refine tsum_congr fun ρ => ?_
    rw [xiLiPairedTerm, Complex.re_ofReal_mul, liTerm_xiRootV]
  rw [hre]
  exact hn

/-- RH is equivalent to paired-Li nonnegativity on any one fixed positive-step progression. -/
theorem riemannHypothesis_iff_forall_re_xiLiPaired_mul_nonneg
    {k : ℕ} (hk : 0 < k) :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ (xiLiPaired (k * n)).re :=
  ⟨fun hRH n => re_xiLiPaired_nonneg_of_rh hRH (k * n),
    riemannHypothesis_of_forall_re_xiLiPaired_mul_nonneg hk⟩

/-- Positive-degree version of the fixed-step paired-Li criterion. -/
theorem riemannHypothesis_iff_forall_re_xiLiPaired_mul_succ_nonneg
    {k : ℕ} (hk : 0 < k) :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ (xiLiPaired (k * (n + 1))).re := by
  constructor
  · intro hRH n
    exact re_xiLiPaired_nonneg_of_rh hRH (k * (n + 1))
  · intro h
    apply riemannHypothesis_of_forall_re_xiLiPaired_mul_nonneg hk
    intro n
    cases n with
    | zero =>
        have hzero : xiLiPaired 0 = 0 := by
          rw [xiLiPaired]
          apply Eq.trans (tsum_congr ?_) tsum_zero
          intro ρ
          norm_num [xiLiPairedTerm, liTerm]
        simp [hzero]
    | succ n => simpa [Nat.succ_eq_add_one] using h n

private theorem chebyshevT_sq_add_one_sub_X_sq_mul_chebyshevU_sq (n : ℕ) :
    (Polynomial.Chebyshev.T ℂ ((n : ℤ) + 1)) ^ 2 +
      (1 - X ^ 2) * (Polynomial.Chebyshev.U ℂ (n : ℤ)) ^ 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Nat.cast_succ]
      rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring]
      rw [Polynomial.Chebyshev.T_eq_X_mul_T_sub_pol_U ℂ (n : ℤ),
        Polynomial.Chebyshev.U_eq_X_mul_U_add_T ℂ (n : ℤ)]
      linear_combination (norm := ring_nf) ih

/-- The hard-edge weighted Chebyshev square governing the even Li degrees. -/
def liEvenShiftedSquarePolynomial (n : ℕ) : Polynomial ℂ :=
  X * (C 4 - X) *
    ((Polynomial.Chebyshev.U ℂ (n : ℤ)).comp
      (C 1 - C (1 / 2) * X)) ^ 2

/-- The even Li polynomial is one fixed hard-edge weight times a Chebyshev square. -/
theorem liShiftedMomentPolynomial_two_mul_eq_weighted_chebyshevU_square (n : ℕ) :
    liShiftedMomentPolynomial (2 * (n + 1)) = liEvenShiftedSquarePolynomial n := by
  rw [liEvenShiftedSquarePolynomial]
  have hnorm := chebyshevT_sq_add_one_sub_X_sq_mul_chebyshevU_sq n
  have hdouble :=
    Polynomial.Chebyshev.T_mul_T ℂ ((n : ℤ) + 1) ((n : ℤ) + 1)
  have hind : ((n : ℤ) + 1) - ((n : ℤ) + 1) = 0 := by ring
  have hsum : ((n : ℤ) + 1) + ((n : ℤ) + 1) = (2 * (n + 1) : ℕ) := by omega
  rw [hind, hsum, Polynomial.Chebyshev.T_zero] at hdouble
  have hcore :
      (2 : Polynomial ℂ) - 2 * Polynomial.Chebyshev.T ℂ (2 * (n + 1) : ℕ) =
        4 * (1 - X ^ 2) * (Polynomial.Chebyshev.U ℂ (n : ℤ)) ^ 2 := by
    linear_combination (norm := ring_nf) -4 * hnorm + 2 * hdouble
  let A : Polynomial ℂ := C 1 - C (1 / 2) * X
  have hcomp := congrArg (fun P : Polynomial ℂ => P.comp A) hcore
  simp only [sub_comp, mul_comp, ofNat_comp, one_comp, X_comp, pow_comp] at hcomp
  rw [liShiftedMomentPolynomial]
  change (2 : Polynomial ℂ) - 2 *
      (Polynomial.Chebyshev.T ℂ (2 * (n + 1) : ℕ)).comp A =
    X * (4 - X) * ((Polynomial.Chebyshev.U ℂ (n : ℤ)).comp A) ^ 2
  calc
    (2 : Polynomial ℂ) - 2 *
        (Polynomial.Chebyshev.T ℂ (2 * (n + 1) : ℕ)).comp A =
      4 * (1 - A ^ 2) * ((Polynomial.Chebyshev.U ℂ (n : ℤ)).comp A) ^ 2 := hcomp
    _ = X * (4 - X) * ((Polynomial.Chebyshev.U ℂ (n : ℤ)).comp A) ^ 2 := by
      have hhalf : (2 : Polynomial ℂ) * C (1 / 2 : ℂ) = 1 := by
        rw [← C_ofNat, ← map_mul]
        norm_num
      dsimp only [A]
      simp only [map_one]
      linear_combination (norm := ring_nf)
        (4 * X * ((Polynomial.Chebyshev.U ℂ (n : ℤ)).comp
            (1 - C (1 / 2) * X)) ^ 2 -
          (2 * C (1 / 2) + 1) * X ^ 2 *
            ((Polynomial.Chebyshev.U ℂ (n : ℤ)).comp
              (1 - C (1 / 2) * X)) ^ 2) * hhalf

/-- Literal completed prime--Gamma source formed with the even weighted-square polynomial. -/
def liPrimeArchEvenSquareSource (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range ((liEvenShiftedSquarePolynomial n).natDegree + 1),
    (liEvenShiftedSquarePolynomial n).coeff j *
      primeArchShiftedReciprocalMoment (1 / 4) (j - 1)

/-- The existing Li source at a positive even degree is exactly the weighted-square source. -/
theorem liPrimeArchShiftedMomentSource_two_mul_eq_evenSquareSource (n : ℕ) :
    liPrimeArchShiftedMomentSource (2 * (n + 1)) = liPrimeArchEvenSquareSource n := by
  rw [liPrimeArchShiftedMomentSource, liPrimeArchEvenSquareSource,
    liShiftedMomentPolynomial_two_mul_eq_weighted_chebyshevU_square]

/-- Every positive even paired Li coefficient is the literal weighted-square source value. -/
theorem xiLiPaired_two_mul_eq_liPrimeArchEvenSquareSource (n : ℕ) :
    xiLiPaired (2 * (n + 1)) = liPrimeArchEvenSquareSource n := by
  rw [xiLiPaired_eq_liPrimeArchShiftedMomentSource,
    liPrimeArchShiftedMomentSource_two_mul_eq_evenSquareSource]

/-- Source-only even-square Li criterion. -/
theorem riemannHypothesis_iff_forall_re_liPrimeArchEvenSquareSource_nonneg :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ (liPrimeArchEvenSquareSource n).re := by
  rw [riemannHypothesis_iff_forall_re_xiLiPaired_mul_succ_nonneg (by norm_num : 0 < 2)]
  constructor <;> intro h n
  · rw [← xiLiPaired_two_mul_eq_liPrimeArchEvenSquareSource]
    exact h n
  · rw [xiLiPaired_two_mul_eq_liPrimeArchEvenSquareSource]
    exact h n

end

end RHTower
