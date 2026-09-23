import GaloisForLFunctions.RHTower.XiResolventWeightedTuranMachine
import GaloisForLFunctions.RHTower.XiResolventHankelEquivalence

/-!
# Spectral descent: RH as the polynomial Turán ladder

The universal level-cleansing machine iterates down the zero spectrum.  For any divisor copy,
strong induction on the number of copies of larger resolvent modulus cleanses everything above
it: the strictly higher copies are real atoms, the polynomial vanishing at those finitely many
atom values kills them as a weight, and the machine — fed the Turán minors of that polynomial
weight — cleanses the copy's own level.  Every copy is reached, so the whole divisor lies on the
critical line.

**Theorem**: at any one shift `X ≥ 0`,

`RH  ↔  ∀ p : Polynomial ℝ, ∀ n, 0 ≤ Re (M_p n * M_p (n+2) - M_p (n+1)^(2 : ℕ))`

where `M_p k = sum_q u_q^(k+1) (p (u_q))^(2 : ℕ)` are the `p`-weighted resolvent moments.  The data on
the right is the family of Turán (log-convexity) inequalities of the polynomially reweighted
moment sequences — the two-dimensional slice of the full Hankel positivity carved out by squared
real polynomial weights — and the forward implication proceeds by infinite descent down the zero
spectrum, locating the zeros on the critical line level by level from the lowest upward.
-/

open Complex

namespace RHTower

noncomputable section

/-- The `p`-weighted resolvent moments. -/
def xiPolyMoment (p : Polynomial ℝ) (k : ℕ) (X : ℝ) : ℂ :=
  xiWeightedResolventMoment
    (fun q => evalRealPolynomial p (xiResolventPoint X q) ^ (2 : ℕ)) k X

/-- Norm-summability of the polynomially weighted atoms. -/
theorem summable_norm_polyAtom {X : ℝ} (hX : 0 ≤ X) (p : Polynomial ℝ) (k : ℕ) :
    Summable (fun q : XiZeroCopy =>
      ‖xiResolventPoint X q ^ (k + 1) *
        evalRealPolynomial p (xiResolventPoint X q) ^ (2 : ℕ)‖) := by
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    ((summable_norm_xiResolventPoint hX).mul_right (evalRealPolynomialNormBound p 1 ^ (2 : ℕ)))
  rw [norm_mul]
  have h1 : ‖xiResolventPoint X q ^ (k + 1)‖ ≤ ‖xiResolventPoint X q‖ := by
    rw [norm_pow, pow_succ']
    have hle1 : ‖xiResolventPoint X q‖ ^ k ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_xiResolventPoint_le_one hX q)
    nlinarith [norm_nonneg (xiResolventPoint X q),
      pow_nonneg (norm_nonneg (xiResolventPoint X q)) k]
  have h2 : ‖evalRealPolynomial p (xiResolventPoint X q) ^ (2 : ℕ)‖ ≤
      evalRealPolynomialNormBound p 1 ^ (2 : ℕ) := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_evalRealPolynomial_le p (norm_xiResolventPoint_le_one hX q)) 2
  exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)

/-- **The polynomially weighted variance expansion.** -/
theorem two_mul_polyTuranMinorAt_eq_tsum_pair {X : ℝ} (hX : 0 ≤ X)
    (p : Polynomial ℝ) (n : ℕ) :
    2 * (xiPolyMoment p n X * xiPolyMoment p (n + 2) X - xiPolyMoment p (n + 1) X ^ (2 : ℕ)) =
      ∑' z : XiZeroCopy × XiZeroCopy,
        (xiResolventPoint X z.1 * xiResolventPoint X z.2) ^ (n + 1) *
          (evalRealPolynomial p (xiResolventPoint X z.1) ^ (2 : ℕ) *
            evalRealPolynomial p (xiResolventPoint X z.2) ^ (2 : ℕ)) *
          (xiResolventPoint X z.1 - xiResolventPoint X z.2) ^ (2 : ℕ) := by
  have h0 := summable_norm_polyAtom hX p n
  have h1 := summable_norm_polyAtom hX p (n + 1)
  have h2 := summable_norm_polyAtom hX p (n + 2)
  have hA := tsum_mul_tsum_of_summable_norm h0 h2
  have hB := tsum_mul_tsum_of_summable_norm h1 h1
  have hC := tsum_mul_tsum_of_summable_norm h2 h0
  have hsumA := summable_mul_of_summable_norm h0 h2
  have hsumB := summable_mul_of_summable_norm h1 h1
  have hsumC := summable_mul_of_summable_norm h2 h0
  have hpt : ∀ z : XiZeroCopy × XiZeroCopy,
      (xiResolventPoint X z.1 * xiResolventPoint X z.2) ^ (n + 1) *
        (evalRealPolynomial p (xiResolventPoint X z.1) ^ (2 : ℕ) *
          evalRealPolynomial p (xiResolventPoint X z.2) ^ (2 : ℕ)) *
        (xiResolventPoint X z.1 - xiResolventPoint X z.2) ^ (2 : ℕ) =
      (((xiResolventPoint X z.1 ^ (n + 1) *
          evalRealPolynomial p (xiResolventPoint X z.1) ^ (2 : ℕ)) *
          (xiResolventPoint X z.2 ^ (n + 2 + 1) *
            evalRealPolynomial p (xiResolventPoint X z.2) ^ (2 : ℕ)) -
        2 * ((xiResolventPoint X z.1 ^ (n + 1 + 1) *
            evalRealPolynomial p (xiResolventPoint X z.1) ^ (2 : ℕ)) *
          (xiResolventPoint X z.2 ^ (n + 1 + 1) *
            evalRealPolynomial p (xiResolventPoint X z.2) ^ (2 : ℕ)))) +
        (xiResolventPoint X z.1 ^ (n + 2 + 1) *
          evalRealPolynomial p (xiResolventPoint X z.1) ^ (2 : ℕ)) *
          (xiResolventPoint X z.2 ^ (n + 1) *
            evalRealPolynomial p (xiResolventPoint X z.2) ^ (2 : ℕ))) := by
    intro z
    ring
  rw [show xiPolyMoment p n X = ∑' q : XiZeroCopy, xiResolventPoint X q ^ (n + 1) *
      evalRealPolynomial p (xiResolventPoint X q) ^ (2 : ℕ) from rfl,
    show xiPolyMoment p (n + 1) X = ∑' q : XiZeroCopy,
      xiResolventPoint X q ^ (n + 1 + 1) *
        evalRealPolynomial p (xiResolventPoint X q) ^ (2 : ℕ) from rfl,
    show xiPolyMoment p (n + 2) X = ∑' q : XiZeroCopy,
      xiResolventPoint X q ^ (n + 2 + 1) *
        evalRealPolynomial p (xiResolventPoint X q) ^ (2 : ℕ) from rfl,
    tsum_congr hpt, (hsumA.sub (hsumB.mul_left 2)).tsum_add hsumC,
    hsumA.tsum_sub (hsumB.mul_left 2), tsum_mul_left, ← hA, ← hB, ← hC]
  ring

/-- **Under RH every polynomial Turán minor is nonnegative**: the pair expansion is a sum of
nonnegative reals. -/
theorem polyTuranMinor_re_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 ≤ X) (p : Polynomial ℝ) (n : ℕ) :
    0 ≤ (xiPolyMoment p n X * xiPolyMoment p (n + 2) X -
      xiPolyMoment p (n + 1) X ^ (2 : ℕ)).re := by
  have hhalf : (0 : ℝ) ≤ (2 * (xiPolyMoment p n X * xiPolyMoment p (n + 2) X -
      xiPolyMoment p (n + 1) X ^ (2 : ℕ))).re := by
    rw [two_mul_polyTuranMinorAt_eq_tsum_pair hX p n]
    have hterm : ∀ z : XiZeroCopy × XiZeroCopy, ∃ w : ℝ, 0 ≤ w ∧
        (xiResolventPoint X z.1 * xiResolventPoint X z.2) ^ (n + 1) *
          (evalRealPolynomial p (xiResolventPoint X z.1) ^ (2 : ℕ) *
            evalRealPolynomial p (xiResolventPoint X z.2) ^ (2 : ℕ)) *
          (xiResolventPoint X z.1 - xiResolventPoint X z.2) ^ (2 : ℕ) = (w : ℂ) := by
      intro z
      obtain ⟨v₁, hv₁, he₁⟩ := exists_pos_ofReal_xiResolventPoint_of_rh hRH hX z.1
      obtain ⟨v₂, hv₂, he₂⟩ := exists_pos_ofReal_xiResolventPoint_of_rh hRH hX z.2
      refine ⟨(v₁ * v₂) ^ (n + 1) *
        (Polynomial.eval v₁ p ^ (2 : ℕ) * Polynomial.eval v₂ p ^ (2 : ℕ)) * (v₁ - v₂) ^ (2 : ℕ),
        by positivity, ?_⟩
      rw [he₁, he₂, evalRealPolynomial_ofReal, evalRealPolynomial_ofReal]
      push_cast
      ring
    choose w hw hweq using hterm
    rw [tsum_congr hweq]
    by_cases hsum : Summable (fun z : XiZeroCopy × XiZeroCopy => ((w z : ℝ) : ℂ))
    · rw [Complex.re_tsum hsum]
      exact tsum_nonneg fun z => by simpa using hw z
    · rw [tsum_eq_zero_of_not_summable hsum]
      simp
  have h2 : (2 * (xiPolyMoment p n X * xiPolyMoment p (n + 2) X -
      xiPolyMoment p (n + 1) X ^ (2 : ℕ))).re =
      2 * (xiPolyMoment p n X * xiPolyMoment p (n + 2) X -
        xiPolyMoment p (n + 1) X ^ (2 : ℕ)).re := by
    simp [Complex.mul_re]
  rw [h2] at hhalf
  linarith

set_option maxHeartbeats 1600000 in
/-- **Spectral descent**: polynomial Turán data at one shift places the entire divisor on the
critical line, by strong induction on the number of copies of larger resolvent modulus. -/
theorem forall_criticalLine_of_forall_polyTuranMinor_re_nonneg {X : ℝ} (hX : 0 ≤ X)
    (hpoly : ∀ (p : Polynomial ℝ) (n : ℕ),
      0 ≤ (xiPolyMoment p n X * xiPolyMoment p (n + 2) X -
        xiPolyMoment p (n + 1) X ^ (2 : ℕ)).re) :
    ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 := by
  classical
  have hdescent : ∀ N : ℕ, ∀ q : XiZeroCopy,
      {q' : XiZeroCopy | ‖xiResolventPoint X q‖ ≤ ‖xiResolventPoint X q'‖}.ncard ≤ N →
      (xiSpectralPoint q).im = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro q hcard
      have hqpos : 0 < ‖xiResolventPoint X q‖ :=
        norm_pos_iff.mpr (xiResolventPoint_ne_zero hX q)
      have hfin : {q' : XiZeroCopy |
          ‖xiResolventPoint X q‖ ≤ ‖xiResolventPoint X q'‖}.Finite :=
        finite_setOf_le_norm_xiResolventPoint hX hqpos
      have hIH : ∀ q', ‖xiResolventPoint X q‖ < ‖xiResolventPoint X q'‖ →
          (xiSpectralPoint q').im = 0 := by
        intro q' hq'
        have hssub : {q'' : XiZeroCopy |
            ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q''‖} ⊂
            {q'' : XiZeroCopy |
              ‖xiResolventPoint X q‖ ≤ ‖xiResolventPoint X q''‖} := by
          constructor
          · intro q'' h
            exact le_trans hq'.le h
          · intro hsub
            have hqmem : q ∈ {q'' : XiZeroCopy |
                ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q''‖} :=
              hsub (le_refl ‖xiResolventPoint X q‖)
            have : ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q‖ := hqmem
            linarith
        have hlt : {q'' : XiZeroCopy |
            ‖xiResolventPoint X q'‖ ≤ ‖xiResolventPoint X q''‖}.ncard <
            {q'' : XiZeroCopy |
              ‖xiResolventPoint X q‖ ≤ ‖xiResolventPoint X q''‖}.ncard :=
          Set.ncard_lt_ncard hssub hfin
        exact IH _ (lt_of_lt_of_le hlt hcard) q' le_rfl
      have hval' : ∀ q', ‖xiResolventPoint X q‖ < ‖xiResolventPoint X q'‖ →
          xiResolventPoint X q' = ((‖xiResolventPoint X q'‖ : ℝ) : ℂ) := by
        intro q' hq'
        exact xiResolventPoint_eq_ofReal_of_im_eq_zero hX (lt_trans hqpos hq')
          (xiResolventPoint_im_eq_zero_of_spectral (hIH q' hq')) rfl
      set A : Finset XiZeroCopy := hfin.toFinset.filter
        (fun q' => ‖xiResolventPoint X q‖ < ‖xiResolventPoint X q'‖) with hA
      set atoms : Finset ℝ := A.image (fun q' => ‖xiResolventPoint X q'‖) with hatoms
      have hatomgt : ∀ r ∈ atoms, ‖xiResolventPoint X q‖ < r := by
        intro r hr
        rw [hatoms, Finset.mem_image] at hr
        obtain ⟨q', hq'A, rfl⟩ := hr
        rw [hA, Finset.mem_filter] at hq'A
        exact hq'A.2
      set P : Polynomial ℝ := ∏ r ∈ atoms, (Polynomial.X - Polynomial.C r) with hP
      have hPeval : ∀ z : ℂ, evalRealPolynomial P z =
          ∏ r ∈ atoms, (z - ((r : ℝ) : ℂ)) := by
        intro z
        rw [hP, evalRealPolynomial, Polynomial.map_prod, Polynomial.eval_prod]
        refine Finset.prod_congr rfl fun r _ => ?_
        simp
      have hWbound : ∀ q' : XiZeroCopy,
          ‖evalRealPolynomial P (xiResolventPoint X q') ^ (2 : ℕ)‖ ≤
            evalRealPolynomialNormBound P 1 ^ (2 : ℕ) := by
        intro q'
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_evalRealPolynomial_le P (norm_xiResolventPoint_le_one hX q')) 2
      have hvalW : ∀ q₁ q₂ : XiZeroCopy,
          xiResolventPoint X q₂ = (starRingEnd ℂ) (xiResolventPoint X q₁) →
          evalRealPolynomial P (xiResolventPoint X q₂) ^ (2 : ℕ) =
            (starRingEnd ℂ) (evalRealPolynomial P (xiResolventPoint X q₁) ^ (2 : ℕ)) := by
        intro q₁ q₂ h
        rw [h, evalRealPolynomial_conj, ← map_pow]
      have hkill : ∀ q', ‖xiResolventPoint X q‖ < ‖xiResolventPoint X q'‖ →
          evalRealPolynomial P (xiResolventPoint X q') ^ (2 : ℕ) = 0 := by
        intro q' hq'
        have hmemA : q' ∈ A := by
          rw [hA, Finset.mem_filter, Set.Finite.mem_toFinset]
          exact ⟨le_of_lt hq', hq'⟩
        have hmematoms : ‖xiResolventPoint X q'‖ ∈ atoms := by
          rw [hatoms, Finset.mem_image]
          exact ⟨q', hmemA, rfl⟩
        have hPzero : evalRealPolynomial P (xiResolventPoint X q') = 0 := by
          rw [hPeval]
          refine Finset.prod_eq_zero hmematoms ?_
          rw [sub_eq_zero]
          exact hval' q' hq'
        rw [hPzero]
        ring
      have hnz : ∀ q', ‖xiResolventPoint X q'‖ = ‖xiResolventPoint X q‖ →
          evalRealPolynomial P (xiResolventPoint X q') ^ (2 : ℕ) ≠ 0 := by
        intro q' hq' hzero
        have hPzero : evalRealPolynomial P (xiResolventPoint X q') = 0 :=
          pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
        rw [hPeval] at hPzero
        obtain ⟨r, hr, hfac⟩ := Finset.prod_eq_zero_iff.mp hPzero
        have hval : xiResolventPoint X q' = ((r : ℝ) : ℂ) := sub_eq_zero.mp hfac
        have hnorm : ‖xiResolventPoint X q'‖ = r := by
          rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
          exact lt_trans hqpos (hatomgt r hr)
        rw [hq'] at hnorm
        have := hatomgt r hr
        linarith
      have hmachine := forall_level_criticalLine_of_weighted_turanMinors hX
        hWbound hvalW hqpos hkill hnz (fun n => hpoly P n)
      exact hmachine q rfl
  intro q
  exact hdescent _ q le_rfl

/-- Polynomial Turán data at one shift proves RH. -/
theorem riemannHypothesis_of_forall_polyTuranMinor_re_nonneg {X : ℝ} (hX : 0 ≤ X)
    (hpoly : ∀ (p : Polynomial ℝ) (n : ℕ),
      0 ≤ (xiPolyMoment p n X * xiPolyMoment p (n + 2) X -
        xiPolyMoment p (n + 1) X ^ (2 : ℕ)).re) :
    RiemannHypothesis := by
  have hall := forall_criticalLine_of_forall_polyTuranMinor_re_nonneg hX hpoly
  by_contra hRH
  obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
  have h1 : (xiSpectralPoint q ^ (2 : ℕ)).im = 0 := by
    rw [sq, Complex.mul_im, hall q]
    ring
  rw [h1] at hq
  exact lt_irrefl 0 hq

/-- **RH is the polynomial Turán ladder**: at any one shift, the Riemann hypothesis is
equivalent to the Turán inequalities of all polynomially reweighted resolvent moment
sequences. -/
theorem riemannHypothesis_iff_forall_polyTuranMinor_re_nonneg {X : ℝ} (hX : 0 ≤ X) :
    RiemannHypothesis ↔ ∀ (p : Polynomial ℝ) (n : ℕ),
      0 ≤ (xiPolyMoment p n X * xiPolyMoment p (n + 2) X -
        xiPolyMoment p (n + 1) X ^ (2 : ℕ)).re :=
  ⟨fun hRH p n => polyTuranMinor_re_nonneg_of_riemannHypothesis hRH hX p n,
    riemannHypothesis_of_forall_polyTuranMinor_re_nonneg hX⟩

end

end RHTower
