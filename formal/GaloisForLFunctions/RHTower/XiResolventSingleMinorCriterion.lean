import GaloisForLFunctions.RHTower.XiResolventEvenTuranMachine

/-!
# RH as a single Turán minor per polynomial

The moment-index quantifier of the polynomial Turán ladder is redundant: multiplying the weight
polynomial by `X^m` shifts every moment index by `2m`, since
`u^(k+1) * (u^m * p(u))^2 = u^(k+2m+1) * p(u)^2`.  The polynomial quantifier therefore
regenerates the whole even-index minor ladder from the single minor at index `0`, and the
even ladder drives the spectral descent through the parity-robust level-cleansing machine.

**Theorem**: at any one shift `X ≥ 0`,

`RH  ↔  ∀ p : Polynomial ℝ, 0 ≤ Re (M_p 0 * M_p 2 - M_p 1 ^ 2)`

where `M_p k = sum_q u_q^(k+1) (p (u_q))^2` — one Cauchy–Schwarz inequality per real
polynomial.  The criterion never demands positivity of any moment: a globally negated weight
system satisfies every minor inequality, yet for the resolvent divisor the minors alone force
every copy onto the critical line through oscillation, not through measure positivity.
-/

open Complex

namespace RHTower

noncomputable section

/-- Evaluation of the real polynomial `X` at a complex point. -/
theorem evalRealPolynomial_X (z : ℂ) : evalRealPolynomial Polynomial.X z = z := by
  simp [evalRealPolynomial]

/-- Multiplying the weight polynomial by `X^m` shifts the moment index by `2m`. -/
theorem xiPolyMoment_X_pow_mul (m : ℕ) (p : Polynomial ℝ) (k : ℕ) (X : ℝ) :
    xiPolyMoment (Polynomial.X ^ m * p) k X = xiPolyMoment p (k + 2 * m) X := by
  rw [show xiPolyMoment (Polynomial.X ^ m * p) k X = ∑' q : XiZeroCopy,
      xiResolventPoint X q ^ (k + 1) *
        evalRealPolynomial (Polynomial.X ^ m * p) (xiResolventPoint X q) ^ 2 from rfl,
    show xiPolyMoment p (k + 2 * m) X = ∑' q : XiZeroCopy,
      xiResolventPoint X q ^ (k + 2 * m + 1) *
        evalRealPolynomial p (xiResolventPoint X q) ^ 2 from rfl]
  refine tsum_congr fun q => ?_
  rw [evalRealPolynomial_mul, evalRealPolynomial_pow, evalRealPolynomial_X]
  ring

/-- **Single-minor spectral descent**: the index-`0` polynomial Turán minors alone, at one
shift, place the entire divisor on the critical line. -/
theorem forall_criticalLine_of_forall_polyTuranMinor_zero_re_nonneg {X : ℝ} (hX : 0 ≤ X)
    (hpoly : ∀ p : Polynomial ℝ,
      0 ≤ (xiPolyMoment p 0 X * xiPolyMoment p 2 X - xiPolyMoment p 1 X ^ 2).re) :
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
          ‖evalRealPolynomial P (xiResolventPoint X q') ^ 2‖ ≤
            evalRealPolynomialNormBound P 1 ^ 2 := by
        intro q'
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_evalRealPolynomial_le P (norm_xiResolventPoint_le_one hX q')) 2
      have hvalW : ∀ q₁ q₂ : XiZeroCopy,
          xiResolventPoint X q₂ = (starRingEnd ℂ) (xiResolventPoint X q₁) →
          evalRealPolynomial P (xiResolventPoint X q₂) ^ 2 =
            (starRingEnd ℂ) (evalRealPolynomial P (xiResolventPoint X q₁) ^ 2) := by
        intro q₁ q₂ h
        rw [h, evalRealPolynomial_conj, ← map_pow]
      have hkill : ∀ q', ‖xiResolventPoint X q‖ < ‖xiResolventPoint X q'‖ →
          evalRealPolynomial P (xiResolventPoint X q') ^ 2 = 0 := by
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
          evalRealPolynomial P (xiResolventPoint X q') ^ 2 ≠ 0 := by
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
      have hminorE : ∀ n : ℕ, 0 ≤ (xiPolyMoment P (2 * n) X *
          xiPolyMoment P (2 * n + 2) X - xiPolyMoment P (2 * n + 1) X ^ 2).re := by
        intro n
        have h := hpoly (Polynomial.X ^ n * P)
        rw [xiPolyMoment_X_pow_mul, xiPolyMoment_X_pow_mul, xiPolyMoment_X_pow_mul] at h
        have e0 : 0 + 2 * n = 2 * n := by omega
        have e2 : 2 + 2 * n = 2 * n + 2 := by omega
        have e1 : 1 + 2 * n = 2 * n + 1 := by omega
        rw [e0, e2, e1] at h
        exact h
      have hmachine := forall_level_criticalLine_of_weighted_turanMinors_even hX
        hWbound hvalW hqpos hkill hnz hminorE
      exact hmachine q rfl
  intro q
  exact hdescent _ q le_rfl

/-- The index-`0` polynomial Turán data at one shift proves RH. -/
theorem riemannHypothesis_of_forall_polyTuranMinor_zero_re_nonneg {X : ℝ} (hX : 0 ≤ X)
    (hpoly : ∀ p : Polynomial ℝ,
      0 ≤ (xiPolyMoment p 0 X * xiPolyMoment p 2 X - xiPolyMoment p 1 X ^ 2).re) :
    RiemannHypothesis := by
  have hall := forall_criticalLine_of_forall_polyTuranMinor_zero_re_nonneg hX hpoly
  by_contra hRH
  obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
  have h1 : (xiSpectralPoint q ^ 2).im = 0 := by
    rw [sq, Complex.mul_im, hall q]
    ring
  rw [h1] at hq
  exact lt_irrefl 0 hq

/-- **RH is a single Turán minor per polynomial**: at any one shift, the Riemann hypothesis
is equivalent to the index-`0` Turán (Cauchy–Schwarz) inequality of every polynomially
reweighted resolvent moment sequence — one inequality per real polynomial. -/
theorem riemannHypothesis_iff_forall_polyTuranMinor_zero_re_nonneg {X : ℝ} (hX : 0 ≤ X) :
    RiemannHypothesis ↔ ∀ p : Polynomial ℝ,
      0 ≤ (xiPolyMoment p 0 X * xiPolyMoment p 2 X - xiPolyMoment p 1 X ^ 2).re := by
  constructor
  · intro hRH p
    have h := polyTuranMinor_re_nonneg_of_riemannHypothesis hRH hX p 0
    simpa only [Nat.zero_add] using h
  · exact riemannHypothesis_of_forall_polyTuranMinor_zero_re_nonneg hX

end

end RHTower
