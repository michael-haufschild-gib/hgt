import GaloisForLFunctions.RHTower.XiResolventEffectivePolynomialDescent

/-!
# The nodal single-minor criterion

The spectral descent consumes polynomial Turán data only at killing products `∏ (X − r)` over
the real atoms strictly above the working level, and the single-minor reduction consumes only
`X^m`-shifts of those.  Hence the polynomial quantifier of the single-minor criterion collapses
to the *nodal family*: monic real-rooted polynomials `X^m · ∏_{r ∈ R} (X − r)` with node set
`R ⊂ (0,1]`.

At any one interior shift, the Riemann hypothesis is equivalent to the nonnegativity of the
single `(0,2,1)` Turán minor of the resolvent moments reweighted by the square of each nodal
polynomial — a test family of real-rooted squares, in place of arbitrary real polynomials.
-/

open Complex

namespace RHTower

noncomputable section

/-- The monic real polynomial with the prescribed finite set of real nodes as roots. -/
def nodalPolynomial (R : Finset ℝ) : Polynomial ℝ :=
  ∏ r ∈ R, (Polynomial.X - Polynomial.C r)

/-- Complex evaluation of a nodal polynomial is the product of the root offsets. -/
theorem evalRealPolynomial_nodalPolynomial (R : Finset ℝ) (z : ℂ) :
    evalRealPolynomial (nodalPolynomial R) z = ∏ r ∈ R, (z - ((r : ℝ) : ℂ)) := by
  rw [nodalPolynomial, evalRealPolynomial, Polynomial.map_prod, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun r _ => ?_
  simp

set_option maxHeartbeats 800000 in
/-- **The nodal descent**: single-minor Turán data at the shifted nodal polynomials with nodes
in `(0,1]` place every spectral point on the critical line. -/
theorem forall_criticalLine_of_forall_nodal_single_minor {X : ℝ} (hX : 0 ≤ X)
    (h0 : ∀ R : Finset ℝ, (∀ r ∈ R, 0 < r ∧ r ≤ 1) → ∀ m : ℕ,
      0 ≤ (xiPolyMoment (Polynomial.X ^ m * nodalPolynomial R) 0 X *
        xiPolyMoment (Polynomial.X ^ m * nodalPolynomial R) 2 X -
        xiPolyMoment (Polynomial.X ^ m * nodalPolynomial R) 1 X ^ (2 : ℕ)).re) :
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
      have hRconstraint : ∀ r ∈ atoms, 0 < r ∧ r ≤ 1 := by
        intro r hr
        refine ⟨lt_trans hqpos (hatomgt r hr), ?_⟩
        rw [hatoms, Finset.mem_image] at hr
        obtain ⟨q', _, rfl⟩ := hr
        exact norm_xiResolventPoint_le_one hX q'
      set P : Polynomial ℝ := nodalPolynomial atoms with hP
      have hPeval : ∀ z : ℂ, evalRealPolynomial P z =
          ∏ r ∈ atoms, (z - ((r : ℝ) : ℂ)) := by
        intro z
        rw [hP]
        exact evalRealPolynomial_nodalPolynomial atoms z
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
      have hminorW : ∀ n : ℕ,
          0 ≤ (xiPolyMoment P (2 * n) X * xiPolyMoment P (2 * n + 2) X -
            xiPolyMoment P (2 * n + 1) X ^ (2 : ℕ)).re := by
        intro n
        have h := h0 atoms hRconstraint n
        rw [xiPolyMoment_X_pow_mul, xiPolyMoment_X_pow_mul, xiPolyMoment_X_pow_mul] at h
        have e0 : 0 + 2 * n = 2 * n := by omega
        have e2 : 2 + 2 * n = 2 * n + 2 := by omega
        have e1 : 1 + 2 * n = 2 * n + 1 := by omega
        rw [e0, e2, e1] at h
        exact h
      have hmachine := forall_level_criticalLine_of_weighted_turanMinors_even hX
        hWbound hvalW hqpos hkill hnz hminorW
      exact hmachine q rfl
  intro q
  exact hdescent _ q le_rfl

/-- Nodal single-minor Turán data at one shift proves RH. -/
theorem riemannHypothesis_of_forall_nodal_single_minor {X : ℝ} (hX : 0 ≤ X)
    (h0 : ∀ R : Finset ℝ, (∀ r ∈ R, 0 < r ∧ r ≤ 1) → ∀ m : ℕ,
      0 ≤ (xiPolyMoment (Polynomial.X ^ m * nodalPolynomial R) 0 X *
        xiPolyMoment (Polynomial.X ^ m * nodalPolynomial R) 2 X -
        xiPolyMoment (Polynomial.X ^ m * nodalPolynomial R) 1 X ^ (2 : ℕ)).re) :
    RiemannHypothesis := by
  have hall := forall_criticalLine_of_forall_nodal_single_minor hX h0
  by_contra hRH
  obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
  have h1 : (xiSpectralPoint q ^ (2 : ℕ)).im = 0 := by
    rw [sq, Complex.mul_im, hall q]
    ring
  rw [h1] at hq
  exact lt_irrefl 0 hq

/-- **The nodal single-minor criterion**: at any one interior shift, the Riemann hypothesis is
equivalent to the single `(0,2,1)` Turán minor inequality of the resolvent moments reweighted
by the squares of the shifted nodal polynomials `X^m · ∏_{r ∈ R} (X − r)`, over finite node
sets `R ⊂ (0,1]` — the arbitrary real polynomial of the single-minor criterion collapses to
the monic real-rooted family. -/
theorem riemannHypothesis_iff_forall_nodal_single_minor {X : ℝ} (hX : 0 ≤ X) :
    RiemannHypothesis ↔ ∀ R : Finset ℝ, (∀ r ∈ R, 0 < r ∧ r ≤ 1) → ∀ m : ℕ,
      0 ≤ (xiPolyMoment (Polynomial.X ^ m * nodalPolynomial R) 0 X *
        xiPolyMoment (Polynomial.X ^ m * nodalPolynomial R) 2 X -
        xiPolyMoment (Polynomial.X ^ m * nodalPolynomial R) 1 X ^ (2 : ℕ)).re :=
  ⟨fun hRH R _ m => by
    simpa only [Nat.zero_add] using
      polyTuranMinor_re_nonneg_of_riemannHypothesis hRH hX
        (Polynomial.X ^ m * nodalPolynomial R) 0,
    riemannHypothesis_of_forall_nodal_single_minor hX⟩

end

end RHTower
