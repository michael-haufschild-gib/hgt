import GaloisForLFunctions.RHTower.XiResolventTailSurrogate

/-!
# The relative nodal criterion: RH beyond any verification height

Line placement above one resolvent scale `δ` converts the nodal single-minor criterion into a
*relative* criterion: for a real polynomial `P` killing every copy above scale and alive below,
the Riemann hypothesis follows from the single `(0,2,1)` Turán minors of the polynomials
`X^m · ∏_{r∈R}(X − r) · P` alone.  Since `(P·p)²`-weighted moments are supported on the
sub-`δ` copies, the relative data live entirely on the truncated divisor: one verified scale
reduces RH to a countable list of inequalities about the remaining spectrum.

The complementary no-go is also recorded: under line placement the witness factor
`(eval_{r₁} (p·P))²` of the two-scale supply theorem vanishes for every admissible witness, so
the supply mechanism can never feed the relative data — the supply family and the certificate
family of polynomials are disjoint.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Truncation of the weighted moments**: when `P` kills every copy above scale, the
`(p·P)²`-weighted moments are supported on the sub-`δ` copies. -/
theorem xiPolyMoment_mul_eq_tsum_subtype_of_kill {X δ : ℝ}
    (P : Polynomial ℝ)
    (hPkill : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ →
      evalRealPolynomial P (xiResolventPoint X q) = 0)
    (p : Polynomial ℝ) (k : ℕ) :
    xiPolyMoment (p * P) k X =
      ∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
        xiResolventPoint X (q : XiZeroCopy) ^ (k + 1) *
          evalRealPolynomial (p * P) (xiResolventPoint X (q : XiZeroCopy)) ^ 2 := by
  rw [show xiPolyMoment (p * P) k X = ∑' q : XiZeroCopy,
    xiResolventPoint X q ^ (k + 1) *
      evalRealPolynomial (p * P) (xiResolventPoint X q) ^ 2 from rfl]
  refine (tsum_subtype_eq_of_support_subset ?_).symm
  intro q hq
  rw [Function.mem_support] at hq
  by_contra hqmem
  simp only [Set.mem_setOf_eq, not_lt] at hqmem
  refine hq ?_
  rw [evalRealPolynomial_mul, hPkill q hqmem]
  ring

/-- **The supply/certificate disjointness no-go**: under line placement above scale, the
two-scale supply's witness factor vanishes for every polynomial multiple of the killing
polynomial — the supply mechanism can never feed the relative data. -/
theorem eval_norm_mul_kill_eq_zero_of_line {X δ : ℝ} (hX : 0 ≤ X)
    (hline : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0)
    (P : Polynomial ℝ)
    (hPkill : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ →
      evalRealPolynomial P (xiResolventPoint X q) = 0)
    (p : Polynomial ℝ) {q₁ : XiZeroCopy} (h1 : δ ≤ ‖xiResolventPoint X q₁‖) (hδ : 0 < δ) :
    Polynomial.eval ‖xiResolventPoint X q₁‖ (p * P) = 0 := by
  have hreal : xiResolventPoint X q₁ = ((‖xiResolventPoint X q₁‖ : ℝ) : ℂ) :=
    xiResolventPoint_eq_ofReal_of_im_eq_zero hX (lt_of_lt_of_le hδ h1)
      (xiResolventPoint_im_eq_zero_of_spectral (hline q₁ h1)) rfl
  have hz : evalRealPolynomial P (xiResolventPoint X q₁) = 0 := hPkill q₁ h1
  rw [hreal, evalRealPolynomial_ofReal] at hz
  have hzr : Polynomial.eval ‖xiResolventPoint X q₁‖ P = 0 := by
    exact_mod_cast hz
  rw [Polynomial.eval_mul, hzr]
  ring

set_option maxHeartbeats 800000 in
/-- **The relative nodal descent**: line placement above one scale plus the relative nodal
single-minor data place every spectral point on the critical line. -/
theorem forall_criticalLine_of_partial_line_and_relative_nodal {X δ : ℝ} (hX : 0 ≤ X)
    (hline : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0)
    (P : Polynomial ℝ)
    (hPnz : ∀ q : XiZeroCopy, ‖xiResolventPoint X q‖ < δ →
      evalRealPolynomial P (xiResolventPoint X q) ≠ 0)
    (hdata : ∀ R : Finset ℝ, (∀ r ∈ R, 0 < r ∧ r ≤ 1) → ∀ m : ℕ,
      0 ≤ (xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 0 X *
        xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 2 X -
        xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 1 X ^ 2).re) :
    ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 := by
  classical
  have hdescent : ∀ N : ℕ, ∀ q : XiZeroCopy,
      {q' : XiZeroCopy | ‖xiResolventPoint X q‖ ≤ ‖xiResolventPoint X q'‖}.ncard ≤ N →
      (xiSpectralPoint q).im = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro q hcard
      by_cases hqδ : δ ≤ ‖xiResolventPoint X q‖
      · exact hline q hqδ
      rw [not_le] at hqδ
      have hqpos : 0 < ‖xiResolventPoint X q‖ :=
        norm_pos_iff.mpr (xiResolventPoint_ne_zero hX q)
      have hfin : {q' : XiZeroCopy |
          ‖xiResolventPoint X q‖ ≤ ‖xiResolventPoint X q'‖}.Finite :=
        finite_setOf_le_norm_xiResolventPoint hX hqpos
      have hIH : ∀ q', ‖xiResolventPoint X q‖ < ‖xiResolventPoint X q'‖ →
          (xiSpectralPoint q').im = 0 := by
        intro q' hq'
        by_cases hq'δ : δ ≤ ‖xiResolventPoint X q'‖
        · exact hline q' hq'δ
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
      set W : Polynomial ℝ := nodalPolynomial atoms * P with hW
      have hWeval : ∀ z : ℂ, evalRealPolynomial W z =
          (∏ r ∈ atoms, (z - ((r : ℝ) : ℂ))) * evalRealPolynomial P z := by
        intro z
        rw [hW, evalRealPolynomial_mul, evalRealPolynomial_nodalPolynomial]
      have hWbound : ∀ q' : XiZeroCopy,
          ‖evalRealPolynomial W (xiResolventPoint X q') ^ 2‖ ≤
            evalRealPolynomialNormBound W 1 ^ 2 := by
        intro q'
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_evalRealPolynomial_le W (norm_xiResolventPoint_le_one hX q')) 2
      have hvalW : ∀ q₁ q₂ : XiZeroCopy,
          xiResolventPoint X q₂ = (starRingEnd ℂ) (xiResolventPoint X q₁) →
          evalRealPolynomial W (xiResolventPoint X q₂) ^ 2 =
            (starRingEnd ℂ) (evalRealPolynomial W (xiResolventPoint X q₁) ^ 2) := by
        intro q₁ q₂ h
        rw [h, evalRealPolynomial_conj, ← map_pow]
      have hkill : ∀ q', ‖xiResolventPoint X q‖ < ‖xiResolventPoint X q'‖ →
          evalRealPolynomial W (xiResolventPoint X q') ^ 2 = 0 := by
        intro q' hq'
        have hmemA : q' ∈ A := by
          rw [hA, Finset.mem_filter, Set.Finite.mem_toFinset]
          exact ⟨le_of_lt hq', hq'⟩
        have hmematoms : ‖xiResolventPoint X q'‖ ∈ atoms := by
          rw [hatoms, Finset.mem_image]
          exact ⟨q', hmemA, rfl⟩
        have hnodal : (∏ r ∈ atoms, (xiResolventPoint X q' - ((r : ℝ) : ℂ))) = 0 := by
          refine Finset.prod_eq_zero hmematoms ?_
          rw [sub_eq_zero]
          exact hval' q' hq'
        rw [hWeval, hnodal]
        ring
      have hnz : ∀ q', ‖xiResolventPoint X q'‖ = ‖xiResolventPoint X q‖ →
          evalRealPolynomial W (xiResolventPoint X q') ^ 2 ≠ 0 := by
        intro q' hq' hzero
        have hWzero : evalRealPolynomial W (xiResolventPoint X q') = 0 :=
          pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
        rw [hWeval] at hWzero
        rcases mul_eq_zero.mp hWzero with hnodal | hP
        · obtain ⟨r, hr, hfac⟩ := Finset.prod_eq_zero_iff.mp hnodal
          have hval : xiResolventPoint X q' = ((r : ℝ) : ℂ) := sub_eq_zero.mp hfac
          have hnorm : ‖xiResolventPoint X q'‖ = r := by
            rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
            exact lt_trans hqpos (hatomgt r hr)
          rw [hq'] at hnorm
          have := hatomgt r hr
          linarith
        · exact hPnz q' (by rw [hq']; exact hqδ) hP
      have hminorW : ∀ n : ℕ,
          0 ≤ (xiPolyMoment W (2 * n) X * xiPolyMoment W (2 * n + 2) X -
            xiPolyMoment W (2 * n + 1) X ^ 2).re := by
        intro n
        have h := hdata atoms hRconstraint n
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

/-- **The relative nodal criterion**: line placement above one resolvent scale, together with
the countable relative nodal single-minor data at multiples of the killing polynomial, proves
the Riemann hypothesis — RH beyond any verified scale is exactly the truncated-spectrum
list. -/
theorem riemannHypothesis_of_partial_line_and_relative_nodal {X δ : ℝ} (hX : 0 ≤ X)
    (hline : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0)
    (P : Polynomial ℝ)
    (hPnz : ∀ q : XiZeroCopy, ‖xiResolventPoint X q‖ < δ →
      evalRealPolynomial P (xiResolventPoint X q) ≠ 0)
    (hdata : ∀ R : Finset ℝ, (∀ r ∈ R, 0 < r ∧ r ≤ 1) → ∀ m : ℕ,
      0 ≤ (xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 0 X *
        xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 2 X -
        xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 1 X ^ 2).re) :
    RiemannHypothesis := by
  have hall := forall_criticalLine_of_partial_line_and_relative_nodal hX hline P
    hPnz hdata
  by_contra hRH
  obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
  have h1 : (xiSpectralPoint q ^ 2).im = 0 := by
    rw [sq, Complex.mul_im, hall q]
    ring
  rw [h1] at hq
  exact lt_irrefl 0 hq

end

end RHTower
namespace RHTower

noncomputable section

/-- **RH beyond any verified scale, as an equivalence**: for any scale `δ` and any killing
polynomial alive below scale, the Riemann hypothesis is equivalent to line placement above the
scale together with the countable relative nodal single-minor list. -/
theorem riemannHypothesis_iff_partial_line_and_relative_nodal {X δ : ℝ} (hX : 0 ≤ X)
    (P : Polynomial ℝ)
    (hPnz : ∀ q : XiZeroCopy, ‖xiResolventPoint X q‖ < δ →
      evalRealPolynomial P (xiResolventPoint X q) ≠ 0) :
    RiemannHypothesis ↔
      ((∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0) ∧
        ∀ R : Finset ℝ, (∀ r ∈ R, 0 < r ∧ r ≤ 1) → ∀ m : ℕ,
          0 ≤ (xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 0 X *
            xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 2 X -
            xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 1 X ^ 2).re) := by
  constructor
  · intro hRH
    constructor
    · intro q _
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
      rw [ht, Complex.ofReal_im]
    · intro R _ m
      simpa only [Nat.zero_add] using
        polyTuranMinor_re_nonneg_of_riemannHypothesis hRH hX
          (Polynomial.X ^ m * (nodalPolynomial R * P)) 0
  · rintro ⟨hline, hdata⟩
    exact riemannHypothesis_of_partial_line_and_relative_nodal hX hline P hPnz hdata

end

end RHTower
