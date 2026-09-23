import GaloisForLFunctions.RHTower.XiResolventRelativeNodalCriterion

/-!
# Line placement above the Ward floor is unconditional

The corpus's certified off-line height floor — every off-critical zero of `ξ` has squared
ordinate above `65` — transfers to the spectral chart: every off-line divisor copy satisfies
`65 < Re(α)²`.  Consequently line placement above the resolvent scale `1/(X + 259/4)` is a
theorem: for `‖u_q(X)‖ ≥ δ ≥ 1/(X + 259/4)` the copy must be on the critical line, since an
off-line copy would have `Re(α² + X) > X + 259/4` and hence resolvent norm below the scale.

The relative nodal criterion therefore loses its line-placement hypothesis at the floor scale:
for any real polynomial alive below the scale, the Riemann hypothesis is equivalent to the
countable relative nodal single-minor list alone — a fully unconditional scale-factored
equivalence over a certified verified region.  The two-scale supply theorems at scales above
the floor likewise lose their line-placement hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The off-line height floor in the spectral chart**: every off-line divisor copy has
squared height above `65`. -/
theorem offline_height_sq_gt_sixtyfive (q : XiZeroCopy)
    (hoff : (xiSpectralPoint q).im ≠ 0) :
    (65 : ℝ) < (xiSpectralPoint q).re ^ (2 : ℕ) := by
  have hright : ∀ qr : XiRightZeroCopy, (65 : ℝ) < (xiSpectralPoint qr.1).re ^ (2 : ℕ) := by
    intro qr
    have hcen_im : ∀ qr' : XiRightZeroCopy,
        (xiRightCenteredZero qr').im = (xiSpectralPoint qr'.1).re := by
      intro qr'
      rw [xiRightCenteredZero, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    by_cases him : 0 < (xiRightCenteredZero qr).im
    · have h := xiWard_offlinePair_height_sq_gt_sixtyfive ⟨qr, him⟩
      rw [hcen_im qr] at h
      exact h
    · set qc := xiRightZeroCopyConjEquiv qr with hqc
      have hne := xiRightCenteredZero_im_ne_zero qr
      have hlt : (xiRightCenteredZero qr).im < 0 :=
        lt_of_le_of_ne (not_lt.mp him) hne
      have him' : 0 < (xiRightCenteredZero qc).im := by
        rw [hqc, xiRightCenteredZero_conj, Complex.conj_im]
        linarith
      have h := xiWard_offlinePair_height_sq_gt_sixtyfive ⟨qc, him'⟩
      have hval : (xiRightCenteredZero qc).im = -(xiSpectralPoint qr.1).re := by
        rw [hqc, xiRightCenteredZero_conj, Complex.conj_im, hcen_im qr]
      rw [hval, neg_sq] at h
      exact h
  rcases lt_or_gt_of_ne hoff with hneg | hpos
  · have hcond : 0 < (I * xiSpectralPoint q).re := by
      rw [Complex.mul_re, Complex.I_re, Complex.I_im]
      simp only [zero_mul, one_mul, zero_sub]
      linarith
    exact hright ⟨q, hcond⟩
  · set q' := xiZeroCopyReflectEquiv q with hq'
    have hα' : xiSpectralPoint q' = -xiSpectralPoint q := by
      rw [hq']
      exact xiSpectralPoint_reflect q
    have hcond : 0 < (I * xiSpectralPoint q').re := by
      rw [hα', Complex.mul_re, Complex.I_re, Complex.I_im]
      simp only [Complex.neg_im, Complex.neg_re, zero_mul, one_mul, zero_sub, neg_neg]
      linarith
    have h := hright ⟨q', hcond⟩
    rw [show (⟨q', hcond⟩ : XiRightZeroCopy).1 = q' from rfl, hα', Complex.neg_re,
      neg_sq] at h
    exact h

/-- **Unconditional line placement above the floor scale**: every copy with resolvent norm at
least `1/(X + 259/4)` lies on the critical line. -/
theorem hline_of_floor {X δ : ℝ} (hX : 0 ≤ X) (hδfloor : 1 / (X + 259 / 4) ≤ δ) :
    ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0 := by
  intro q hq
  by_contra hoff
  have hfloor := offline_height_sq_gt_sixtyfive q hoff
  have hs := xiSpectralPoint_im_sq_lt_quarter q
  have hzre : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re =
      (xiSpectralPoint q).re ^ (2 : ℕ) - (xiSpectralPoint q).im ^ (2 : ℕ) + X :=
    xiSpectralSq_add_ofReal_re_eq X q
  have hzre_gt : X + 259 / 4 < (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re := by
    rw [hzre]
    linarith
  have hnorm_lt : ‖xiResolventPoint X q‖ < 1 / (X + 259 / 4) := by
    have hXpos : (0 : ℝ) < X + 259 / 4 := by linarith
    have hnorm_le : ‖xiResolventPoint X q‖ ≤
        1 / (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re := by
      have hre_le : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re ≤
          ‖xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)‖ :=
        Complex.re_le_norm _
      have hrepos : (0 : ℝ) < (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re := by linarith
      rw [show ‖xiResolventPoint X q‖ = ‖xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)‖⁻¹ by
        rw [xiResolventPoint, norm_inv], inv_eq_one_div]
      exact one_div_le_one_div_of_le hrepos hre_le
    have hstep : 1 / (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re < 1 / (X + 259 / 4) :=
      one_div_lt_one_div_of_lt hXpos hzre_gt
    linarith
  linarith [hq, hnorm_lt, hδfloor]

/-- **The unconditional scale-factored endpoint**: for any real polynomial alive below the
floor scale, the Riemann hypothesis is equivalent to the countable relative nodal single-minor
list alone — the line-placement input is a theorem. -/
theorem riemannHypothesis_iff_relative_nodal_floor {X : ℝ} (hX : 0 ≤ X)
    (P : Polynomial ℝ)
    (hPnz : ∀ q : XiZeroCopy, ‖xiResolventPoint X q‖ < 1 / (X + 259 / 4) →
      evalRealPolynomial P (xiResolventPoint X q) ≠ 0) :
    RiemannHypothesis ↔
      ∀ R : Finset ℝ, (∀ r ∈ R, 0 < r ∧ r ≤ 1) → ∀ m : ℕ,
        0 ≤ (xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 0 X *
          xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 2 X -
          xiPolyMoment (Polynomial.X ^ m * (nodalPolynomial R * P)) 1 X ^ (2 : ℕ)).re := by
  rw [riemannHypothesis_iff_partial_line_and_relative_nodal (δ := 1 / (X + 259 / 4)) hX
    P hPnz]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨hline_of_floor hX (le_refl _), h⟩

/-- **Supply above the floor with line placement discharged**: at any scale above
`1/(X + 259/4)` the two-scale supply needs only the witnesses and the mass inequality. -/
theorem polyTuranMinor_supply_of_floor {X δ : ℝ} (hX : 0 ≤ X)
    (hδfloor : 1 / (X + 259 / 4) ≤ δ)
    (p : Polynomial ℝ) (m : ℕ) {B : ℝ}
    (hB : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖evalRealPolynomial p z‖ ≤ B)
    {q₁ q₂ : XiZeroCopy}
    (h1 : δ ≤ ‖xiResolventPoint X q₁‖) (h2 : δ ≤ ‖xiResolventPoint X q₂‖)
    (hne : ‖xiResolventPoint X q₁‖ ≠ ‖xiResolventPoint X q₂‖)
    (hmass : 8 * B ^ (4 : ℕ) * (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
        ‖xiResolventPoint X (q : XiZeroCopy)‖) *
        (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖) ≤
      2 * ((‖xiResolventPoint X q₁‖ * ‖xiResolventPoint X q₂‖) ^ (2 * m + 1) *
        (Polynomial.eval ‖xiResolventPoint X q₁‖ p ^ (2 : ℕ) *
          Polynomial.eval ‖xiResolventPoint X q₂‖ p ^ (2 : ℕ)) *
        (‖xiResolventPoint X q₁‖ - ‖xiResolventPoint X q₂‖) ^ (2 : ℕ))) :
    0 ≤ (xiPolyMoment (Polynomial.X ^ m * p) 0 X *
      xiPolyMoment (Polynomial.X ^ m * p) 2 X -
      xiPolyMoment (Polynomial.X ^ m * p) 1 X ^ (2 : ℕ)).re := by
  have hδpos : (0 : ℝ) < δ :=
    lt_of_lt_of_le (by positivity) hδfloor
  exact polyTuranMinor_supply_of_partial_line hX hδpos (hline_of_floor hX hδfloor)
    p m hB h1 h2 hne hmass

end

end RHTower
