import GaloisForLFunctions.RHTower.XiResolventTraceMassControl

/-!
# Quadratic decay of the imaginary mass in the shift

The `ℓ²` imaginary mass that carries the whole Hankel obstruction decays quadratically in the
shift: termwise the height gap and the strip give

`(Im u_q)² ≤ 2 / (‖α_q‖² (X+1)²)`,

so `M(X) ≤ 2 H / (X+1)²` with `H = Σ 1/‖α_q‖²` the genus-one Hadamard sum.  Combined with the
order-uniform mass control this yields an explicit decaying floor for every polynomial
resolvent trace:

`Re (xiResolventTrace X p) ≥ −4 L_p² H / (X+1)²`.

Every instance of the RH-equivalent Hankel positivity therefore holds up to an explicitly
quantified error that vanishes quadratically toward the far-right chamber — the trace-level
quantitative complement of the shifted-Hankel far-right positivity. -/

open Complex

namespace RHTower

noncomputable section

/-- **Termwise quadratic decay** of the squared imaginary part of a resolvent coordinate. -/
theorem im_sq_xiResolventPoint_le {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    (xiResolventPoint X q).im ^ (2 : ℕ) ≤
      2 / (‖xiSpectralPoint q‖ ^ (2 : ℕ) * (X + 1) ^ (2 : ℕ)) := by
  set γ := (xiSpectralPoint q).re with hγdef
  set b := (xiSpectralPoint q).im with hbdef
  have hγ2 : 2 < γ ^ (2 : ℕ) := by
    have h := xiZeroCopy_two_lt_im_sq q
    rwa [← xiSpectralPoint_re_eq] at h
  have hb2 : b ^ (2 : ℕ) < 1 / 4 := by
    have h := abs_xiSpectralPoint_im_lt_half q
    rw [← hbdef] at h
    nlinarith [abs_nonneg b, sq_abs b]
  have hwim : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im = 2 * γ * b := by
    simp [sq, Complex.add_im, Complex.mul_im]
    ring
  have hwre : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re = γ ^ (2 : ℕ) - b ^ (2 : ℕ) + X := by
    simp [sq, Complex.add_re, Complex.mul_re]
    rw [← hγdef, ← hbdef]
  have hne := xiSpectralSq_add_ofReal_ne_zero hX q
  have hnsq : 0 < Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) :=
    Complex.normSq_pos.mpr hne
  have him : (xiResolventPoint X q).im =
      -(2 * γ * b) / Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) := by
    rw [xiResolventPoint, Complex.inv_im, hwim]
  have hnormSq_ge : (γ ^ (2 : ℕ) - b ^ (2 : ℕ) + X) ^ (2 : ℕ) ≤
      Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) := by
    rw [Complex.normSq_apply, hwre, hwim]
    nlinarith [sq_nonneg (2 * γ * b)]
  have hbase : (7 / 8) * (γ ^ (2 : ℕ) + X) ≤ γ ^ (2 : ℕ) - b ^ (2 : ℕ) + X := by
    nlinarith
  have hXfac : (X + 1) ≤ γ ^ (2 : ℕ) + X := by linarith
  have hγfac : γ ^ (2 : ℕ) ≤ γ ^ (2 : ℕ) + X := by linarith
  have hbasepos : (0 : ℝ) < γ ^ (2 : ℕ) + X := by nlinarith
  have hquart : (7 / 8) ^ (2 : ℕ) * (γ ^ (2 : ℕ) * (X + 1)) ≤ (γ ^ (2 : ℕ) - b ^ (2 : ℕ) + X) ^ (2 : ℕ) := by
    have hnn : (0 : ℝ) ≤ (7 / 8) * (γ ^ (2 : ℕ) + X) := by positivity
    have hsq' : (7 / 8) ^ (2 : ℕ) * (γ ^ (2 : ℕ) + X) ^ (2 : ℕ) ≤ (γ ^ (2 : ℕ) - b ^ (2 : ℕ) + X) ^ (2 : ℕ) := by
      have h := pow_le_pow_left₀ hnn hbase 2
      calc (7 / 8) ^ (2 : ℕ) * (γ ^ (2 : ℕ) + X) ^ (2 : ℕ) = ((7 / 8) * (γ ^ (2 : ℕ) + X)) ^ (2 : ℕ) := by ring
        _ ≤ (γ ^ (2 : ℕ) - b ^ (2 : ℕ) + X) ^ (2 : ℕ) := h
    have hprod : γ ^ (2 : ℕ) * (X + 1) ≤ (γ ^ (2 : ℕ) + X) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (γ ^ (2 : ℕ) - 1), sq_nonneg X, hγ2, hX]
    calc (7 / 8) ^ (2 : ℕ) * (γ ^ (2 : ℕ) * (X + 1)) ≤ (7 / 8) ^ (2 : ℕ) * (γ ^ (2 : ℕ) + X) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ (γ ^ (2 : ℕ) - b ^ (2 : ℕ) + X) ^ (2 : ℕ) := hsq'
  have hmass : (xiResolventPoint X q).im ^ (2 : ℕ) =
      (2 * γ * b) ^ (2 : ℕ) / Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) ^ (2 : ℕ) := by
    rw [him]
    rw [div_pow, neg_pow]
    ring_nf
  have hnum : (2 * γ * b) ^ (2 : ℕ) ≤ γ ^ (2 : ℕ) := by nlinarith [sq_nonneg (γ * b)]
  have hden : (7 / 8) ^ (4 : ℕ) * (γ ^ (2 : ℕ) * (X + 1)) ^ (2 : ℕ) ≤
      Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) ^ (2 : ℕ) := by
    have h1 : ((7 / 8) ^ (2 : ℕ) * (γ ^ (2 : ℕ) * (X + 1))) ^ (2 : ℕ) ≤
        ((γ ^ (2 : ℕ) - b ^ (2 : ℕ) + X) ^ (2 : ℕ)) ^ (2 : ℕ) := by
      have hnn : (0 : ℝ) ≤ (7 / 8) ^ (2 : ℕ) * (γ ^ (2 : ℕ) * (X + 1)) := by positivity
      exact pow_le_pow_left₀ hnn hquart 2
    have h2 : ((γ ^ (2 : ℕ) - b ^ (2 : ℕ) + X) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (sq_nonneg _) hnormSq_ge 2
    calc (7 / 8) ^ (4 : ℕ) * (γ ^ (2 : ℕ) * (X + 1)) ^ (2 : ℕ) =
        ((7 / 8) ^ (2 : ℕ) * (γ ^ (2 : ℕ) * (X + 1))) ^ (2 : ℕ) := by ring
      _ ≤ ((γ ^ (2 : ℕ) - b ^ (2 : ℕ) + X) ^ (2 : ℕ)) ^ (2 : ℕ) := h1
      _ ≤ Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) ^ (2 : ℕ) := h2
  have hnormpt : ‖xiSpectralPoint q‖ ^ (2 : ℕ) = γ ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hγdef, hbdef]
    ring
  have hnormle : ‖xiSpectralPoint q‖ ^ (2 : ℕ) ≤ (9 / 8) * γ ^ (2 : ℕ) := by
    rw [hnormpt]
    nlinarith
  rw [hmass]
  have hdenpos : (0 : ℝ) < Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) ^ (2 : ℕ) := by
    positivity
  have hXpos : (0 : ℝ) < (X + 1) ^ (2 : ℕ) := by positivity
  have hγpos : (0 : ℝ) < γ ^ (2 : ℕ) := by linarith
  have hnormpos : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    have := xiSpectralPoint_ne_zero q
    positivity
  rw [div_le_div_iff₀ hdenpos (mul_pos hnormpos hXpos)]
  have hgoal : (2 * γ * b) ^ (2 : ℕ) * (‖xiSpectralPoint q‖ ^ (2 : ℕ) * (X + 1) ^ (2 : ℕ)) ≤
      γ ^ (2 : ℕ) * ((9 / 8) * γ ^ (2 : ℕ) * (X + 1) ^ (2 : ℕ)) := by
    have hstep : (2 * γ * b) ^ (2 : ℕ) * (‖xiSpectralPoint q‖ ^ (2 : ℕ) * (X + 1) ^ (2 : ℕ)) ≤
        γ ^ (2 : ℕ) * (‖xiSpectralPoint q‖ ^ (2 : ℕ) * (X + 1) ^ (2 : ℕ)) := by
      apply mul_le_mul_of_nonneg_right hnum (by positivity)
    have hstep2 : γ ^ (2 : ℕ) * (‖xiSpectralPoint q‖ ^ (2 : ℕ) * (X + 1) ^ (2 : ℕ)) ≤
        γ ^ (2 : ℕ) * ((9 / 8) * γ ^ (2 : ℕ) * (X + 1) ^ (2 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hγpos)
      apply mul_le_mul_of_nonneg_right hnormle (le_of_lt hXpos)
    linarith
  have hfinal : γ ^ (2 : ℕ) * ((9 / 8) * γ ^ (2 : ℕ) * (X + 1) ^ (2 : ℕ)) ≤
      2 * Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) ^ (2 : ℕ) := by
    have hid : γ ^ (2 : ℕ) * ((9 / 8) * γ ^ (2 : ℕ) * (X + 1) ^ (2 : ℕ)) =
        (9 / 8) * (γ ^ (2 : ℕ) * (X + 1)) ^ (2 : ℕ) := by ring
    rw [hid]
    nlinarith [hden, sq_nonneg (γ ^ (2 : ℕ) * (X + 1))]
  linarith

/-- **Quadratic decay of the imaginary mass**: the whole Hankel obstruction is bounded by the
Hadamard sum divided by the squared shift. -/
theorem xiResolventImSqMass_le {X : ℝ} (hX : 0 ≤ X) :
    xiResolventImSqMass X ≤
      2 / (X + 1) ^ (2 : ℕ) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  rw [xiResolventImSqMass, ← tsum_mul_left]
  apply (summable_im_sq_xiResolventPoint hX).tsum_le_tsum
    (fun q => ?_) (xiSpectralPoint_inv_sq_summable.mul_left _)
  have h := im_sq_xiResolventPoint_le hX q
  have hnormpos : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    have := xiSpectralPoint_ne_zero q
    positivity
  have hXpos : (0 : ℝ) < (X + 1) ^ (2 : ℕ) := by positivity
  calc (xiResolventPoint X q).im ^ (2 : ℕ) ≤
      2 / (‖xiSpectralPoint q‖ ^ (2 : ℕ) * (X + 1) ^ (2 : ℕ)) := h
    _ = 2 / (X + 1) ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
        field_simp

/-- **The decaying floor of every polynomial resolvent trace**: the possible negativity of
every instance of the RH-equivalent Hankel positivity vanishes quadratically in the shift,
with explicit constant. -/
theorem xiResolventTrace_re_ge_neg_div {X : ℝ} (hX : 0 ≤ X) (p : Polynomial ℝ) :
    -(4 * evalRealPolynomialLipBound p ^ (2 : ℕ) / (X + 1) ^ (2 : ℕ) *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) ≤
      (xiResolventTrace X p).re := by
  have hmass := xiResolventImSqMass_le hX
  have hcontrol := xiResolventTrace_re_ge_neg_mass hX p
  have hL := evalRealPolynomialLipBound_nonneg p
  have hXpos : (0 : ℝ) < (X + 1) ^ (2 : ℕ) := by positivity
  have hstep : 2 * evalRealPolynomialLipBound p ^ (2 : ℕ) * xiResolventImSqMass X ≤
      4 * evalRealPolynomialLipBound p ^ (2 : ℕ) / (X + 1) ^ (2 : ℕ) *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    have h1 : 2 * evalRealPolynomialLipBound p ^ (2 : ℕ) * xiResolventImSqMass X ≤
        2 * evalRealPolynomialLipBound p ^ (2 : ℕ) *
          (2 / (X + 1) ^ (2 : ℕ) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left hmass (by positivity)
    calc 2 * evalRealPolynomialLipBound p ^ (2 : ℕ) * xiResolventImSqMass X ≤
        2 * evalRealPolynomialLipBound p ^ (2 : ℕ) *
          (2 / (X + 1) ^ (2 : ℕ) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := h1
      _ = 4 * evalRealPolynomialLipBound p ^ (2 : ℕ) / (X + 1) ^ (2 : ℕ) *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by ring
  linarith

end

end RHTower
