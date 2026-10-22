import GaloisForLFunctions.RHTower.FrankensteinSourceGammaCenteredMonodromyCartier
import GaloisForLFunctions.RHTower.ThetaHalfPlaneBound

/-!
# Admission of the literal theta source under logarithmic clock shifts

The integer-labelled complex theta-cusp series is summable exactly when
`Re (exp z ^ (2 : ℕ)) > 0`, equivalently `cos (2 Im z) > 0`. The polynomial Gaussian
majorant proves convergence inside these sectors; outside them the terms fail
to tend to zero. No continuous full logarithmic turn stays in this admission
set, although the sum retains the atom's anti-periodicity between sectors.

This classifies the original series representation. It does not exclude other
analytic continuations or identify logarithmic scale with physical Hawking time.
-/

open Complex Filter Topology


namespace RHTower

private theorem gaussianPolynomial_summable {A B q : ℂ} (hq : 0 < q.re) :
    Summable (fun n : ℕ => (A*(n:ℂ)^(4 : ℕ)+B*(n:ℂ)^(2 : ℕ))*Complex.exp (-q*(n:ℂ)^(2 : ℕ))) := by
  have hsq (n : ℕ) : (n:ℝ) ≤ (n:ℝ)^(2 : ℕ) := by
    cases n with
    | zero => norm_num
    | succ n => push_cast; nlinarith [sq_nonneg (n:ℝ)]
  have he (n : ℕ) : ‖Complex.exp (-q*(n:ℂ)^(2 : ℕ))‖ = Real.exp (-q.re*(n:ℝ)^(2 : ℕ)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, Complex.mul_re, Complex.mul_im]
  refine Summable.of_norm_bounded
    (((summable_pow_mul_exp_neg 4 hq).mul_left ‖A‖).add
      ((summable_pow_mul_exp_neg 2 hq).mul_left ‖B‖)) ?_
  intro n
  rw [norm_mul, he]
  have hp : ‖A*(n:ℂ)^(4 : ℕ)+B*(n:ℂ)^(2 : ℕ)‖ ≤ ‖A‖*(n:ℝ)^(4 : ℕ)+‖B‖*(n:ℝ)^(2 : ℕ) := by
    calc
      _ ≤ ‖A*(n:ℂ)^(4 : ℕ)‖+‖B*(n:ℂ)^(2 : ℕ)‖ := norm_add_le _ _
      _ = _ := by rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_pow,
        Complex.norm_pow, Complex.norm_natCast]
  have hle : Real.exp (-q.re*(n:ℝ)^(2 : ℕ)) ≤ Real.exp (-q.re*(n:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hsq n) (neg_nonpos.mpr hq.le))
  calc
    _ ≤ (‖A‖*(n:ℝ)^(4 : ℕ)+‖B‖*(n:ℝ)^(2 : ℕ))*Real.exp (-q.re*(n:ℝ)) :=
      mul_le_mul hp hle (Real.exp_pos _).le (by positivity)
    _ = _ := by simp only [neg_mul, mul_comm q.re (n:ℝ)]; ring

private theorem gaussianPolynomial_not_summable {A B q : ℂ}
    (hA : A ≠ 0) (hq : q.re ≤ 0) :
    ¬ Summable (fun n : ℕ => (A*(n:ℂ)^(4 : ℕ)+B*(n:ℂ)^(2 : ℕ))*Complex.exp (-q*(n:ℂ)^(2 : ℕ))) := by
  intro hsum
  have ha : 0 < ‖A‖ := norm_pos_iff.mpr hA
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 ((‖B‖+1)/‖A‖))
  have hlarge : ∀ᶠ n : ℕ in atTop,
      1 ≤ ‖(A*(n:ℂ)^(4 : ℕ)+B*(n:ℂ)^(2 : ℕ))*Complex.exp (-q*(n:ℂ)^(2 : ℕ))‖ := by
    refine Filter.eventually_atTop.2 ⟨N,fun n hn => ?_⟩
    have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn1 : 1 ≤ (n:ℝ) := (le_max_left _ _).trans (hN.le.trans hNn)
    have hnb : (‖B‖+1)/‖A‖ ≤ (n:ℝ) := (le_max_right _ _).trans (hN.le.trans hNn)
    have hlin := (div_le_iff₀ ha).mp hnb
    have hn2 : (n:ℝ) ≤ (n:ℝ)^(2 : ℕ) := by nlinarith
    have hcoef : ‖B‖+1 ≤ ‖A‖*(n:ℝ)^(2 : ℕ) := by
      nlinarith [mul_le_mul_of_nonneg_left hn2 ha.le]
    have hrev : ‖A‖*(n:ℝ)^(4 : ℕ)-‖B‖*(n:ℝ)^(2 : ℕ) ≤ ‖A*(n:ℂ)^(4 : ℕ)+B*(n:ℂ)^(2 : ℕ)‖ := by
      have h := norm_sub_norm_le (A*(n:ℂ)^(4 : ℕ)) (-(B*(n:ℂ)^(2 : ℕ)))
      rw [sub_neg_eq_add, norm_neg, Complex.norm_mul, Complex.norm_mul,
        Complex.norm_pow, Complex.norm_pow, Complex.norm_natCast] at h
      exact h
    have hp : (n:ℝ)^(2 : ℕ) ≤ ‖A*(n:ℂ)^(4 : ℕ)+B*(n:ℂ)^(2 : ℕ)‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg (n:ℝ))]
    have he : 1 ≤ ‖Complex.exp (-q*(n:ℂ)^(2 : ℕ))‖ := by
      rw [Complex.norm_exp, Real.one_le_exp_iff]
      have hreal : (-q*(n:ℂ)^(2 : ℕ)).re = -q.re*(n:ℝ)^(2 : ℕ) := by
        simp [pow_two, Complex.mul_re, Complex.mul_im]
      rw [hreal]
      exact mul_nonneg (neg_nonneg.mpr hq) (sq_nonneg _)
    rw [_root_.norm_mul]
    calc
      1 ≤ (n:ℝ)^(2 : ℕ)*1 := by nlinarith
      _ ≤ _ := mul_le_mul hp he zero_le_one (norm_nonneg _)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ‖(A*(n:ℂ)^(4 : ℕ)+B*(n:ℂ)^(2 : ℕ))*Complex.exp (-q*(n:ℂ)^(2 : ℕ))‖ < 1 := by
    have h : Tendsto (fun n : ℕ =>
        ‖(A*(n:ℂ)^(4 : ℕ)+B*(n:ℂ)^(2 : ℕ))*Complex.exp (-q*(n:ℂ)^(2 : ℕ))‖) atTop (𝓝 (0:ℝ)) := by
      simpa only [norm_zero] using hsum.tendsto_atTop_zero.norm
    exact h.eventually_lt_const zero_lt_one
  obtain ⟨n,hl,hs⟩ := (hlarge.and hsmall).exists
  exact (not_lt_of_ge hl) hs

/-- Exact summability domain of the original integer-labelled complex source. -/
theorem thetaCuspComplexSourceTerm_summable_iff (z : ℂ) :
    Summable (thetaCuspComplexSourceTerm z) ↔ 0 < (Complex.exp z ^ (2 : ℕ)).re := by
  let A := Complex.exp (z/2)*4*(Real.pi:ℂ)^(2 : ℕ)*Complex.exp z ^ (4 : ℕ)
  let B := -(Complex.exp (z/2)*6*(Real.pi:ℂ)*Complex.exp z ^ (2 : ℕ))
  let q := (Real.pi:ℂ)*Complex.exp z ^ (2 : ℕ)
  have heq (n : ℕ) : thetaCuspComplexSourceTerm z n =
      (A*(n:ℂ)^(4 : ℕ)+B*(n:ℂ)^(2 : ℕ))*Complex.exp (-q*(n:ℂ)^(2 : ℕ)) := by
    change Complex.exp (z/2)*(2*(Real.pi:ℂ)*
      (2*(Real.pi:ℂ)*((n:ℂ)*Complex.exp z)^(4 : ℕ)-3*((n:ℂ)*Complex.exp z)^(2 : ℕ))*
        Complex.exp (-(Real.pi:ℂ)*((n:ℂ)*Complex.exp z)^(2 : ℕ))) = _
    have hexp : -(Real.pi:ℂ)*((n:ℂ)*Complex.exp z)^(2 : ℕ) = -q*(n:ℂ)^(2 : ℕ) := by
      dsimp only [q]; ring
    rw [hexp]
    dsimp only [A,B]
    ring
  have hA : A ≠ 0 := by
    dsimp only [A]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (by norm_num))
      (pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)))
      (pow_ne_zero _ (Complex.exp_ne_zero _))
  have hq : q.re = Real.pi*(Complex.exp z ^ (2 : ℕ)).re := by simp [q, Complex.mul_re]
  constructor
  · intro h
    by_contra hpos
    have hnon : q.re ≤ 0 := by rw [hq]; exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (le_of_not_gt hpos)
    exact gaussianPolynomial_not_summable hA hnon (h.congr heq)
  · intro hpos
    have hqp : 0 < q.re := by rw [hq]; exact mul_pos Real.pi_pos hpos
    exact (gaussianPolynomial_summable (A:=A) (B:=B) hqp).congr (fun n => (heq n).symm)

/-- The admission set consists of disjoint horizontal logarithmic sectors. -/
theorem thetaCuspComplexSourceTerm_summable_iff_cos (z : ℂ) :
    Summable (thetaCuspComplexSourceTerm z) ↔ 0 < Real.cos (2*z.im) := by
  rw [thetaCuspComplexSourceTerm_summable_iff]
  have he : Complex.exp z ^ (2 : ℕ) = Complex.exp (2*z) := by
    rw [two_mul, Complex.exp_add, pow_two]
  rw [he, Complex.exp_re]
  have hparts : (2*z).re = 2*z.re ∧ (2*z).im = 2*z.im := by
    constructor <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hparts.1,hparts.2]
  exact mul_pos_iff_of_pos_left (Real.exp_pos _)

/-- Every continuous logarithmic turn crosses a nonsummable source boundary. -/
theorem no_summable_theta_source_logarithmic_turn (x : ℝ) :
    ¬ ∃ gamma : ℝ → ℂ,
      ContinuousOn gamma (Set.Icc 0 1) ∧ gamma 0 = (x:ℂ) ∧
      gamma 1 = (x:ℂ)+2*(Real.pi:ℂ)*Complex.I ∧
      ∀ t ∈ Set.Icc 0 1, Summable (thetaCuspComplexSourceTerm (gamma t)) := by
  rintro ⟨gamma,hc,h0,h1,hs⟩
  have him : ContinuousOn (fun t => (gamma t).im) (Set.Icc 0 1) :=
    Complex.continuous_im.comp_continuousOn hc
  have htarget : Real.pi/4 ∈ Set.Icc ((gamma 0).im) ((gamma 1).im) := by
    rw [h0,h1]
    have hend : ((x:ℂ)+2*(Real.pi:ℂ)*Complex.I).im = 2*Real.pi := by
      simp [Complex.mul_im, Complex.mul_re]
    rw [hend,Complex.ofReal_im]
    constructor <;> linarith [Real.pi_pos]
  obtain ⟨t,ht,hvalue⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) him htarget
  change (gamma t).im = Real.pi/4 at hvalue
  have hpos := (thetaCuspComplexSourceTerm_summable_iff_cos (gamma t)).mp (hs t ht)
  rw [hvalue, show 2*(Real.pi/4)=Real.pi/2 by ring, Real.cos_pi_div_two] at hpos
  exact lt_irrefl 0 hpos

/-- The summed source retains anti-periodicity; on the summability domain this
relates convergent sums in different components. -/
theorem thetaCuspComplexSourceSum_add_two_pi_I (z : ℂ) :
    (∑' n : ℕ, thetaCuspComplexSourceTerm (z+2*(Real.pi:ℂ)*Complex.I) n) =
      -(∑' n : ℕ, thetaCuspComplexSourceTerm z n) := by
  simp_rw [thetaCuspComplexSourceTerm_add_two_pi_I]
  exact tsum_neg

end RHTower
