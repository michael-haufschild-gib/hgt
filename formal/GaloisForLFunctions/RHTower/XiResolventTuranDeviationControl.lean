import GaloisForLFunctions.RHTower.XiResolventHankelEquivalence

/-!
# Quantitative control of the Turán defect by imaginary mass

The resolvent Turán minor is the first Hankel obstruction that is not visible copy-by-copy.
This module bounds its possible negativity explicitly: in the variance expansion every ordered
pair satisfies the pointwise inequality

`Re (u·v·(u−v)²) ≥ Re u·Re v·(Re u − Re v)² − err(u,v)`,

where the error is an explicit sum of product-form terms in `|Im u|, (Im u)², ‖u‖` — and the
bulk term is nonnegative because every resolvent coordinate has positive real part.  Summing,
the Turán defect is bounded below by an explicit combination of three mass functionals

`S₁ = Σ |Im u_q|`, `M = Σ (Im u_q)²`, `S₀ = Σ ‖u_q‖`,

all unconditionally finite:

`Re (2·(M₀M₂ − M₁²)) ≥ −(4 S₁² + 4 M S₀ + 8 S₁ S₀)`.

The imaginary masses vanish exactly on RH (`riemannHypothesis_iff_xiResolventImSqMass_eq_zero`),
so the theorem is a quantitative version of the Hamburger direction at order two: the Hankel
obstruction is controlled by the same deviation-type mass that the Krein and Weil charts
carry. -/

open Complex

namespace RHTower

noncomputable section

/-! ## The mass functionals -/

/-- The `ℓ¹` mass of the resolvent coordinates. -/
def xiResolventNormMass (X : ℝ) : ℝ := ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖

/-- The `ℓ¹` mass of the imaginary parts of the resolvent coordinates. -/
def xiResolventImMass (X : ℝ) : ℝ := ∑' q : XiZeroCopy, |(xiResolventPoint X q).im|

/-- The `ℓ²` mass of the imaginary parts of the resolvent coordinates. -/
def xiResolventImSqMass (X : ℝ) : ℝ := ∑' q : XiZeroCopy, (xiResolventPoint X q).im ^ (2 : ℕ)

theorem summable_abs_im_xiResolventPoint {X : ℝ} (hX : 0 ≤ X) :
    Summable (fun q : XiZeroCopy => |(xiResolventPoint X q).im|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun _ => Complex.abs_im_le_norm _) (summable_norm_xiResolventPoint hX)

theorem summable_im_sq_xiResolventPoint {X : ℝ} (hX : 0 ≤ X) :
    Summable (fun q : XiZeroCopy => (xiResolventPoint X q).im ^ (2 : ℕ)) := by
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
    (summable_norm_xiResolventPoint hX)
  have h1 : |(xiResolventPoint X q).im| ≤ ‖xiResolventPoint X q‖ :=
    Complex.abs_im_le_norm _
  have h2 : ‖xiResolventPoint X q‖ ≤ 1 := norm_xiResolventPoint_le_one hX q
  calc (xiResolventPoint X q).im ^ (2 : ℕ) = |(xiResolventPoint X q).im| ^ (2 : ℕ) := (sq_abs _).symm
    _ ≤ ‖xiResolventPoint X q‖ ^ (2 : ℕ) :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ ≤ ‖xiResolventPoint X q‖ := by nlinarith [norm_nonneg (xiResolventPoint X q)]

/-! ## The pointwise pair inequality -/

/-- **The pointwise pair inequality.**  For unit-bounded complex numbers the real part of the
variance pair term is bounded below by its real-part bulk minus an explicit product-form
error. -/
theorem re_pair_ge_bulk_sub_err {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    u.re * v.re * (u.re - v.re) ^ (2 : ℕ) -
        (4 * (|u.im| * |v.im|) + (2 * (u.im ^ (2 : ℕ) * ‖v‖) + 2 * (v.im ^ (2 : ℕ) * ‖u‖)) +
          (4 * (|u.im| * ‖v‖) + 4 * (‖u‖ * |v.im|))) ≤
      (u * v * (u - v) ^ (2 : ℕ)).re := by
  have hkey : (u * v * (u - v) ^ (2 : ℕ)).re =
      u.re * v.re * (u.re - v.re) ^ (2 : ℕ) -
        (u.im * v.im * (u.re - v.re) ^ (2 : ℕ) +
          (u.re * v.re - u.im * v.im) * (u.im - v.im) ^ (2 : ℕ) +
          2 * (u.re * v.im + u.im * v.re) * (u.re - v.re) * (u.im - v.im)) := by
    simp [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    ring
  have hare : |u.re| ≤ 1 := le_trans (Complex.abs_re_le_norm u) hu
  have hcre : |v.re| ≤ 1 := le_trans (Complex.abs_re_le_norm v) hv
  have haim : |u.im| ≤ ‖u‖ := Complex.abs_im_le_norm u
  have hcim : |v.im| ≤ ‖v‖ := Complex.abs_im_le_norm v
  have hsub : (u.re - v.re) ^ (2 : ℕ) ≤ 4 := by
    nlinarith [abs_nonneg u.re, abs_nonneg v.re, le_abs_self u.re, neg_abs_le u.re,
      le_abs_self v.re, neg_abs_le v.re]
  have hT1 : |u.im * v.im * (u.re - v.re) ^ (2 : ℕ)| ≤ 4 * (|u.im| * |v.im|) := by
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg (sq_nonneg (u.re - v.re))]
    nlinarith [abs_nonneg u.im, abs_nonneg v.im, mul_nonneg (abs_nonneg u.im) (abs_nonneg v.im)]
  have hprod_re : |u.re * v.re - u.im * v.im| ≤ ‖u‖ * ‖v‖ := by
    have h := Complex.abs_re_le_norm (u * v)
    rw [Complex.mul_re] at h
    rw [norm_mul] at h
    exact h
  have hprod_im : |u.re * v.im + u.im * v.re| ≤ ‖u‖ * ‖v‖ := by
    have h := Complex.abs_im_le_norm (u * v)
    rw [Complex.mul_im] at h
    rw [norm_mul] at h
    exact h
  have hT2 : |(u.re * v.re - u.im * v.im) * (u.im - v.im) ^ (2 : ℕ)| ≤
      2 * (u.im ^ (2 : ℕ) * ‖v‖) + 2 * (v.im ^ (2 : ℕ) * ‖u‖) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (u.im - v.im))]
    have hd2 : (u.im - v.im) ^ (2 : ℕ) ≤ 2 * u.im ^ (2 : ℕ) + 2 * v.im ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (u.im + v.im)]
    have hnu : 0 ≤ ‖u‖ := norm_nonneg u
    have hnv : 0 ≤ ‖v‖ := norm_nonneg v
    have habs2 : |u.re * v.re - u.im * v.im| * (u.im - v.im) ^ (2 : ℕ) ≤
        (‖u‖ * ‖v‖) * (2 * u.im ^ (2 : ℕ) + 2 * v.im ^ (2 : ℕ)) := by
      apply mul_le_mul hprod_re hd2 (sq_nonneg _) (by positivity)
    calc |u.re * v.re - u.im * v.im| * (u.im - v.im) ^ (2 : ℕ) ≤
        (‖u‖ * ‖v‖) * (2 * u.im ^ (2 : ℕ) + 2 * v.im ^ (2 : ℕ)) := habs2
      _ ≤ 2 * (u.im ^ (2 : ℕ) * ‖v‖) + 2 * (v.im ^ (2 : ℕ) * ‖u‖) := by
          nlinarith [sq_nonneg u.im, sq_nonneg v.im, hnu, hnv, hu, hv,
            mul_nonneg hnu hnv, mul_nonneg (sq_nonneg u.im) hnv,
            mul_nonneg (sq_nonneg v.im) hnu]
  have hT3 : |2 * (u.re * v.im + u.im * v.re) * (u.re - v.re) * (u.im - v.im)| ≤
      4 * (|u.im| * ‖v‖) + 4 * (‖u‖ * |v.im|) := by
    rw [abs_mul, abs_mul, abs_mul]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    have hac : |u.re - v.re| ≤ 2 := by
      have := abs_sub_abs_le_abs_sub u.re v.re
      have htri : |u.re - v.re| ≤ |u.re| + |v.re| := abs_sub _ _
      linarith
    have hbd : |u.im - v.im| ≤ |u.im| + |v.im| := abs_sub _ _
    have hnu : 0 ≤ ‖u‖ := norm_nonneg u
    have hnv : 0 ≤ ‖v‖ := norm_nonneg v
    have hstep : 2 * |u.re * v.im + u.im * v.re| * |u.re - v.re| * |u.im - v.im| ≤
        2 * (‖u‖ * ‖v‖) * 2 * (|u.im| + |v.im|) := by
      have h1 : 2 * |u.re * v.im + u.im * v.re| ≤ 2 * (‖u‖ * ‖v‖) := by linarith
      have hnn1 : 0 ≤ 2 * |u.re * v.im + u.im * v.re| := by positivity
      have hnn2 : 0 ≤ |u.re - v.re| := abs_nonneg _
      have hnn3 : 0 ≤ |u.im - v.im| := abs_nonneg _
      calc 2 * |u.re * v.im + u.im * v.re| * |u.re - v.re| * |u.im - v.im| ≤
          2 * (‖u‖ * ‖v‖) * |u.re - v.re| * |u.im - v.im| := by
            apply mul_le_mul_of_nonneg_right _ hnn3
            exact mul_le_mul_of_nonneg_right h1 hnn2
        _ ≤ 2 * (‖u‖ * ‖v‖) * 2 * |u.im - v.im| := by
            apply mul_le_mul_of_nonneg_right _ hnn3
            apply mul_le_mul_of_nonneg_left hac (by positivity)
        _ ≤ 2 * (‖u‖ * ‖v‖) * 2 * (|u.im| + |v.im|) := by
            apply mul_le_mul_of_nonneg_left hbd (by positivity)
    calc 2 * |u.re * v.im + u.im * v.re| * |u.re - v.re| * |u.im - v.im| ≤
        2 * (‖u‖ * ‖v‖) * 2 * (|u.im| + |v.im|) := hstep
      _ = 4 * (‖u‖ * ‖v‖ * |u.im|) + 4 * (‖u‖ * ‖v‖ * |v.im|) := by ring
      _ ≤ 4 * (|u.im| * ‖v‖) + 4 * (‖u‖ * |v.im|) := by
          have hb1 : ‖u‖ * ‖v‖ * |u.im| ≤ |u.im| * ‖v‖ := by
            have hfac : 0 ≤ (1 - ‖u‖) * (‖v‖ * |u.im|) :=
              mul_nonneg (by linarith) (mul_nonneg hnv (abs_nonneg _))
            nlinarith [hfac]
          have hb2 : ‖u‖ * ‖v‖ * |v.im| ≤ ‖u‖ * |v.im| := by
            have hfac : 0 ≤ (1 - ‖v‖) * (‖u‖ * |v.im|) :=
              mul_nonneg (by linarith) (mul_nonneg hnu (abs_nonneg _))
            nlinarith [hfac]
          linarith
  rw [hkey]
  have habs1 := abs_le.mp hT1
  have habs2 := abs_le.mp hT2
  have habs3 := abs_le.mp hT3
  linarith [habs1.1, habs1.2, habs2.1, habs2.2, habs3.1, habs3.2]

/-! ## The assembled control theorem -/

/-- The product-form error of one ordered pair. -/
def xiResolventPairErr (X : ℝ) (z : XiZeroCopy × XiZeroCopy) : ℝ :=
  4 * (|(xiResolventPoint X z.1).im| * |(xiResolventPoint X z.2).im|) +
    (2 * ((xiResolventPoint X z.1).im ^ (2 : ℕ) * ‖xiResolventPoint X z.2‖) +
      2 * ((xiResolventPoint X z.2).im ^ (2 : ℕ) * ‖xiResolventPoint X z.1‖)) +
    (4 * (|(xiResolventPoint X z.1).im| * ‖xiResolventPoint X z.2‖) +
      4 * (‖xiResolventPoint X z.1‖ * |(xiResolventPoint X z.2).im|))

theorem summable_xiResolventPairErr {X : ℝ} (hX : 0 ≤ X) :
    Summable (xiResolventPairErr X) := by
  have h₁ := summable_abs_im_xiResolventPoint hX
  have h₂ := summable_im_sq_xiResolventPoint hX
  have h₀ := summable_norm_xiResolventPoint hX
  have hprod : ∀ (f g : XiZeroCopy → ℝ), Summable f → Summable g →
      (∀ q, 0 ≤ f q) → (∀ q, 0 ≤ g q) →
      Summable (fun z : XiZeroCopy × XiZeroCopy => f z.1 * g z.2) := by
    intro f g hf hg hfpos hgpos
    apply summable_mul_of_summable_norm (f := f) (g := g)
    · refine hf.congr fun q => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hfpos q)]
    · refine hg.congr fun q => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hgpos q)]
  refine (((hprod _ _ h₁ h₁ (fun q => abs_nonneg _) (fun q => abs_nonneg _)).mul_left 4).add
    (((hprod _ _ h₂ h₀ (fun q => sq_nonneg _) (fun q => norm_nonneg _)).mul_left 2).add
      ((hprod _ _ h₀ h₂ (fun q => norm_nonneg _) (fun q => sq_nonneg _)).mul_left 2))).add
    (((hprod _ _ h₁ h₀ (fun q => abs_nonneg _) (fun q => norm_nonneg _)).mul_left 4).add
      ((hprod _ _ h₀ h₁ (fun q => norm_nonneg _) (fun q => abs_nonneg _)).mul_left 4)) |>.congr ?_
  intro z
  rw [xiResolventPairErr]
  ring

/-- The error masses evaluate in closed form. -/
theorem tsum_xiResolventPairErr {X : ℝ} (hX : 0 ≤ X) :
    ∑' z : XiZeroCopy × XiZeroCopy, xiResolventPairErr X z =
      4 * xiResolventImMass X ^ (2 : ℕ) +
        4 * (xiResolventImSqMass X * xiResolventNormMass X) +
        8 * (xiResolventImMass X * xiResolventNormMass X) := by
  have h₁ := summable_abs_im_xiResolventPoint hX
  have h₂ := summable_im_sq_xiResolventPoint hX
  have h₀ := summable_norm_xiResolventPoint hX
  have hnorm : ∀ (f : XiZeroCopy → ℝ), (∀ q, 0 ≤ f q) → Summable f →
      Summable (fun q => ‖f q‖) := by
    intro f hfpos hf
    refine hf.congr fun q => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hfpos q)]
  have h₁n := hnorm _ (fun q => abs_nonneg _) h₁
  have h₂n := hnorm _ (fun q => sq_nonneg _) h₂
  have h₀n := hnorm _ (fun q => norm_nonneg _) h₀
  have hA := tsum_mul_tsum_of_summable_norm h₁n h₁n
  have hB := tsum_mul_tsum_of_summable_norm h₂n h₀n
  have hC := tsum_mul_tsum_of_summable_norm h₀n h₂n
  have hD := tsum_mul_tsum_of_summable_norm h₁n h₀n
  have hE := tsum_mul_tsum_of_summable_norm h₀n h₁n
  have hsA := summable_mul_of_summable_norm h₁n h₁n
  have hsB := summable_mul_of_summable_norm h₂n h₀n
  have hsC := summable_mul_of_summable_norm h₀n h₂n
  have hsD := summable_mul_of_summable_norm h₁n h₀n
  have hsE := summable_mul_of_summable_norm h₀n h₁n
  have hsplit : ∀ z : XiZeroCopy × XiZeroCopy, xiResolventPairErr X z =
      (4 * (|(xiResolventPoint X z.1).im| * |(xiResolventPoint X z.2).im|) +
        (2 * ((xiResolventPoint X z.1).im ^ (2 : ℕ) * ‖xiResolventPoint X z.2‖) +
          2 * (‖xiResolventPoint X z.1‖ * (xiResolventPoint X z.2).im ^ (2 : ℕ)))) +
      (4 * (|(xiResolventPoint X z.1).im| * ‖xiResolventPoint X z.2‖) +
        4 * (‖xiResolventPoint X z.1‖ * |(xiResolventPoint X z.2).im|)) := by
    intro z
    rw [xiResolventPairErr]
    ring
  rw [tsum_congr hsplit,
    Summable.tsum_add ((hsA.mul_left 4).add ((hsB.mul_left 2).add (hsC.mul_left 2)))
      ((hsD.mul_left 4).add (hsE.mul_left 4)),
    Summable.tsum_add (hsA.mul_left 4) ((hsB.mul_left 2).add (hsC.mul_left 2)),
    Summable.tsum_add (hsB.mul_left 2) (hsC.mul_left 2),
    Summable.tsum_add (hsD.mul_left 4) (hsE.mul_left 4),
    tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left,
    ← hA, ← hB, ← hC, ← hD, ← hE]
  rw [xiResolventImMass, xiResolventImSqMass, xiResolventNormMass]
  ring

/-- **Quantitative Turán control.**  The Turán defect of the resolvent moments is bounded
below by an explicit combination of the imaginary masses: the entire possible failure of the
order-two Hankel inequality is carried by the deviation of the divisor from the real axis. -/
theorem two_mul_xiResolventTuranMinor_re_ge {X : ℝ} (hX : 0 ≤ X) :
    -(4 * xiResolventImMass X ^ (2 : ℕ) +
        4 * (xiResolventImSqMass X * xiResolventNormMass X) +
        8 * (xiResolventImMass X * xiResolventNormMass X)) ≤
      (2 * (xiResolventMoment 0 X * xiResolventMoment 2 X -
        xiResolventMoment 1 X ^ (2 : ℕ))).re := by
  rw [two_mul_xiResolventTuranMinor_eq_tsum_pair hX]
  have h₀ := summable_norm_xiResolventPoint hX
  have hpair_bound : ∀ z : XiZeroCopy × XiZeroCopy,
      ‖xiResolventPairTerm X z‖ ≤ 4 * (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖) := by
    intro z
    rw [xiResolventPairTerm, norm_mul, norm_mul, norm_pow]
    have h1 : ‖xiResolventPoint X z.1‖ ≤ 1 := norm_xiResolventPoint_le_one hX z.1
    have h2 : ‖xiResolventPoint X z.2‖ ≤ 1 := norm_xiResolventPoint_le_one hX z.2
    have htri : ‖xiResolventPoint X z.1 - xiResolventPoint X z.2‖ ≤ 2 := by
      calc ‖xiResolventPoint X z.1 - xiResolventPoint X z.2‖ ≤
          ‖xiResolventPoint X z.1‖ + ‖xiResolventPoint X z.2‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    have hsq : ‖xiResolventPoint X z.1 - xiResolventPoint X z.2‖ ^ (2 : ℕ) ≤ 4 := by
      nlinarith [norm_nonneg (xiResolventPoint X z.1 - xiResolventPoint X z.2)]
    nlinarith [norm_nonneg (xiResolventPoint X z.1), norm_nonneg (xiResolventPoint X z.2),
      mul_nonneg (norm_nonneg (xiResolventPoint X z.1)) (norm_nonneg (xiResolventPoint X z.2))]
  have hnormprod : Summable (fun z : XiZeroCopy × XiZeroCopy =>
      4 * (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖)) := by
    have h₀n : Summable (fun q : XiZeroCopy => ‖‖xiResolventPoint X q‖‖) := by
      refine h₀.congr fun q => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (summable_mul_of_summable_norm h₀n h₀n).mul_left 4
  have hpair : Summable (xiResolventPairTerm X) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun z => norm_nonneg _) hpair_bound hnormprod
  have hpair_re : Summable (fun z : XiZeroCopy × XiZeroCopy =>
      (xiResolventPairTerm X z).re) := by
    simpa only [Function.comp_apply] using!
      hpair.map Complex.reCLM Complex.reCLM.continuous
  have hbulk : Summable (fun z : XiZeroCopy × XiZeroCopy =>
      (xiResolventPoint X z.1).re * (xiResolventPoint X z.2).re *
        ((xiResolventPoint X z.1).re - (xiResolventPoint X z.2).re) ^ (2 : ℕ)) := by
    refine Summable.of_nonneg_of_le (fun z => ?_) (fun z => ?_) hnormprod
    · have ha := xiResolventPoint_re_pos hX z.1
      have hb := xiResolventPoint_re_pos hX z.2
      positivity
    · have ha1 : |(xiResolventPoint X z.1).re| ≤ ‖xiResolventPoint X z.1‖ :=
        Complex.abs_re_le_norm _
      have ha2 : |(xiResolventPoint X z.2).re| ≤ ‖xiResolventPoint X z.2‖ :=
        Complex.abs_re_le_norm _
      have h1 : ‖xiResolventPoint X z.1‖ ≤ 1 := norm_xiResolventPoint_le_one hX z.1
      have h2 : ‖xiResolventPoint X z.2‖ ≤ 1 := norm_xiResolventPoint_le_one hX z.2
      have hd : ((xiResolventPoint X z.1).re - (xiResolventPoint X z.2).re) ^ (2 : ℕ) ≤ 4 := by
        nlinarith [abs_nonneg (xiResolventPoint X z.1).re,
          abs_nonneg (xiResolventPoint X z.2).re,
          le_abs_self (xiResolventPoint X z.1).re, neg_abs_le (xiResolventPoint X z.1).re,
          le_abs_self (xiResolventPoint X z.2).re, neg_abs_le (xiResolventPoint X z.2).re]
      have hstep1 : (xiResolventPoint X z.1).re * (xiResolventPoint X z.2).re ≤
          ‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖ := by
        apply mul_le_mul (le_trans (le_abs_self _) ha1) (le_trans (le_abs_self _) ha2)
          (xiResolventPoint_re_pos hX z.2).le (norm_nonneg _)
      have hpp : 0 ≤ (xiResolventPoint X z.1).re * (xiResolventPoint X z.2).re := by
        have hra := xiResolventPoint_re_pos hX z.1
        have hrb := xiResolventPoint_re_pos hX z.2
        positivity
      calc (xiResolventPoint X z.1).re * (xiResolventPoint X z.2).re *
          ((xiResolventPoint X z.1).re - (xiResolventPoint X z.2).re) ^ (2 : ℕ) ≤
          (xiResolventPoint X z.1).re * (xiResolventPoint X z.2).re * 4 :=
            mul_le_mul_of_nonneg_left hd hpp
        _ ≤ ‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖ * 4 :=
            mul_le_mul_of_nonneg_right hstep1 (by norm_num)
        _ = 4 * (‖xiResolventPoint X z.1‖ * ‖xiResolventPoint X z.2‖) := by ring
  have hpt : ∀ z : XiZeroCopy × XiZeroCopy,
      (xiResolventPoint X z.1).re * (xiResolventPoint X z.2).re *
          ((xiResolventPoint X z.1).re - (xiResolventPoint X z.2).re) ^ (2 : ℕ) -
        xiResolventPairErr X z ≤ (xiResolventPairTerm X z).re := by
    intro z
    have h := re_pair_ge_bulk_sub_err (norm_xiResolventPoint_le_one hX z.1)
      (norm_xiResolventPoint_le_one hX z.2)
    rw [xiResolventPairTerm, xiResolventPairErr]
    convert h using 2
  have hre : (∑' z : XiZeroCopy × XiZeroCopy, xiResolventPairTerm X z).re =
      ∑' z : XiZeroCopy × XiZeroCopy, (xiResolventPairTerm X z).re :=
    Complex.re_tsum hpair
  rw [hre]
  have hlower : (∑' z : XiZeroCopy × XiZeroCopy,
      ((xiResolventPoint X z.1).re * (xiResolventPoint X z.2).re *
        ((xiResolventPoint X z.1).re - (xiResolventPoint X z.2).re) ^ (2 : ℕ) -
        xiResolventPairErr X z)) ≤
      ∑' z : XiZeroCopy × XiZeroCopy, (xiResolventPairTerm X z).re :=
    (hbulk.sub (summable_xiResolventPairErr hX)).tsum_le_tsum hpt hpair_re
  have hsplit : (∑' z : XiZeroCopy × XiZeroCopy,
      ((xiResolventPoint X z.1).re * (xiResolventPoint X z.2).re *
        ((xiResolventPoint X z.1).re - (xiResolventPoint X z.2).re) ^ (2 : ℕ) -
        xiResolventPairErr X z)) =
      (∑' z : XiZeroCopy × XiZeroCopy,
        (xiResolventPoint X z.1).re * (xiResolventPoint X z.2).re *
          ((xiResolventPoint X z.1).re - (xiResolventPoint X z.2).re) ^ (2 : ℕ)) -
        ∑' z : XiZeroCopy × XiZeroCopy, xiResolventPairErr X z :=
    hbulk.tsum_sub (summable_xiResolventPairErr hX)
  have hbulk_nonneg : (0 : ℝ) ≤ ∑' z : XiZeroCopy × XiZeroCopy,
      (xiResolventPoint X z.1).re * (xiResolventPoint X z.2).re *
        ((xiResolventPoint X z.1).re - (xiResolventPoint X z.2).re) ^ (2 : ℕ) := by
    apply tsum_nonneg
    intro z
    have ha := xiResolventPoint_re_pos hX z.1
    have hb := xiResolventPoint_re_pos hX z.2
    positivity
  rw [hsplit, tsum_xiResolventPairErr hX] at hlower
  linarith

/-! ## The imaginary mass is the RH obstruction -/

/-- **RH ⟺ the imaginary square mass vanishes** at any one shift: the mass functionals in the
Turán control are exactly the deviation of the divisor from the real axis. -/
theorem riemannHypothesis_iff_xiResolventImSqMass_eq_zero {X : ℝ} (hX : 0 ≤ X) :
    RiemannHypothesis ↔ xiResolventImSqMass X = 0 := by
  constructor
  · intro hRH
    rw [xiResolventImSqMass]
    have hzero : ∀ q : XiZeroCopy, (xiResolventPoint X q).im ^ (2 : ℕ) = 0 := by
      intro q
      obtain ⟨v, hv, hveq⟩ := exists_pos_ofReal_xiResolventPoint_of_rh hRH hX q
      rw [hveq]
      simp
    rw [tsum_congr hzero, tsum_zero]
  · intro hmass
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hle : (xiResolventPoint X q).im ^ (2 : ℕ) ≤ xiResolventImSqMass X :=
      (summable_im_sq_xiResolventPoint hX).le_tsum q fun r _ => sq_nonneg _
    have hzero : (xiResolventPoint X q).im = 0 := by
      have h2 : (xiResolventPoint X q).im ^ (2 : ℕ) ≤ 0 := hmass ▸ hle
      have h3 : (xiResolventPoint X q).im ^ (2 : ℕ) = 0 :=
        le_antisymm h2 (sq_nonneg _)
      exact pow_eq_zero_iff two_ne_zero |>.mp h3
    have hne := xiSpectralSq_add_ofReal_ne_zero hX q
    rw [xiResolventPoint, Complex.inv_im] at hzero
    have hnormSq : Complex.normSq (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)) ≠ 0 :=
      fun hc => hne (Complex.normSq_eq_zero.mp hc)
    have him2 : (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im = 0 := by
      rw [div_eq_zero_iff] at hzero
      rcases hzero with h | h
      · linarith [neg_eq_zero.mp h]
      · exact absurd h hnormSq
    simp only [Complex.add_im, Complex.ofReal_im, add_zero] at him2
    have hsq : (xiSpectralPoint q ^ (2 : ℕ)).im =
        2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
      simp [sq, Complex.mul_im]
      ring
    rw [hsq] at him2
    have hγ : (xiSpectralPoint q).re ≠ 0 := by
      have h := xiZeroCopy_two_lt_im_sq q
      rw [← xiSpectralPoint_re_eq] at h
      intro hcon
      rw [hcon] at h
      norm_num at h
    have hb : (xiSpectralPoint q).im = 0 := by
      rcases mul_eq_zero.mp him2 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · norm_num at h'
        · exact absurd h' hγ
      · exact h
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, hb]

end

end RHTower
