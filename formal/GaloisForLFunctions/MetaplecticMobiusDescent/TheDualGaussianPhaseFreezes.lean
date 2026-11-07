/-
Portions adapted from OpenAI’s Gauss-sum formalization, Apache-2.0.
See LICENSE and NOTICE in this directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.ShiftedEisensteinGaussianMass

/-!
# Replacing the varying dual phase by its limiting phase

A quadratic moment is bounded by a Gaussian at half the scale. The exact
Gaussian Abel mass then shows that the normalized phase error tends to zero.
All summability and domination estimates are proved from positive damping.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
namespace GaloisForLFunctions.MetaplecticMobiusDescent

namespace GaussianPhasePointwise

theorem exp_imag_diff_le (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) -
      Complex.exp (Complex.I * (v : ℂ))‖ ≤ |u - v| := by
  have heq :
      Complex.exp (Complex.I * (u : ℂ)) -
        Complex.exp (Complex.I * (v : ℂ)) =
      (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (v : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v))

theorem exp_imag_denominator_error (θ A η : ℝ) (hA : 0 ≤ A) :
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
      |θ| * (A * η ^ 2) := by
  let r : ℝ := 1 + A * η ^ 2
  have hAη : 0 ≤ A * η ^ 2 := mul_nonneg hA (sq_nonneg _)
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hdiff : |θ / r - θ| = |θ| * ((r - 1) / r) := by
    have heq : θ / r - θ = -θ * ((r - 1) / r) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hrpos.le)]
  have hfrac : (r - 1) / r ≤ r - 1 := by
    apply (div_le_iff₀ hrpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr)]
  have hbound := exp_imag_diff_le (θ / r) θ
  dsimp [r] at hbound ⊢
  calc
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
        |θ / (1 + A * η ^ 2) - θ| := hbound
    _ = |θ| * (((1 + A * η ^ 2) - 1) / (1 + A * η ^ 2)) := hdiff
    _ ≤ |θ| * (A * η ^ 2) := by
      have hfrac' := hfrac
      dsimp [r] at hfrac'
      nlinarith [mul_nonneg (abs_nonneg θ) (sub_nonneg.mpr hfrac')]

end GaussianPhasePointwise

namespace GaussianMoment

theorem x_exp_neg_le (x : ℝ) (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have hlin : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-x)).le
  calc
    x * Real.exp (-x) = 2 * ((x / 2) * Real.exp (-x)) := by ring
    _ ≤ 2 * (Real.exp (x / 2) * Real.exp (-x)) := by
      gcongr
    _ = 2 * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

theorem gaussian_moment_term_bound (q t : ℝ) (hq : 0 ≤ q) (ht : 0 < t) :
    q * Real.exp (-t * q) ≤
      (2 / t) * Real.exp (-(t * q / 2)) := by
  have h := x_exp_neg_le (t * q) (mul_nonneg ht.le hq)
  have hpos : 0 ≤ t := ht.le
  calc
    q * Real.exp (-t * q) =
        ((t * q) * Real.exp (-(t * q))) / t := by
          field_simp
    _ ≤ (2 * Real.exp (-(t * q / 2))) / t :=
      div_le_div_of_nonneg_right h hpos
    _ = (2 / t) * Real.exp (-(t * q / 2)) := by ring


noncomputable def realGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * RankTwoPoisson.eisQ z)

theorem realGauss_nonneg (t : ℝ) (z : ℤ × ℤ) :
    0 ≤ realGauss t z := (Real.exp_pos _).le

theorem realGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (realGauss t) := by
  have h := (RankTwoPoisson.eis_gauss_summable ht).norm
  convert h using 1
  funext z
  dsimp [realGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp

theorem realGauss_cast (t : ℝ) (z : ℤ × ℤ) :
    (realGauss t z : ℂ) = RankTwoEisShift.shifted t 0 0 z := by
  dsimp [realGauss, RankTwoPoisson.eisQ,
    RankTwoEisShift.shifted, RankTwoEisShift.Q]
  rw [← Complex.ofReal_exp]
  congr 1
  ring_nf

theorem real_gaussian_mass :
    Tendsto (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  have hC := EisensteinAbelFiber.shifted_gaussian_mass 0 0
  have hRe := (Complex.continuous_re.tendsto
    (((2 / Real.sqrt 3 : ℝ) : ℂ))).comp hC
  have hsum (t : ℝ) :
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
        (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) := by
    calc
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
          ∑' z : ℤ × ℤ, (realGauss t z : ℂ) := by
            apply tsum_congr
            intro z
            exact (realGauss_cast t z).symm
      _ = (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) :=
        (Complex.ofReal_tsum (realGauss t)).symm
  have hfun (t : ℝ) :
      t * (∑' z : ℤ × ℤ, realGauss t z) =
        (((t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z)).re) := by
    rw [hsum]
    norm_cast
  have hEq :
      (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z)) =
        (Complex.re ∘
          (fun t : ℝ => (t : ℂ) *
            (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z))) := by
    funext t
    exact hfun t
  rw [← hEq] at hRe
  simpa only [Complex.ofReal_re] using hRe


private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]

private theorem moment_term_bound {t : ℝ} (ht : 0 < t) (z : ℤ × ℤ) :
    RankTwoPoisson.eisQ z * realGauss t z ≤
      (2 / (Real.pi * t)) * realGauss (t / 2) z := by
  have h := gaussian_moment_term_bound (RankTwoPoisson.eisQ z) (Real.pi * t)
    (eisQ_nonneg z) (mul_pos Real.pi_pos ht)
  convert h using 1 <;> dsimp [realGauss] <;> ring_nf

private theorem moment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => RankTwoPoisson.eisQ z * realGauss t z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  exact hmajor.of_nonneg_of_le
    (fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z))
    (moment_term_bound ht)

private theorem moment_tsum_bound {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
      (2 / (Real.pi * t)) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  have h := Summable.tsum_le_tsum (moment_term_bound ht)
    (moment_summable ht) hmajor
  simpa only [tsum_mul_left] using h

private theorem moment_tsum_nonneg (t : ℝ) :
    0 ≤ (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) := by
  exact tsum_nonneg fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z)

private theorem half_tendsto_within :
    Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => t / 2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact half_pos ht

private theorem t_tendsto_zero :
    Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

private theorem scaled_half_mass_tendsto :
    Tendsto
      (fun t : ℝ => (t / 2) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  simpa only [Function.comp_def] using real_gaussian_mass.comp half_tendsto_within

/-- The Gaussian moment costs two inverse powers of scale, leaving one vanishing power. -/
theorem scaled_moment_vanishes :
    Tendsto
      (fun t : ℝ => t ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hright : Tendsto
      (fun t : ℝ => (4 / Real.pi) * t *
        ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (t_tendsto_zero.mul scaled_half_mass_tendsto).const_mul (4 / Real.pi)
    simpa only [zero_mul, mul_zero, Function.comp_def, mul_assoc] using h
  have hleft : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact mul_nonneg (pow_nonneg ht.le _) (moment_tsum_nonneg t)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have h := moment_tsum_bound ht
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht.le _
    have hmul := mul_le_mul_of_nonneg_left h ht3
    calc
      t ^ 3 * (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
          t ^ 3 * ((2 / (Real.pi * t)) *
            (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := hmul
      _ = (4 / Real.pi) * t *
          ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := by
        field_simp [ht.ne']
        ring


theorem scaled_moment_vanishes_const (K : ℝ) (hK : 0 < K) :
    Tendsto
      (fun η : ℝ => η ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss (K * η) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hscale : Tendsto (fun η : ℝ => K * η)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun η : ℝ => K * η) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      change 0 < η at hη
      exact mul_pos hK hη
  have h := scaled_moment_vanishes.comp hscale
  have h' := h.const_mul (1 / K ^ 3)
  convert h' using 1
  · funext η
    dsimp [Function.comp_def]
    field_simp [hK.ne']
  · simp

end GaussianMoment

namespace OscSpecial

noncomputable def phaseBoundConstant (a b : ℝ) : ℝ :=
  2 * (|a - b| + |a| + |b|) + 1

theorem phaseBoundConstant_pos (a b : ℝ) :
    0 < phaseBoundConstant a b := by
  unfold phaseBoundConstant
  positivity

theorem quadratic_phase_abs_le (a b k l : ℝ) :
    |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
      phaseBoundConstant a b * (k ^ 2 + k * l + l ^ 2) := by
  let Q : ℝ := k ^ 2 + k * l + l ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    nlinarith only [sq_nonneg (k + l), sq_nonneg k, sq_nonneg l]
  have hsum : k ^ 2 + l ^ 2 ≤ 2 * Q := by
    dsimp [Q]
    nlinarith only [sq_nonneg (k + l)]
  have hcross : 2 * |k| * |l| ≤ k ^ 2 + l ^ 2 := by
    nlinarith only [sq_nonneg (|k| - |l|), sq_abs k, sq_abs l]
  have hk : k ^ 2 ≤ 2 * Q := by nlinarith only [hsum, sq_nonneg l]
  have hl : l ^ 2 ≤ 2 * Q := by nlinarith only [hsum, sq_nonneg k]
  have hkl : 2 * |k| * |l| ≤ 2 * Q := hcross.trans hsum
  have h1 := mul_le_mul_of_nonneg_left hk (abs_nonneg (a - b))
  have h2 := mul_le_mul_of_nonneg_left hkl (abs_nonneg a)
  have h3 := mul_le_mul_of_nonneg_left hl (abs_nonneg b)
  have htri :
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
        |a - b| * k ^ 2 + 2 * |a| * |k| * |l| + |b| * l ^ 2 := by
    calc
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
          |(a - b) * k ^ 2| + |2 * a * k * l| + |b * l ^ 2| := by
        calc
          _ ≤ |(a - b) * k ^ 2 + 2 * a * k * l| + |b * l ^ 2| := abs_add_le _ _
          _ ≤ _ := by
            have hh := abs_add_le ((a - b) * k ^ 2) (2 * a * k * l)
            linarith
      _ = _ := by
        simp [abs_mul,  abs_of_nonneg (sq_nonneg k),
          abs_of_nonneg (sq_nonneg l)]
  unfold phaseBoundConstant
  nlinarith only [htri, h1, h2, h3, hQ]


noncomputable def dualQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 + (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2

noncomputable def dualTrace (a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  (a - b) * (z.1 : ℝ) ^ 2 + 2 * a * (z.1 : ℝ) * (z.2 : ℝ) +
    b * (z.2 : ℝ) ^ 2

noncomputable def phaseA (a b : ℝ) : ℝ := 3 * q a b / 16
noncomputable def phaseAngle (a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  -(Real.pi / 2) * dualTrace a b z
noncomputable def dualAmp (η a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * (η * q a b / (4 * r η a b)) * dualQ z)
noncomputable def dualVarTerm (η a b : ℝ) (z : ℤ × ℤ) : ℂ :=
  (dualAmp η a b z : ℂ) *
    Complex.exp (Complex.I * ((phaseAngle a b z / r η a b : ℝ) : ℂ))
noncomputable def dualFixedTerm (η a b : ℝ) (z : ℤ × ℤ) : ℂ :=
  (dualAmp η a b z : ℂ) *
    Complex.exp (Complex.I * (phaseAngle a b z : ℂ))

private theorem dualQ_nonneg (z : ℤ × ℤ) : 0 ≤ dualQ z := by
  unfold dualQ
  nlinarith [sq_nonneg ((z.1 : ℝ) + (z.2 : ℝ)), sq_nonneg (z.1 : ℝ),
    sq_nonneg (z.2 : ℝ)]

private theorem phaseAngle_bound (a b : ℝ) (z : ℤ × ℤ) :
    |phaseAngle a b z| ≤
      (Real.pi / 2) * phaseBoundConstant a b * dualQ z := by
  have h := quadratic_phase_abs_le a b (z.1 : ℝ) (z.2 : ℝ)
  dsimp [phaseAngle, dualTrace, dualQ]
  rw [abs_mul, abs_neg, abs_of_pos (half_pos Real.pi_pos)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left h (half_pos Real.pi_pos).le

private theorem r_eq_one_add_phaseA (η a b : ℝ) :
    r η a b = 1 + phaseA a b * η ^ 2 := by
  unfold r phaseA
  ring

private theorem phaseA_nonneg {a b : ℝ} (hq : 0 ≤ q a b) :
    0 ≤ phaseA a b := by
  unfold phaseA
  positivity

theorem dual_phase_term_error {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
      dualAmp η a b z *
        ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
        (phaseA a b * η ^ 2) := by
  have hA : 0 ≤ phaseA a b := phaseA_nonneg hq.le
  have hamp : 0 ≤ dualAmp η a b z := (Real.exp_pos _).le
  have hphase := GaussianPhasePointwise.exp_imag_denominator_error
    (phaseAngle a b z) (phaseA a b) η hA
  rw [← r_eq_one_add_phaseA η a b] at hphase
  have hangle := phaseAngle_bound a b z
  have hangle' := mul_le_mul_of_nonneg_right hangle
    (mul_nonneg hA (sq_nonneg η))
  dsimp [dualVarTerm, dualFixedTerm]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hamp]
  nlinarith only [mul_le_mul_of_nonneg_left hphase hamp,
    mul_le_mul_of_nonneg_left hangle' hamp]

noncomputable def dualRealGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * dualQ z)

private theorem dualRealGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (dualRealGauss t) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss t (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable ht)
  convert hE.norm using 1
  funext z
  dsimp [dualRealGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_re]
  congr 1
  dsimp [dualQ, RankTwoPoisson.eisQ]
  push_cast
  ring

private theorem dualMoment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => dualQ z * dualRealGauss t z) := by
  have hmaj : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * dualRealGauss (t / 2) z) :=
    (dualRealGauss_summable (half_pos ht)).mul_left _
  apply hmaj.of_nonneg_of_le
  · intro z
    exact mul_nonneg (dualQ_nonneg z) (Real.exp_pos _).le
  · intro z
    have h := GaussianMoment.gaussian_moment_term_bound
      (dualQ z) (Real.pi * t) (dualQ_nonneg z) (mul_pos Real.pi_pos ht)
    convert h using 1 <;> dsimp [dualRealGauss] <;> ring_nf

private theorem dualAmp_eq_realGauss (η a b : ℝ) (z : ℤ × ℤ) :
    dualAmp η a b z = dualRealGauss (η * q a b / (4 * r η a b)) z := rfl

private theorem dualAmp_norm_var (η a b : ℝ) (z : ℤ × ℤ) :
    ‖dualVarTerm η a b z‖ = dualAmp η a b z := by
  dsimp [dualVarTerm]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real]
  exact abs_of_nonneg (Real.exp_pos _).le

private theorem dualAmp_norm_fixed (η a b : ℝ) (z : ℤ × ℤ) :
    ‖dualFixedTerm η a b z‖ = dualAmp η a b z := by
  dsimp [dualFixedTerm]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real]
  exact abs_of_nonneg (Real.exp_pos _).le

private theorem dualAmp_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualAmp η a b) := by
  have hr : 0 < r η a b := r_pos hη hq
  have ht : 0 < η * q a b / (4 * r η a b) := by positivity
  convert dualRealGauss_summable ht using 1
  funext z
  exact dualAmp_eq_realGauss η a b z

private theorem dualVar_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualVarTerm η a b) :=
  (dualAmp_summable hη hq).of_norm_bounded
    (fun z => le_of_eq (dualAmp_norm_var η a b z))

private theorem dualFixed_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualFixedTerm η a b) :=
  (dualAmp_summable hη hq).of_norm_bounded
    (fun z => le_of_eq (dualAmp_norm_fixed η a b z))

private theorem dualAmp_le_small {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (hrle : r η a b ≤ 2)
    (z : ℤ × ℤ) :
    dualAmp η a b z ≤ dualRealGauss (η * q a b / 8) z := by
  have hr : 0 < r η a b := r_pos hη hq
  have hp : 0 < η * q a b := mul_pos hη hq
  have ht : η * q a b / 8 ≤ η * q a b / (4 * r η a b) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (by positivity : 0 < 4 * r η a b)).2
    nlinarith [mul_le_mul_of_nonneg_left hrle hp.le]
  dsimp [dualAmp, dualRealGauss]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right ht
    (mul_nonneg Real.pi_pos.le (dualQ_nonneg z))
  nlinarith [hm]

noncomputable def phaseErrorConstant (a b : ℝ) : ℝ :=
  (Real.pi / 2) * phaseBoundConstant a b * phaseA a b

private theorem phaseErrorConstant_nonneg {a b : ℝ} (hq : 0 < q a b) :
    0 ≤ phaseErrorConstant a b := by
  unfold phaseErrorConstant
  exact mul_nonneg (mul_nonneg (half_pos Real.pi_pos).le
    (phaseBoundConstant_pos a b).le) (phaseA_nonneg hq.le)

theorem normalized_dual_phase_sum_error {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (hrle : r η a b ≤ 2) :
    η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
      (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖ ≤
      phaseErrorConstant a b * η ^ 3 *
        (∑' z : ℤ × ℤ,
          dualQ z * dualRealGauss (η * q a b / 8) z) := by
  let t : ℝ := η * q a b / 8
  have ht : 0 < t := by dsimp [t]; positivity
  have hK : 0 ≤ phaseErrorConstant a b := phaseErrorConstant_nonneg hq
  have hpoint (z : ℤ × ℤ) :
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
        (phaseErrorConstant a b * η ^ 2) *
          (dualQ z * dualRealGauss t z) := by
    have hbase := dual_phase_term_error hη hq z
    have hamp := dualAmp_le_small hη hq hrle z
    have hfac : 0 ≤
        ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (half_pos Real.pi_pos).le
          (phaseBoundConstant_pos a b).le) (dualQ_nonneg z))
        (mul_nonneg (phaseA_nonneg hq.le) (sq_nonneg η))
    have hmul := mul_le_mul_of_nonneg_right hamp hfac
    dsimp [t, phaseErrorConstant]
    calc
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
        dualAmp η a b z *
          ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := hbase
      _ ≤ dualRealGauss (η * q a b / 8) z *
          ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := by nlinarith only [hmul]
      _ = ((Real.pi / 2 * phaseBoundConstant a b * phaseA a b) * η ^ 2) *
          (dualQ z * dualRealGauss (η * q a b / 8) z) := by ring
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (phaseErrorConstant a b * η ^ 2) *
        (dualQ z * dualRealGauss t z)) :=
    (dualMoment_summable ht).mul_left _
  have hnorm : Summable (fun z : ℤ × ℤ =>
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖) :=
    hmajor.of_nonneg_of_le (fun z => norm_nonneg _) hpoint
  have hsum := norm_tsum_le_tsum_norm hnorm
  have htsum := Summable.tsum_le_tsum hpoint hnorm hmajor
  have hvar := dualVar_summable hη hq
  have hfixed := dualFixed_summable hη hq
  calc
    η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
      (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖ =
      η * ‖(∑' z : ℤ × ℤ, (dualVarTerm η a b z - dualFixedTerm η a b z))‖ := by
        rw [hvar.tsum_sub hfixed]
    _ ≤ η * (∑' z : ℤ × ℤ,
          ‖dualVarTerm η a b z - dualFixedTerm η a b z‖) :=
      mul_le_mul_of_nonneg_left hsum hη.le
    _ ≤ η * (∑' z : ℤ × ℤ,
          (phaseErrorConstant a b * η ^ 2) *
            (dualQ z * dualRealGauss t z)) :=
      mul_le_mul_of_nonneg_left htsum hη.le
    _ = phaseErrorConstant a b * η ^ 3 *
          (∑' z : ℤ × ℤ, dualQ z * dualRealGauss (η * q a b / 8) z) := by
      rw [tsum_mul_left]
      dsimp [t]
      ring


private theorem dual_moment_reindex (t : ℝ) :
    (∑' z : ℤ × ℤ, dualQ z * dualRealGauss t z) =
      ∑' z : ℤ × ℤ,
        RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  calc
    (∑' z : ℤ × ℤ, dualQ z * dualRealGauss t z) =
        ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisQ (e z) * GaussianMoment.realGauss t (e z) := by
      apply tsum_congr
      intro z
      have hQ : RankTwoPoisson.eisQ (e z) = dualQ z := by
        rcases z with ⟨k,l⟩
        change (k : ℝ) ^ 2 - (k : ℝ) * ((-l : ℤ) : ℝ) +
          ((-l : ℤ) : ℝ) ^ 2 =
          (k : ℝ) ^ 2 + (k : ℝ) * (l : ℝ) + (l : ℝ) ^ 2
        push_cast
        ring
      simp only [GaussianMoment.realGauss, dualRealGauss, hQ]
    _ = ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z :=
      e.tsum_eq (fun z : ℤ × ℤ =>
        RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z)

/-- Freezing the dual phase preserves the normalized Abel limit. -/
theorem normalized_dual_phase_sum_error_tendsto_zero {a b : ℝ}
    (hq : 0 < q a b) :
    Tendsto
      (fun η : ℝ =>
        η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
          (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let K : ℝ := q a b / 8
  have hK : 0 < K := by dsimp [K]; positivity
  have hmoment :
      Tendsto
        (fun η : ℝ => η ^ 3 *
          (∑' z : ℤ × ℤ,
            dualQ z * dualRealGauss (η * q a b / 8) z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert GaussianMoment.scaled_moment_vanishes_const K hK using 1
    funext η
    dsimp [K]
    rw [dual_moment_reindex]
    ring_nf
  have hright :
      Tendsto
        (fun η : ℝ => phaseErrorConstant a b * η ^ 3 *
          (∑' z : ℤ × ℤ,
            dualQ z * dualRealGauss (η * q a b / 8) z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert hmoment.const_mul (phaseErrorConstant a b) using 1
    · funext η
      ring
    · simp
  have hr_lim : Tendsto (fun η : ℝ => r η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun η : ℝ => r η a b) 0 := by
      unfold r
      fun_prop
    simpa [r] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hrle : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), r η a b ≤ 2 := by
    have hevent : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), x ≤ 2 :=
      eventually_le_nhds (by norm_num)
    exact hr_lim.eventually hevent
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hright
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact mul_nonneg hη.le (norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin, hrle] with η hη hbound
    exact normalized_dual_phase_sum_error hη hq hbound

theorem dualGaussian_eq_dualVarTerm {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      dualVarTerm η a b z := by
  rw [dualGaussian_explicit hη hq z]
  have hQ :
      ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) =
        (dualQ z : ℂ) := by
    dsimp [dualQ]
    push_cast
    ring
  have hT :
      (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
        2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
        (b : ℂ) * (z.2 : ℂ) ^ 2) =
        (dualTrace a b z : ℂ) := by
    dsimp [dualTrace]
    push_cast
    ring
  rw [hQ, hT]
  have hrC : (r η a b : ℂ) ≠ 0 := by
    exact_mod_cast (r_pos hη hq).ne'
  have harg :
      -(Real.pi : ℂ) *
        ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ)) *
          (dualQ z : ℂ) +
          Complex.I / (2 * (r η a b : ℂ)) * (dualTrace a b z : ℂ)) =
      (((-Real.pi * (η * q a b / (4 * r η a b)) * dualQ z : ℝ) : ℂ)) +
        Complex.I * ((phaseAngle a b z / r η a b : ℝ) : ℂ) := by
    dsimp [phaseAngle]
    push_cast
    field_simp [hrC]
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  rfl



noncomputable def dualScale (η a b : ℝ) : ℝ :=
  η * q a b / (4 * r η a b)

theorem dualScale_tendsto (a b : ℝ) (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have hnum : ContinuousAt (fun η : ℝ => η * q a b) 0 := by fun_prop
  have hden : ContinuousAt (fun η : ℝ => 4 * r η a b) 0 := by
    change ContinuousAt
      (fun η : ℝ => 4 * (1 + 3 * q a b * η ^ 2 / 16)) 0
    fun_prop
  have hden0 : 4 * r 0 a b ≠ 0 := by simp [r]
  have hcont : ContinuousAt (fun η : ℝ => dualScale η a b) 0 := by
    exact hnum.div hden hden0
  have hlim : Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [dualScale] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact hlim
  · filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hr : 0 < r η a b := by
      unfold r
      positivity
    exact div_pos (mul_pos hη hq) (mul_pos (by norm_num) hr)

/-- The dual damping rescales Abel mass by the limiting ratio of the two scales. -/
theorem abel_mass_dual_scale (a b : ℝ) (hq : 0 < q a b)
    (F : ℝ → ℂ) (L : ℂ)
    (hF : Tendsto (fun t : ℝ => (t : ℂ) * F t)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun η : ℝ => (η : ℂ) * F (dualScale η a b))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((4 / q a b : ℝ) : ℂ) * L)) := by
  have hscale := dualScale_tendsto a b hq
  have hF' := hF.comp hscale
  have hrcont : ContinuousAt
      (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ)) 0 := by
    change ContinuousAt
      (fun η : ℝ => ((4 * (1 + 3 * q a b * η ^ 2 / 16) / q a b : ℝ) : ℂ)) 0
    fun_prop
  have hr : Tendsto (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((4 / q a b : ℝ) : ℂ)) := by
    simpa [r] using hrcont.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := hr.mul hF'
  have heq : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      (η : ℂ) * F (dualScale η a b) =
        ((4 * r η a b / q a b : ℝ) : ℂ) *
          (((dualScale η a b : ℝ) : ℂ) * F (dualScale η a b)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hrpos : 0 < r η a b := by
      unfold r
      positivity
    have hqC : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hrC : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    dsimp [dualScale]
    push_cast
    field_simp [hqC, hrC]
  exact hprod.congr' (heq.mono fun η h => h.symm)


private theorem R_eq_four_r_div_q {η a b : ℝ} (hq : q a b ≠ 0) :
    R η a b = 4 * r η a b / q a b := by
  unfold R r
  field_simp [hq]
  ring

private theorem sqrt_R_eq {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b) :
    Real.sqrt (R η a b) = 2 * Real.sqrt (r η a b) / Real.sqrt (q a b) := by
  rw [R_eq_four_r_div_q hq.ne']
  rw [Real.sqrt_div' (4 * r η a b) hq.le]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs4]

theorem prefactor_eq_real_sqrt {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ) := by
  have hR : 0 ≤ R η a b := by unfold R; positivity
  have hqS : Real.sqrt (q a b) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hrS : Real.sqrt (r η a b) ≠ 0 :=
    (Real.sqrt_pos.mpr (r_pos hη hq)).ne'
  have hcpow : (R η a b : ℂ) ^ (1 / 2 : ℂ) =
      ((R η a b) ^ (1 / 2 : ℝ) : ℝ) := by
    simpa using (Complex.ofReal_cpow hR (1 / 2 : ℝ)).symm
  rw [hcpow]
  simp only [Complex.ofReal_div]
  rw [← Real.sqrt_eq_rpow, sqrt_R_eq hη hq]
  push_cast
  field_simp [hqS, hrS]


/-- The principal Poisson prefactor tends to half the square root of the norm form. -/
theorem prefactor_tendsto {a b : ℝ} (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) := by
  have hrcont : Continuous (fun η : ℝ => r η a b) := by
    unfold r
    fun_prop
  have hr : Tendsto (fun η : ℝ => r η a b) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [r] using (hrcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun η : ℝ => Real.sqrt (r η a b))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have hd : Tendsto (fun η : ℝ => Real.sqrt (q a b) /
      (2 * Real.sqrt (r η a b))) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (q a b) / 2)) := by
    simpa only [Pi.div_def, mul_one] using
      (tendsto_const_nhds (x := Real.sqrt (q a b))).div
        ((tendsto_const_nhds (x := (2 : ℝ))).mul hs)
        (by norm_num : (2 : ℝ) * 1 ≠ 0)
  have hc : Tendsto (fun η : ℝ =>
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hd
  have heq : (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact prefactor_eq_real_sqrt hη hq
  exact hc.congr' heq.symm

end OscSpecial

/-- A vanishing normalized phase error transfers an Abel limit through a convergent prefactor. -/
theorem abel_transfer (P V W : ℝ → ℂ) (p w : ℂ)
    (hP : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 p))
    (hW : Tendsto (fun η : ℝ => (η : ℂ) * W η) (𝓝[>] (0 : ℝ)) (𝓝 w))
    (hE : Tendsto (fun η => η * ‖V η - W η‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Tendsto (fun η : ℝ => (η : ℂ) * (P η * V η))
      (𝓝[>] (0 : ℝ)) (𝓝 (p * w)) := by
  have hdiff : Tendsto (fun η : ℝ => (η : ℂ) * (V η - W η))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun η : ℝ => ‖(η : ℂ) * (V η - W η)‖) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun η => η * ‖V η - W η‖) := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    exact hE.congr' heq.symm
  have hV : Tendsto (fun η : ℝ => (η : ℂ) * V η)
      (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    convert hW.add hdiff using 1
    · funext η; ring
    · simp
  convert hP.mul hV using 1
  · funext η; ring


end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.GaussianMoment.scaled_moment_vanishes

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.OscSpecial.normalized_dual_phase_sum_error_tendsto_zero

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.OscSpecial.abel_mass_dual_scale

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.OscSpecial.prefactor_tendsto
