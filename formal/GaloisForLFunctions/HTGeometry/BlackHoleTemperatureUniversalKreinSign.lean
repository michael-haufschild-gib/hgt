import GaloisForLFunctions.HTGeometry.BlackHoleSpectralDualityCommonMode
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Temperature-universal Hawking Krein-sign selection

Grozdanov--Vrbica's exact four-dimensional black-hole spectral-duality law is

`S(ω) - S(-ω) = 2 I λ sinh(β ω / 2)`.

After division by the nonzero spectral weight, the square of the odd response is therefore the
universal thermal factor `sinh(β ω / 2)^(2 : ℕ)`.  On a purely imaginary frequency this lies in the
negative real Krein chamber for every positive inverse temperature.

This file proves the fixed-frequency converse and then audits its physical scaling:

* `sinh(β ω / 2)^(2 : ℕ) ∈ ℝ_{≤ 0}` for every `β > 0` exactly when `Re ω = 0`;
* every single fixed `β > 0` has an explicit off-axis blind point in the same strict chamber.
* a self-similar black-hole mode `ω(β) = carrier / β` keeps `β ω(β)` constant, so varying
  temperature supplies no additional selection along a comoving QNM branch.

Thus neither fixed-temperature passivity nor self-similar mass/temperature variation can select
the critical axis.  A Hawking-based RH producer must break thermal self-similarity
coefficient-faithfully.  For the FZZ-cigar direction, finite string level and fractional-winding
replica backreaction provide such a dimensionless deformation.  The still-open physical statement
is that critical puncture backreaction and three-region completion put every nontrivial
continuum-Mellin divisor zero in the resulting level-universal chamber.  No such source weld is
assumed here.

Physics provenance:

* Grozdanov--Vrbica, arXiv:2505.14229, equations (100)--(101).
* Giveon--Itzhaki--Troost, arXiv:1311.5189, exterior/interior/trumpet genus cancellation.
* Brustein--Giveon--Itzhaki--Zigdon, arXiv:2112.03048, critical punctured cigar.
* Halder--Jafferis, arXiv:2402.00932, fractional-winding replica area operator.
-/

open Complex

namespace GaloisForLFunctions

private lemma real_sinh_ne_zero_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    Real.sinh x ≠ 0 := by
  intro hs
  rw [Real.sinh_eq] at hs
  have he : Real.exp x = Real.exp (-x) := by linarith
  have hxneg : x = -x := Real.exp_injective he
  apply hx
  linarith

private lemma complex_sinh_re (z : ℂ) :
    (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im := by
  have h : Complex.sinh z
      = ((Real.sinh z.re * Real.cos z.im : ℝ) : ℂ)
        + ((Real.cosh z.re * Real.sin z.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh]
    push_cast
    ring
  rw [h, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma complex_sinh_im (z : ℂ) :
    (Complex.sinh z).im = Real.cosh z.re * Real.sin z.im := by
  have h : Complex.sinh z
      = ((Real.sinh z.re * Real.cos z.im : ℝ) : ℂ)
        + ((Real.cosh z.re * Real.sin z.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh]
    push_cast
    ring
  rw [h, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The normalized odd Hawking response stays in the nonpositive real Krein chamber throughout
the full positive-temperature family. -/
def HawkingTemperatureUniversalKreinSign (ω : ℂ) : Prop :=
  ∀ β : ℝ, 0 < β →
    ((Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ)).im = 0 ∧
      ((Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ)).re ≤ 0

/-- A comoving black-hole frequency with fixed dimensionless thermal carrier. -/
noncomputable def blackHoleSelfSimilarFrequency (carrier : ℂ) (β : ℝ) : ℂ :=
  carrier / (β : ℂ)

/-- Exact self-similar thermal collapse: inverse temperature cancels the comoving frequency
scale. -/
theorem blackHoleSelfSimilar_thermalArgument
    (carrier : ℂ) {β : ℝ} (hβ : β ≠ 0) :
    ((β : ℂ) * blackHoleSelfSimilarFrequency carrier β) / 2 = carrier / 2 := by
  rw [blackHoleSelfSimilarFrequency]
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  field_simp

/-- The spectral-duality odd response is temperature-blind along every self-similar QNM branch.
This is the exact obstruction to using mass/temperature rescaling as the RH selector. -/
theorem blackHoleSelfSimilar_oddSquare_independent
    (carrier : ℂ) {β : ℝ} (hβ : β ≠ 0) :
    (Complex.sinh (((β : ℂ) * blackHoleSelfSimilarFrequency carrier β) / 2)) ^ (2 : ℕ) =
      (Complex.sinh (carrier / 2)) ^ (2 : ℕ) := by
  rw [blackHoleSelfSimilar_thermalArgument carrier hβ]

/-- **Temperature-universal Hawking selection.**  Universal Krein sign is exactly imaginary-axis
frequency.  Unlike a fixed KMS temperature, the full surface-gravity family has no tilted blind
comb. -/
theorem hawkingTemperatureUniversalKreinSign_iff_re_eq_zero (ω : ℂ) :
    HawkingTemperatureUniversalKreinSign ω ↔ ω.re = 0 := by
  constructor
  · intro hsign
    by_contra hre
    by_cases himpos : 0 < ω.im
    · let β : ℝ := Real.pi / (2 * ω.im)
      have hβ : 0 < β := div_pos Real.pi_pos (mul_pos zero_lt_two himpos)
      obtain ⟨himZero, _⟩ := hsign β hβ
      let z : ℂ := ((β : ℂ) * ω) / 2
      have hzre : z.re = β * ω.re / 2 := by
        simp [z, Complex.mul_re]
      have hzim_general : z.im = β * ω.im / 2 := by
        simp [z, Complex.mul_im]
      have hzim : z.im = Real.pi / 4 := by
        rw [hzim_general]
        dsimp only [β]
        field_simp [ne_of_gt himpos]
        norm_num
      have hzre_ne : z.re ≠ 0 := by
        rw [hzre]
        exact div_ne_zero (mul_ne_zero hβ.ne' hre) (by norm_num)
      have hsin_ne : Real.sin z.im ≠ 0 := by
        rw [hzim, Real.sin_pi_div_four]
        positivity
      have hcos_ne : Real.cos z.im ≠ 0 := by
        rw [hzim, Real.cos_pi_div_four]
        positivity
      have hsinh_re_ne : (Complex.sinh z).re ≠ 0 := by
        rw [complex_sinh_re]
        exact mul_ne_zero (real_sinh_ne_zero_of_ne_zero hzre_ne) hcos_ne
      have hsinh_im_ne : (Complex.sinh z).im ≠ 0 := by
        rw [complex_sinh_im]
        exact mul_ne_zero (ne_of_gt (Real.cosh_pos z.re)) hsin_ne
      have hsq_im_ne : ((Complex.sinh z) ^ (2 : ℕ)).im ≠ 0 := by
        intro hzero
        rw [pow_two, Complex.mul_im] at hzero
        have hprod : 2 * (Complex.sinh z).re * (Complex.sinh z).im ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) hsinh_re_ne) hsinh_im_ne
        apply hprod
        calc
          2 * (Complex.sinh z).re * (Complex.sinh z).im =
              (Complex.sinh z).re * (Complex.sinh z).im +
                (Complex.sinh z).im * (Complex.sinh z).re := by ring
          _ = 0 := hzero
      exact hsq_im_ne himZero
    · by_cases himneg : ω.im < 0
      · let β : ℝ := -Real.pi / (2 * ω.im)
        have hβ : 0 < β :=
          div_pos_of_neg_of_neg (neg_lt_zero.mpr Real.pi_pos)
            (mul_neg_of_pos_of_neg zero_lt_two himneg)
        obtain ⟨himZero, _⟩ := hsign β hβ
        let z : ℂ := ((β : ℂ) * ω) / 2
        have hzre : z.re = β * ω.re / 2 := by
          simp [z, Complex.mul_re]
        have hzim_general : z.im = β * ω.im / 2 := by
          simp [z, Complex.mul_im]
        have hzim : z.im = -Real.pi / 4 := by
          rw [hzim_general]
          dsimp only [β]
          field_simp [ne_of_lt himneg]
          norm_num
        have hzre_ne : z.re ≠ 0 := by
          rw [hzre]
          exact div_ne_zero (mul_ne_zero hβ.ne' hre) (by norm_num)
        have hsin_ne : Real.sin z.im ≠ 0 := by
          rw [hzim, show -Real.pi / 4 = -(Real.pi / 4) by ring,
            Real.sin_neg, Real.sin_pi_div_four]
          exact neg_ne_zero.mpr (by positivity)
        have hcos_ne : Real.cos z.im ≠ 0 := by
          rw [hzim, show -Real.pi / 4 = -(Real.pi / 4) by ring,
            Real.cos_neg, Real.cos_pi_div_four]
          positivity
        have hsinh_re_ne : (Complex.sinh z).re ≠ 0 := by
          rw [complex_sinh_re]
          exact mul_ne_zero (real_sinh_ne_zero_of_ne_zero hzre_ne) hcos_ne
        have hsinh_im_ne : (Complex.sinh z).im ≠ 0 := by
          rw [complex_sinh_im]
          exact mul_ne_zero (ne_of_gt (Real.cosh_pos z.re)) hsin_ne
        have hsq_im_ne : ((Complex.sinh z) ^ (2 : ℕ)).im ≠ 0 := by
          intro hzero
          rw [pow_two, Complex.mul_im] at hzero
          have hprod : 2 * (Complex.sinh z).re * (Complex.sinh z).im ≠ 0 :=
            mul_ne_zero (mul_ne_zero (by norm_num) hsinh_re_ne) hsinh_im_ne
          apply hprod
          calc
            2 * (Complex.sinh z).re * (Complex.sinh z).im =
                (Complex.sinh z).re * (Complex.sinh z).im +
                  (Complex.sinh z).im * (Complex.sinh z).re := by ring
            _ = 0 := hzero
        exact hsq_im_ne himZero
      · have him : ω.im = 0 := by linarith
        obtain ⟨_, hreNonpos⟩ := hsign 1 zero_lt_one
        let x : ℝ := ω.re
        have hω : ω = (x : ℂ) := by
          apply Complex.ext
          · simp [x]
          · simp [him]
        have hx : x ≠ 0 := by simpa [x] using hre
        have harg : (((1 : ℝ) : ℂ) * ω) / 2 = ((x / 2 : ℝ) : ℂ) := by
          rw [hω]
          norm_num
        have hsinh_ne : Real.sinh (x / 2) ≠ 0 :=
          real_sinh_ne_zero_of_ne_zero (div_ne_zero hx (by norm_num))
        have hpos : 0 < Real.sinh (x / 2) ^ (2 : ℕ) := by
          positivity
        have hsinhval :
            Complex.sinh ((((1 : ℝ) : ℂ) * ω) / 2) =
              ((Real.sinh (x / 2) : ℝ) : ℂ) := by
          rw [harg, ← Complex.ofReal_sinh]
        have hqre :
            ((Complex.sinh ((((1 : ℝ) : ℂ) * ω) / 2)) ^ (2 : ℕ)).re =
              Real.sinh (x / 2) ^ (2 : ℕ) := by
          have hq :
              (Complex.sinh ((((1 : ℝ) : ℂ) * ω) / 2)) ^ (2 : ℕ) =
                ((Real.sinh (x / 2) ^ (2 : ℕ) : ℝ) : ℂ) := by
            rw [hsinhval]
            push_cast
            ring
          have hh := congrArg Complex.re hq
          rw [Complex.ofReal_re] at hh
          exact hh
        rw [hqre] at hreNonpos
        exact (not_lt_of_ge hreNonpos hpos).elim
  · intro hre β hβ
    let y : ℝ := ω.im
    have hω : ω = (y : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [hre]
      · simp [y]
    have harg : ((β : ℂ) * ω) / 2 = (((β * y / 2 : ℝ) : ℂ) * Complex.I) := by
      rw [hω]
      push_cast
      ring
    have hsinhval :
        Complex.sinh (((β : ℂ) * ω) / 2) =
          ((Real.sin (β * y / 2) : ℝ) : ℂ) * Complex.I := by
      rw [harg, Complex.sinh_mul_I, ← Complex.ofReal_sin]
    let r : ℝ := Real.sin (β * y / 2)
    have hq :
        (Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ) = -((r ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [hsinhval]
      change (((r : ℂ) * Complex.I) ^ (2 : ℕ)) = -((r ^ (2 : ℕ) : ℝ) : ℂ)
      rw [mul_pow, Complex.I_sq]
      push_cast
      ring
    constructor
    · have hi := congrArg Complex.im hq
      rw [Complex.neg_im, Complex.ofReal_im, neg_zero] at hi
      exact hi
    · have hqre :
          ((Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ)).re = -(r ^ (2 : ℕ)) := by
        have hr := congrArg Complex.re hq
        rw [Complex.neg_re, Complex.ofReal_re] at hr
        exact hr
      rw [hqre]
      exact neg_nonpos.mpr (sq_nonneg r)

/-- **Sharp fixed-temperature no-go.**  Every individual Hawking temperature admits an explicit
off-axis point whose normalized odd response square lies strictly in the negative real chamber.
Thus one-temperature passivity cannot supply RH selection. -/
theorem fixed_hawking_temperature_has_offAxis_krein_blind_point
    (β : ℝ) (hβ : 0 < β) :
    ∃ ω : ℂ,
      ω.re ≠ 0 ∧
        ((Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ)).im = 0 ∧
        ((Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ)).re < 0 := by
  let ω : ℂ := ((2 / β : ℝ) : ℂ) + ((Real.pi / β : ℝ) : ℂ) * Complex.I
  refine ⟨ω, ?_, ?_, ?_⟩
  · simp only [ω, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero]
    exact div_ne_zero (by norm_num) hβ.ne'
  · have harg :
        ((β : ℂ) * ω) / 2 =
          (1 : ℂ) + (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
      dsimp only [ω]
      push_cast
      field_simp [hβ.ne']
    have hsinhval :
        Complex.sinh (((β : ℂ) * ω) / 2) =
          ((Real.cosh 1 : ℝ) : ℂ) * Complex.I := by
      rw [harg, Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
        ← Complex.ofReal_sin, ← Complex.ofReal_cos,
        Real.sin_pi_div_two, Real.cos_pi_div_two]
      norm_num
    have hq :
        (Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ) =
          -(((Real.cosh 1) ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [hsinhval, mul_pow, Complex.I_sq]
      push_cast
      ring
    have hi := congrArg Complex.im hq
    rw [Complex.neg_im, Complex.ofReal_im, neg_zero] at hi
    exact hi
  · have harg :
        ((β : ℂ) * ω) / 2 =
          (1 : ℂ) + (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
      dsimp only [ω]
      push_cast
      field_simp [hβ.ne']
    have hsinhval :
        Complex.sinh (((β : ℂ) * ω) / 2) =
          ((Real.cosh 1 : ℝ) : ℂ) * Complex.I := by
      rw [harg, Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
        ← Complex.ofReal_sin, ← Complex.ofReal_cos,
        Real.sin_pi_div_two, Real.cos_pi_div_two]
      norm_num
    have hq :
        (Complex.sinh (((β : ℂ) * ω) / 2)) ^ (2 : ℕ) =
          -(((Real.cosh 1) ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [hsinhval, mul_pow, Complex.I_sq]
      push_cast
      ring
    have hr := congrArg Complex.re hq
    rw [Complex.neg_re, Complex.ofReal_re] at hr
    rw [hr]
    have hcosh : 0 < Real.cosh (1 : ℝ) := Real.cosh_pos 1
    have hsquare : 0 < Real.cosh (1 : ℝ) ^ (2 : ℕ) := by positivity
    exact neg_lt_zero.mpr hsquare

end GaloisForLFunctions
