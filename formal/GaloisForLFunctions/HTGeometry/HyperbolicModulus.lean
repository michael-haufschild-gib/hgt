import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import GaloisForLFunctions.HTGeometry.LabelledAtomicMeasure

/-!
# The modulus of a hyperbolic sine on a vertical line

Along the line `Re = a` the hyperbolic sine has squared modulus `sinh²a cos²θ + cosh²a sin²θ`: the
real and imaginary parts separate into the two hyperbolic functions against the two circular ones.

At the quarter-period frequencies, where the cosine vanishes, the squared modulus is exactly
`cosh²a` — independent of the frequency.  That constancy is what makes a free clock's spectral
weights flat: the factor `1 + x²` in the weight is cancelled by the `1 + x²` hidden in the
denominator `|1 - i x|²`, leaving no dependence on the mode.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- **The squared modulus of `sinh` on a vertical line.**  The real and imaginary parts separate
into hyperbolic times circular factors. -/
theorem normSq_sinh_sub_mul_I (a θ : ℝ) :
    Complex.normSq (Complex.sinh ((a : ℂ) - (θ : ℂ) * Complex.I))
      = Real.sinh a ^ 2 * Real.cos θ ^ 2 + Real.cosh a ^ 2 * Real.sin θ ^ 2 := by
  rw [Complex.sinh_sub, Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **At a quarter-period frequency the modulus is constant.**  Where the cosine vanishes the
squared modulus is `cosh²a`, with no dependence on the frequency. -/
theorem normSq_sinh_sub_mul_I_of_cos_eq_zero {a θ : ℝ} (h : Real.cos θ = 0) :
    Complex.normSq (Complex.sinh ((a : ℂ) - (θ : ℂ) * Complex.I)) = Real.cosh a ^ 2 := by
  rw [normSq_sinh_sub_mul_I, h]
  have hs : Real.sin θ ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq θ
    rw [h] at this
    linarith
  rw [hs]
  ring

/-- The cosine vanishes at every half-odd multiple of `π`, which is where the quarter-period
frequencies `x_k = (k + 1/2)π/a` of aperture `a` send `x a`. -/
theorem cos_quarterPeriod_eq_zero (k : ℤ) :
    Real.cos ((k + 1 / 2) * Real.pi) = 0 := by
  have : ((k : ℝ) + 1 / 2) * Real.pi = (k : ℝ) * Real.pi + Real.pi / 2 := by ring
  rw [this, Real.cos_add_pi_div_two]
  simp [Real.sin_int_mul_pi]

/-- **The free-clock cancellation.**  At a quarter-period frequency the product of `1 + x²` with the
squared modulus of `sinh(a - i x a)/(1 - i x)` is `cosh²a`, independent of `x`: the `1 + x²` of the
weight is exactly cancelled by `|1 - i x|²`. -/
theorem quarterPeriod_weight_const {a x : ℝ} (h : Real.cos (x * a) = 0) :
    (1 + x ^ 2) *
        (Complex.normSq (Complex.sinh ((a : ℂ) - ((x * a : ℝ) : ℂ) * Complex.I)) /
          Complex.normSq (1 - (x : ℂ) * Complex.I))
      = Real.cosh a ^ 2 := by
  have hden : Complex.normSq (1 - (x : ℂ) * Complex.I) = 1 + x ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im]
    ring
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [hden, normSq_sinh_sub_mul_I_of_cos_eq_zero h]
  field_simp

/-! ## The free-clock normalizations

The two normalizing integrals of the free model are elementary: the squared norm of the deficiency
vector is a hyperbolic sine, and that of an eigenvector is the aperture length.  Combining them with
the constant modulus above collapses the weight to `coth a / a` by the double-angle identity. -/

/-- The deficiency normalization of the free model. -/
theorem integral_exp_two_mul (a : ℝ) :
    ∫ s in (-a)..a, Real.exp (2 * s) = Real.sinh (2 * a) := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (two_ne_zero), integral_exp,
    Real.sinh_eq]
  rw [show (2 : ℝ) * -a = -(2 * a) by ring]
  rw [smul_eq_mul]
  ring

/-- The eigenvector normalization of the free model: a unimodular eigenfunction has squared norm the
aperture length. -/
theorem integral_one_symm (a : ℝ) : ∫ _s in (-a)..a, (1 : ℝ) = 2 * a := by
  simp
  ring

/-- **The free-clock weight.**  The constant modulus over the two normalizations is `coth a / a`, by
the double-angle identity for the hyperbolic sine. -/
theorem freeClockWeight_eq_coth {a : ℝ} (ha : a ≠ 0) (hs : Real.sinh a ≠ 0) :
    4 * Real.cosh a ^ 2 / (2 * a * Real.sinh (2 * a))
      = Real.cosh a / (a * Real.sinh a) := by
  rw [Real.sinh_two_mul]
  have hc : Real.cosh a ≠ 0 := ne_of_gt (Real.cosh_pos a)
  field_simp
  ring

/-! ## The free-model deficiency transform

For the free model the deficiency transform is a symmetric exponential integral, which evaluates to
a hyperbolic sine over the spectral factor.  Its squared modulus against `1 + x²` is then the
constant of the previous section, so the free clock's weights are flat by computation, not by
assumption. -/

/-- The symmetric exponential integral is a hyperbolic sine over the exponent. -/
theorem integral_exp_mul_symm {w : ℂ} (hw : w ≠ 0) (a : ℝ) :
    ∫ s in (-a)..a, Complex.exp (w * s) = 2 * Complex.sinh (w * (a : ℂ)) / w := by
  rw [integral_exp_mul_complex hw, show ((-a : ℝ) : ℂ) = -(a : ℂ) by push_cast; ring,
    show w * -(a : ℂ) = -(w * (a : ℂ)) by ring]
  have hsinh : Complex.sinh (w * (a : ℂ))
      = (Complex.exp (w * (a : ℂ)) - Complex.exp (-(w * (a : ℂ)))) / 2 := Complex.ext rfl rfl
  rw [hsinh]
  field_simp

/-- **The free-model weight is flat.**  At a quarter-period frequency the squared modulus of the
deficiency transform, against the factor `1 + x²`, is `4 cosh²a` — independent of the mode. -/
theorem normSq_freeDeficiencyTransform {a x : ℝ} (h : Real.cos (x * a) = 0) :
    (1 + x ^ 2) *
        Complex.normSq (2 * Complex.sinh ((1 - (x : ℂ) * Complex.I) * (a : ℂ)) /
          (1 - (x : ℂ) * Complex.I))
      = 4 * Real.cosh a ^ 2 := by
  have harg : (1 - (x : ℂ) * Complex.I) * (a : ℂ)
      = (a : ℂ) - ((x * a : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.normSq_div, Complex.normSq_mul]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by
    simp
    norm_num
  rw [h2, show (4 : ℝ) * Complex.normSq (Complex.sinh ((a : ℂ) - ((x * a : ℝ) : ℂ) * Complex.I)) /
      Complex.normSq (1 - (x : ℂ) * Complex.I)
      = 4 * (Complex.normSq (Complex.sinh ((a : ℂ) - ((x * a : ℝ) : ℂ) * Complex.I)) /
        Complex.normSq (1 - (x : ℂ) * Complex.I)) by ring]
  rw [show (1 + x ^ 2) * (4 * (Complex.normSq (Complex.sinh ((a : ℂ) -
      ((x * a : ℝ) : ℂ) * Complex.I)) / Complex.normSq (1 - (x : ℂ) * Complex.I)))
      = 4 * ((1 + x ^ 2) * (Complex.normSq (Complex.sinh ((a : ℂ) -
        ((x * a : ℝ) : ℂ) * Complex.I)) / Complex.normSq (1 - (x : ℂ) * Complex.I))) by ring,
    quarterPeriod_weight_const h]

/-! ## The free model's even pencil

The even characteristic pencil of the free model is the sum of the two deficiency transforms, and
the sum of hyperbolic sines at conjugate arguments collapses to a hyperbolic sine times a cosine.
Since the hyperbolic sine of a nonzero aperture never vanishes, the pencil's zeros are exactly the
zeros of the cosine — the quarter-period frequencies. -/

/-- **Conjugate hyperbolic sines add to a cosine.**  The odd parts cancel, leaving `2 sinh a` times
`cos(z a)`. -/
theorem sinh_add_sinh_conj (a : ℝ) (z : ℂ) :
    Complex.sinh ((a : ℂ) + Complex.I * z * a) + Complex.sinh ((a : ℂ) - Complex.I * z * a)
      = 2 * Complex.sinh (a : ℂ) * Complex.cos (z * a) := by
  rw [Complex.sinh_add, Complex.sinh_sub,
    show Complex.I * z * (a : ℂ) = (z * a) * Complex.I by ring,
    Complex.cosh_mul_I, Complex.sinh_mul_I]
  ring

/-- **The free model's even spectrum.**  For a nonzero aperture the even pencil vanishes exactly at
the zeros of `cos(z a)`, which are the quarter-period frequencies `(k + 1/2)π/a`. -/
theorem freeEvenPencil_eq_zero_iff {a : ℝ} (ha : a ≠ 0) (z : ℂ) :
    Complex.sinh ((a : ℂ) + Complex.I * z * a) + Complex.sinh ((a : ℂ) - Complex.I * z * a) = 0
      ↔ ∃ k : ℤ, z * a = (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 := by
  rw [sinh_add_sinh_conj]
  have hsinh : Complex.sinh (a : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sinh, Ne, Complex.ofReal_eq_zero]
    exact _root_.Real.sinh_ne_zero.mpr ha
  have h2 : (2 : ℂ) * Complex.sinh (a : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hsinh
  rw [mul_eq_zero]
  constructor
  · rintro (hbad | h)
    · exact absurd hbad h2
    · exact Complex.cos_eq_zero_iff.mp h
  · intro h
    exact Or.inr (Complex.cos_eq_zero_iff.mpr h)

/-! ## The free model's odd pencil, and the concrete interlacing

The odd pencil is the difference of the same two transforms; there the *even* parts cancel, leaving
a hyperbolic cosine times a sine.  So the odd spectrum is the integer multiples of `pi/a` and the
even spectrum the half-odd ones, which interlace strictly — and the centre lies in the odd spectrum
only, which is the parity clause. -/

/-- **Conjugate hyperbolic sines subtract to a sine.**  The even parts cancel, leaving `2 cosh a`
times `sin(z a)`. -/
theorem sinh_sub_sinh_conj (a : ℝ) (z : ℂ) :
    Complex.sinh ((a : ℂ) + Complex.I * z * a) - Complex.sinh ((a : ℂ) - Complex.I * z * a)
      = 2 * Complex.cosh (a : ℂ) * (Complex.sin (z * a) * Complex.I) := by
  rw [Complex.sinh_add, Complex.sinh_sub,
    show Complex.I * z * (a : ℂ) = (z * a) * Complex.I by ring,
    Complex.cosh_mul_I, Complex.sinh_mul_I]
  ring

/-- **The free model's odd spectrum.**  The odd pencil vanishes exactly at the zeros of `sin(z a)`,
the integer multiples of `pi/a`.  Unlike the even pencil this needs no hypothesis on the aperture:
the hyperbolic cosine never vanishes, whereas the hyperbolic sine vanishes at zero. -/
theorem freeOddPencil_eq_zero_iff {a : ℝ} (z : ℂ) :
    Complex.sinh ((a : ℂ) + Complex.I * z * a) - Complex.sinh ((a : ℂ) - Complex.I * z * a) = 0
      ↔ ∃ k : ℤ, z * a = (k : ℂ) * (Real.pi : ℂ) := by
  rw [sinh_sub_sinh_conj]
  have hcosh : Complex.cosh (a : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh, Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.cosh_pos a)
  have h2 : (2 : ℂ) * Complex.cosh (a : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hcosh
  rw [mul_eq_zero]
  constructor
  · rintro (hbad | h)
    · exact absurd hbad h2
    · rcases mul_eq_zero.mp h with h' | hI
      · exact Complex.sin_eq_zero_iff.mp h'
      · exact absurd hI Complex.I_ne_zero
  · intro h
    exact Or.inr (mul_eq_zero.mpr (Or.inl (Complex.sin_eq_zero_iff.mpr h)))

/-- **The two free spectra interlace strictly.**  Between consecutive odd points `k pi/a` and
`(k+1) pi/a` sits exactly the even point `(k + 1/2) pi/a`. -/
theorem freeSpectra_interlace {a : ℝ} (ha : 0 < a) (k : ℤ) :
    (k : ℝ) * Real.pi / a < ((k : ℝ) + 1 / 2) * Real.pi / a ∧
      ((k : ℝ) + 1 / 2) * Real.pi / a < ((k : ℝ) + 1) * Real.pi / a := by
  have hpi := Real.pi_pos
  constructor
  · exact (div_lt_div_iff_of_pos_right ha).mpr (by nlinarith)
  · exact (div_lt_div_iff_of_pos_right ha).mpr (by nlinarith)

/-- **The centre lies in the odd spectrum only.**  The sine vanishes at the origin and the cosine
does not, which is the parity clause of the interlacing. -/
theorem freeCentre_odd_not_even (a : ℝ) :
    Complex.sin ((0 : ℂ) * a) = 0 ∧ Complex.cos ((0 : ℂ) * a) ≠ 0 := by
  constructor
  · rw [zero_mul, Complex.sin_zero]
  · rw [zero_mul, Complex.cos_zero]
    exact one_ne_zero

/-! ## The free measure

The free spectrum is a strictly monotone family of labels, so it carries a labelled atomic measure
whose mass at each atom is the constant weight.  That is `(16)`: the free Nevanlinna measure is
`coth(a)/a` times the counting measure on the quarter-period frequencies. -/

/-- The quarter-period frequencies are strictly increasing in the index, hence distinct. -/
theorem freeEvenSpectrum_strictMono {a : ℝ} (ha : 0 < a) :
    StrictMono fun k : ℤ => ((k : ℝ) + 1 / 2) * Real.pi / a := by
  intro j k hjk
  have hpi := Real.pi_pos
  refine (div_lt_div_iff_of_pos_right ha).mpr ?_
  have : (j : ℝ) < k := by exact_mod_cast hjk
  nlinarith

theorem freeEvenSpectrum_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective fun k : ℤ => ((k : ℝ) + 1 / 2) * Real.pi / a :=
  (freeEvenSpectrum_strictMono ha).injective

/-- **`(16)`, the free measure.**  The labelled measure carrying the constant weight `coth(a)/a` at
the quarter-period frequencies assigns exactly that mass to each of them. -/
theorem freeMeasure_singleton {a : ℝ} (ha : 0 < a) (k : ℤ) :
    labelledMeasure (fun _ : ℤ => ENNReal.ofReal (Real.cosh a / (a * Real.sinh a)))
        (fun j : ℤ => ((j : ℝ) + 1 / 2) * Real.pi / a)
        {((k : ℝ) + 1 / 2) * Real.pi / a}
      = ENNReal.ofReal (Real.cosh a / (a * Real.sinh a)) :=
  labelledMeasure_singleton (freeEvenSpectrum_injective ha) k

end GaloisForLFunctions.HTGeometry
