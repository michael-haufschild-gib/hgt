import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The cosh quartet envelope

For a nonzero real displacement `a`, the product

`cosh (z - a) * cosh (z + a)`

is an entire, real-even, `π i`-periodic envelope.  Its zeros form two explicit vertical lattices,
while its restriction to the imaginary axis is a strictly positive real norm square.  Thus one
object simultaneously realizes the quartet symmetries, the displaced lattice, and global
imaginary-axis positivity.
-/

open Complex

namespace RHTower

noncomputable section

/-- The zeros of complex `cosh` are the odd half-integer multiples of `-π i`. -/
theorem cosh_eq_zero_iff_exists_int {z : ℂ} :
    Complex.cosh z = 0 ↔
      ∃ k : ℤ, z = -((2 * k + 1 : ℂ) * Real.pi / 2) * I := by
  rw [← Complex.cos_mul_I, Complex.cos_eq_zero_iff]
  apply exists_congr
  intro k
  constructor
  · intro h
    calc
      z = -z * (I * I) := by simp
      _ = -(z * I) * I := by ring
      _ = -((2 * k + 1 : ℂ) * Real.pi / 2) * I := by rw [h]
  · intro h
    rw [h]
    calc
      (-((2 * k + 1 : ℂ) * Real.pi / 2) * I) * I =
          -((2 * k + 1 : ℂ) * Real.pi / 2) * (I * I) := by ring
      _ = (2 * k + 1 : ℂ) * Real.pi / 2 := by simp

/-- A nonzero real part places a point outside the zero lattice of `cosh`. -/
theorem cosh_ne_zero_of_re_ne_zero {z : ℂ} (hz : z.re ≠ 0) :
    Complex.cosh z ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := cosh_eq_zero_iff_exists_int.mp hzero
  have hre := congrArg Complex.re hk
  simp at hre
  exact hz hre

/-- The unit level set of complex `cosh` is the integral `2π i` lattice. -/
theorem cosh_eq_one_iff_exists_int {z : ℂ} :
    Complex.cosh z = 1 ↔ ∃ k : ℤ, z = (k : ℂ) * (2 * Real.pi * I) := by
  constructor
  · intro h
    have hw : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
    rw [Complex.cosh, Complex.exp_neg] at h
    have hsquare : (Complex.exp z - 1) ^ (2 : ℕ) = 0 := by
      field_simp [hw] at h
      linear_combination h
    have hexp : Complex.exp z = 1 := by
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    exact Complex.exp_eq_one_iff.mp hexp
  · rintro ⟨k, hk⟩
    have hexp : Complex.exp z = 1 := Complex.exp_eq_one_iff.mpr ⟨k, hk⟩
    rw [Complex.cosh, Complex.exp_neg, hexp]
    norm_num

/-- Entire quartet envelope with two zero lattices displaced symmetrically from the imaginary
axis. -/
def coshQuartetEnvelope (a : ℝ) (z : ℂ) : ℂ :=
  Complex.cosh (z - (a : ℂ)) * Complex.cosh (z + (a : ℂ))

/-- The cosh quartet envelope is entire. -/
theorem coshQuartetEnvelope_analyticAt (a : ℝ) (z : ℂ) :
    AnalyticAt ℂ (coshQuartetEnvelope a) z := by
  apply AnalyticAt.mul
  · exact Complex.analyticAt_cosh.comp (analyticAt_id.sub analyticAt_const)
  · exact Complex.analyticAt_cosh.comp (analyticAt_id.add analyticAt_const)

/-- The cosh quartet envelope is even. -/
theorem coshQuartetEnvelope_neg (a : ℝ) (z : ℂ) :
    coshQuartetEnvelope a (-z) = coshQuartetEnvelope a z := by
  rw [coshQuartetEnvelope, coshQuartetEnvelope]
  rw [show -z - (a : ℂ) = -(z + (a : ℂ)) by ring,
    show -z + (a : ℂ) = -(z - (a : ℂ)) by ring,
    Complex.cosh_neg, Complex.cosh_neg]
  ring

/-- The cosh quartet envelope is Schwarz-real. -/
theorem coshQuartetEnvelope_conj (a : ℝ) (z : ℂ) :
    coshQuartetEnvelope a ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (coshQuartetEnvelope a z) := by
  rw [coshQuartetEnvelope, coshQuartetEnvelope, map_mul,
    ← Complex.cosh_conj, ← Complex.cosh_conj]
  congr 2 <;> simp

/-- The sign changes of the two cosh factors cancel, giving period `π i`. -/
theorem coshQuartetEnvelope_add_pi_mul_I (a : ℝ) (z : ℂ) :
    coshQuartetEnvelope a (z + Real.pi * I) = coshQuartetEnvelope a z := by
  rw [coshQuartetEnvelope, coshQuartetEnvelope]
  rw [show z + Real.pi * I - (a : ℂ) = (z - (a : ℂ)) + Real.pi * I by ring,
    show z + Real.pi * I + (a : ℂ) = (z + (a : ℂ)) + Real.pi * I by ring,
    Complex.cosh_add_pi_mul_I, Complex.cosh_add_pi_mul_I]
  ring

/-- Product-to-sum identity exposing the single hyperbolic frequency of the envelope. -/
theorem two_mul_coshQuartetEnvelope (a : ℝ) (z : ℂ) :
    2 * coshQuartetEnvelope a z =
      Complex.cosh (2 * z) + Complex.cosh (2 * (a : ℂ)) := by
  rw [coshQuartetEnvelope]
  have hadd := Complex.cosh_add (z - (a : ℂ)) (z + (a : ℂ))
  have hsub := Complex.cosh_sub (z + (a : ℂ)) (z - (a : ℂ))
  calc
    2 * (Complex.cosh (z - (a : ℂ)) * Complex.cosh (z + (a : ℂ))) =
        Complex.cosh ((z - (a : ℂ)) + (z + (a : ℂ))) +
          Complex.cosh ((z + (a : ℂ)) - (z - (a : ℂ))) := by
            rw [hadd, hsub]
            ring
    _ = Complex.cosh (2 * z) + Complex.cosh (2 * (a : ℂ)) := by congr 1 <;> ring_nf

/-- **Complete period classification.** The period group of every cosh quartet envelope is exactly
`π i ℤ`. -/
theorem coshQuartetEnvelope_periodic_iff (a : ℝ) (h : ℂ) :
    Function.Periodic (coshQuartetEnvelope a) h ↔
      ∃ k : ℤ, h = (k : ℂ) * (Real.pi * I) := by
  constructor
  · intro hperiod
    have hvalue := hperiod 0
    have hscaled : Complex.cosh (2 * h) = 1 := by
      have hleft := two_mul_coshQuartetEnvelope a h
      have hzero := two_mul_coshQuartetEnvelope a 0
      rw [show coshQuartetEnvelope a h = coshQuartetEnvelope a 0 by
        simpa using hvalue] at hleft
      have heq := hleft.symm.trans hzero
      have hcancel : Complex.cosh (2 * h) = Complex.cosh (2 * 0) :=
        add_right_cancel heq
      simpa using hcancel
    obtain ⟨k, hk⟩ := cosh_eq_one_iff_exists_int.mp hscaled
    refine ⟨k, ?_⟩
    calc
      h = (2 : ℂ)⁻¹ * (2 * h) := by ring
      _ = (2 : ℂ)⁻¹ * ((k : ℂ) * (2 * Real.pi * I)) := by rw [hk]
      _ = (k : ℂ) * (Real.pi * I) := by ring
  · rintro ⟨k, rfl⟩
    have hbase : Function.Periodic (coshQuartetEnvelope a) (Real.pi * I) :=
      coshQuartetEnvelope_add_pi_mul_I a
    exact hbase.int_mul k

/-- On the imaginary axis the envelope is exactly a real norm square. -/
theorem coshQuartetEnvelope_mul_I_ofReal (a y : ℝ) :
    coshQuartetEnvelope a ((y : ℂ) * I) =
      ((Complex.normSq (Complex.cosh ((a : ℂ) + (y : ℂ) * I)) : ℝ) : ℂ) := by
  rw [coshQuartetEnvelope]
  have hleft : Complex.cosh ((y : ℂ) * I - (a : ℂ)) =
      (starRingEnd ℂ) (Complex.cosh ((a : ℂ) + (y : ℂ) * I)) := by
    rw [show (y : ℂ) * I - (a : ℂ) = -((a : ℂ) - (y : ℂ) * I) by ring,
      Complex.cosh_neg, ← Complex.cosh_conj]
    congr 1
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hleft]
  rw [show (y : ℂ) * I + (a : ℂ) = (a : ℂ) + (y : ℂ) * I by ring]
  rw [mul_comm, Complex.mul_conj]

/-- Every nontrivially displaced cosh quartet envelope is strictly positive real on the entire
imaginary axis. -/
theorem coshQuartetEnvelope_mul_I_pos_real {a y : ℝ} (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ coshQuartetEnvelope a ((y : ℂ) * I) = (r : ℂ) := by
  let z : ℂ := (a : ℂ) + (y : ℂ) * I
  have hzre : z.re ≠ 0 := by simp [z, ha]
  have hcosh : Complex.cosh z ≠ 0 := cosh_ne_zero_of_re_ne_zero hzre
  refine ⟨Complex.normSq (Complex.cosh z), Complex.normSq_pos.mpr hcosh, ?_⟩
  exact coshQuartetEnvelope_mul_I_ofReal a y

/-- The complete realizable zero set is the union of two vertical odd-half-integer lattices. -/
theorem coshQuartetEnvelope_eq_zero_iff {a : ℝ} {z : ℂ} :
    coshQuartetEnvelope a z = 0 ↔
      (∃ k : ℤ, z = (a : ℂ) - ((2 * k + 1 : ℂ) * Real.pi / 2) * I) ∨
      (∃ k : ℤ, z = -(a : ℂ) - ((2 * k + 1 : ℂ) * Real.pi / 2) * I) := by
  rw [coshQuartetEnvelope, mul_eq_zero,
    cosh_eq_zero_iff_exists_int, cosh_eq_zero_iff_exists_int]
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · left
      refine ⟨k, ?_⟩
      calc
        z = (z - (a : ℂ)) + (a : ℂ) := by ring
        _ = -((2 * k + 1 : ℂ) * Real.pi / 2) * I + (a : ℂ) := by rw [hk]
        _ = (a : ℂ) - ((2 * k + 1 : ℂ) * Real.pi / 2) * I := by ring
    · right
      refine ⟨k, ?_⟩
      calc
        z = (z + (a : ℂ)) - (a : ℂ) := by ring
        _ = -((2 * k + 1 : ℂ) * Real.pi / 2) * I - (a : ℂ) := by rw [hk]
        _ = -(a : ℂ) - ((2 * k + 1 : ℂ) * Real.pi / 2) * I := by ring
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · left
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    · right
      refine ⟨k, ?_⟩
      rw [hk]
      ring

/-- **Positive realizability package.** For every nonzero real displacement, one entire function
simultaneously realizes evenness, Schwarz reality, period `π i`, strict imaginary-axis positivity,
and exactly the two displaced vertical zero lattices. -/
theorem exists_entire_quartet_envelope_realizer (a : ℝ) (ha : a ≠ 0) :
    ∃ F : ℂ → ℂ,
      (∀ z, AnalyticAt ℂ F z) ∧
      (∀ z, F (-z) = F z) ∧
      (∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z)) ∧
      (∀ h, Function.Periodic F h ↔ ∃ k : ℤ, h = (k : ℂ) * (Real.pi * I)) ∧
      (∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ F ((y : ℂ) * I) = (r : ℂ)) ∧
      (∀ z, F z = 0 ↔
        (∃ k : ℤ, z = (a : ℂ) - ((2 * k + 1 : ℂ) * Real.pi / 2) * I) ∨
        (∃ k : ℤ, z = -(a : ℂ) - ((2 * k + 1 : ℂ) * Real.pi / 2) * I)) := by
  refine ⟨coshQuartetEnvelope a,
    coshQuartetEnvelope_analyticAt a,
    coshQuartetEnvelope_neg a,
    coshQuartetEnvelope_conj a,
    coshQuartetEnvelope_periodic_iff a,
    fun y => coshQuartetEnvelope_mul_I_pos_real ha,
    fun z => coshQuartetEnvelope_eq_zero_iff⟩

end

end RHTower
