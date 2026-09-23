import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Harmonic modes on the affine Kummer leaf cylinder

On the leaf cylinder `(0, ∞) × T` the leafwise Hodge equations, restricted to the character of
frequency `μ`, are the two-term system `b' = i μ a`, `a' = -i μ b`.  For `μ ≠ 0` it has the
decaying solution

`α_μ (r) = e^{-|μ| r} (dr - i ε dy)`,  `ε = sgn μ`,

which is closed, coclosed, of definite chirality `*α = i ε α`, and square integrable with squared
norm `1 / |μ|`.

Coefficients of leafwise one-forms are complex pairs: the Hodge star is the quarter turn and the
wedge is the determinant, so the chirality equation is the eigenvalue equation of the star, whose
eigenvalues are `± i`.

* `deningerCxStar`, `deningerCxWedge` : the complex leafwise star and wedge.
* `deningerMode` : the decaying chiral mode.
* `deningerMode_closed`, `deningerMode_coclosed` : the leafwise Hodge equations.
* `deningerMode_chirality` : definite chirality.
* `deningerMode_normSq` : the squared norm `1 / |μ|`.
* `deningerMode_scale` : the radial scaling law behind the power correspondence.
-/

namespace RHTower

open MeasureTheory Set

section LeafwiseAlgebra

/-- The leafwise Hodge star on complex one-form coefficient pairs: `*dr = dy`, `*dy = -dr`. -/
def deningerCxStar (a : ℂ × ℂ) : ℂ × ℂ := (-a.2, a.1)

/-- The wedge coefficient of two complex leafwise one-forms. -/
def deningerCxWedge (a b : ℂ × ℂ) : ℂ := a.1 * b.2 - a.2 * b.1

theorem deningerCxStar_star (a : ℂ × ℂ) : deningerCxStar (deningerCxStar a) = -a := by
  rcases a with ⟨x, y⟩
  simp [deningerCxStar, Prod.neg_mk]

theorem deningerCxWedge_antisymm (a b : ℂ × ℂ) :
    deningerCxWedge a b = -deningerCxWedge b a := by
  rw [deningerCxWedge, deningerCxWedge]
  ring

theorem deningerCxWedge_self (a : ℂ × ℂ) : deningerCxWedge a a = 0 := by
  rw [deningerCxWedge]
  ring

theorem deningerCxWedge_smul_left (c : ℂ) (a b : ℂ × ℂ) :
    deningerCxWedge (c • a) b = c * deningerCxWedge a b := by
  rcases a with ⟨x, y⟩
  rcases b with ⟨z, w⟩
  simp only [deningerCxWedge, Prod.smul_mk, smul_eq_mul]
  ring

theorem deningerCxWedge_smul_right (c : ℂ) (a b : ℂ × ℂ) :
    deningerCxWedge a (c • b) = c * deningerCxWedge a b := by
  rcases a with ⟨x, y⟩
  rcases b with ⟨z, w⟩
  simp only [deningerCxWedge, Prod.smul_mk, smul_eq_mul]
  ring

end LeafwiseAlgebra

section Sign

/-- The sign of a frequency. -/
noncomputable def deningerFreqSign (μ : ℝ) : ℝ := if 0 < μ then 1 else -1

theorem deningerFreqSign_sq (μ : ℝ) : deningerFreqSign μ * deningerFreqSign μ = 1 := by
  rw [deningerFreqSign]
  split_ifs <;> norm_num

/-- The sign times the absolute value is the frequency. -/
theorem deningerFreqSign_mul_abs {μ : ℝ} (hμ : μ ≠ 0) : deningerFreqSign μ * |μ| = μ := by
  rw [deningerFreqSign]
  rcases lt_trichotomy μ 0 with h | h | h
  · rw [if_neg (not_lt.mpr h.le), abs_of_neg h]
    ring
  · exact absurd h hμ
  · rw [if_pos h, abs_of_pos h]
    ring

/-- The absolute value in terms of the sign. -/
theorem deningerFreqSign_abs {μ : ℝ} (hμ : μ ≠ 0) : |μ| = deningerFreqSign μ * μ := by
  calc |μ| = 1 * |μ| := (one_mul _).symm
    _ = (deningerFreqSign μ * deningerFreqSign μ) * |μ| := by rw [deningerFreqSign_sq]
    _ = deningerFreqSign μ * (deningerFreqSign μ * |μ|) := by ring
    _ = deningerFreqSign μ * μ := by rw [deningerFreqSign_mul_abs hμ]

theorem deningerFreqSign_neg {μ : ℝ} (hμ : μ ≠ 0) :
    deningerFreqSign (-μ) = -deningerFreqSign μ := by
  rw [deningerFreqSign, deningerFreqSign]
  rcases lt_trichotomy μ 0 with h | h | h
  · rw [if_neg (not_lt.mpr h.le), if_pos (neg_pos.mpr h)]
    norm_num
  · exact absurd h hμ
  · rw [if_pos h, if_neg (not_lt.mpr (neg_nonpos.mpr h.le))]

theorem deningerFreqSign_pos_mul {q μ : ℝ} (hq : 0 < q) :
    deningerFreqSign (q * μ) = deningerFreqSign μ := by
  rw [deningerFreqSign, deningerFreqSign]
  by_cases h : 0 < μ
  · rw [if_pos h, if_pos (mul_pos hq h)]
  · rw [if_neg h, if_neg]
    intro hc
    have hle : μ ≤ 0 := not_lt.mp h
    nlinarith

end Sign

section Mode

/-- The radial profile `e^{-|μ| r}` of the decaying mode. -/
noncomputable def deningerModeProfile (μ : ℝ) (r : ℝ) : ℝ := Real.exp (-|μ| * r)

theorem deningerModeProfile_pos (μ r : ℝ) : 0 < deningerModeProfile μ r := Real.exp_pos _

theorem deningerModeProfile_hasDerivAt (μ r : ℝ) :
    HasDerivAt (deningerModeProfile μ) (deningerModeProfile μ r * -|μ|) r := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (-|μ| * x))
      (Real.exp (-|μ| * r) * -|μ|) r := by
    simpa using ((hasDerivAt_id r).const_mul (-|μ|)).exp
  exact h

/-- **The decaying chiral mode** `α_μ (r) = e^{-|μ| r} (dr - i ε dy)`, as the pair of its
leafwise coefficients. -/
noncomputable def deningerMode (μ : ℝ) (r : ℝ) : ℂ × ℂ :=
  ((deningerModeProfile μ r : ℂ),
    -(Complex.I * (deningerFreqSign μ : ℂ)) * (deningerModeProfile μ r : ℂ))

@[simp] theorem deningerMode_fst (μ r : ℝ) :
    (deningerMode μ r).1 = (deningerModeProfile μ r : ℂ) := rfl

@[simp] theorem deningerMode_snd (μ r : ℝ) :
    (deningerMode μ r).2
      = -(Complex.I * (deningerFreqSign μ : ℂ)) * (deningerModeProfile μ r : ℂ) := rfl

/-- **The mode is coclosed**: `a' + i μ b = 0`. -/
theorem deningerMode_coclosed {μ : ℝ} (hμ : μ ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => (deningerMode μ r).1)
      (-(Complex.I * (μ : ℂ) * (deningerMode μ r).2)) r := by
  have h : HasDerivAt (fun r => ((deningerModeProfile μ r : ℝ) : ℂ))
      ((deningerModeProfile μ r * -|μ| : ℝ) : ℂ) r :=
    (deningerModeProfile_hasDerivAt μ r).ofReal_comp
  have hval : ((deningerModeProfile μ r * -|μ| : ℝ) : ℂ)
      = -(Complex.I * (μ : ℂ) * (deningerMode μ r).2) := by
    rw [deningerMode_snd, deningerFreqSign_abs hμ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← hval]
  exact h

/-- **The mode is closed**: `b' - i μ a = 0`. -/
theorem deningerMode_closed {μ : ℝ} (hμ : μ ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => (deningerMode μ r).2)
      (Complex.I * (μ : ℂ) * (deningerMode μ r).1) r := by
  have h : HasDerivAt (fun r => ((deningerModeProfile μ r : ℝ) : ℂ))
      ((deningerModeProfile μ r * -|μ| : ℝ) : ℂ) r :=
    (deningerModeProfile_hasDerivAt μ r).ofReal_comp
  have h2 := h.const_mul (-(Complex.I * (deningerFreqSign μ : ℂ)))
  have hval : -(Complex.I * (deningerFreqSign μ : ℂ))
        * ((deningerModeProfile μ r * -|μ| : ℝ) : ℂ)
      = Complex.I * (μ : ℂ) * (deningerMode μ r).1 := by
    have hsq : (deningerFreqSign μ : ℂ) * (deningerFreqSign μ : ℂ) = 1 := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_sq μ)
    rw [deningerMode_fst, deningerFreqSign_abs hμ]
    push_cast
    linear_combination (Complex.I * (μ : ℂ) * (deningerModeProfile μ r : ℂ)) * hsq
  rw [← hval]
  exact h2

/-- **The mode has definite chirality**: `*α = i ε α`. -/
theorem deningerMode_chirality (μ : ℝ) (r : ℝ) :
    deningerCxStar (deningerMode μ r)
      = (Complex.I * (deningerFreqSign μ : ℂ)) • deningerMode μ r := by
  have hsq : (deningerFreqSign μ : ℂ) * (deningerFreqSign μ : ℂ) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_sq μ)
  refine Prod.ext ?_ ?_
  · show -(-(Complex.I * (deningerFreqSign μ : ℂ)) * (deningerModeProfile μ r : ℂ))
        = Complex.I * (deningerFreqSign μ : ℂ) * (deningerModeProfile μ r : ℂ)
    ring
  · show (deningerModeProfile μ r : ℂ)
        = Complex.I * (deningerFreqSign μ : ℂ)
            * (-(Complex.I * (deningerFreqSign μ : ℂ)) * (deningerModeProfile μ r : ℂ))
    have hI : Complex.I ^ (2 : ℕ) = -1 := Complex.I_sq
    calc (deningerModeProfile μ r : ℂ)
        = (-(Complex.I ^ (2 : ℕ))) * ((deningerFreqSign μ : ℂ) * (deningerFreqSign μ : ℂ))
            * (deningerModeProfile μ r : ℂ) := by rw [hI, hsq]; ring
      _ = Complex.I * (deningerFreqSign μ : ℂ)
            * (-(Complex.I * (deningerFreqSign μ : ℂ)) * (deningerModeProfile μ r : ℂ)) := by
          ring

/-- The pointwise squared length of the mode is twice the squared profile. -/
theorem deningerMode_pointwise_normSq (μ : ℝ) (r : ℝ) :
    ‖(deningerMode μ r).1‖ ^ (2 : ℕ) + ‖(deningerMode μ r).2‖ ^ (2 : ℕ)
      = 2 * deningerModeProfile μ r ^ (2 : ℕ) := by
  have hprof : ‖((deningerModeProfile μ r : ℝ) : ℂ)‖ = deningerModeProfile μ r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (deningerModeProfile_pos μ r)]
  have hsign : ‖(deningerFreqSign μ : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, deningerFreqSign]
    split_ifs <;> norm_num
  rw [deningerMode_fst, deningerMode_snd, norm_mul, norm_neg, norm_mul, Complex.norm_I,
    hsign, hprof]
  ring

/-- The radial integral of the squared profile. -/
theorem deningerModeProfile_integral {μ : ℝ} (hμ : μ ≠ 0) :
    ∫ r in Ioi (0 : ℝ), deningerModeProfile μ r ^ (2 : ℕ) = 1 / (2 * |μ|) := by
  have hpos : (0 : ℝ) < 2 * |μ| := by positivity
  have hsq : ∀ r : ℝ, deningerModeProfile μ r ^ (2 : ℕ) = Real.exp (-((2 * |μ|) * r)) := by
    intro r
    rw [deningerModeProfile, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun r _ => hsq r]
  have hcomp := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 hpos
  rw [show (fun x : ℝ => Real.exp (-((2 * |μ|) * x)))
      = fun x : ℝ => (fun y : ℝ => Real.exp (-y)) ((2 * |μ|) * x) from rfl, hcomp,
    mul_zero, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, smul_eq_mul, mul_one, one_div]

/-- **The squared norm of the mode is `1 / |μ|`.** -/
theorem deningerMode_normSq {μ : ℝ} (hμ : μ ≠ 0) :
    ∫ r in Ioi (0 : ℝ), (‖(deningerMode μ r).1‖ ^ (2 : ℕ) + ‖(deningerMode μ r).2‖ ^ (2 : ℕ))
      = 1 / |μ| := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    fun r _ => deningerMode_pointwise_normSq μ r, integral_const_mul,
    deningerModeProfile_integral hμ]
  have habs : |μ| ≠ 0 := abs_ne_zero.mpr hμ
  field_simp

/-- **The radial scaling law.**  Rescaling the radius by `q` is the same as scaling the frequency,
which is why the power correspondence sends the mode of `a` to the mode of `q a`. -/
theorem deningerMode_scale {μ q : ℝ} (hq : 0 < q) (r : ℝ) :
    deningerMode μ (q * r) = deningerMode (q * μ) r := by
  have hprof : deningerModeProfile μ (q * r) = deningerModeProfile (q * μ) r := by
    rw [deningerModeProfile, deningerModeProfile, abs_mul, abs_of_pos hq]
    congr 1
    ring
  rw [deningerMode, deningerMode, hprof, deningerFreqSign_pos_mul hq]

end Mode

end RHTower
