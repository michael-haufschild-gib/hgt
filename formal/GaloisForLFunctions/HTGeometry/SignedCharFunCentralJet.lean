import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# The central jet of a signed characteristic function

A signed source on `ℝ` is presented as a difference of two finite measures; its characteristic
function is the corresponding difference of characteristic functions.  Two facts about it:

* its derivative at the origin is `I` times the first moment of the source;
* if the negative part is the reflection of the positive part, the characteristic is an **odd**
  function.

Both are read off from mathlib's `charFun` differentiation and reflection lemmas.  Oddness is the
hypothesis under which the odd part of a quotient by the characteristic collapses to the even part
of its numerator.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory

noncomputable section

/-- Characteristic function of a signed source presented as a difference of two finite measures. -/
def signedCharFun (mp mn : Measure ℝ) (t : ℝ) : ℂ := charFun mp t - charFun mn t

variable {mp mn : Measure ℝ} [IsFiniteMeasure mp] [IsFiniteMeasure mn]

theorem contDiff_signedCharFun (hp : MemLp id 1 mp) (hn : MemLp id 1 mn) :
    ContDiff ℝ 1 (signedCharFun mp mn) := by
  have hp' : MemLp id ((1 : ℕ) : ENNReal) mp := by simpa using hp
  have hn' : MemLp id ((1 : ℕ) : ENNReal) mn := by simpa using hn
  exact (contDiff_charFun hp').sub (contDiff_charFun hn')

/-- **Central jet of a signed characteristic.**  Its derivative at the origin is `I` times the
first moment of the signed source. -/
theorem deriv_signedCharFun_zero (hp : MemLp id 1 mp) (hn : MemLp id 1 mn) :
    deriv (signedCharFun mp mn) 0 = I * ((∫ x, x ∂mp) - ∫ x, x ∂mn) := by
  have hp' : MemLp id ((1 : ℕ) : ENNReal) mp := by simpa using hp
  have hn' : MemLp id ((1 : ℕ) : ENNReal) mn := by simpa using hn
  have hdp : DifferentiableAt ℝ (charFun mp) 0 :=
    ((contDiff_charFun hp').differentiable (by norm_num)) 0
  have hdn : DifferentiableAt ℝ (charFun mn) 0 :=
    ((contDiff_charFun hn').differentiable (by norm_num)) 0
  have hp1 := iteratedDeriv_charFun_zero (μ := mp) (n := 1) hp'
  have hn1 := iteratedDeriv_charFun_zero (μ := mn) (n := 1) hn'
  rw [iteratedDeriv_one] at hp1 hn1
  simp only [pow_one] at hp1 hn1
  have hfun : signedCharFun mp mn = charFun mp - charFun mn := rfl
  rw [hfun, deriv_sub hdp hdn, hp1, hn1]
  ring

/-- A source whose negative part is the reflection of its positive part has an **odd**
characteristic function. -/
theorem signedCharFun_reflected_odd (mp : Measure ℝ) (t : ℝ) :
    signedCharFun mp (mp.map (fun x : ℝ => -x)) (-t)
      = -signedCharFun mp (mp.map (fun x : ℝ => -x)) t := by
  have hmap : ∀ u : ℝ, charFun (mp.map (fun x : ℝ => -x)) u = charFun mp (-u) := by
    intro u
    have h := charFun_map_smul (μ := mp) (-1 : ℝ) u
    simpa using h
  simp only [signedCharFun, hmap, neg_neg]
  ring

/-! ## Endpoint atoms and the normalized edge ratio -/

/-- **Endpoint atom pairing.**  The signed pair of endpoint atoms `delta_{-a} - delta_a`, paired
against `y ↦ H (a - y)` for a primitive vanishing at the origin, returns the value of the primitive
at the full aperture. -/
theorem integral_endpointAtomPair (a : ℝ) (H : ℝ → ℂ) (hH0 : H 0 = 0) :
    (∫ y, H (a - y) ∂(Measure.dirac (-a))) - (∫ y, H (a - y) ∂(Measure.dirac a))
      = H (2 * a) := by
  rw [integral_dirac, integral_dirac, show a - -a = 2 * a by ring, sub_self, hH0, sub_zero]

/-- **Normalized edge ratio.**  Dividing the paired atom value by the central jet and applying the
Weyl normalization `q_norm = -I q_phys` returns the aperture average of the primitive: the two
factors of `I` cancel and the edge weight divides out. -/
theorem normalizedEdgeRatio {a : ℝ} (ha : (a : ℂ) ≠ 0) {c H2a : ℂ} (hc : c ≠ 0) :
    -I * ((I * (2 * c) * H2a) / (4 * (a : ℂ) * c)) = H2a / (2 * (a : ℂ)) := by
  have hI : I * I = -1 := Complex.I_mul_I
  rw [mul_div_assoc']
  have h1 : -I * (I * (2 * c) * H2a) = 2 * c * H2a := by
    linear_combination (-(2 * c * H2a)) * hI
  rw [h1]
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
