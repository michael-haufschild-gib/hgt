import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

/-- **The endpoint atom coefficients of an exponential edge pair.**  Zero-extending `exp` and
`exp ∘ neg` from `[-a, a]` puts atoms at both endpoints; paired against a test value the two
contributions combine into `2 cosh a` times the endpoint difference.

This is the coefficient of `(4)`'s limit atom pair, in the test-function form that integration by
parts supplies: the boundary term of `∫ f' φ = [f φ] - ∫ f φ'`. -/
theorem exponentialEdge_atomCoefficients (a : ℝ) (phi : ℝ → ℝ) :
    (Real.exp (-a) * phi (-a) - Real.exp a * phi a)
        + (Real.exp a * phi (-a) - Real.exp (-a) * phi a)
      = 2 * Real.cosh a * (phi (-a) - phi a) := by
  rw [Real.cosh_eq]
  ring

/-- The same coefficient identity read against the signed atom pair `delta_{-a} - delta_a`: the
combined edge contribution is `2 cosh a` times that pair. -/
theorem integral_exponentialEdge_atomPair (a : ℝ) (phi : ℝ → ℝ) :
    (Real.exp (-a) * phi (-a) - Real.exp a * phi a)
        + (Real.exp a * phi (-a) - Real.exp (-a) * phi a)
      = 2 * Real.cosh a *
        ((∫ y, phi y ∂(Measure.dirac (-a))) - ∫ y, phi y ∂(Measure.dirac a)) := by
  rw [integral_dirac, integral_dirac]
  exact exponentialEdge_atomCoefficients a phi

/-- **Endpoint atoms of the zero-extended exponential, in test-function form.**  Pairing the
distributional derivative of `exp` restricted to `[-a, a]` against a `C^1` test function is the
interior integral plus the two endpoint atoms `exp(-a) delta_{-a} - exp a * delta_a`.

Integration by parts *is* that statement: no distribution theory is needed to say it, only the
boundary term of `∫ u v' = [u v] - ∫ u' v`. -/
theorem neg_integral_exp_mul_deriv (a : ℝ) {phi phi' : ℝ → ℝ}
    (hphi : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt phi (phi' x) x)
    (hphi'int : IntervalIntegrable phi' volume (-a) a) :
    -(∫ x in (-a)..a, Real.exp x * phi' x)
      = (∫ x in (-a)..a, Real.exp x * phi x)
        + (Real.exp (-a) * phi (-a) - Real.exp a * phi a) := by
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := Real.exp) (u' := Real.exp) (v := phi) (v' := phi')
    (fun x _ => Real.hasDerivAt_exp x) hphi
    (Real.continuous_exp.intervalIntegrable _ _) hphi'int
  linarith [hIBP]

/-- The reflected edge.  Zero-extending `x ↦ exp (-x)` from `[-a, a]` puts the atoms
`exp a * delta_{-a} - exp (-a) * delta_a` at the endpoints. -/
theorem neg_integral_expNeg_mul_deriv (a : ℝ) {phi phi' : ℝ → ℝ}
    (hphi : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt phi (phi' x) x)
    (hphi'int : IntervalIntegrable phi' volume (-a) a) :
    -(∫ x in (-a)..a, Real.exp (-x) * phi' x)
      = (∫ x in (-a)..a, -Real.exp (-x) * phi x)
        + (Real.exp a * phi (-a) - Real.exp (-a) * phi a) := by
  have hu : ∀ x ∈ Set.uIcc (-a) a,
      HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    intro x _
    simpa using ((hasDerivAt_id x).neg).exp
  have hu'int : IntervalIntegrable (fun x : ℝ => -Real.exp (-x)) volume (-a) a := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => Real.exp (-y)) (u' := fun y : ℝ => -Real.exp (-y))
    (v := phi) (v' := phi') hu hphi hu'int hphi'int
  simp only [neg_neg] at hIBP
  linarith [hIBP]

/-- **The limit pairing of the odd source combination.**  Pairing `v' - v` on the `exp` edge and
`v' + v` on the `exp (-·)` edge against a `C^1` test function makes **every interior term cancel**,
leaving exactly the endpoint atom pair with coefficient `2 cosh a`.

This is the mechanism behind the card's "interior terms cancel for limiting exponentials": the
integration-by-parts interior term of each edge is cancelled by that edge's own zeroth-order term,
with the sign pattern of the combination doing the cancelling. -/
theorem exponentialSourceCombination_pairing (a : ℝ) {phi phi' : ℝ → ℝ}
    (hphi : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt phi (phi' x) x)
    (hphi'int : IntervalIntegrable phi' volume (-a) a) :
    (-(∫ x in (-a)..a, Real.exp x * phi' x) - ∫ x in (-a)..a, Real.exp x * phi x)
        + (-(∫ x in (-a)..a, Real.exp (-x) * phi' x)
            + ∫ x in (-a)..a, Real.exp (-x) * phi x)
      = 2 * Real.cosh a * (phi (-a) - phi a) := by
  have h1 := neg_integral_exp_mul_deriv a hphi hphi'int
  have h2 := neg_integral_expNeg_mul_deriv a hphi hphi'int
  have hneg : (∫ x in (-a)..a, -Real.exp (-x) * phi x)
      = -∫ x in (-a)..a, Real.exp (-x) * phi x := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [hneg] at h2
  rw [h1, h2]
  have hc := exponentialEdge_atomCoefficients a phi
  linarith [hc]

/-- **The normalized edge quotient converges.**  If the numerator and denominator of the physical
edge quotient converge to the central-jet values, the Weyl-normalized quotient converges to the
aperture average `H (2a) / (2a)`.  This is the passage from the two central-jet limits to the
normalized limit, with the `-i` normalization algebra supplied by `normalizedEdgeRatio`. -/
theorem tendsto_normalizedEdgeQuotient {α : Type*} {l : Filter α} {T W : α → ℂ} {a : ℝ}
    {c H2a : ℂ}
    (ha : (a : ℂ) ≠ 0) (hc : c ≠ 0)
    (hnum : Filter.Tendsto T l (nhds (I * (2 * c) * H2a)))
    (hden : Filter.Tendsto W l (nhds (4 * (a : ℂ) * c))) :
    Filter.Tendsto (fun lam => -I * (T lam / W lam)) l
      (nhds (H2a / (2 * (a : ℂ)))) := by
  have hne : (4 * (a : ℂ) * c) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha) hc
  have hquot := hnum.div hden hne
  have hmul := (tendsto_const_nhds (x := -I) (f := l)).mul hquot
  rwa [normalizedEdgeRatio ha hc] at hmul

/-- **The numerator value equation `(7)`, in integral form.**  Pairing the exponential source
combination against the reflected primitive `y => H (a - y)` gives `2 cosh a * H (2a)`: the interior
terms cancel, the endpoint atoms at `-a` and `a` contribute `H (2a)` and `H 0`, and `H 0 = 0`
removes the second.

This is the numerator companion of `integral_edgeDenominatorSum`, and together with it supplies
both value equations of the normalized edge quotient. -/
theorem exponentialSourceCombination_primitive_pairing (a : ℝ) {H H' : ℝ → ℝ}
    (hH : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt (fun y => H (a - y)) (-(H' (a - x))) x)
    (hint : IntervalIntegrable (fun x => -(H' (a - x))) volume (-a) a)
    (hH0 : H 0 = 0) :
    (-(∫ x in (-a)..a, Real.exp x * -(H' (a - x))) - ∫ x in (-a)..a, Real.exp x * H (a - x))
        + (-(∫ x in (-a)..a, Real.exp (-x) * -(H' (a - x)))
            + ∫ x in (-a)..a, Real.exp (-x) * H (a - x))
      = 2 * Real.cosh a * H (2 * a) := by
  have h := exponentialSourceCombination_pairing a (phi := fun y => H (a - y))
    (phi' := fun x => -(H' (a - x))) hH hint
  rw [h, show a - -a = 2 * a by ring, sub_self, hH0, sub_zero]

end

end GaloisForLFunctions.HTGeometry
