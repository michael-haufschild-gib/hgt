import GaloisForLFunctions.HTGeometry.FrullaniIntegral

/-!
# Regular generalized integers do not constrain the zeros

A Beurling generalized prime system is recorded, in the logarithmic coordinate `t = log u`, by a
positive density `w` on `(0, ∞)`; its zeta function is `exp (∫_0^∞ e^{-st} w t dt)`, and the poles
of that zeta in `Re s > 0` govern the generalized-integer counting function `N`.

For every `β ∈ (1/2, 1)`, every `γ ≠ 0` and every `θ > 0` this module constructs an explicit
positive density whose zeta function is the rational function

```
ζ(s) = ( (s - β)² + γ² ) · s^{A-1} / ( (s - 1) · (s - δ)^A ),        0 < δ < θ,
```

so that

* `ζ` has a **simple pole at `s = 1`** and no other singularity with `Re s > δ`; since `δ < θ` is
  arbitrarily small, the generalized integers satisfy `N(x) = ρ x + O(x^{θ})` for every `θ > 0`,
  which is *more* regularity than the Riemann hypothesis asserts for the rational integers;
* `ζ` **vanishes at `β ± iγ`**, a pair of points with real part `β > 1/2` that may be taken
  arbitrarily close to `1`.

So the size of `N(x) - ρ x` carries no information whatsoever about the location of the zeros: an
arbitrarily regular integer-counting function coexists with zeta zeros arbitrarily far to the right
of the critical line.

The density is

```
w(t) = ( e^t + A e^{δ t} - (A - 1) - 2 e^{β t} cos (γ t) ) / t,
```

with `A` a positive integer chosen large enough.  Its numerator vanishes at `t = 0` (the coefficient
count `1 + A - (A-1) - 2` is zero), so `w` is bounded near the origin and the system is locally
finite; nonnegativity comes from the derivative test, and the Laplace transform is three
applications of the Frullani integral.

All statements are unconditional.
-/

open MeasureTheory Set Filter Topology Complex GaloisForLFunctions.HTGeometry

namespace RHTower.BeurlingRegularIntegers

noncomputable section

/-! ## Choosing the compensating coefficient -/

/-- For `0 < δ < β < 1/2 < β < 1` there is a coefficient making the derivative of the density
numerator nonnegative on `[0, ∞)`.  Threshold: past `t₀ = log (2β)/(1-β)` the pole term `e^t`
already dominates `2β e^{βt}`; before it, the constant `A δ` does. -/
theorem exists_regularCoefficient {β δ : ℝ} (hδ0 : 0 < δ) (hβhalf : 1 / 2 < β) (hβ1 : β < 1) :
    ∃ A : ℝ, 0 < A ∧
      ∀ t : ℝ, 0 ≤ t → 2 * β * Real.exp (β * t) ≤ Real.exp t + A * δ * Real.exp (δ * t) := by
  have hβ0 : 0 < β := by linarith
  have h2β : 1 < 2 * β := by linarith
  have h1β : 0 < 1 - β := by linarith
  set t₀ : ℝ := Real.log (2 * β) / (1 - β) with ht₀
  have ht₀nonneg : 0 ≤ t₀ := by
    apply div_nonneg _ h1β.le
    exact Real.log_nonneg (by linarith)
  set C : ℝ := 2 * β * Real.exp (β * t₀) with hC
  have hCpos : 0 < C := by
    have := Real.exp_pos (β * t₀)
    positivity
  refine ⟨C / δ, by positivity, ?_⟩
  intro t ht
  rcases le_total t t₀ with hle | hge
  · -- before the threshold: the constant term suffices
    have h1 : 2 * β * Real.exp (β * t) ≤ C := by
      rw [hC]
      have : Real.exp (β * t) ≤ Real.exp (β * t₀) :=
        Real.exp_le_exp.mpr (by nlinarith)
      nlinarith [Real.exp_pos (β * t)]
    have h2 : C ≤ C / δ * δ * Real.exp (δ * t) := by
      have hCδ : C / δ * δ = C := by field_simp
      rw [hCδ]
      have : (1 : ℝ) ≤ Real.exp (δ * t) := Real.one_le_exp (by positivity)
      nlinarith
    have h3 : (0 : ℝ) < Real.exp t := Real.exp_pos t
    linarith
  · -- past the threshold: the pole term suffices
    have hkey : 2 * β * Real.exp (β * t) ≤ Real.exp t := by
      have hexp : 2 * β ≤ Real.exp ((1 - β) * t) := by
        have hlog : Real.log (2 * β) ≤ (1 - β) * t := by
          rw [div_le_iff₀ h1β] at hge
          simpa [mul_comm] using hge
        calc 2 * β = Real.exp (Real.log (2 * β)) := (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp ((1 - β) * t) := Real.exp_le_exp.mpr hlog
      calc 2 * β * Real.exp (β * t) ≤ Real.exp ((1 - β) * t) * Real.exp (β * t) := by
            nlinarith [Real.exp_pos (β * t)]
        _ = Real.exp t := by rw [← Real.exp_add]; ring_nf
    have : (0 : ℝ) ≤ C / δ * δ * Real.exp (δ * t) := by positivity
    linarith

/-! ## The density -/

/-- Numerator of the logarithmic-coordinate density. -/
def regularNumerator (β γ δ A t : ℝ) : ℝ :=
  Real.exp t + A * Real.exp (δ * t) - (A - 1) - 2 * Real.exp (β * t) * Real.cos (γ * t)

/-- The comparison numerator obtained by replacing `cos` by its maximum. -/
def regularNumeratorMajorant (β δ A t : ℝ) : ℝ :=
  Real.exp t + A * Real.exp (δ * t) - (A - 1) - 2 * Real.exp (β * t)

theorem regularNumeratorMajorant_le (β γ δ A t : ℝ) :
    regularNumeratorMajorant β δ A t ≤ regularNumerator β γ δ A t := by
  unfold regularNumeratorMajorant regularNumerator
  have hcos : Real.cos (γ * t) ≤ 1 := Real.cos_le_one _
  nlinarith [Real.exp_pos (β * t)]

theorem regularNumeratorMajorant_zero (β δ A : ℝ) :
    regularNumeratorMajorant β δ A 0 = 0 := by
  unfold regularNumeratorMajorant
  simp
  ring

theorem hasDerivAt_regularNumeratorMajorant (β δ A t : ℝ) :
    HasDerivAt (regularNumeratorMajorant β δ A)
      (Real.exp t + A * δ * Real.exp (δ * t) - 2 * β * Real.exp (β * t)) t := by
  have h1 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h2 : HasDerivAt (fun x : ℝ => A * Real.exp (δ * x)) (A * (δ * Real.exp (δ * t))) t := by
    have := ((Real.hasDerivAt_exp (δ * t)).comp t ((hasDerivAt_id t).const_mul δ))
    simpa [mul_comm] using this.const_mul A
  have h3 : HasDerivAt (fun x : ℝ => 2 * Real.exp (β * x)) (2 * (β * Real.exp (β * t))) t := by
    have := ((Real.hasDerivAt_exp (β * t)).comp t ((hasDerivAt_id t).const_mul β))
    simpa [mul_comm] using this.const_mul 2
  have h4 := ((h1.add h2).sub_const (A - 1)).sub h3
  refine h4.congr_deriv ?_
  ring

/-- **Nonnegativity of the density numerator.** -/
theorem regularNumerator_nonneg {β γ δ A : ℝ}
    (hA : ∀ t : ℝ, 0 ≤ t → 2 * β * Real.exp (β * t) ≤ Real.exp t + A * δ * Real.exp (δ * t))
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ regularNumerator β γ δ A t := by
  refine le_trans ?_ (regularNumeratorMajorant_le β γ δ A t)
  rw [← regularNumeratorMajorant_zero β δ A]
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun x hx => (hasDerivAt_regularNumeratorMajorant β δ A x).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_regularNumeratorMajorant β δ A x).differentiableAt.differentiableWithinAt)
    ?_ (Set.self_mem_Ici) (by simpa using ht) ht
  intro x hx
  rw [interior_Ici] at hx
  rw [(hasDerivAt_regularNumeratorMajorant β δ A x).deriv]
  have := hA x (le_of_lt hx)
  linarith

/-- Logarithmic-coordinate density of the generalized primes. -/
def regularDensity (β γ δ A t : ℝ) : ℝ := regularNumerator β γ δ A t / t

theorem regularDensity_nonneg {β γ δ A : ℝ}
    (hA : ∀ t : ℝ, 0 ≤ t → 2 * β * Real.exp (β * t) ≤ Real.exp t + A * δ * Real.exp (δ * t))
    {t : ℝ} (ht : 0 < t) : 0 ≤ regularDensity β γ δ A t :=
  div_nonneg (regularNumerator_nonneg hA ht.le) ht.le

/-! ## The Laplace transform -/

/-- Splitting of the weighted density into three Frullani integrands. -/
theorem cexp_mul_regularDensity (β γ δ : ℝ) (A : ℕ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    Complex.exp (-(s * t)) * (regularDensity β γ δ A t : ℂ) =
      (Complex.exp (-((s - 1) * t)) - Complex.exp (-((s - β - γ * I) * t))) / t +
      ((Complex.exp (-((s - δ) * t)) - Complex.exp (-((s - β + γ * I) * t))) / t +
        ((A : ℂ) - 1) *
          ((Complex.exp (-((s - δ) * t)) - Complex.exp (-(s * t))) / t)) := by
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have ecos : Complex.exp (((γ : ℂ) * (t : ℂ)) * I) + Complex.exp (-(((γ : ℂ) * (t : ℂ)) * I)) =
      2 * Complex.cos ((γ : ℂ) * (t : ℂ)) := by
    rw [Complex.exp_mul_I, show -(((γ : ℂ) * (t : ℂ)) * I) = (-((γ : ℂ) * (t : ℂ))) * I by ring,
      Complex.exp_mul_I]
    simp [Complex.cos_neg, Complex.sin_neg]
    ring
  have e1 : Complex.exp (-((s - (β : ℂ) - (γ : ℂ) * I) * t)) =
      Complex.exp (-(s * (t : ℂ))) *
        (Complex.exp ((β : ℂ) * (t : ℂ)) * Complex.exp (((γ : ℂ) * (t : ℂ)) * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    ring_nf
  have e2 : Complex.exp (-((s - (β : ℂ) + (γ : ℂ) * I) * t)) =
      Complex.exp (-(s * (t : ℂ))) *
        (Complex.exp ((β : ℂ) * (t : ℂ)) * Complex.exp (-(((γ : ℂ) * (t : ℂ)) * I))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    ring_nf
  have e3 : Complex.exp (-((s - 1) * t)) =
      Complex.exp (-(s * (t : ℂ))) * Complex.exp ((t : ℂ)) := by
    rw [← Complex.exp_add]
    ring_nf
  have e4 : Complex.exp (-((s - (δ : ℂ)) * t)) =
      Complex.exp (-(s * (t : ℂ))) * Complex.exp ((δ : ℂ) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    ring_nf
  have hnum : Complex.exp ((t : ℂ)) + (A : ℂ) * Complex.exp ((δ : ℂ) * (t : ℂ)) - ((A : ℂ) - 1) -
        2 * Complex.exp ((β : ℂ) * (t : ℂ)) * Complex.cos ((γ : ℂ) * (t : ℂ)) =
      (Complex.exp ((t : ℂ)) -
          Complex.exp ((β : ℂ) * (t : ℂ)) * Complex.exp (((γ : ℂ) * (t : ℂ)) * I)) +
        ((Complex.exp ((δ : ℂ) * (t : ℂ)) -
            Complex.exp ((β : ℂ) * (t : ℂ)) * Complex.exp (-(((γ : ℂ) * (t : ℂ)) * I))) +
          ((A : ℂ) - 1) * (Complex.exp ((δ : ℂ) * (t : ℂ)) - 1)) := by
    linear_combination (Complex.exp ((β : ℂ) * (t : ℂ))) * ecos
  have hdens : (regularDensity β γ δ A t : ℂ) =
      (Complex.exp ((t : ℂ)) + (A : ℂ) * Complex.exp ((δ : ℂ) * (t : ℂ)) - ((A : ℂ) - 1) -
        2 * Complex.exp ((β : ℂ) * (t : ℂ)) * Complex.cos ((γ : ℂ) * (t : ℂ))) / (t : ℂ) := by
    unfold regularDensity regularNumerator
    push_cast
    ring
  rw [e1, e2, e3, e4, hdens, hnum]
  field_simp

theorem re_pos_of_one_lt {a : ℝ} {s : ℂ} (ha : a ≤ 1) (hs : 1 < s.re) :
    0 < (s - (a : ℂ)).re := by
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

theorem re_pos_sub_conj {β γ : ℝ} {s : ℂ} (hβ : β < 1) (hs : 1 < s.re) :
    0 < (s - (β : ℂ) - (γ : ℂ) * I).re ∧ 0 < (s - (β : ℂ) + (γ : ℂ) * I).re := by
  constructor <;>
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im] <;> linarith

/-- **The zeta function of the constructed system.** -/
theorem integral_cexp_mul_regularDensity {β γ δ : ℝ} (A : ℕ)
    (hδ1 : δ < 1) (hβ1 : β < 1) {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (regularDensity β γ δ A t : ℂ)) =
      (Complex.log (s - (β : ℂ) - (γ : ℂ) * I) - Complex.log (s - 1)) +
        ((Complex.log (s - (β : ℂ) + (γ : ℂ) * I) - Complex.log (s - (δ : ℂ))) +
          ((A : ℂ) - 1) * (Complex.log s - Complex.log (s - (δ : ℂ)))) := by
  have h1 : 0 < (s - (1 : ℂ)).re := by
    simpa using re_pos_of_one_lt (a := 1) le_rfl hs
  have hδ : 0 < (s - (δ : ℂ)).re := re_pos_of_one_lt hδ1.le hs
  have h0 : 0 < s.re := lt_trans one_pos hs
  obtain ⟨hm, hp⟩ := re_pos_sub_conj (β := β) (γ := γ) hβ1 hs
  have hsplit :
      (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (regularDensity β γ δ A t : ℂ)) =
        ∫ t in Ioi (0 : ℝ),
          ((Complex.exp (-((s - 1) * t)) - Complex.exp (-((s - β - γ * I) * t))) / t +
          ((Complex.exp (-((s - δ) * t)) - Complex.exp (-((s - β + γ * I) * t))) / t +
            ((A : ℂ) - 1) *
              ((Complex.exp (-((s - δ) * t)) - Complex.exp (-(s * t))) / t))) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    exact cexp_mul_regularDensity β γ δ A s ht
  have hint3 : IntegrableOn
      (fun t : ℝ => ((A : ℂ) - 1) *
        ((Complex.exp (-((s - (δ : ℂ)) * t)) - Complex.exp (-(s * t))) / t)) (Ioi (0 : ℝ)) := by
    have := integrableOn_frullani hδ h0
    exact this.const_mul _
  have hint2 : IntegrableOn
      (fun t : ℝ => (Complex.exp (-((s - (δ : ℂ)) * t)) -
          Complex.exp (-((s - (β : ℂ) + (γ : ℂ) * I) * t))) / t +
        ((A : ℂ) - 1) *
          ((Complex.exp (-((s - (δ : ℂ)) * t)) - Complex.exp (-(s * t))) / t))
      (Ioi (0 : ℝ)) := (integrableOn_frullani hδ hp).add hint3
  rw [hsplit, integral_add (integrableOn_frullani h1 hm) hint2,
    integral_add (integrableOn_frullani hδ hp) hint3,
    integral_const_mul, integral_frullani h1 hm, integral_frullani hδ hp,
    integral_frullani hδ h0]

/-- The rational zeta function of the constructed system. -/
def regularZeta (β γ δ : ℝ) (A : ℕ) (s : ℂ) : ℂ :=
  ((s - (β : ℂ)) ^ 2 + (γ : ℂ) ^ 2) * s ^ (A - 1) /
    ((s - 1) * (s - (δ : ℂ)) ^ A)

theorem cexp_integral_regularDensity {β γ δ : ℝ} {A : ℕ} (hA : 1 ≤ A)
    (hδ1 : δ < 1) (hβ1 : β < 1) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) *
        (regularDensity β γ δ A t : ℂ)) = regularZeta β γ δ A s := by
  have h1 : 0 < (s - (1 : ℂ)).re := by
    simpa using re_pos_of_one_lt (a := 1) le_rfl hs
  have hδ : 0 < (s - (δ : ℂ)).re := re_pos_of_one_lt hδ1.le hs
  have h0re : 0 < s.re := lt_trans one_pos hs
  obtain ⟨hm, hp⟩ := re_pos_sub_conj (β := β) (γ := γ) hβ1 hs
  have n1 : s - (1 : ℂ) ≠ 0 := by intro h; rw [h] at h1; simp at h1
  have nδ : s - (δ : ℂ) ≠ 0 := by intro h; rw [h] at hδ; simp at hδ
  have n0 : s ≠ 0 := by intro h; rw [h] at h0re; simp at h0re
  have nm : s - (β : ℂ) - (γ : ℂ) * I ≠ 0 := by intro h; rw [h] at hm; simp at hm
  have np : s - (β : ℂ) + (γ : ℂ) * I ≠ 0 := by intro h; rw [h] at hp; simp at hp
  rw [integral_cexp_mul_regularDensity A hδ1 hβ1 hs]
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_add, Complex.exp_sub,
    Complex.exp_log nm, Complex.exp_log n1, Complex.exp_log np, Complex.exp_log nδ]
  have hpow : Complex.exp (((A : ℂ) - 1) * (Complex.log s - Complex.log (s - (δ : ℂ)))) =
      s ^ (A - 1) / (s - (δ : ℂ)) ^ (A - 1) := by
    have hAc : ((A : ℂ) - 1) = ((A - 1 : ℕ) : ℂ) := by
      have : (1 : ℕ) ≤ A := hA
      push_cast [Nat.cast_sub this]
      ring
    rw [hAc, Complex.exp_nat_mul, Complex.exp_sub, Complex.exp_log n0, Complex.exp_log nδ,
      div_pow]
  rw [hpow, regularZeta]
  have hApow : (s - (δ : ℂ)) ^ A = (s - (δ : ℂ)) * (s - (δ : ℂ)) ^ (A - 1) := by
    conv_lhs => rw [show A = 1 + (A - 1) from by omega]
    rw [pow_add, pow_one]
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hfac : (s - (β : ℂ)) ^ 2 + (γ : ℂ) ^ 2 =
      (s - (β : ℂ) - (γ : ℂ) * I) * (s - (β : ℂ) + (γ : ℂ) * I) := by
    linear_combination ((γ : ℂ) ^ 2) * hI
  rw [hApow, hfac]
  have hdpow : (s - (δ : ℂ)) ^ (A - 1) ≠ 0 := pow_ne_zero _ nδ
  field_simp

/-! ## The two properties -/

/-- **The zeta function vanishes at `β + iγ`.** -/
theorem regularZeta_eq_zero (β γ δ : ℝ) (A : ℕ) :
    regularZeta β γ δ A ((β : ℂ) + (γ : ℂ) * I) = 0 := by
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hnum : (((β : ℂ) + (γ : ℂ) * I) - (β : ℂ)) ^ 2 + (γ : ℂ) ^ 2 = 0 := by
    have h : (((β : ℂ) + (γ : ℂ) * I) - (β : ℂ)) = (γ : ℂ) * I := by ring
    rw [h, mul_pow, hI]
    ring
  rw [regularZeta, hnum, zero_mul, zero_div]

/-- The vanishing at `β + iγ` is a genuine zero: the denominator does not vanish there. -/
theorem regularZeta_denom_ne_zero_at_zero {β γ δ : ℝ} {A : ℕ} (hγ : γ ≠ 0) :
    (((β : ℂ) + (γ : ℂ) * I) - 1) * (((β : ℂ) + (γ : ℂ) * I) - (δ : ℂ)) ^ A ≠ 0 := by
  have him : ∀ c : ℝ, (((β : ℂ) + (γ : ℂ) * I) - (c : ℂ)).im = γ := by
    intro c
    simp
  refine mul_ne_zero ?_ (pow_ne_zero _ ?_) <;> intro h
  · have := him 1
    rw [show ((β : ℂ) + (γ : ℂ) * I) - (1 : ℂ) = ((β : ℂ) + (γ : ℂ) * I) - ((1 : ℝ) : ℂ) by
      push_cast; ring] at h
    rw [h] at this
    simp at this
    exact hγ this.symm
  · have := him δ
    rw [h] at this
    simp at this
    exact hγ this.symm

/-- **The only singularity with real part above `δ` is the simple pole at `s = 1`.** -/
theorem regularZeta_denom_ne_zero {δ : ℝ} {A : ℕ} {s : ℂ}
    (hs : δ < s.re) (hne : s ≠ 1) :
    (s - 1) * (s - (δ : ℂ)) ^ A ≠ 0 := by
  have hδ : 0 < (s - (δ : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have nδ : s - (δ : ℂ) ≠ 0 := by intro h; rw [h] at hδ; simp at hδ
  exact mul_ne_zero (sub_ne_zero.mpr hne) (pow_ne_zero _ nδ)

/-- **Regular generalized integers do not constrain the zeros.**

For every `β` strictly between `1/2` and `1`, every `γ ≠ 0`, and every `θ > 0` there are
`0 < δ < θ`, a positive integer `A`, and a nonnegative logarithmic-coordinate density `w` on
`(0, ∞)` whose Beurling zeta function is

```
ζ(s) = ( (s-β)² + γ² ) s^{A-1} / ( (s-1)(s-δ)^A ),
```

with the exponential identity valid on `Re s > 1`.  This `ζ` is holomorphic apart from the simple
pole at `s = 1` on the whole half plane `Re s > δ`, and it vanishes at `β + iγ`.

Since `δ` can be taken below any prescribed `θ > 0`, the generalized integers of the system are
as regular as one likes — `N(x) = ρ x + O(x^θ)` for every `θ > 0` — while the zeta zeros sit at
real part `β`, arbitrarily close to `1`.  So no asymptotic regularity of the integer-counting
function implies the Riemann hypothesis. -/
theorem regular_integers_do_not_constrain_zeros
    {β : ℝ} (hβhalf : 1 / 2 < β) (hβ1 : β < 1) {γ : ℝ} (hγ : γ ≠ 0) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (δ : ℝ) (A : ℕ), 0 < δ ∧ δ < θ ∧ 1 ≤ A ∧
      (∀ t : ℝ, 0 < t → 0 ≤ regularDensity β γ δ A t) ∧
      (∀ s : ℂ, 1 < s.re →
        Complex.exp (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) *
          (regularDensity β γ δ A t : ℂ)) = regularZeta β γ δ A s) ∧
      regularZeta β γ δ A ((β : ℂ) + (γ : ℂ) * I) = 0 ∧
      (((β : ℂ) + (γ : ℂ) * I - 1) * ((β : ℂ) + (γ : ℂ) * I - (δ : ℂ)) ^ A ≠ 0) ∧
      (∀ s : ℂ, δ < s.re → s ≠ 1 → (s - 1) * (s - (δ : ℂ)) ^ A ≠ 0) := by
  set δ : ℝ := min (θ / 2) (1 / 4) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδθ : δ < θ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨A₀, hA₀pos, hA₀⟩ := exists_regularCoefficient (β := β) (δ := δ) hδ0 hβhalf hβ1
  obtain ⟨A, hA⟩ := exists_nat_ge (max A₀ 1)
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := le_trans (le_max_right A₀ 1) hA
  have hAnat : 1 ≤ A := by exact_mod_cast hA1
  have hAge : A₀ ≤ (A : ℝ) := le_trans (le_max_left A₀ 1) hA
  have hAmono : ∀ t : ℝ, 0 ≤ t →
      2 * β * Real.exp (β * t) ≤ Real.exp t + (A : ℝ) * δ * Real.exp (δ * t) := by
    intro t ht
    have h := hA₀ t ht
    have hstep : A₀ * δ * Real.exp (δ * t) ≤ (A : ℝ) * δ * Real.exp (δ * t) := by
      have : (0 : ℝ) < δ * Real.exp (δ * t) := by positivity
      nlinarith
    linarith
  exact ⟨δ, A, hδ0, hδθ, hAnat,
    fun t ht => regularDensity_nonneg hAmono ht,
    fun s hs => cexp_integral_regularDensity hAnat hδ1 hβ1 hs,
    regularZeta_eq_zero β γ δ A,
    regularZeta_denom_ne_zero_at_zero hγ,
    fun s hs hne => regularZeta_denom_ne_zero hs hne⟩

end

end RHTower.BeurlingRegularIntegers
