import GaloisForLFunctions.RHTower.CCM.CCMSawtoothDilationMean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import GaloisForLFunctions.RHTower.SawtoothFourierSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The endpoint Fourier jet of a compactly supported `C²` source

Two integrations by parts on `[0, λ]` express the cosine transform of a `C²` source through its
endpoint jet: the value and derivative at `λ`, plus a second-derivative remainder carrying the extra
factor `y^{-2}`.  With `f'(0) = 0` — automatic for the even extension of a smooth source — the
boundary terms at the origin drop out.

* `hasDerivAt_sinScaled`, `hasDerivAt_negCosScaled` — the two antiderivatives used.
* `integral_mul_cos_ibp`, `integral_mul_sin_ibp` — the two integrations by parts.
* `integral_mul_cos_twice_ibp` — the endpoint jet identity: for `y ≠ 0`,

  ```text
  ∫_0^λ f(x) cos(2π x y) dx
    = f(λ) sin(2π λ y)/(2π y) + f'(λ) cos(2π λ y)/(4π² y²)
      - f'(0)/(4π² y²) - (1/(4π² y²)) ∫_0^λ f''(x) cos(2π x y) dx.
  ```
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral Set

/-! ## The two antiderivatives -/

theorem two_pi_mul_ne_zero {y : ℝ} (hy : y ≠ 0) : (2 * Real.pi * y) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hy

theorem hasDerivAt_linScaled (y x : ℝ) :
    HasDerivAt (fun t : ℝ => 2 * Real.pi * t * y) (2 * Real.pi * y) x := by
  have h := ((hasDerivAt_id x).const_mul (2 * Real.pi)).mul_const y
  simpa using h

theorem hasDerivAt_sinScaled {y : ℝ} (hy : y ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (2 * Real.pi * t * y) / (2 * Real.pi * y))
      (Real.cos (2 * Real.pi * x * y)) x := by
  have hne := two_pi_mul_ne_zero hy
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * Real.pi * t * y))
      (Real.cos (2 * Real.pi * x * y) * (2 * Real.pi * y)) x :=
    (hasDerivAt_linScaled y x).sin
  have hdiv := hsin.div_const (2 * Real.pi * y)
  have hval : Real.cos (2 * Real.pi * x * y) * (2 * Real.pi * y) / (2 * Real.pi * y)
      = Real.cos (2 * Real.pi * x * y) := by
    field_simp
  rw [← hval]
  exact hdiv

theorem hasDerivAt_negCosScaled {y : ℝ} (hy : y ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -Real.cos (2 * Real.pi * t * y) / (2 * Real.pi * y))
      (Real.sin (2 * Real.pi * x * y)) x := by
  have hne := two_pi_mul_ne_zero hy
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2 * Real.pi * t * y))
      (-Real.sin (2 * Real.pi * x * y) * (2 * Real.pi * y)) x :=
    (hasDerivAt_linScaled y x).cos
  have hneg : HasDerivAt (fun t : ℝ => -Real.cos (2 * Real.pi * t * y))
      (-(-Real.sin (2 * Real.pi * x * y) * (2 * Real.pi * y))) x := hcos.fun_neg
  have hdiv := hneg.div_const (2 * Real.pi * y)
  have hval : -(-Real.sin (2 * Real.pi * x * y) * (2 * Real.pi * y)) / (2 * Real.pi * y)
      = Real.sin (2 * Real.pi * x * y) := by
    field_simp
  rw [← hval]
  exact hdiv

theorem continuous_cosScaled (y : ℝ) : Continuous fun x : ℝ => Real.cos (2 * Real.pi * x * y) := by
  fun_prop

theorem continuous_sinScaled (y : ℝ) : Continuous fun x : ℝ => Real.sin (2 * Real.pi * x * y) := by
  fun_prop

/-! ## The two integrations by parts -/

theorem integral_mul_cos_ibp {f f' : ℝ → ℝ} {lam y : ℝ} (hy : y ≠ 0)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f') :
    (∫ x in (0 : ℝ)..lam, f x * Real.cos (2 * Real.pi * x * y))
      = f lam * Real.sin (2 * Real.pi * lam * y) / (2 * Real.pi * y)
        - (1 / (2 * Real.pi * y)) * ∫ x in (0 : ℝ)..lam,
            f' x * Real.sin (2 * Real.pi * x * y) := by
  have hne := two_pi_mul_ne_zero hy
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f) (u' := f') (v := fun t : ℝ => Real.sin (2 * Real.pi * t * y) / (2 * Real.pi * y))
    (v' := fun x : ℝ => Real.cos (2 * Real.pi * x * y))
    (a := (0 : ℝ)) (b := lam)
    (fun x _ => hf x) (fun x _ => hasDerivAt_sinScaled hy x)
    (hf'c.intervalIntegrable _ _) ((continuous_cosScaled y).intervalIntegrable _ _)
  have hzero : Real.sin (2 * Real.pi * (0 : ℝ) * y) / (2 * Real.pi * y) = 0 := by
    simp
  rw [hzero, mul_zero, sub_zero] at hibp
  have hpull : (∫ x in (0 : ℝ)..lam,
      f' x * (Real.sin (2 * Real.pi * x * y) / (2 * Real.pi * y)))
      = (1 / (2 * Real.pi * y)) * ∫ x in (0 : ℝ)..lam,
          f' x * Real.sin (2 * Real.pi * x * y) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    field_simp
  rw [hibp, hpull]
  ring

theorem integral_mul_sin_ibp {g g' : ℝ → ℝ} {lam y : ℝ} (hy : y ≠ 0)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'c : Continuous g') :
    (∫ x in (0 : ℝ)..lam, g x * Real.sin (2 * Real.pi * x * y))
      = -(g lam * Real.cos (2 * Real.pi * lam * y)) / (2 * Real.pi * y)
        + g 0 / (2 * Real.pi * y)
        + (1 / (2 * Real.pi * y)) * ∫ x in (0 : ℝ)..lam,
            g' x * Real.cos (2 * Real.pi * x * y) := by
  have hne := two_pi_mul_ne_zero hy
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (u' := g') (v := fun t : ℝ => -Real.cos (2 * Real.pi * t * y) / (2 * Real.pi * y))
    (v' := fun x : ℝ => Real.sin (2 * Real.pi * x * y))
    (a := (0 : ℝ)) (b := lam)
    (fun x _ => hg x) (fun x _ => hasDerivAt_negCosScaled hy x)
    (hg'c.intervalIntegrable _ _) ((continuous_sinScaled y).intervalIntegrable _ _)
  have hzero : -Real.cos (2 * Real.pi * (0 : ℝ) * y) / (2 * Real.pi * y)
      = -1 / (2 * Real.pi * y) := by
    simp
  rw [hzero] at hibp
  have hpull : (∫ x in (0 : ℝ)..lam,
      g' x * (-Real.cos (2 * Real.pi * x * y) / (2 * Real.pi * y)))
      = -(1 / (2 * Real.pi * y)) * ∫ x in (0 : ℝ)..lam,
          g' x * Real.cos (2 * Real.pi * x * y) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    field_simp
  rw [hibp, hpull]
  field_simp
  ring

/-! ## The endpoint jet identity -/

/-- **Equation (6).**  The cosine transform of a `C²` source on the endpoint half-interval, expressed
through its endpoint jet with a second-derivative remainder of order `y^{-2}`. -/
theorem integral_mul_cos_twice_ibp {f f' f'' : ℝ → ℝ} {lam y : ℝ} (hy : y ≠ 0)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'c : Continuous f') (hf''c : Continuous f'') :
    (∫ x in (0 : ℝ)..lam, f x * Real.cos (2 * Real.pi * x * y))
      = f lam * Real.sin (2 * Real.pi * lam * y) / (2 * Real.pi * y)
        + f' lam * Real.cos (2 * Real.pi * lam * y) / (4 * Real.pi ^ 2 * y ^ 2)
        - f' 0 / (4 * Real.pi ^ 2 * y ^ 2)
        - (1 / (4 * Real.pi ^ 2 * y ^ 2)) * ∫ x in (0 : ℝ)..lam,
            f'' x * Real.cos (2 * Real.pi * x * y) := by
  have hne := two_pi_mul_ne_zero hy
  rw [integral_mul_cos_ibp hy hf hf'c, integral_mul_sin_ibp hy hf' hf''c]
  field_simp
  ring

/-! ## Even and odd reduction to the endpoint half-interval -/

theorem integral_symm_eq_two_mul_of_even {g : ℝ → ℝ} {lam : ℝ} (hg : Continuous g)
    (heven : ∀ x, g (-x) = g x) :
    (∫ x in (-lam)..lam, g x) = 2 * ∫ x in (0 : ℝ)..lam, g x := by
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (a := -lam) (b := (0 : ℝ)) (c := lam)
    (hg.intervalIntegrable (μ := volume) _ _) (hg.intervalIntegrable (μ := volume) _ _)
  have hneg : (∫ x in (0 : ℝ)..lam, g (-x)) = ∫ x in (-lam)..(0 : ℝ), g x := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := lam) g
    rw [neg_zero] at h
    exact h
  have hcongr : (∫ x in (0 : ℝ)..lam, g (-x)) = ∫ x in (0 : ℝ)..lam, g x :=
    intervalIntegral.integral_congr fun x _ => heven x
  rw [← hadj, ← hneg, hcongr]
  ring

theorem integral_symm_eq_zero_of_odd {g : ℝ → ℝ} {lam : ℝ} (hg : Continuous g)
    (hodd : ∀ x, g (-x) = -g x) :
    (∫ x in (-lam)..lam, g x) = 0 := by
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (a := -lam) (b := (0 : ℝ)) (c := lam)
    (hg.intervalIntegrable (μ := volume) _ _) (hg.intervalIntegrable (μ := volume) _ _)
  have hneg : (∫ x in (0 : ℝ)..lam, g (-x)) = ∫ x in (-lam)..(0 : ℝ), g x := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := lam) g
    rw [neg_zero] at h
    exact h
  have hcongr : (∫ x in (0 : ℝ)..lam, g (-x)) = -∫ x in (0 : ℝ)..lam, g x := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun x _ => hodd x
  rw [← hadj, ← hneg, hcongr]
  ring

/-- The cosine transform of an even source folds onto the endpoint half-interval. -/
theorem integral_symm_mul_cos_eq {f : ℝ → ℝ} {lam y : ℝ} (hf : Continuous f)
    (heven : ∀ x, f (-x) = f x) :
    (∫ x in (-lam)..lam, f x * Real.cos (2 * Real.pi * x * y))
      = 2 * ∫ x in (0 : ℝ)..lam, f x * Real.cos (2 * Real.pi * x * y) := by
  refine integral_symm_eq_two_mul_of_even (hf.mul (continuous_cosScaled y)) fun x => ?_
  have hcos : Real.cos (2 * Real.pi * (-x) * y) = Real.cos (2 * Real.pi * x * y) := by
    rw [show 2 * Real.pi * (-x) * y = -(2 * Real.pi * x * y) by ring, Real.cos_neg]
  rw [heven x, hcos]

/-- The sine transform of an even source vanishes: this is the imaginary part of the Fourier
transform. -/
theorem integral_symm_mul_sin_eq_zero {f : ℝ → ℝ} {lam y : ℝ} (hf : Continuous f)
    (heven : ∀ x, f (-x) = f x) :
    (∫ x in (-lam)..lam, f x * Real.sin (2 * Real.pi * x * y)) = 0 := by
  refine integral_symm_eq_zero_of_odd (hf.mul (continuous_sinScaled y)) fun x => ?_
  have hsin : Real.sin (2 * Real.pi * (-x) * y) = -Real.sin (2 * Real.pi * x * y) := by
    rw [show 2 * Real.pi * (-x) * y = -(2 * Real.pi * x * y) by ring, Real.sin_neg]
  rw [heven x, hsin]
  ring

/-- **Equation (6) for the Fourier transform of the even extension.**  With `f'(0) = 0` the endpoint
jet at `λ` carries the whole transform up to a second-derivative remainder of order `y^{-2}`. -/
theorem integral_symm_mul_cos_endpoint_jet {f f' f'' : ℝ → ℝ} {lam y : ℝ} (hy : y ≠ 0)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'c : Continuous f') (hf''c : Continuous f'') (heven : ∀ x, f (-x) = f x)
    (hf'0 : f' 0 = 0) :
    (∫ x in (-lam)..lam, f x * Real.cos (2 * Real.pi * x * y))
      = f lam * Real.sin (2 * Real.pi * lam * y) / (Real.pi * y)
        + f' lam * Real.cos (2 * Real.pi * lam * y) / (2 * Real.pi ^ 2 * y ^ 2)
        - (1 / (2 * Real.pi ^ 2 * y ^ 2)) * ∫ x in (0 : ℝ)..lam,
            f'' x * Real.cos (2 * Real.pi * x * y) := by
  have hne := two_pi_mul_ne_zero hy
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  rw [integral_symm_mul_cos_eq hfc heven,
    integral_mul_cos_twice_ibp hy hf hf' hf'c hf''c, hf'0]
  field_simp
  ring

/-! ## The Fourier-side endpoint tail -/

open Filter Topology in
/-- The leading endpoint term of the Fourier tail at sampling scale `v`: the `1/y` part of `(6)`
evaluated at `y = n v`. -/
def endpointLeadTerm (A lam v : ℝ) (n : ℕ) : ℝ :=
  A * Real.sin (2 * Real.pi * lam * ((n : ℝ) * v)) / (Real.pi * ((n : ℝ) * v))

/-- The remainder terms of the Fourier tail: the two `1/y²` parts of `(6)` at `y = n v`. -/
def endpointRemTerm (B : ℝ) (R : ℝ → ℝ) (lam v : ℝ) (n : ℕ) : ℝ :=
  B * Real.cos (2 * Real.pi * lam * ((n : ℝ) * v)) / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2)
    - R ((n : ℝ) * v) / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2)

theorem endpointLeadTerm_eq (A lam v : ℝ) (hv : 0 < v) (n : ℕ) :
    endpointLeadTerm A lam v n
      = (A / (Real.pi * v)) *
        (Real.sin ((n : ℝ) * (2 * Real.pi * lam * v)) / (n : ℝ)) := by
  have harg : 2 * Real.pi * lam * ((n : ℝ) * v) = (n : ℝ) * (2 * Real.pi * lam * v) := by ring
  rw [endpointLeadTerm, harg]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hvne : v ≠ 0 := ne_of_gt hv
    field_simp

/-- **The leading endpoint series.**  Off the lattice it converges, and its sum is at most
`|A|/(2v)` — the endpoint jump is the only input. -/
theorem exists_tendsto_sum_endpointLeadTerm {A lam v : ℝ} (hv : 0 < v)
    (hlam : ∀ k : ℤ, lam * v ≠ (k : ℝ)) :
    ∃ S : ℝ, Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, endpointLeadTerm A lam v n)
        Filter.atTop (nhds S)
      ∧ |S| ≤ |A| / (2 * v) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hθ : ∀ k : ℤ, 2 * Real.pi * lam * v ≠ (k : ℝ) * (2 * Real.pi) := by
    intro k h
    refine hlam k ?_
    have h2 : (2 * Real.pi) * (lam * v) = (2 * Real.pi) * (k : ℝ) := by linarith [h]
    exact mul_left_cancel₀ (by positivity) h2
  obtain ⟨S', hS', hbound⟩ := exists_sum_sawtoothSine_abs_le_of_ne hθ
  refine ⟨(A / (Real.pi * v)) * S', ?_, ?_⟩
  · have hmul := hS'.const_mul (A / (Real.pi * v))
    refine hmul.congr fun N => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => (endpointLeadTerm_eq A lam v hv n).symm
  · rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.pi * v)]
    calc |A| / (Real.pi * v) * |S'| ≤ |A| / (Real.pi * v) * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = |A| / (2 * v) := by
          have hvne : v ≠ 0 := ne_of_gt hv
          have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
          field_simp

theorem summable_one_div_sq : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
  hasSum_zeta_two.summable

theorem abs_endpointRemTerm_le {B C : ℝ} {R : ℝ → ℝ} (hR : ∀ y, |R y| ≤ C) {lam v : ℝ}
    (hv : 0 < v) (n : ℕ) :
    |endpointRemTerm B R lam v n|
      ≤ ((|B| + C) / (2 * Real.pi ^ 2 * v ^ 2)) * (1 / (n : ℝ) ^ 2) := by
  have hC : (0 : ℝ) ≤ C := le_trans (abs_nonneg (R 0)) (hR 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [endpointRemTerm]
    simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hden : (0 : ℝ) < 2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2 := by positivity
    have hb1 : |B * Real.cos (2 * Real.pi * lam * ((n : ℝ) * v))
        / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2)|
        ≤ |B| / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2) := by
      rw [abs_div, abs_of_pos hden, abs_mul]
      refine div_le_div_of_nonneg_right ?_ hden.le
      nlinarith [Real.abs_cos_le_one (2 * Real.pi * lam * ((n : ℝ) * v)), abs_nonneg B]
    have hb2 : |R ((n : ℝ) * v) / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2)|
        ≤ C / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2) := by
      rw [abs_div, abs_of_pos hden]
      exact div_le_div_of_nonneg_right (hR _) hden.le
    have hcomb : |B| / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2)
        + C / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2)
        = ((|B| + C) / (2 * Real.pi ^ 2 * v ^ 2)) * (1 / (n : ℝ) ^ 2) := by
      have hvne : v ≠ 0 := ne_of_gt hv
      have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
      field_simp
    rw [endpointRemTerm]
    calc |B * Real.cos (2 * Real.pi * lam * ((n : ℝ) * v))
          / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2)
        - R ((n : ℝ) * v) / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2)|
        ≤ |B| / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2)
          + C / (2 * Real.pi ^ 2 * ((n : ℝ) * v) ^ 2) := (abs_sub _ _).trans (add_le_add hb1 hb2)
      _ = ((|B| + C) / (2 * Real.pi ^ 2 * v ^ 2)) * (1 / (n : ℝ) ^ 2) := hcomb

/-- **The remainder series converges absolutely**, with the endpoint derivative and the second
derivative mass as the only inputs. -/
theorem summable_endpointRemTerm {B C : ℝ} {R : ℝ → ℝ} (hR : ∀ y, |R y| ≤ C) {lam v : ℝ}
    (hv : 0 < v) : Summable (endpointRemTerm B R lam v) := by
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ((|B| + C) / (2 * Real.pi ^ 2 * v ^ 2)) * (1 / (n : ℝ) ^ 2))
    (summable_one_div_sq.mul_left _) fun n => ?_
  rw [Real.norm_eq_abs]
  exact abs_endpointRemTerm_le hR hv n

theorem abs_tsum_endpointRemTerm_le {B C : ℝ} {R : ℝ → ℝ} (hR : ∀ y, |R y| ≤ C) {lam v : ℝ}
    (hv : 0 < v) :
    |∑' n : ℕ, endpointRemTerm B R lam v n| ≤ (|B| + C) / (12 * v ^ 2) := by
  have hC : (0 : ℝ) ≤ C := le_trans (abs_nonneg (R 0)) (hR 0)
  have hsum := summable_endpointRemTerm hR hv (B := B) (lam := lam)
  have hdom : Summable fun n : ℕ =>
      ((|B| + C) / (2 * Real.pi ^ 2 * v ^ 2)) * (1 / (n : ℝ) ^ 2) :=
    summable_one_div_sq.mul_left _
  calc |∑' n : ℕ, endpointRemTerm B R lam v n|
      ≤ ∑' n : ℕ, |endpointRemTerm B R lam v n| := by
        have h := norm_tsum_le_tsum_norm (f := endpointRemTerm B R lam v) hsum.norm
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' n : ℕ, ((|B| + C) / (2 * Real.pi ^ 2 * v ^ 2)) * (1 / (n : ℝ) ^ 2) :=
        Summable.tsum_le_tsum (fun n => abs_endpointRemTerm_le hR hv n) hsum.abs hdom
    _ = ((|B| + C) / (2 * Real.pi ^ 2 * v ^ 2)) * (Real.pi ^ 2 / 6) := by
        rw [tsum_mul_left, hasSum_zeta_two.tsum_eq]
    _ = (|B| + C) / (12 * v ^ 2) := by
        have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
        have hvne : v ≠ 0 := ne_of_gt hv
        field_simp
        ring

/-! ## Equation (3): the assembled endpoint bound -/

/-- **Equation (3).**  The Fourier-side endpoint tail converges and is bounded by the endpoint jet:
the jump and the central value at scale `v^{-1/2}`, the endpoint derivative and the second-derivative
mass at scale `v^{-3/2}`.  The leading term is *not* estimated term by term — its sum is controlled by
the sawtooth series, which is why the bound has no logarithm. -/
theorem abs_fourierTail_le {A B f0 C : ℝ} {R : ℝ → ℝ} (hR : ∀ y, |R y| ≤ C) {lam v : ℝ}
    (hv : 0 < v) (hlam : ∀ k : ℤ, lam * v ≠ (k : ℝ)) :
    ∃ S : ℝ,
      Filter.Tendsto (fun N => ∑ n ∈ Finset.range N,
          (endpointLeadTerm A lam v n + endpointRemTerm B R lam v n))
        Filter.atTop (nhds S)
      ∧ |Real.sqrt v * S - f0 / (2 * Real.sqrt v)|
          ≤ (|A| + |f0|) / (2 * Real.sqrt v)
            + (|B| + C) / (12 * (v * Real.sqrt v)) := by
  obtain ⟨Sl, hSl, hSlb⟩ := exists_tendsto_sum_endpointLeadTerm (A := A) hv hlam
  have hsum := summable_endpointRemTerm hR hv (B := B) (lam := lam)
  have hSr := hsum.hasSum.tendsto_sum_nat
  have hSrb := abs_tsum_endpointRemTerm_le hR hv (B := B) (lam := lam)
  refine ⟨Sl + ∑' n : ℕ, endpointRemTerm B R lam v n, ?_, ?_⟩
  · have hadd := hSl.add hSr
    refine hadd.congr fun N => ?_
    rw [Finset.sum_add_distrib]
  · have hsv0 : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hv
    have hsv : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv.le
    have hAnn : (0 : ℝ) ≤ |A| := abs_nonneg A
    have hC : (0 : ℝ) ≤ C := le_trans (abs_nonneg (R 0)) (hR 0)
    have hBnn : (0 : ℝ) ≤ |B| := abs_nonneg B
    have hstep : |Real.sqrt v * (Sl + ∑' n : ℕ, endpointRemTerm B R lam v n)
        - f0 / (2 * Real.sqrt v)|
        ≤ Real.sqrt v * (|A| / (2 * v)) + Real.sqrt v * ((|B| + C) / (12 * v ^ 2))
          + |f0| / (2 * Real.sqrt v) := by
      have h1 : |Real.sqrt v * (Sl + ∑' n : ℕ, endpointRemTerm B R lam v n)
          - f0 / (2 * Real.sqrt v)|
          ≤ |Real.sqrt v * (Sl + ∑' n : ℕ, endpointRemTerm B R lam v n)|
            + |f0 / (2 * Real.sqrt v)| := abs_sub _ _
      have h2 : |Real.sqrt v * (Sl + ∑' n : ℕ, endpointRemTerm B R lam v n)|
          ≤ Real.sqrt v * (|A| / (2 * v)) + Real.sqrt v * ((|B| + C) / (12 * v ^ 2)) := by
        rw [abs_mul, abs_of_pos hsv0]
        have h3 : |Sl + ∑' n : ℕ, endpointRemTerm B R lam v n|
            ≤ |A| / (2 * v) + (|B| + C) / (12 * v ^ 2) :=
          (abs_add_le _ _).trans (add_le_add hSlb hSrb)
        nlinarith [h3, hsv0]
      have h4 : |f0 / (2 * Real.sqrt v)| = |f0| / (2 * Real.sqrt v) := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sqrt v)]
      rw [h4] at h1
      linarith [h1, h2]
    refine hstep.trans (le_of_eq ?_)
    have hvne : v ≠ 0 := ne_of_gt hv
    have hsvne : Real.sqrt v ≠ 0 := ne_of_gt hsv0
    field_simp
    rw [Real.sq_sqrt hv.le]
    ring

/-! ## Equation (4): the `L²(d*v)` bound -/

theorem inv_pow_eq_rpow {v : ℝ} (hv : 0 < v) (k : ℕ) : 1 / v ^ k = v ^ (-(k : ℝ)) := by
  rw [Real.rpow_neg hv.le, Real.rpow_natCast, one_div]

theorem integrableOn_Ioi_inv_pow {lam : ℝ} (hlam : 0 < lam) {k : ℕ} (hk : 2 ≤ k) :
    IntegrableOn (fun v : ℝ => 1 / v ^ k) (Ioi lam) := by
  have hk1 : (-(k : ℝ)) < -1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hbase := integrableOn_Ioi_rpow_of_lt hk1 hlam
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro v hv
  exact (inv_pow_eq_rpow (lt_trans hlam hv) k).symm

theorem integral_Ioi_inv_pow {lam : ℝ} (hlam : 0 < lam) {k : ℕ} (hk : 2 ≤ k) :
    (∫ v in Ioi lam, 1 / v ^ k) = -lam ^ (-(k : ℝ) + 1) / (-(k : ℝ) + 1) := by
  have hk1 : (-(k : ℝ)) < -1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hcongr : (∫ v in Ioi lam, 1 / v ^ k) = ∫ v in Ioi lam, v ^ (-(k : ℝ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    exact inv_pow_eq_rpow (lt_trans hlam hv) k
  rw [hcongr, integral_Ioi_rpow_of_lt hk1 hlam]

theorem integral_Ioi_inv_sq {lam : ℝ} (hlam : 0 < lam) : (∫ v in Ioi lam, 1 / v ^ 2) = 1 / lam := by
  have h := integral_Ioi_inv_pow hlam (k := 2) (by norm_num)
  have hcast : (-((2 : ℕ) : ℝ) + 1) = -1 := by norm_num
  rw [hcast] at h
  rw [h, Real.rpow_neg_one]
  field_simp

theorem integral_Ioi_inv_cube {lam : ℝ} (hlam : 0 < lam) :
    (∫ v in Ioi lam, 1 / v ^ 3) = 1 / (2 * lam ^ 2) := by
  have h := integral_Ioi_inv_pow hlam (k := 3) (by norm_num)
  have hcast : (-((3 : ℕ) : ℝ) + 1) = -(2 : ℝ) := by norm_num
  rw [hcast] at h
  rw [h, Real.rpow_neg hlam.le,
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hne : lam ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (ne_of_gt hlam)
  field_simp

theorem integral_Ioi_inv_four {lam : ℝ} (hlam : 0 < lam) :
    (∫ v in Ioi lam, 1 / v ^ 4) = 1 / (3 * lam ^ 3) := by
  have h := integral_Ioi_inv_pow hlam (k := 4) (by norm_num)
  have hcast : (-((4 : ℕ) : ℝ) + 1) = -(3 : ℝ) := by norm_num
  rw [hcast] at h
  rw [h, Real.rpow_neg hlam.le,
    show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hne : lam ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 (ne_of_gt hlam)
  field_simp

/-- The dominating profile of `(3)`, squared and weighted by the multiplicative measure. -/
theorem integrableOn_endpointDominant {lam a b : ℝ} (hlam : 0 < lam) :
    IntegrableOn (fun v : ℝ => a ^ 2 * (1 / v ^ 2) + 2 * a * b * (1 / v ^ 3)
      + b ^ 2 * (1 / v ^ 4)) (Ioi lam) :=
  (((integrableOn_Ioi_inv_pow hlam (by norm_num : 2 ≤ 2)).const_mul _).add
    ((integrableOn_Ioi_inv_pow hlam (by norm_num : 2 ≤ 3)).const_mul _)).add
    ((integrableOn_Ioi_inv_pow hlam (by norm_num : 2 ≤ 4)).const_mul _)

theorem integral_endpointDominant {lam a b : ℝ} (hlam : 0 < lam) :
    (∫ v in Ioi lam, (a ^ 2 * (1 / v ^ 2) + 2 * a * b * (1 / v ^ 3) + b ^ 2 * (1 / v ^ 4)))
      = a ^ 2 / lam + a * b / lam ^ 2 + b ^ 2 / (3 * lam ^ 3) := by
  have h1 : IntegrableOn (fun v : ℝ => a ^ 2 * (1 / v ^ 2)) (Ioi lam) :=
    (integrableOn_Ioi_inv_pow hlam (by norm_num : 2 ≤ 2)).const_mul _
  have h2 : IntegrableOn (fun v : ℝ => 2 * a * b * (1 / v ^ 3)) (Ioi lam) :=
    (integrableOn_Ioi_inv_pow hlam (by norm_num : 2 ≤ 3)).const_mul _
  have h3 : IntegrableOn (fun v : ℝ => b ^ 2 * (1 / v ^ 4)) (Ioi lam) :=
    (integrableOn_Ioi_inv_pow hlam (by norm_num : 2 ≤ 4)).const_mul _
  have hsplit1 : (∫ v in Ioi lam,
      (a ^ 2 * (1 / v ^ 2) + 2 * a * b * (1 / v ^ 3) + b ^ 2 * (1 / v ^ 4)))
      = (∫ v in Ioi lam, (a ^ 2 * (1 / v ^ 2) + 2 * a * b * (1 / v ^ 3)))
        + ∫ v in Ioi lam, b ^ 2 * (1 / v ^ 4) :=
    MeasureTheory.integral_add (h1.add h2) h3
  have hsplit2 : (∫ v in Ioi lam, (a ^ 2 * (1 / v ^ 2) + 2 * a * b * (1 / v ^ 3)))
      = (∫ v in Ioi lam, a ^ 2 * (1 / v ^ 2)) + ∫ v in Ioi lam, 2 * a * b * (1 / v ^ 3) :=
    MeasureTheory.integral_add h1 h2
  rw [hsplit1, hsplit2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, integral_Ioi_inv_sq hlam, integral_Ioi_inv_cube hlam,
    integral_Ioi_inv_four hlam]
  have hne : lam ≠ 0 := ne_of_gt hlam
  field_simp

/-- **Equation (4).**  The pointwise endpoint bound `(3)` integrates against the multiplicative measure
to the card's `L²` bound `(a‖v^{-1/2}‖ + b‖v^{-3/2}‖)²`.  No Minkowski inequality is needed: the cross
term is explicit, and the only comparison used is `√3 ≤ 2`, in the form
`√(1/λ)·√(1/(3λ³)) ≥ 1/(2λ²)`. -/
theorem integral_sq_div_le_of_endpoint_bound {G : ℝ → ℝ} {lam a b : ℝ} (hlam : 0 < lam)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hGm : Measurable G)
    (hG : ∀ v, lam < v → |G v| ≤ a / Real.sqrt v + b / (v * Real.sqrt v)) :
    (∫ v in Ioi lam, (G v) ^ 2 / v)
      ≤ (a * Real.sqrt (1 / lam) + b * Real.sqrt (1 / (3 * lam ^ 3))) ^ 2 := by
  have hdom : ∀ v ∈ Ioi lam, (G v) ^ 2 / v
      ≤ a ^ 2 * (1 / v ^ 2) + 2 * a * b * (1 / v ^ 3) + b ^ 2 * (1 / v ^ 4) := by
    intro v hv
    have hvpos : (0 : ℝ) < v := lt_trans hlam hv
    have hsv : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hvpos
    have hsvsq : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hvpos.le
    have hsq : (G v) ^ 2 ≤ (a / Real.sqrt v + b / (v * Real.sqrt v)) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (G v)) (hG v hv) 2
      rwa [sq_abs] at h
    have hexp : (a / Real.sqrt v + b / (v * Real.sqrt v)) ^ 2 / v
        = a ^ 2 * (1 / v ^ 2) + 2 * a * b * (1 / v ^ 3) + b ^ 2 * (1 / v ^ 4) := by
      have hvne : v ≠ 0 := ne_of_gt hvpos
      have hsvne : Real.sqrt v ≠ 0 := ne_of_gt hsv
      field_simp
      nlinarith [hsvsq, hvpos, hsv]
    calc (G v) ^ 2 / v ≤ (a / Real.sqrt v + b / (v * Real.sqrt v)) ^ 2 / v :=
          div_le_div_of_nonneg_right hsq hvpos.le
      _ = a ^ 2 * (1 / v ^ 2) + 2 * a * b * (1 / v ^ 3) + b ^ 2 * (1 / v ^ 4) := hexp
  have hmeas : Measurable fun v : ℝ => (G v) ^ 2 / v := (hGm.pow_const 2).div measurable_id
  have hint : IntegrableOn (fun v : ℝ => (G v) ^ 2 / v) (Ioi lam) := by
    refine (integrableOn_endpointDominant (a := a) (b := b) hlam).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hvpos : (0 : ℝ) < v := lt_trans hlam hv
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (G v) ^ 2 / v)]
    exact hdom v hv
  have hmono := MeasureTheory.setIntegral_mono_on hint
    (integrableOn_endpointDominant (a := a) (b := b) hlam) measurableSet_Ioi hdom
  rw [integral_endpointDominant hlam] at hmono
  refine hmono.trans ?_
  -- the two weight norms
  have h1nn : (0 : ℝ) ≤ 1 / lam := by positivity
  have h2nn : (0 : ℝ) ≤ 1 / (3 * lam ^ 3) := by positivity
  have hs1 : Real.sqrt (1 / lam) ^ 2 = 1 / lam := Real.sq_sqrt h1nn
  have hs2 : Real.sqrt (1 / (3 * lam ^ 3)) ^ 2 = 1 / (3 * lam ^ 3) := Real.sq_sqrt h2nn
  have hs1nn : (0 : ℝ) ≤ Real.sqrt (1 / lam) := Real.sqrt_nonneg _
  have hs2nn : (0 : ℝ) ≤ Real.sqrt (1 / (3 * lam ^ 3)) := Real.sqrt_nonneg _
  -- the cross term is at least `1/(2 λ²)`
  have hcross : 1 / (2 * lam ^ 2)
      ≤ Real.sqrt (1 / lam) * Real.sqrt (1 / (3 * lam ^ 3)) := by
    rw [← Real.sqrt_mul h1nn]
    have hval : (1 / lam) * (1 / (3 * lam ^ 3)) = 1 / (3 * lam ^ 4) := by
      have hne : lam ≠ 0 := ne_of_gt hlam
      field_simp
    rw [hval]
    have hsq : (1 / (2 * lam ^ 2)) ^ 2 = 1 / (4 * lam ^ 4) := by
      have hne : lam ≠ 0 := ne_of_gt hlam
      field_simp
      ring
    have hle : 1 / (4 * lam ^ 4) ≤ 1 / (3 * lam ^ 4) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [pow_pos hlam 4]
    calc 1 / (2 * lam ^ 2) = Real.sqrt ((1 / (2 * lam ^ 2)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (1 / (4 * lam ^ 4)) := by rw [hsq]
      _ ≤ Real.sqrt (1 / (3 * lam ^ 4)) := Real.sqrt_le_sqrt hle
  have hexpand : (a * Real.sqrt (1 / lam) + b * Real.sqrt (1 / (3 * lam ^ 3))) ^ 2
      = a ^ 2 / lam + 2 * a * b * (Real.sqrt (1 / lam) * Real.sqrt (1 / (3 * lam ^ 3)))
        + b ^ 2 / (3 * lam ^ 3) := by
    have hone : a ^ 2 * Real.sqrt (1 / lam) ^ 2 = a ^ 2 / lam := by rw [hs1]; ring
    have htwo : b ^ 2 * Real.sqrt (1 / (3 * lam ^ 3)) ^ 2 = b ^ 2 / (3 * lam ^ 3) := by
      rw [hs2]; ring
    nlinarith [hone, htwo, hs1, hs2]
  rw [hexpand]
  have habnn : (0 : ℝ) ≤ a * b := mul_nonneg ha hb
  have hkey : a * b / lam ^ 2
      ≤ 2 * a * b * (Real.sqrt (1 / lam) * Real.sqrt (1 / (3 * lam ^ 3))) := by
    have h := mul_le_mul_of_nonneg_left hcross (by positivity : (0 : ℝ) ≤ 2 * (a * b))
    have heq : 2 * (a * b) * (1 / (2 * lam ^ 2)) = a * b / lam ^ 2 := by
      have hne : lam ≠ 0 := ne_of_gt hlam
      field_simp
    rw [heq] at h
    nlinarith [h]
  linarith [hkey]

end GaloisForLFunctions.RHTower

end
