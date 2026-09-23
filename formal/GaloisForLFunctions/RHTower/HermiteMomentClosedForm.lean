import GaloisForLFunctions.RHTower.HermiteLineIntegral
import GaloisForLFunctions.RHTower.ConstrainedProlateHermiteContrast

/-!
# Closed forms for the Hermite moments and the Hermite shape ratio

The `L²` norm of a Hermite function obeys the same kind of one-step recursion as its first moment:

```text
∫_ℝ φ_{m+1}²  =  (m+1) · ∫_ℝ φ_m² .
```

Both recursions come from the same two pointwise identities — the three-term recursion and the
Appell law — written in the uniform form that also covers the bottom rung, where the shifted term is
killed by the coefficient rather than by an index convention.  Pairing them against `φ_{m+1}` and
using that the derivative of a product of Hermite functions integrates to zero, the cross moment
`∫ x φ_m φ_{m+1}` is evaluated, and substituting it into the three-term recursion gives the norm.

With the two Gaussian values `∫_ℝ φ_0 = √(2π)` and `∫_ℝ φ_0² = √π`, the shape ratio at an even rung
is therefore

```text
(∫_ℝ φ_{2k})² / ∫_ℝ φ_{2k}²  =  2√π · binom(2k, k) / 4^k ,
```

the same central-binomial profile that the constrained-prolate Hermite weights carry.
-/

noncomputable section

open MeasureTheory Set Filter Topology Polynomial

namespace RHTower

/-! ## The two pointwise identities in uniform form -/

theorem hermiteFun_one_eq (x : ℝ) : hermiteFun 1 x = Real.sqrt 2 * x * hermiteFun 0 x := by
  have h1 : Polynomial.hermite 1 = Polynomial.X := by
    rw [Polynomial.hermite_succ 0, Polynomial.hermite_zero]
    simp
  show Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite 1)
      * Real.exp (-((Real.sqrt 2 * x) ^ (2 : ℕ) / 4))
    = Real.sqrt 2 * x * (Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite 0)
      * Real.exp (-((Real.sqrt 2 * x) ^ (2 : ℕ) / 4)))
  rw [h1, Polynomial.hermite_zero]
  simp only [Polynomial.aeval_X, map_one]
  ring

theorem deriv_hermiteFun_zero (x : ℝ) :
    deriv (hermiteFun 0) x = -(x * hermiteFun 0 x) := by
  have hfun : hermiteFun 0 = fun y : ℝ => Real.exp (-(y ^ (2 : ℕ) / 2)) := funext hermiteFun_zero_eq
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ (2 : ℕ) / 2)) (-x) x := by
    have h0 := ((hasDerivAt_pow 2 x).div_const 2).neg
    refine h0.congr_deriv ?_
    push_cast
    ring
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ (2 : ℕ) / 2)))
      (-(x * Real.exp (-(x ^ (2 : ℕ) / 2)))) x := by
    refine h1.exp.congr_deriv ?_
    ring
  rw [hfun, h2.deriv]

/-- **Uniform three-term recursion.**  At the bottom rung the shifted term is killed by its
coefficient. -/
theorem hermiteFun_succ_uniform (m : ℕ) (x : ℝ) :
    hermiteFun (m + 1) x
      = Real.sqrt 2 * x * hermiteFun m x - (m : ℝ) * hermiteFun (m - 1) x := by
  cases m with
  | zero => simpa using hermiteFun_one_eq x
  | succ k =>
      have h := hermiteFun_add_two k x
      simpa using h

/-- **Uniform Appell law.**  `φ_m′ + x·φ_m = √2·m·φ_{m−1}`, with the bottom rung included. -/
theorem deriv_hermiteFun_add_id_mul (m : ℕ) (x : ℝ) :
    deriv (hermiteFun m) x + x * hermiteFun m x
      = Real.sqrt 2 * (m : ℝ) * hermiteFun (m - 1) x := by
  cases m with
  | zero =>
      rw [deriv_hermiteFun_zero]
      simp
  | succ k =>
      have h := deriv_hermiteFun_succ k x
      simp only [Nat.add_sub_cancel]
      rw [h]
      push_cast
      ring

/-! ## Integrability of the products -/

theorem integrable_hermiteFun_mul (m n : ℕ) :
    Integrable fun x : ℝ => hermiteFun m x * hermiteFun n x := by
  obtain ⟨p, hp⟩ := exists_poly_hermiteFun m
  obtain ⟨q, hq⟩ := exists_poly_hermiteFun n
  refine (integrable_polyEval_mul_gauss (p * q) (b := 1) (by norm_num)).congr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  show Polynomial.eval x (p * q) * Real.exp (-(1 * x ^ (2 : ℕ))) = hermiteFun m x * hermiteFun n x
  have hexp : Real.exp (-(1 / 2 * x ^ (2 : ℕ))) * Real.exp (-(1 / 2 * x ^ (2 : ℕ)))
      = Real.exp (-(1 * x ^ (2 : ℕ))) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hp x, hq x, Polynomial.eval_mul, ← hexp]
  ring

theorem integrable_id_mul_hermiteFun_mul (m n : ℕ) :
    Integrable fun x : ℝ => x * (hermiteFun m x * hermiteFun n x) := by
  obtain ⟨p, hp⟩ := exists_poly_hermiteFun m
  obtain ⟨q, hq⟩ := exists_poly_hermiteFun n
  refine (integrable_polyEval_mul_gauss (Polynomial.X * (p * q)) (b := 1) (by norm_num)).congr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  show Polynomial.eval x (Polynomial.X * (p * q)) * Real.exp (-(1 * x ^ (2 : ℕ)))
      = x * (hermiteFun m x * hermiteFun n x)
  have hexp : Real.exp (-(1 / 2 * x ^ (2 : ℕ))) * Real.exp (-(1 / 2 * x ^ (2 : ℕ)))
      = Real.exp (-(1 * x ^ (2 : ℕ))) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hp x, hq x, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_mul, ← hexp]
  ring

/-! ## Orthogonality on the line -/

theorem integral_hermiteFun_mul_eq_zero_of_ne {m n : ℕ} (hmn : m ≠ n) :
    (∫ x, hermiteFun m x * hermiteFun n x) = 0 := by
  have h1 : Tendsto (fun R : ℝ => ∫ x in (-R)..R, hermiteFun m x * hermiteFun n x) atTop
      (𝓝 (∫ x, hermiteFun m x * hermiteFun n x)) :=
    intervalIntegral_tendsto_integral (integrable_hermiteFun_mul m n)
      tendsto_neg_atTop_atBot tendsto_id
  have h2 := tendsto_integral_hermiteFun_mul hmn
  exact (tendsto_nhds_unique h1 h2)

/-! ## The cross moment -/

theorem integral_deriv_hermiteFun_mul_succ (m : ℕ) :
    (∫ x, deriv (fun y => hermiteFun m y * hermiteFun (m + 1) y) x) = 0 := by
  set F : ℝ → ℝ := fun y => hermiteFun m y * hermiteFun (m + 1) y with hF
  have hderiv : ∀ x : ℝ, deriv F x
      = deriv (hermiteFun m) x * hermiteFun (m + 1) x
        + hermiteFun m x * deriv (hermiteFun (m + 1)) x := by
    intro x
    exact ((hasDerivAt_hermiteFun m x).mul (hasDerivAt_hermiteFun (m + 1) x)).deriv
  have hint : Integrable (deriv F) := by
    have hA : Integrable fun x : ℝ =>
        Real.sqrt 2 * (m : ℝ) * hermiteFun (m - 1) x * hermiteFun (m + 1) x := by
      have := (integrable_hermiteFun_mul (m - 1) (m + 1)).const_mul (Real.sqrt 2 * (m : ℝ))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      ring
    have hB : Integrable fun x : ℝ => x * (hermiteFun m x * hermiteFun (m + 1) x) :=
      integrable_id_mul_hermiteFun_mul m (m + 1)
    have hC : Integrable fun x : ℝ =>
        Real.sqrt 2 * ((m : ℝ) + 1) * hermiteFun m x * hermiteFun m x := by
      have := (integrable_hermiteFun_mul m m).const_mul (Real.sqrt 2 * ((m : ℝ) + 1))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      ring
    have hsum : Integrable fun x : ℝ =>
        (Real.sqrt 2 * (m : ℝ) * hermiteFun (m - 1) x * hermiteFun (m + 1) x
          - x * (hermiteFun m x * hermiteFun (m + 1) x))
        + (Real.sqrt 2 * ((m : ℝ) + 1) * hermiteFun m x * hermiteFun m x
          - x * (hermiteFun m x * hermiteFun (m + 1) x)) := ((hA.sub hB).add (hC.sub hB))
    refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
    rw [hderiv x]
    have h1 := deriv_hermiteFun_add_id_mul m x
    have h2 := deriv_hermiteFun_succ m x
    have e1 : deriv (hermiteFun m) x
        = Real.sqrt 2 * (m : ℝ) * hermiteFun (m - 1) x - x * hermiteFun m x := by linarith
    rw [e1, h2]
    ring
  have hwin : ∀ R : ℝ, (∫ x in (-R)..R, deriv F x) = F R - F (-R) := by
    intro R
    refine intervalIntegral.integral_deriv_eq_sub (fun x _ => ?_) ?_
    · exact ((differentiable_hermiteFun m x).mul (differentiable_hermiteFun (m + 1) x))
    · have hFd : deriv F = fun x => deriv (hermiteFun m) x * hermiteFun (m + 1) x
          + hermiteFun m x * deriv (hermiteFun (m + 1)) x := funext hderiv
      rw [hFd]
      exact ((((continuous_deriv_hermiteFun m).mul (continuous_hermiteFun (m + 1))).add
        ((continuous_hermiteFun m).mul
          (continuous_deriv_hermiteFun (m + 1))))).intervalIntegrable _ _
  have hlim1 : Tendsto (fun R : ℝ => ∫ x in (-R)..R, deriv F x) atTop (𝓝 (∫ x, deriv F x)) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hlim2 : Tendsto (fun R : ℝ => F R - F (-R)) atTop (𝓝 0) := by
    have hA : Tendsto F atTop (𝓝 0) := by
      have := (tendsto_hermiteFun_atTop m).mul (tendsto_hermiteFun_atTop (m + 1))
      simpa [hF] using this
    have hB : Tendsto (fun R : ℝ => F (-R)) atTop (𝓝 0) := by
      have h := ((tendsto_hermiteFun_atBot m).mul
        (tendsto_hermiteFun_atBot (m + 1))).comp tendsto_neg_atTop_atBot
      rw [mul_zero] at h
      exact h
    simpa using hA.sub hB
  have hcongr : Tendsto (fun R : ℝ => ∫ x in (-R)..R, deriv F x) atTop (𝓝 0) :=
    hlim2.congr fun R => (hwin R).symm
  exact tendsto_nhds_unique hlim1 hcongr

/-- **The cross moment.** -/
theorem integral_id_mul_hermiteFun_mul_succ (m : ℕ) :
    (∫ x, x * (hermiteFun m x * hermiteFun (m + 1) x))
      = (Real.sqrt 2 / 2) * ((m : ℝ) + 1) * ∫ x, hermiteFun m x * hermiteFun m x := by
  have hA : Integrable fun x : ℝ =>
      Real.sqrt 2 * (m : ℝ) * hermiteFun (m - 1) x * hermiteFun (m + 1) x := by
    have := (integrable_hermiteFun_mul (m - 1) (m + 1)).const_mul (Real.sqrt 2 * (m : ℝ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hB : Integrable fun x : ℝ => x * (hermiteFun m x * hermiteFun (m + 1) x) :=
    integrable_id_mul_hermiteFun_mul m (m + 1)
  have hC : Integrable fun x : ℝ =>
      Real.sqrt 2 * ((m : ℝ) + 1) * hermiteFun m x * hermiteFun m x := by
    have := (integrable_hermiteFun_mul m m).const_mul (Real.sqrt 2 * ((m : ℝ) + 1))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hzero := integral_deriv_hermiteFun_mul_succ m
  have hsplit : (∫ x, deriv (fun y => hermiteFun m y * hermiteFun (m + 1) y) x)
      = ((∫ x, Real.sqrt 2 * (m : ℝ) * hermiteFun (m - 1) x * hermiteFun (m + 1) x)
          - ∫ x, x * (hermiteFun m x * hermiteFun (m + 1) x))
        + ((∫ x, Real.sqrt 2 * ((m : ℝ) + 1) * hermiteFun m x * hermiteFun m x)
          - ∫ x, x * (hermiteFun m x * hermiteFun (m + 1) x)) := by
    have hAB : Integrable fun x : ℝ =>
        Real.sqrt 2 * (m : ℝ) * hermiteFun (m - 1) x * hermiteFun (m + 1) x
          - x * (hermiteFun m x * hermiteFun (m + 1) x) := hA.sub hB
    have hCB : Integrable fun x : ℝ =>
        Real.sqrt 2 * ((m : ℝ) + 1) * hermiteFun m x * hermiteFun m x
          - x * (hermiteFun m x * hermiteFun (m + 1) x) := hC.sub hB
    rw [← MeasureTheory.integral_sub hA hB, ← MeasureTheory.integral_sub hC hB,
      ← MeasureTheory.integral_add hAB hCB]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hderiv : deriv (fun y => hermiteFun m y * hermiteFun (m + 1) y) x
        = deriv (hermiteFun m) x * hermiteFun (m + 1) x
          + hermiteFun m x * deriv (hermiteFun (m + 1)) x :=
      ((hasDerivAt_hermiteFun m x).mul (hasDerivAt_hermiteFun (m + 1) x)).deriv
    rw [hderiv]
    have h1 := deriv_hermiteFun_add_id_mul m x
    have h2 := deriv_hermiteFun_succ m x
    have e1 : deriv (hermiteFun m) x
        = Real.sqrt 2 * (m : ℝ) * hermiteFun (m - 1) x - x * hermiteFun m x := by linarith
    rw [e1, h2]
    ring
  have hortho : (∫ x, Real.sqrt 2 * (m : ℝ) * hermiteFun (m - 1) x * hermiteFun (m + 1) x) = 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hne : m - 1 ≠ m + 1 := by omega
      have hz := integral_hermiteFun_mul_eq_zero_of_ne hne
      have hrw : (∫ x, Real.sqrt 2 * (m : ℝ) * hermiteFun (m - 1) x * hermiteFun (m + 1) x)
          = Real.sqrt 2 * (m : ℝ) * ∫ x, hermiteFun (m - 1) x * hermiteFun (m + 1) x := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring
      rw [hrw, hz, mul_zero]
  have hconst : (∫ x, Real.sqrt 2 * ((m : ℝ) + 1) * hermiteFun m x * hermiteFun m x)
      = Real.sqrt 2 * ((m : ℝ) + 1) * ∫ x, hermiteFun m x * hermiteFun m x := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hsplit, hortho, hconst] at hzero
  linarith

/-! ## The norm recursion -/

/-- **The `L²` norm recursion of the Hermite functions.** -/
theorem integral_hermiteFun_sq_succ (m : ℕ) :
    (∫ x, hermiteFun (m + 1) x ^ (2 : ℕ)) = ((m : ℝ) + 1) * ∫ x, hermiteFun m x ^ (2 : ℕ) := by
  have hA : Integrable fun x : ℝ =>
      Real.sqrt 2 * (x * (hermiteFun m x * hermiteFun (m + 1) x)) :=
    (integrable_id_mul_hermiteFun_mul m (m + 1)).const_mul _
  have hB : Integrable fun x : ℝ =>
      (m : ℝ) * (hermiteFun (m - 1) x * hermiteFun (m + 1) x) :=
    (integrable_hermiteFun_mul (m - 1) (m + 1)).const_mul _
  have hsplit : (∫ x, hermiteFun (m + 1) x ^ (2 : ℕ))
      = (∫ x, Real.sqrt 2 * (x * (hermiteFun m x * hermiteFun (m + 1) x)))
        - ∫ x, (m : ℝ) * (hermiteFun (m - 1) x * hermiteFun (m + 1) x) := by
    rw [← MeasureTheory.integral_sub hA hB]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have h := hermiteFun_succ_uniform m x
    show hermiteFun (m + 1) x ^ (2 : ℕ)
        = Real.sqrt 2 * (x * (hermiteFun m x * hermiteFun (m + 1) x))
          - (m : ℝ) * (hermiteFun (m - 1) x * hermiteFun (m + 1) x)
    rw [sq]
    nth_rewrite 1 [h]
    ring
  have hortho : (∫ x, (m : ℝ) * (hermiteFun (m - 1) x * hermiteFun (m + 1) x)) = 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hne : m - 1 ≠ m + 1 := by omega
      rw [MeasureTheory.integral_const_mul, integral_hermiteFun_mul_eq_zero_of_ne hne, mul_zero]
  have hcross := integral_id_mul_hermiteFun_mul_succ m
  have hsq : (∫ x, hermiteFun m x * hermiteFun m x) = ∫ x, hermiteFun m x ^ (2 : ℕ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show hermiteFun m x * hermiteFun m x = hermiteFun m x ^ (2 : ℕ)
    rw [sq]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [hsplit, hortho, MeasureTheory.integral_const_mul, hcross, hsq]
  linear_combination (((m : ℝ) + 1) / 2 * ∫ x, hermiteFun m x ^ (2 : ℕ)) * hs2

/-! ## The two Gaussian values -/

theorem integral_hermiteFun_zero_val :
    (∫ x, hermiteFun 0 x) = Real.sqrt (2 * Real.pi) := by
  have hfun : (∫ x, hermiteFun 0 x) = ∫ x : ℝ, Real.exp (-(1 / 2) * x ^ (2 : ℕ)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show hermiteFun 0 x = Real.exp (-(1 / 2) * x ^ (2 : ℕ))
    rw [hermiteFun_zero_eq]
    congr 1
    ring
  rw [hfun, integral_gaussian]
  congr 1
  field_simp

theorem integral_hermiteFun_zero_sq :
    (∫ x, hermiteFun 0 x ^ (2 : ℕ)) = Real.sqrt Real.pi := by
  have hfun : (∫ x, hermiteFun 0 x ^ (2 : ℕ)) = ∫ x : ℝ, Real.exp (-1 * x ^ (2 : ℕ)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show hermiteFun 0 x ^ (2 : ℕ) = Real.exp (-1 * x ^ (2 : ℕ))
    rw [hermiteFun_zero_eq, sq, ← Real.exp_add]
    congr 1
    ring
  rw [hfun, integral_gaussian]
  congr 1
  field_simp

/-! ## The shape ratio at an even rung -/

/-- The whole-line shape ratio of a Hermite function. -/
def hermiteShapeRatio (n : ℕ) : ℝ :=
  (∫ x, hermiteFun n x) ^ (2 : ℕ) / ∫ x, hermiteFun n x ^ (2 : ℕ)

theorem hermiteShapeRatio_zero : hermiteShapeRatio 0 = 2 * Real.sqrt Real.pi := by
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hsq : Real.sqrt (2 * Real.pi) ^ (2 : ℕ) = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  rw [hermiteShapeRatio, integral_hermiteFun_zero_val, integral_hermiteFun_zero_sq, hsq,
    div_eq_iff hpi.ne']
  nlinarith [hpp]

/-- **The even shape ratios follow the central-binomial profile.** -/
theorem hermiteShapeRatio_two_mul (k : ℕ) :
    hermiteShapeRatio (2 * k) = 2 * Real.sqrt Real.pi * (Nat.centralBinom k : ℝ) / 4 ^ k := by
  induction k with
  | zero => simpa [Nat.centralBinom_zero] using hermiteShapeRatio_zero
  | succ m ih =>
      have hI : (∫ x, hermiteFun (2 * m + 2) x)
          = ((2 * m : ℕ) + 1 : ℝ) * ∫ x, hermiteFun (2 * m) x :=
        integral_hermiteFun_add_two (2 * m)
      have hN1 : (∫ x, hermiteFun (2 * m + 1) x ^ (2 : ℕ))
          = ((2 * m : ℕ) + 1 : ℝ) * ∫ x, hermiteFun (2 * m) x ^ (2 : ℕ) :=
        integral_hermiteFun_sq_succ (2 * m)
      have hN2 : (∫ x, hermiteFun (2 * m + 2) x ^ (2 : ℕ))
          = ((2 * m + 1 : ℕ) + 1 : ℝ) * ∫ x, hermiteFun (2 * m + 1) x ^ (2 : ℕ) :=
        integral_hermiteFun_sq_succ (2 * m + 1)
      have hNpos : (0 : ℝ) < ∫ x, hermiteFun (2 * m) x ^ (2 : ℕ) :=
        integral_hermiteFun_sq_pos_line (2 * m)
      have hbin := Nat.succ_mul_centralBinom_succ m
      have hbinR : ((m : ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ)
          = 2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hbin
      have hidx : 2 * (m + 1) = 2 * m + 2 := by ring
      rw [hidx, hermiteShapeRatio, hI, hN2, hN1]
      rw [hermiteShapeRatio] at ih
      have hm1 : (0 : ℝ) < (2 * m : ℕ) + 1 := by positivity
      have hm2 : (0 : ℝ) < (2 * m + 1 : ℕ) + 1 := by positivity
      have hIH : (∫ x, hermiteFun (2 * m) x) ^ (2 : ℕ)
          = (2 * Real.sqrt Real.pi * (Nat.centralBinom m : ℝ) / 4 ^ m)
            * ∫ x, hermiteFun (2 * m) x ^ (2 : ℕ) := by
        rw [← ih]
        field_simp
      push_cast at hm1 hm2 hIH ⊢
      rw [mul_pow, hIH]
      have h4 : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
      field_simp
      linear_combination (-2 * (4 : ℝ) ^ m) * hbinR

/-! ## The bridge to the constrained-prolate Hermite coordinate -/

theorem hermiteShapeRatio_four_mul (j : ℕ) :
    hermiteShapeRatio (4 * j)
      = 2 * Real.sqrt Real.pi * (Nat.choose (4 * j) (2 * j) : ℝ) / 16 ^ j := by
  have hidx : (4 : ℕ) * j = 2 * (2 * j) := by ring
  have hcb : (Nat.centralBinom (2 * j) : ℝ) = (Nat.choose (4 * j) (2 * j) : ℝ) := by
    rw [Nat.centralBinom, ← hidx]
  have hpow : ((4 : ℝ)) ^ (2 * j) = (16 : ℝ) ^ j := by
    rw [pow_mul]
    norm_num
  calc hermiteShapeRatio (4 * j) = hermiteShapeRatio (2 * (2 * j)) := by rw [hidx]
    _ = 2 * Real.sqrt Real.pi * (Nat.centralBinom (2 * j) : ℝ) / 4 ^ (2 * j) :=
        hermiteShapeRatio_two_mul (2 * j)
    _ = 2 * Real.sqrt Real.pi * (Nat.choose (4 * j) (2 * j) : ℝ) / 16 ^ j := by
        rw [hcb, hpow]

/-- **The Hermite shape ratio is the constrained-prolate Hermite coordinate, squared.**  The two
carry the same central-binomial profile; the constant `√(2π)` is the whole difference between the
analytic normalization and the constrained-prolate one. -/
theorem hermiteShapeRatio_four_mul_eq_coordinate_sq (j : ℕ) :
    hermiteShapeRatio (4 * j)
      = Real.sqrt (2 * Real.pi) * constrainedProlateHermiteCoordinate j ^ (2 : ℕ) := by
  have hw : (0 : ℝ) ≤ Real.sqrt 2 * constrainedProlateHermiteWeight j :=
    le_of_lt (mul_pos (Real.sqrt_pos.2 (by norm_num)) (constrainedProlateHermiteWeight_pos j))
  have hcoord : constrainedProlateHermiteCoordinate j ^ (2 : ℕ)
      = Real.sqrt 2 * constrainedProlateHermiteWeight j := by
    rw [constrainedProlateHermiteCoordinate, Real.sq_sqrt hw]
  have hconst : Real.sqrt (2 * Real.pi) * Real.sqrt 2 = 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Real.pi, mul_comm (Real.sqrt 2) (Real.sqrt Real.pi)]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [h2, Real.sqrt_nonneg Real.pi, Real.sqrt_nonneg 2]
  rw [hcoord, hermiteShapeRatio_four_mul, constrainedProlateHermiteWeight, ← mul_assoc, hconst]
  ring

end RHTower

end
