import GaloisForLFunctions.RHTower.HermiteFunctionOrthogonality
import GaloisForLFunctions.RHTower.OscillatorEvenRigidity

/-!
# The whole-line integral of a Hermite function

The first moment of the Hermite functions satisfies a two-step recursion with no analysis in it
beyond one vanishing boundary term:

```text
∫_ℝ φ_{n+2} = (n+1) · ∫_ℝ φ_n .
```

Two pointwise identities carry it.  The three-term recursion of the Hermite polynomials gives
`φ_{n+2} = √2·x·φ_{n+1} − (n+1)·φ_n`, and the Appell law `He_{n+1}′ = (n+1)He_n` gives
`φ_{n+1}′ = √2(n+1)·φ_n − x·φ_{n+1}`.  A Hermite function and its derivative are polynomials times
a Gaussian, so both are integrable and the derivative integrates to zero; that turns the second
identity into `∫ x·φ_{n+1} = √2(n+1)∫φ_n`, and substituting it into the first gives the recursion.

Since `φ_0` is a Gaussian, the even first moments are all positive.  That is the nonvanishing the
shape-ratio normalization consumes: the limiting shape ratio of a prolate mode at an even rung is
not zero.
-/

noncomputable section

open MeasureTheory Set Filter Topology Polynomial

namespace RHTower

/-! ## Integrability on the line -/

theorem integrable_hermiteFun (n : ℕ) : Integrable (hermiteFun n) := by
  obtain ⟨p, hp⟩ := exists_poly_hermiteFun n
  refine (integrable_polyEval_mul_gauss p (b := 1 / 2) (by norm_num)).congr ?_
  exact Filter.Eventually.of_forall fun x => (hp x).symm

theorem integral_hermiteFun_sq_pos_line (n : ℕ) : 0 < ∫ x, hermiteFun n x ^ 2 := by
  have hint : Integrable fun x => hermiteFun n x ^ 2 := integrable_hermiteFun_sq n
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume] fun x => hermiteFun n x ^ 2 :=
    Filter.Eventually.of_forall fun x => by simpa using sq_nonneg (hermiteFun n x)
  have hwin : 0 < ∫ x in (-1 : ℝ)..1, hermiteFun n x ^ 2 :=
    integral_hermiteFun_sq_pos n (by norm_num : (-1 : ℝ) < 1)
  have hset : (∫ x in (-1 : ℝ)..1, hermiteFun n x ^ 2)
      = ∫ x in Ioc (-1 : ℝ) 1, hermiteFun n x ^ 2 :=
    intervalIntegral.integral_of_le (by norm_num)
  have hle : (∫ x in Ioc (-1 : ℝ) 1, hermiteFun n x ^ 2) ≤ ∫ x, hermiteFun n x ^ 2 :=
    MeasureTheory.setIntegral_le_integral hint hnn
  rw [hset] at hwin
  linarith

theorem tendsto_intervalIntegral_hermiteFun (n : ℕ) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, hermiteFun n x) atTop (𝓝 (∫ x, hermiteFun n x)) :=
  intervalIntegral_tendsto_integral (integrable_hermiteFun n) tendsto_neg_atTop_atBot tendsto_id

/-! ## Two pointwise identities -/

theorem hermiteFun_zero_eq (x : ℝ) : hermiteFun 0 x = Real.exp (-(x ^ 2 / 2)) := by
  show probHermiteFun 0 (Real.sqrt 2 * x) = _
  rw [probHermiteFun, Polynomial.hermite_zero]
  have hsq : (Real.sqrt 2 * x) ^ 2 = 2 * x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsq]
  simp only [map_one, one_mul]
  congr 1
  ring

theorem hermiteFun_zero_pos (x : ℝ) : 0 < hermiteFun 0 x := by
  rw [hermiteFun_zero_eq]
  exact Real.exp_pos _

/-- **Three-term recursion for the Hermite functions.** -/
theorem hermiteFun_add_two (n : ℕ) (x : ℝ) :
    hermiteFun (n + 2) x
      = Real.sqrt 2 * x * hermiteFun (n + 1) x - ((n : ℝ) + 1) * hermiteFun n x := by
  have hrec : Polynomial.hermite (n + 2)
      = Polynomial.X * Polynomial.hermite (n + 1) - ((n : Polynomial ℤ) + 1) * hermite n := by
    rw [Polynomial.hermite_succ (n + 1), derivative_hermite_succ n]
  show probHermiteFun (n + 2) (Real.sqrt 2 * x) = _
  show Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite (n + 2))
      * Real.exp (-((Real.sqrt 2 * x) ^ 2 / 4)) = _
  show _ = Real.sqrt 2 * x * (Polynomial.aeval (Real.sqrt 2 * x)
      (Polynomial.hermite (n + 1)) * Real.exp (-((Real.sqrt 2 * x) ^ 2 / 4)))
    - ((n : ℝ) + 1) * (Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n)
      * Real.exp (-((Real.sqrt 2 * x) ^ 2 / 4)))
  rw [hrec]
  simp only [map_sub, map_mul, map_add, map_natCast, map_one, Polynomial.aeval_X]
  ring

/-- **Appell law for the Hermite functions.** -/
theorem deriv_hermiteFun_succ (n : ℕ) (x : ℝ) :
    deriv (hermiteFun (n + 1)) x
      = Real.sqrt 2 * ((n : ℝ) + 1) * hermiteFun n x - x * hermiteFun (n + 1) x := by
  rw [deriv_hermiteFun_eq, deriv_probHermiteFun]
  simp only
  rw [derivative_hermite_succ n]
  have hsq : (Real.sqrt 2 * x) ^ 2 = 2 * x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hval1 : probHermiteFun (n + 1) (Real.sqrt 2 * x) = hermiteFun (n + 1) x := rfl
  have hvaln : Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n)
      * Real.exp (-((Real.sqrt 2 * x) ^ 2 / 4)) = hermiteFun n x := rfl
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [map_mul, map_add, map_natCast, map_one]
  rw [hval1]
  linear_combination (Real.sqrt 2 * ((n : ℝ) + 1)) * hvaln
    - (x * hermiteFun (n + 1) x / 2) * hs2

/-! ## Integrability -/

theorem integrable_id_mul_hermiteFun (n : ℕ) : Integrable fun x : ℝ => x * hermiteFun n x := by
  obtain ⟨p, hp⟩ := exists_poly_hermiteFun n
  refine (integrable_polyEval_mul_gauss (Polynomial.X * p) (b := 1 / 2) (by norm_num)).congr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  show Polynomial.eval x (Polynomial.X * p) * Real.exp (-(1 / 2 * x ^ 2)) = x * hermiteFun n x
  rw [hp x, Polynomial.eval_mul, Polynomial.eval_X]
  ring

theorem integrable_deriv_hermiteFun_succ (n : ℕ) : Integrable (deriv (hermiteFun (n + 1))) := by
  have h1 : Integrable fun x : ℝ => Real.sqrt 2 * ((n : ℝ) + 1) * hermiteFun n x :=
    (integrable_hermiteFun n).const_mul _
  have h2 : Integrable fun x : ℝ => x * hermiteFun (n + 1) x :=
    integrable_id_mul_hermiteFun (n + 1)
  refine (h1.sub h2).congr ?_
  exact Filter.Eventually.of_forall fun x => (deriv_hermiteFun_succ n x).symm

/-! ## The derivative integrates to zero -/

theorem integral_deriv_hermiteFun_succ (n : ℕ) : (∫ x, deriv (hermiteFun (n + 1)) x) = 0 := by
  have hint := integrable_deriv_hermiteFun_succ n
  have hwin : ∀ R : ℝ, (∫ x in (-R)..R, deriv (hermiteFun (n + 1)) x)
      = hermiteFun (n + 1) R - hermiteFun (n + 1) (-R) := by
    intro R
    refine intervalIntegral.integral_deriv_eq_sub (fun x _ => differentiable_hermiteFun _ x) ?_
    exact (continuous_deriv_hermiteFun _).intervalIntegrable _ _
  have hlim1 : Tendsto (fun R : ℝ => ∫ x in (-R)..R, deriv (hermiteFun (n + 1)) x) atTop
      (𝓝 (∫ x, deriv (hermiteFun (n + 1)) x)) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hlim2 : Tendsto (fun R : ℝ => hermiteFun (n + 1) R - hermiteFun (n + 1) (-R)) atTop
      (𝓝 0) := by
    have hA := tendsto_hermiteFun_atTop (n + 1)
    have hB := (tendsto_hermiteFun_atBot (n + 1)).comp tendsto_neg_atTop_atBot
    simpa using hA.sub hB
  have hcongr : Tendsto (fun R : ℝ => ∫ x in (-R)..R, deriv (hermiteFun (n + 1)) x) atTop
      (𝓝 0) := by
    refine hlim2.congr fun R => (hwin R).symm
  exact tendsto_nhds_unique hlim1 hcongr

/-! ## The two-step recursion of the first moment -/

theorem integral_id_mul_hermiteFun_succ (n : ℕ) :
    (∫ x, x * hermiteFun (n + 1) x)
      = Real.sqrt 2 * ((n : ℝ) + 1) * ∫ x, hermiteFun n x := by
  have h1 : Integrable fun x : ℝ => Real.sqrt 2 * ((n : ℝ) + 1) * hermiteFun n x :=
    (integrable_hermiteFun n).const_mul _
  have h2 : Integrable fun x : ℝ => x * hermiteFun (n + 1) x :=
    integrable_id_mul_hermiteFun (n + 1)
  have hzero := integral_deriv_hermiteFun_succ n
  have hsplit : (∫ x, deriv (hermiteFun (n + 1)) x)
      = (∫ x, Real.sqrt 2 * ((n : ℝ) + 1) * hermiteFun n x)
        - ∫ x, x * hermiteFun (n + 1) x := by
    rw [← MeasureTheory.integral_sub h1 h2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact deriv_hermiteFun_succ n x
  rw [hsplit, MeasureTheory.integral_const_mul] at hzero
  linarith

/-- **The two-step recursion of the Hermite first moment.** -/
theorem integral_hermiteFun_add_two (n : ℕ) :
    (∫ x, hermiteFun (n + 2) x) = ((n : ℝ) + 1) * ∫ x, hermiteFun n x := by
  have h1 : Integrable fun x : ℝ => Real.sqrt 2 * (x * hermiteFun (n + 1) x) :=
    (integrable_id_mul_hermiteFun (n + 1)).const_mul _
  have h2 : Integrable fun x : ℝ => ((n : ℝ) + 1) * hermiteFun n x :=
    (integrable_hermiteFun n).const_mul _
  have hsplit : (∫ x, hermiteFun (n + 2) x)
      = (∫ x, Real.sqrt 2 * (x * hermiteFun (n + 1) x))
        - ∫ x, ((n : ℝ) + 1) * hermiteFun n x := by
    rw [← MeasureTheory.integral_sub h1 h2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hermiteFun_add_two n x]
    ring
  rw [hsplit, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_id_mul_hermiteFun_succ n]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination (((n : ℝ) + 1) * ∫ x, hermiteFun n x) * hs2

/-! ## Positivity at even rungs -/

theorem integral_hermiteFun_zero_pos : 0 < ∫ x, hermiteFun 0 x := by
  have hint : Integrable (hermiteFun 0) := integrable_hermiteFun 0
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume] hermiteFun 0 :=
    Filter.Eventually.of_forall fun x => by simpa using (hermiteFun_zero_pos x).le
  have hwin : 0 < ∫ x in (-1 : ℝ)..1, hermiteFun 0 x := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_hermiteFun 0).intervalIntegrable _ _) (fun x _ => hermiteFun_zero_pos x)
      (by norm_num)
  have hset : (∫ x in (-1 : ℝ)..1, hermiteFun 0 x)
      = ∫ x in Ioc (-1 : ℝ) 1, hermiteFun 0 x :=
    intervalIntegral.integral_of_le (by norm_num)
  have hle : (∫ x in Ioc (-1 : ℝ) 1, hermiteFun 0 x) ≤ ∫ x, hermiteFun 0 x :=
    MeasureTheory.setIntegral_le_integral hint hnn
  rw [hset] at hwin
  linarith

/-- **The even Hermite first moments are positive.** -/
theorem integral_hermiteFun_two_mul_pos (k : ℕ) : 0 < ∫ x, hermiteFun (2 * k) x := by
  induction k with
  | zero => simpa using integral_hermiteFun_zero_pos
  | succ m ih =>
      have hidx : 2 * (m + 1) = 2 * m + 2 := by ring
      rw [hidx, integral_hermiteFun_add_two (2 * m)]
      have hpos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) + 1 := by positivity
      exact mul_pos hpos ih

theorem integral_hermiteFun_two_mul_ne_zero (k : ℕ) : (∫ x, hermiteFun (2 * k) x) ≠ 0 :=
  (integral_hermiteFun_two_mul_pos k).ne'

end RHTower

end
