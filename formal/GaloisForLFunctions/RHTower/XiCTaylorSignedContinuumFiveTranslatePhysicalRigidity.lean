import GaloisForLFunctions.RHTower.XiCTaylorSignedContinuumFiveTranslateRigidity

/-!
# Physical five-translate source-provenance rigidity

This file closes the analytic bridge between translated Lebesgue densities and their five-tap
mask symbols. It proves the value and first-moment factorization for arbitrary coefficients,
proves the base rectangle transform is strictly positive, and hence identifies physical
four-row cancellation exactly with the reciprocal double-root row system.

Combining that equivalence with the algebraic kernel classification proves: at fixed positive
translate spacing, no nonzero five-bump physical source can cancel the reflected value and
derivative rows at two distinct positive dampings.
-/

open Real Set MeasureTheory Filter

namespace RHTower

noncomputable section

/-- Five translated rectangle bumps with an arbitrary real coefficient vector. -/
def routeJFiveBumpPhaseDensityWithCoeff
    (a : Fin 5 → ℝ) (L t : ℝ) : ℝ :=
  a 0 * routeJRectangleBump L 0 t +
    a 1 * routeJRectangleBump L 1 t +
    a 2 * routeJRectangleBump L 2 t +
    a 3 * routeJRectangleBump L 3 t +
    a 4 * routeJRectangleBump L 4 t

/-- Arbitrary five-bump exponential value rows are integrable. -/
theorem integrable_exp_mul_routeJFiveBumpPhaseDensityWithCoeff
    (a : Fin 5 → ℝ) (q L : ℝ) :
    Integrable
      (fun t =>
        Real.exp (q * t) *
          routeJFiveBumpPhaseDensityWithCoeff a L t) := by
  have h0 := (integrable_exp_mul_routeJRectangleBump q L 0).const_mul (a 0)
  have h1 := (integrable_exp_mul_routeJRectangleBump q L 1).const_mul (a 1)
  have h2 := (integrable_exp_mul_routeJRectangleBump q L 2).const_mul (a 2)
  have h3 := (integrable_exp_mul_routeJRectangleBump q L 3).const_mul (a 3)
  have h4 := (integrable_exp_mul_routeJRectangleBump q L 4).const_mul (a 4)
  exact ((((h0.add h1).add h2).add h3).add h4).congr
    (Eventually.of_forall fun t => by
      dsimp [routeJFiveBumpPhaseDensityWithCoeff]
      ring)

/-- Arbitrary five-bump exponential first-moment rows are integrable. -/
theorem integrable_t_mul_exp_mul_routeJFiveBumpPhaseDensityWithCoeff
    (a : Fin 5 → ℝ) (q L : ℝ) :
    Integrable
      (fun t =>
        t * Real.exp (q * t) *
          routeJFiveBumpPhaseDensityWithCoeff a L t) := by
  have h0 :=
    (integrable_t_mul_exp_mul_routeJRectangleBump q L 0).const_mul (a 0)
  have h1 :=
    (integrable_t_mul_exp_mul_routeJRectangleBump q L 1).const_mul (a 1)
  have h2 :=
    (integrable_t_mul_exp_mul_routeJRectangleBump q L 2).const_mul (a 2)
  have h3 :=
    (integrable_t_mul_exp_mul_routeJRectangleBump q L 3).const_mul (a 3)
  have h4 :=
    (integrable_t_mul_exp_mul_routeJRectangleBump q L 4).const_mul (a 4)
  exact ((((h0.add h1).add h2).add h3).add h4).congr
    (Eventually.of_forall fun t => by
      dsimp [routeJFiveBumpPhaseDensityWithCoeff]
      ring)

/-- Exact arbitrary-coefficient value-row factorization through the five-tap symbol. -/
theorem integral_exp_mul_routeJFiveBumpPhaseDensityWithCoeff
    {L : ℝ} (hL : 0 < L) (a : Fin 5 → ℝ) (q : ℝ) :
    (∫ t, Real.exp (q * t) *
        routeJFiveBumpPhaseDensityWithCoeff a L t) =
      (∫ t, Real.exp (q * t) * routeJRectangleBump L 0 t) *
        routeJFiveCoeffValue a (Real.exp (q * L)) := by
  let f : ℕ → ℝ → ℝ := fun j t =>
    Real.exp (q * t) * routeJRectangleBump L j t
  have hj (j : ℕ) :
      Real.exp (q * ((j : ℝ) * L)) = Real.exp (q * L) ^ j := by
    rw [show q * ((j : ℝ) * L) = (j : ℝ) * (q * L) by ring,
      Real.exp_nat_mul]
  have hf0 : Integrable (f 0) :=
    integrable_exp_mul_routeJRectangleBump q L 0
  have hf1 : Integrable (f 1) :=
    integrable_exp_mul_routeJRectangleBump q L 1
  have hf2 : Integrable (f 2) :=
    integrable_exp_mul_routeJRectangleBump q L 2
  have hf3 : Integrable (f 3) :=
    integrable_exp_mul_routeJRectangleBump q L 3
  have hf4 : Integrable (f 4) :=
    integrable_exp_mul_routeJRectangleBump q L 4
  let g0 : ℝ → ℝ := fun t => a 0 * f 0 t
  let g1 : ℝ → ℝ := fun t => a 1 * f 1 t
  let g2 : ℝ → ℝ := fun t => a 2 * f 2 t
  let g3 : ℝ → ℝ := fun t => a 3 * f 3 t
  let g4 : ℝ → ℝ := fun t => a 4 * f 4 t
  have hg0 : Integrable g0 := hf0.const_mul (a 0)
  have hg1 : Integrable g1 := hf1.const_mul (a 1)
  have hg2 : Integrable g2 := hf2.const_mul (a 2)
  have hg3 : Integrable g3 := hf3.const_mul (a 3)
  have hg4 : Integrable g4 := hf4.const_mul (a 4)
  have heq :
      (fun t => Real.exp (q * t) *
        routeJFiveBumpPhaseDensityWithCoeff a L t) =
        (((g0 + g1) + g2) + g3) + g4 := by
    funext t
    simp only [Pi.add_apply]
    dsimp [f, g0, g1, g2, g3, g4,
      routeJFiveBumpPhaseDensityWithCoeff]
    ring
  rw [heq,
    integral_add' (((hg0.add hg1).add hg2).add hg3) hg4,
    integral_add' ((hg0.add hg1).add hg2) hg3,
    integral_add' (hg0.add hg1) hg2,
    integral_add' hg0 hg1]
  dsimp only [g0, g1, g2, g3, g4]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul,
    integral_exp_mul_routeJRectangleBump_shift hL q 1,
    integral_exp_mul_routeJRectangleBump_shift hL q 2,
    integral_exp_mul_routeJRectangleBump_shift hL q 3,
    integral_exp_mul_routeJRectangleBump_shift hL q 4,
    hj 1, hj 2, hj 3, hj 4]
  dsimp [f, g0, g1, g2, g3, g4, routeJFiveCoeffValue]
  ring

/-- Exact arbitrary-coefficient first-moment factorization through value and
dilation-derivative symbol rows. -/
theorem integral_t_mul_exp_mul_routeJFiveBumpPhaseDensityWithCoeff
    {L : ℝ} (hL : 0 < L) (a : Fin 5 → ℝ) (q : ℝ) :
    (∫ t, t * Real.exp (q * t) *
        routeJFiveBumpPhaseDensityWithCoeff a L t) =
      (∫ t, t * Real.exp (q * t) *
          routeJRectangleBump L 0 t) *
          routeJFiveCoeffValue a (Real.exp (q * L)) +
        L * (∫ t, Real.exp (q * t) *
          routeJRectangleBump L 0 t) *
          routeJFiveCoeffDilationDerivative a
            (Real.exp (q * L)) := by
  let f : ℕ → ℝ → ℝ := fun j t =>
    t * Real.exp (q * t) * routeJRectangleBump L j t
  have hj (j : ℕ) :
      Real.exp (q * ((j : ℝ) * L)) = Real.exp (q * L) ^ j := by
    rw [show q * ((j : ℝ) * L) = (j : ℝ) * (q * L) by ring,
      Real.exp_nat_mul]
  have hf0 : Integrable (f 0) :=
    integrable_t_mul_exp_mul_routeJRectangleBump q L 0
  have hf1 : Integrable (f 1) :=
    integrable_t_mul_exp_mul_routeJRectangleBump q L 1
  have hf2 : Integrable (f 2) :=
    integrable_t_mul_exp_mul_routeJRectangleBump q L 2
  have hf3 : Integrable (f 3) :=
    integrable_t_mul_exp_mul_routeJRectangleBump q L 3
  have hf4 : Integrable (f 4) :=
    integrable_t_mul_exp_mul_routeJRectangleBump q L 4
  let g0 : ℝ → ℝ := fun t => a 0 * f 0 t
  let g1 : ℝ → ℝ := fun t => a 1 * f 1 t
  let g2 : ℝ → ℝ := fun t => a 2 * f 2 t
  let g3 : ℝ → ℝ := fun t => a 3 * f 3 t
  let g4 : ℝ → ℝ := fun t => a 4 * f 4 t
  have hg0 : Integrable g0 := hf0.const_mul (a 0)
  have hg1 : Integrable g1 := hf1.const_mul (a 1)
  have hg2 : Integrable g2 := hf2.const_mul (a 2)
  have hg3 : Integrable g3 := hf3.const_mul (a 3)
  have hg4 : Integrable g4 := hf4.const_mul (a 4)
  have heq :
      (fun t => t * Real.exp (q * t) *
        routeJFiveBumpPhaseDensityWithCoeff a L t) =
        (((g0 + g1) + g2) + g3) + g4 := by
    funext t
    simp only [Pi.add_apply]
    dsimp [f, g0, g1, g2, g3, g4,
      routeJFiveBumpPhaseDensityWithCoeff]
    ring
  rw [heq,
    integral_add' (((hg0.add hg1).add hg2).add hg3) hg4,
    integral_add' ((hg0.add hg1).add hg2) hg3,
    integral_add' (hg0.add hg1) hg2,
    integral_add' hg0 hg1]
  dsimp only [g0, g1, g2, g3, g4]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul,
    integral_t_mul_exp_mul_routeJRectangleBump_shift hL q 1,
    integral_t_mul_exp_mul_routeJRectangleBump_shift hL q 2,
    integral_t_mul_exp_mul_routeJRectangleBump_shift hL q 3,
    integral_t_mul_exp_mul_routeJRectangleBump_shift hL q 4,
    hj 1, hj 2, hj 3, hj 4]
  dsimp [f, g0, g1, g2, g3, g4, routeJFiveCoeffValue,
    routeJFiveCoeffDilationDerivative]
  ring

/-- The base rectangle bump has strictly positive real exponential transform. -/
theorem integral_exp_mul_routeJRectangleBump_zero_pos
    {L : ℝ} (hL : 0 < L) (q : ℝ) :
    0 < ∫ t, Real.exp (q * t) * routeJRectangleBump L 0 t := by
  let lo : ℝ := L / 4
  let hi : ℝ := 3 * L / 4
  have hlohi : lo < hi := by
    dsimp [lo, hi]
    linarith
  have heq :
      (fun t => Real.exp (q * t) * routeJRectangleBump L 0 t) =
        (Ioc lo hi).indicator (fun t => Real.exp (q * t)) := by
    funext t
    by_cases ht : t ∈ Ioc lo hi
    · simp [routeJRectangleBump, routeJRectangleBumpSupport,
        lo, hi, ht]
    · simp [routeJRectangleBump, routeJRectangleBumpSupport,
        lo, hi, ht]
  rw [heq, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hlohi.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos
    (by
      exact (by fun_prop : Continuous
        (fun t : ℝ => Real.exp (q * t))).intervalIntegrable lo hi)
    (fun t => Real.exp_pos _) hlohi

/-- Four physical reflected value/first-moment cancellation equations for an arbitrary
five-translate density. -/
def routeJFiveBumpPhysicalRows
    (a : Fin 5 → ℝ) (L c : ℝ) : Prop :=
  (∫ t, Real.exp (c * t) *
      routeJFiveBumpPhaseDensityWithCoeff a L t) = 0 ∧
    (∫ t, t * Real.exp (c * t) *
      routeJFiveBumpPhaseDensityWithCoeff a L t) = 0 ∧
    (∫ t, Real.exp (-c * t) *
      routeJFiveBumpPhaseDensityWithCoeff a L t) = 0 ∧
    (∫ t, t * Real.exp (-c * t) *
      routeJFiveBumpPhaseDensityWithCoeff a L t) = 0

/-- Physical cancellation is equivalent to reciprocal symbol value/dilation-derivative
cancellation. -/
theorem routeJFiveBumpPhysicalRows_iff_coeffReflectedRows
    {a : Fin 5 → ℝ} {L c : ℝ} (hL : 0 < L) :
    routeJFiveBumpPhysicalRows a L c ↔
      routeJFiveCoeffReflectedRows a (Real.exp (c * L)) := by
  let r := Real.exp (c * L)
  have hexp : Real.exp (-c * L) = r⁻¹ := by
    dsimp [r]
    rw [show -c * L = -(c * L) by ring, Real.exp_neg]
  have hVplus :
      (∫ t, Real.exp (c * t) *
        routeJRectangleBump L 0 t) ≠ 0 :=
    (integral_exp_mul_routeJRectangleBump_zero_pos hL c).ne'
  have hVminus :
      (∫ t, Real.exp (-c * t) *
        routeJRectangleBump L 0 t) ≠ 0 :=
    (integral_exp_mul_routeJRectangleBump_zero_pos hL (-c)).ne'
  constructor
  · rintro ⟨hVp, hDp, hVm, hDm⟩
    rw [integral_exp_mul_routeJFiveBumpPhaseDensityWithCoeff hL] at hVp
    rw [integral_t_mul_exp_mul_routeJFiveBumpPhaseDensityWithCoeff hL] at hDp
    rw [integral_exp_mul_routeJFiveBumpPhaseDensityWithCoeff hL] at hVm
    rw [integral_t_mul_exp_mul_routeJFiveBumpPhaseDensityWithCoeff hL] at hDm
    change _ * routeJFiveCoeffValue a r = 0 at hVp
    change _ * routeJFiveCoeffValue a r +
      L * _ * routeJFiveCoeffDilationDerivative a r = 0 at hDp
    rw [hexp] at hVm hDm
    change _ * routeJFiveCoeffValue a r⁻¹ = 0 at hVm
    change _ * routeJFiveCoeffValue a r⁻¹ +
      L * _ * routeJFiveCoeffDilationDerivative a r⁻¹ = 0 at hDm
    have hAr : routeJFiveCoeffValue a r = 0 :=
      (mul_eq_zero.mp hVp).resolve_left hVplus
    have hAi : routeJFiveCoeffValue a r⁻¹ = 0 :=
      (mul_eq_zero.mp hVm).resolve_left hVminus
    have hDAr : routeJFiveCoeffDilationDerivative a r = 0 := by
      rw [hAr, mul_zero, zero_add] at hDp
      exact (mul_eq_zero.mp hDp).resolve_left
        (mul_ne_zero hL.ne' hVplus)
    have hDAi : routeJFiveCoeffDilationDerivative a r⁻¹ = 0 := by
      rw [hAi, mul_zero, zero_add] at hDm
      exact (mul_eq_zero.mp hDm).resolve_left
        (mul_ne_zero hL.ne' hVminus)
    exact ⟨hAr, hDAr, hAi, hDAi⟩
  · rintro ⟨hAr, hDAr, hAi, hDAi⟩
    unfold routeJFiveBumpPhysicalRows
    constructor
    · rw [integral_exp_mul_routeJFiveBumpPhaseDensityWithCoeff hL]
      change _ * routeJFiveCoeffValue a r = 0
      rw [hAr, mul_zero]
    constructor
    · rw [integral_t_mul_exp_mul_routeJFiveBumpPhaseDensityWithCoeff hL]
      change _ * routeJFiveCoeffValue a r +
        L * _ * routeJFiveCoeffDilationDerivative a r = 0
      rw [hAr, hDAr]
      ring
    constructor
    · rw [integral_exp_mul_routeJFiveBumpPhaseDensityWithCoeff hL,
        hexp, hAi, mul_zero]
    · rw [integral_t_mul_exp_mul_routeJFiveBumpPhaseDensityWithCoeff hL,
        hexp, hAi, hDAi]
      ring

/-- At fixed positive spacing, one nonzero physical five-bump source serves at most one positive
damping. -/
theorem routeJFiveBumpPhysicalRows_damping_injective
    {a : Fin 5 → ℝ} {L c d : ℝ}
    (hL : 0 < L) (hc : 0 < c) (hd : 0 < d)
    (ha : ∃ j : Fin 5, a j ≠ 0)
    (hrowsc : routeJFiveBumpPhysicalRows a L c)
    (hrowsd : routeJFiveBumpPhysicalRows a L d) :
    c = d := by
  apply routeJFiveCoeffReflectedRows_damping_injective
    hL hc hd ha
  · exact
      (routeJFiveBumpPhysicalRows_iff_coeffReflectedRows hL).mp hrowsc
  · exact
      (routeJFiveBumpPhysicalRows_iff_coeffReflectedRows hL).mp hrowsd

end

end RHTower
