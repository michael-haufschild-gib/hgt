import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62ReflectedSplit

/-!
# Chen--Gupta--Li Lemma 6.2: off-line reflected Euler correction

The source finite-polynomial contour moves from `Re(s)=-1` to `Re(s)=1/2`.
Its finite Euler correction is extended off the original line here, and is
proved holomorphic on the whole closed displacement strip.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's left finite Euler factor at an arbitrary reflected contour point. -/
def cglLemma62EulerLeftFactorAt (B : CGLLemma62InducedCharacter) (z : ℂ) : ℂ :=
  ∏ p ∈ B.ambient.value.primeFactors,
    (1 - B.primitive.character p * (p : ℂ) ^ (-z))

/-- CGL's reflected right finite Euler factor at an arbitrary contour point. -/
def cglLemma62EulerRightFactorAt (B : CGLLemma62InducedCharacter) (z : ℂ) : ℂ :=
  ∏ p ∈ B.ambient.value.primeFactors,
    (1 - B.primitive.character⁻¹ p * (p : ℂ) ^ (-(1 - z)))

/-- The finite Euler correction used by CGL after functional-equation
reflection, extended across the finite-part displacement strip. -/
def cglLemma62EulerCorrectionAt (B : CGLLemma62InducedCharacter) (z : ℂ) : ℂ :=
  cglLemma62EulerLeftFactorAt B z / cglLemma62EulerRightFactorAt B z

theorem cglLemma62EulerLeftFactorAt_eq_line (B : CGLLemma62InducedCharacter) (t v : ℝ) :
    cglLemma62EulerLeftFactorAt B (cglLemma62LeftPoint t v) =
      cglLemma62EulerLeftFactor B t v := rfl

theorem cglLemma62EulerRightFactorAt_eq_line (B : CGLLemma62InducedCharacter) (t v : ℝ) :
    cglLemma62EulerRightFactorAt B (cglLemma62LeftPoint t v) =
      cglLemma62EulerRightFactor B t v := by
  unfold cglLemma62EulerRightFactorAt cglLemma62EulerRightFactor
  congr 3
  unfold cglLemma62LeftPoint cglLemma62RightPoint
  push_cast
  ring

/-- The off-line correction restricts exactly to CGL's original correction on
the `Re(s)=-1` reflected line. -/
theorem cglLemma62EulerCorrectionAt_eq_line (B : CGLLemma62InducedCharacter) (t v : ℝ) :
    cglLemma62EulerCorrectionAt B (cglLemma62LeftPoint t v) =
      cglLemma62EulerCorrection B t v := by
  unfold cglLemma62EulerCorrectionAt cglLemma62EulerCorrection
  rw [cglLemma62EulerLeftFactorAt_eq_line, cglLemma62EulerRightFactorAt_eq_line]

private theorem cglLemma62EulerRightFactorAt_factor_ne_zero
    (B : CGLLemma62InducedCharacter) (z : ℂ) (hz : z.re ≤ (1 / 2 : ℝ))
    (p : ↑B.ambient.value.primeFactors) :
    1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z)) ≠ 0 := by
  have hpprime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpcastpos : 0 < (p.1 : ℝ) := by exact_mod_cast hpprime.pos
  let w : ℂ := (p.1 : ℂ) ^ (-(1 - z))
  have hpow : ‖w‖ < 1 := by
    dsimp [w]
    change ‖((p.1 : ℝ) : ℂ) ^ (-(1 - z))‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpcastpos]
    have hre : (-(1 - z)).re < (0 : ℝ) := by
      simp only [neg_re, sub_re, one_re]
      linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpprime.one_lt) hre
  have hchar : ‖B.primitive.character⁻¹ p.1‖ ≤ 1 :=
    B.primitive.character⁻¹.norm_le_one p.1
  have hmul : ‖B.primitive.character⁻¹ p.1 * w‖ < 1 := by
    calc
      ‖B.primitive.character⁻¹ p.1 * w‖ = ‖B.primitive.character⁻¹ p.1‖ * ‖w‖ :=
        norm_mul _ _
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hchar (norm_nonneg _)
      _ < 1 := by simpa using hpow
  intro hzero
  have hone : B.primitive.character⁻¹ p.1 * w = 1 := by
    apply (sub_eq_zero.mp ?_).symm
    simpa only [w] using hzero
  have hnorm := congrArg norm hone
  rw [norm_one] at hnorm
  linarith

private theorem cglLemma62EulerLeftFactorAt_differentiable
    (B : CGLLemma62InducedCharacter) :
    Differentiable ℂ (cglLemma62EulerLeftFactorAt B) := by
  intro z
  unfold cglLemma62EulerLeftFactorAt
  have hprod : DifferentiableAt ℂ (Finset.prod B.ambient.value.primeFactors
      (fun p => fun z : ℂ => 1 - B.primitive.character p * (p : ℂ) ^ (-z))) z := by
    apply DifferentiableAt.finsetProd
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) z := by
      exact DifferentiableAt.cpow (differentiableAt_const _) differentiableAt_id.neg
        (Complex.ofReal_mem_slitPlane.mpr hppos)
    exact (differentiableAt_const _).sub ((differentiableAt_const _).mul hpow)
  refine hprod.congr_of_eventuallyEq ?_
  filter_upwards with y
  simp only [Finset.prod_apply]

private theorem cglLemma62EulerRightFactorAt_differentiable
    (B : CGLLemma62InducedCharacter) :
    Differentiable ℂ (cglLemma62EulerRightFactorAt B) := by
  intro z
  unfold cglLemma62EulerRightFactorAt
  have hprod : DifferentiableAt ℂ (Finset.prod B.ambient.value.primeFactors
      (fun p => fun z : ℂ => 1 - B.primitive.character⁻¹ p *
        (p : ℂ) ^ (-(1 - z)))) z := by
    apply DifferentiableAt.finsetProd
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hexp : DifferentiableAt ℂ (fun z : ℂ => -(1 - z)) z :=
      ((differentiableAt_const _).sub differentiableAt_id).neg
    have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-(1 - z))) z := by
      exact DifferentiableAt.cpow (differentiableAt_const _) hexp
        (Complex.ofReal_mem_slitPlane.mpr hppos)
    exact (differentiableAt_const _).sub ((differentiableAt_const _).mul hpow)
  refine hprod.congr_of_eventuallyEq ?_
  filter_upwards with y
  simp only [Finset.prod_apply]

private theorem cglLemma62EulerRightFactorAt_ne_zero_on
    (B : CGLLemma62InducedCharacter) (z : ℂ) (hz : z.re ≤ (1 / 2 : ℝ)) :
    cglLemma62EulerRightFactorAt B z ≠ 0 := by
  unfold cglLemma62EulerRightFactorAt
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact cglLemma62EulerRightFactorAt_factor_ne_zero B z hz ⟨p, hp⟩

/-- The reflected finite Euler correction is holomorphic throughout the full
`-1≤Re(s)≤1/2` contour-displacement strip. -/
theorem cglLemma62EulerCorrectionAt_differentiableOn
    (B : CGLLemma62InducedCharacter) :
    DifferentiableOn ℂ (cglLemma62EulerCorrectionAt B)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) := by
  intro z hz
  unfold cglLemma62EulerCorrectionAt
  exact (((cglLemma62EulerLeftFactorAt_differentiable B z).div
    (cglLemma62EulerRightFactorAt_differentiable B z)
    (cglLemma62EulerRightFactorAt_ne_zero_on B z (by exact hz.2))).differentiableWithinAt)

/-- A certified left-tail point for CGL's finite Euler correction. -/
structure CGLLemma62LeftEulerPoint where
  value : ℂ
  upper : value.re ≤ -1

/-- The finite reflected Euler correction is differentiable at every CGL
left-tail point.  Its denominator is nonzero there by the same strict
Euler-factor estimate used on the finite displacement strip. -/
theorem cglLemma62EulerCorrectionAt_differentiableAt_left
    (B : CGLLemma62InducedCharacter) (z : CGLLemma62LeftEulerPoint) :
    DifferentiableAt ℂ (cglLemma62EulerCorrectionAt B) z.value := by
  unfold cglLemma62EulerCorrectionAt
  exact (cglLemma62EulerLeftFactorAt_differentiable B z.value).div
    (cglLemma62EulerRightFactorAt_differentiable B z.value)
    (cglLemma62EulerRightFactorAt_ne_zero_on B z.value (by linarith [z.upper]))

end

end RHTower
