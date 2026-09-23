import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayAnisotropicPhase

/-!
# Exact coordinate equivalence for a primitive theta ray

The existing arithmetic polar identities recovered the radial and angular variables after the
inverse substitution.  This file proves the converse identities and packages the substitution as
an actual equivalence between the positive source quadrant and the active primitive-ray chamber.
Together with the already proved signed Jacobian, this leaves a measure-theoretic
change-of-variables theorem as the only coordinate-level gap.
-/

open Complex Real MeasureTheory Set

namespace RHTower

noncomputable section

theorem exp_thetaCuspPrimitiveRayRadialLog_sq
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    Real.exp (thetaCuspPrimitiveRayRadialLog a b x y) ^ (2 : ℕ) =
      ((a : ℝ) * Real.exp x) ^ (2 : ℕ) + ((b : ℝ) * Real.exp y) ^ (2 : ℕ) := by
  let S : ℝ := ((a : ℝ) * Real.exp x) ^ (2 : ℕ) + ((b : ℝ) * Real.exp y) ^ (2 : ℕ)
  have hS : 0 < S := by
    dsimp only [S]
    positivity
  unfold thetaCuspPrimitiveRayRadialLog
  change Real.exp ((1 / 2 : ℝ) * Real.log S) ^ (2 : ℕ) = S
  rw [pow_two, ← Real.exp_add]
  rw [show (1 / 2 : ℝ) * Real.log S + (1 / 2 : ℝ) * Real.log S =
      Real.log S by ring,
    Real.exp_log hS]

theorem thetaCuspPrimitiveRayAngularWeight_pos
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    0 < thetaCuspPrimitiveRayAngularWeight a b x y := by
  unfold thetaCuspPrimitiveRayAngularWeight
  positivity

theorem thetaCuspPrimitiveRayAngularWeight_lt_one
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    thetaCuspPrimitiveRayAngularWeight a b x y < 1 := by
  unfold thetaCuspPrimitiveRayAngularWeight
  have hA : 0 ≤ ((a : ℝ) * Real.exp x) ^ (2 : ℕ) := sq_nonneg _
  have hB : 0 < ((b : ℝ) * Real.exp y) ^ (2 : ℕ) :=
    sq_pos_of_pos (mul_pos (by exact_mod_cast hb) (Real.exp_pos y))
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem thetaCuspPrimitiveRayAngularWeight_mul_exp_radialLog_sq
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    thetaCuspPrimitiveRayAngularWeight a b x y *
        Real.exp (thetaCuspPrimitiveRayRadialLog a b x y) ^ (2 : ℕ) =
      ((a : ℝ) * Real.exp x) ^ (2 : ℕ) := by
  rw [exp_thetaCuspPrimitiveRayRadialLog_sq ha hb]
  unfold thetaCuspPrimitiveRayAngularWeight
  field_simp

theorem one_sub_thetaCuspPrimitiveRayAngularWeight_mul_exp_radialLog_sq
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    (1 - thetaCuspPrimitiveRayAngularWeight a b x y) *
        Real.exp (thetaCuspPrimitiveRayRadialLog a b x y) ^ (2 : ℕ) =
      ((b : ℝ) * Real.exp y) ^ (2 : ℕ) := by
  rw [exp_thetaCuspPrimitiveRayRadialLog_sq ha hb]
  unfold thetaCuspPrimitiveRayAngularWeight
  have hden : ((a : ℝ) * Real.exp x) ^ (2 : ℕ) +
      ((b : ℝ) * Real.exp y) ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- First inverse-coordinate identity on the full positive quadrant. -/
theorem thetaCuspPrimitiveRayArithmeticPolarX_radialLog_angularWeight
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    thetaCuspPrimitiveRayArithmeticPolarX a
        (thetaCuspPrimitiveRayRadialLog a b x y)
        (thetaCuspPrimitiveRayAngularWeight a b x y) = x := by
  let r := thetaCuspPrimitiveRayRadialLog a b x y
  let u := thetaCuspPrimitiveRayAngularWeight a b x y
  have hu : 0 < u := thetaCuspPrimitiveRayAngularWeight_pos ha hb x y
  have hsq := thetaCuspPrimitiveRayArithmeticPolarX_scaled_sq ha r hu
  have htarget := thetaCuspPrimitiveRayAngularWeight_mul_exp_radialLog_sq ha hb x y
  change u * Real.exp r ^ (2 : ℕ) = ((a : ℝ) * Real.exp x) ^ (2 : ℕ) at htarget
  rw [htarget] at hsq
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hleft : 0 < (a : ℝ) * Real.exp
      (thetaCuspPrimitiveRayArithmeticPolarX a r u) :=
    mul_pos haR (Real.exp_pos _)
  have hright : 0 < (a : ℝ) * Real.exp x := mul_pos haR (Real.exp_pos x)
  have hmul : (a : ℝ) * Real.exp
      (thetaCuspPrimitiveRayArithmeticPolarX a r u) =
        (a : ℝ) * Real.exp x := by nlinarith
  have hexp : Real.exp (thetaCuspPrimitiveRayArithmeticPolarX a r u) =
      Real.exp x := by nlinarith
  exact Real.exp_injective hexp

/-- Second inverse-coordinate identity on the full positive quadrant. -/
theorem thetaCuspPrimitiveRayArithmeticPolarY_radialLog_angularWeight
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    thetaCuspPrimitiveRayArithmeticPolarY b
        (thetaCuspPrimitiveRayRadialLog a b x y)
        (thetaCuspPrimitiveRayAngularWeight a b x y) = y := by
  let r := thetaCuspPrimitiveRayRadialLog a b x y
  let u := thetaCuspPrimitiveRayAngularWeight a b x y
  have hu : u < 1 := thetaCuspPrimitiveRayAngularWeight_lt_one ha hb x y
  have hsq := thetaCuspPrimitiveRayArithmeticPolarY_scaled_sq hb r hu
  have htarget := one_sub_thetaCuspPrimitiveRayAngularWeight_mul_exp_radialLog_sq ha hb x y
  change (1 - u) * Real.exp r ^ (2 : ℕ) = ((b : ℝ) * Real.exp y) ^ (2 : ℕ) at htarget
  rw [htarget] at hsq
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hleft : 0 < (b : ℝ) * Real.exp
      (thetaCuspPrimitiveRayArithmeticPolarY b r u) :=
    mul_pos hbR (Real.exp_pos _)
  have hright : 0 < (b : ℝ) * Real.exp y := mul_pos hbR (Real.exp_pos y)
  have hmul : (b : ℝ) * Real.exp
      (thetaCuspPrimitiveRayArithmeticPolarY b r u) =
        (b : ℝ) * Real.exp y := by nlinarith
  have hexp : Real.exp (thetaCuspPrimitiveRayArithmeticPolarY b r u) =
      Real.exp y := by nlinarith
  exact Real.exp_injective hexp

/-- Positive source quadrant for the original two-variable core correlation. -/
def ThetaCuspPositiveQuadrant :=
  {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2}

/-- Active radial-angular chamber for a fixed positive arithmetic direction. -/
def ThetaCuspPrimitiveRayActiveChamber (a b : ℕ) :=
  {q : ℝ × ℝ //
    0 < q.2 ∧ q.2 < 1 ∧
      0 < thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2 ∧
      0 < thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2}

/-- **Exact primitive-ray coordinate equivalence.**  For every positive arithmetic direction,
the original positive quadrant and the full active polar chamber are mutually inverse, with no
discarded endpoint or auxiliary cutoff. -/
def thetaCuspPositiveQuadrantEquivPrimitiveRayActiveChamber
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ThetaCuspPositiveQuadrant ≃ ThetaCuspPrimitiveRayActiveChamber a b where
  toFun p := by
    let r := thetaCuspPrimitiveRayRadialLog a b p.1.1 p.1.2
    let u := thetaCuspPrimitiveRayAngularWeight a b p.1.1 p.1.2
    refine ⟨(r, u), ?_⟩
    have hu0 : 0 < u := thetaCuspPrimitiveRayAngularWeight_pos ha hb p.1.1 p.1.2
    have hu1 : u < 1 := thetaCuspPrimitiveRayAngularWeight_lt_one ha hb p.1.1 p.1.2
    refine ⟨hu0, hu1, ?_, ?_⟩
    · rw [thetaCuspPrimitiveRayArithmeticPolarX_radialLog_angularWeight ha hb]
      exact p.property.1
    · rw [thetaCuspPrimitiveRayArithmeticPolarY_radialLog_angularWeight ha hb]
      exact p.property.2
  invFun q := ⟨
    (thetaCuspPrimitiveRayArithmeticPolarX a q.1.1 q.1.2,
      thetaCuspPrimitiveRayArithmeticPolarY b q.1.1 q.1.2),
    q.property.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact thetaCuspPrimitiveRayArithmeticPolarX_radialLog_angularWeight
        ha hb p.1.1 p.1.2
    · exact thetaCuspPrimitiveRayArithmeticPolarY_radialLog_angularWeight
        ha hb p.1.1 p.1.2
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · exact thetaCuspPrimitiveRayRadialLog_arithmeticPolar ha hb q.1.1
        q.property.1 q.property.2.1
    · exact thetaCuspPrimitiveRayAngularWeight_arithmeticPolar ha hb q.1.1
        q.property.1 q.property.2.1

end

end RHTower
