import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1XiCoefficients

/-!
# Affine weights and the degree-rotation exponent

The central and degree coordinates make affine translations quadratic. Their
Weyl action preserves `b² + 4κd`. Pairing `-wλ-ρ` with a torus element and a
positive degree rotation gives an explicit Gaussian exponent on both integer
families of the infinite dihedral group.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1

noncomputable section

/-- Values of an affine weight on the central element, finite coroot, and degree operator. -/
@[ext] structure Weight where
  level : ℂ
  finite : ℂ
  degree : ℂ

/-- Translation by `mα∨` on affine weights. -/
def translateWeight (m : ℤ) (L : Weight) : Weight where
  level := L.level
  finite := L.finite + 2 * m * L.level
  degree := L.degree - m * L.finite - (m : ℂ) ^ 2 * L.level

/-- The finite simple reflection fixes the degree and central coordinates. -/
def reflectWeight (L : Weight) : Weight where
  level := L.level
  finite := -L.finite
  degree := L.degree

private def weightIndex : ZMod 0 ≃+* ℤ := RingEquiv.refl ℤ

/-- The full affine Weyl action on weights. -/
def weightAct : Weyl → Weight → Weight
  | .r m, L => translateWeight (weightIndex m) L
  | .sr m, L => reflectWeight (translateWeight (weightIndex m) L)

@[simp] theorem weightAct_one (L : Weight) : weightAct 1 L = L := by
  rw [DihedralGroup.one_def]
  ext <;> simp only [weightAct, map_zero, translateWeight, Int.cast_zero,
    mul_zero, zero_mul, add_zero, sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

theorem weightAct_mul (w v : Weyl) (L : Weight) :
    weightAct (w * v) L = weightAct w (weightAct v L) := by
  cases w <;> cases v <;>
    simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, weightAct, map_add, map_sub] <;>
    ext <;> simp only [translateWeight, reflectWeight] <;> push_cast <;> ring

instance : MulAction Weyl Weight where
  smul := weightAct
  one_smul := weightAct_one
  mul_smul := weightAct_mul

@[simp] theorem weightAct_level (w : Weyl) (L : Weight) :
    (weightAct w L).level = L.level := by
  cases w <;> rfl

/-- The affine quadratic form explains the degree correction in translations. -/
theorem weightAct_quadratic (w : Weyl) (L : Weight) :
    (weightAct w L).finite ^ 2 + 4 * (weightAct w L).level * (weightAct w L).degree =
      L.finite ^ 2 + 4 * L.level * L.degree := by
  cases w <;> simp only [weightAct, translateWeight, reflectWeight] <;> ring

private theorem act_r_plus (m n : ℤ) : act (.r m) (.plus n) = .plus (n - 2 * m) := rfl
private theorem act_r_minus (m n : ℤ) : act (.r m) (.minus n) = .minus (n + 2 * m) := rfl
private theorem act_sr_plus (m n : ℤ) : act (.sr m) (.plus n) = .minus (n - 2 * m) := rfl
private theorem act_sr_minus (m n : ℤ) : act (.sr m) (.minus n) = .plus (n + 2 * m) := rfl
private theorem inv_r_int (m : ℤ) : (DihedralGroup.r m : Weyl)⁻¹ = .r (-m) := rfl

/-- The weight action is dual to the action on actual affine real coroots. -/
theorem rootArgument_weightAct (w : Weyl) (L : Weight) (β : Root) :
    rootArgument ((weightAct w L).level - (weightAct w L).finite, (weightAct w L).finite) β =
      rootArgument (L.level - L.finite, L.finite) (act w⁻¹ β) := by
  cases w with
  | r m =>
    change ℤ at m
    have hw : weightAct (.r m) L = translateWeight m L := rfl
    cases β <;> rw [hw] <;>
      simp only [inv_r_int, act_r_plus, act_r_minus, rootArgument,
        Root.corootZero, Root.corootOne, translateWeight] <;> push_cast <;> ring
  | sr m =>
    change ℤ at m
    have hw : weightAct (.sr m) L = reflectWeight (translateWeight m L) := rfl
    cases β <;> rw [hw] <;>
      simp only [DihedralGroup.inv_sr, act_sr_plus, act_sr_minus, rootArgument,
        Root.corootZero, Root.corootOne, translateWeight, reflectWeight] <;> push_cast <;> ring

/-- Extend simple-coroot values by zero on the degree operator. -/
def spectralWeight (lam : ℂ × ℂ) : Weight := ⟨lam.1 + lam.2, lam.2, 0⟩

/-- The affine Weyl vector has value one on both simple coroots. -/
def rhoWeight : Weight := ⟨2, 1, 0⟩

/-- Evaluation at `t h₁ + z c - exp(r) D`; exponential coordinates cover all positive rotations. -/
def rotatedEvaluation (L : Weight) (t z r : ℝ) : ℂ :=
  L.finite * t + L.level * z - L.degree * Real.exp r

/-- The logarithm of Garland's torus factor `(a exp(-exp(r)D))^(-wλ-ρ)`. -/
def weylExponent (lam : ℂ × ℂ) (t z r : ℝ) (w : Weyl) : ℂ :=
  -rotatedEvaluation (weightAct w (spectralWeight lam)) t z r -
    rotatedEvaluation rhoWeight t z r

/-- Exact quadratic exponent for every translation. -/
theorem weylExponent_translation (lam : ℂ × ℂ) (t z r : ℝ) (m : ℤ) :
    weylExponent lam t z r (.r m) =
      -(lam.2 + 1) * t - (lam.1 + lam.2 + 2) * z +
        (-2 * (lam.1 + lam.2) * t - Real.exp r * lam.2) * m -
          Real.exp r * (lam.1 + lam.2) * (m : ℂ) ^ 2 := by
  have hm : weightIndex m = m := rfl
  simp only [weylExponent, rotatedEvaluation, weightAct, translateWeight,
    spectralWeight, rhoWeight, hm]
  ring

/-- Exact quadratic exponent for the second dihedral family. -/
theorem weylExponent_reflection (lam : ℂ × ℂ) (t z r : ℝ) (m : ℤ) :
    weylExponent lam t z r (.sr m) =
      (lam.2 - 1) * t - (lam.1 + lam.2 + 2) * z +
        (2 * (lam.1 + lam.2) * t - Real.exp r * lam.2) * m -
          Real.exp r * (lam.1 + lam.2) * (m : ℂ) ^ 2 := by
  have hm : weightIndex m = m := rfl
  simp only [weylExponent, rotatedEvaluation, weightAct, translateWeight,
    reflectWeight, spectralWeight, rhoWeight, hm]
  ring

/-- The common quadratic decay rate of both affine Weyl families. -/
def gaussianRate (p : ℂ × ℂ) (r : ℝ) : ℝ :=
  Real.exp r * ((chamberCoordinate p.1).re + (chamberCoordinate p.2).re)

theorem gaussianRate_pos (p : ℂ × ℂ) (r : ℝ) : 0 < gaussianRate p r := by
  apply mul_pos (Real.exp_pos r)
  have h₀ := chamberCoordinate_re_gt_one p.1
  have h₁ := chamberCoordinate_re_gt_one p.2
  linarith only [h₀, h₁]

/-- Constant term of the real translation exponent. -/
def translationConstant (p : ℂ × ℂ) (t z : ℝ) : ℝ :=
  -((chamberCoordinate p.2).re + 1) * t -
    ((chamberCoordinate p.1).re + (chamberCoordinate p.2).re + 2) * z

/-- Linear term of the real translation exponent. -/
def translationLinear (p : ℂ × ℂ) (t r : ℝ) : ℝ :=
  -2 * ((chamberCoordinate p.1).re + (chamberCoordinate p.2).re) * t -
    Real.exp r * (chamberCoordinate p.2).re

/-- Constant term of the real reflection exponent. -/
def reflectionConstant (p : ℂ × ℂ) (t z : ℝ) : ℝ :=
  ((chamberCoordinate p.2).re - 1) * t -
    ((chamberCoordinate p.1).re + (chamberCoordinate p.2).re + 2) * z

/-- Linear term of the real reflection exponent. -/
def reflectionLinear (p : ℂ × ℂ) (t r : ℝ) : ℝ :=
  2 * ((chamberCoordinate p.1).re + (chamberCoordinate p.2).re) * t -
    Real.exp r * (chamberCoordinate p.2).re

/-- The translation torus factor has exactly a Gaussian modulus. -/
theorem norm_exp_weylExponent_translation (p : ℂ × ℂ) (t z r : ℝ) (m : ℤ) :
    ‖Complex.exp (weylExponent (godementParameter p) t z r (.r m))‖ =
      Real.exp (translationConstant p t z + translationLinear p t r * m -
        gaussianRate p r * (m : ℝ) ^ 2) := by
  rw [Complex.norm_exp, weylExponent_translation]
  congr 1
  simp [translationConstant, translationLinear, gaussianRate, godementParameter,
    Complex.mul_re, Complex.mul_im, Complex.exp_re, pow_two]

/-- The reflection family has the same strictly positive quadratic decay rate. -/
theorem norm_exp_weylExponent_reflection (p : ℂ × ℂ) (t z r : ℝ) (m : ℤ) :
    ‖Complex.exp (weylExponent (godementParameter p) t z r (.sr m))‖ =
      Real.exp (reflectionConstant p t z + reflectionLinear p t r * m -
        gaussianRate p r * (m : ℝ) ^ 2) := by
  rw [Complex.norm_exp, weylExponent_reflection]
  congr 1
  simp [reflectionConstant, reflectionLinear, gaussianRate, godementParameter,
    Complex.mul_re, Complex.mul_im, Complex.exp_re, pow_two]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1
