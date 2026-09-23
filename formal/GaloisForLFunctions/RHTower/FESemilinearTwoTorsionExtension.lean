import GaloisForLFunctions.RHTower.FESemilinearShearExhaustion
import GaloisForLFunctions.RHTower.WeldKreinRateBlindness

/-!
# A genuinely non-split FE-semilinear two-torsion extension

Upper shears over a unit second lane are always split once they satisfy functional-equation
semilinearity.  The first genuinely different presentation must put torsion on both lanes:

`A_(a,b,f)=[[X^a,f(X)],[0,X^b]]`.

This module derives its exact FE condition and constructs the constant unit extension

`E_m=[[X^m,1],[0,X]]`.

The second torsion exponent changes the FE parity: for `b=1`, the off-diagonal coefficient must be
even under `X |-> -X`, so the constant `1` is allowed.  The determinant is `X^(m+1)`.  For `m>0`,
`E_m` is not a two-sided polynomial transform of the split presentation `diag(X^m,X)`: evaluating
at `X=0` kills every entry of every such transform, while the `(0,1)` entry of `E_m` remains `1`.

More generally, for an order-one second lane the FE condition says that `f` is even, and row
splitting is equivalent to `f(0)=0`.  Thus the constant residue is the exact non-splitting detector.
Sending that residue to the canonical FE-weld Gram gives an exact local bridge: the presentation is
split exactly when the Gram is Krein-nonnegative, and nonsplit exactly when the Gram has a negative
direction.

This is a fixed, carrier-free, FE-semilinear torsion extension with a derived local Witt activation.
It is not yet an RH detector: the remaining problem is to derive the two-lane extension from the
completed FE divisor pair and prove that its extension residue distinguishes the critical-line fixed
locus rather than activating uniformly at every divisor pair.
-/

noncomputable section
namespace RHTower

open Matrix Polynomial

/-- Two torsion lanes coupled by an off-diagonal polynomial. -/
def twoTorsionPresentation (a b : ℕ) (f : Polynomial ℚ) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  !![X ^ a, f; 0, X ^ b]

def twoTorsionSplitPresentation (a b : ℕ) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  twoTorsionPresentation a b 0

/-- Source parity forced by the two diagonal torsion equations under `X |-> -X`. -/
def twoTorsionSourceFEParity (a b : ℕ) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  !![-((-1 : Polynomial ℚ) ^ a), 0; 0, (-1 : Polynomial ℚ) ^ b]

theorem twoTorsionSourceFEParity_isFESemilinearInvolution (a b : ℕ) :
    IsFESemilinearInvolution (twoTorsionSourceFEParity a b) := by
  rw [IsFESemilinearInvolution]
  have ha : (((-1 : Polynomial ℚ) ^ a) ^ (2 : ℕ)) = 1 := by
    rw [← pow_mul]
    simp
  have hb : (((-1 : Polynomial ℚ) ^ b) ^ (2 : ℕ)) = 1 := by
    rw [← pow_mul]
    simp
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [twoTorsionSourceFEParity, reflectPolynomialMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]
  · simpa [pow_two] using ha
  · simpa [pow_two] using hb

/-- Exact parity equation for the off-diagonal extension polynomial. -/
def TwoTorsionFECondition (b : ℕ) (f : Polynomial ℚ) : Prop :=
  -(f.comp (-X)) = f * ((-1 : Polynomial ℚ) ^ b)

/-- **Two-torsion FE classification.**  Semilinear equivariance is exactly the forced parity
condition on the extension polynomial. -/
theorem twoTorsionPresentation_feSemilinear_iff (a b : ℕ) (f : Polynomial ℚ) :
    FESemilinearIntertwines feCoefficientParity (twoTorsionSourceFEParity a b)
      (twoTorsionPresentation a b f) ↔ TwoTorsionFECondition b f := by
  constructor
  · intro h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) => M 0 1) h
    simpa [reflectPolynomialMatrix, feCoefficientParity, twoTorsionSourceFEParity,
      twoTorsionPresentation, TwoTorsionFECondition, Matrix.mul_apply,
      Fin.sum_univ_two] using h01
  · intro hf
    rw [FESemilinearIntertwines]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectPolynomialMatrix, feCoefficientParity, twoTorsionSourceFEParity,
        twoTorsionPresentation, TwoTorsionFECondition, Matrix.mul_apply,
        Fin.sum_univ_two] at hf ⊢
    · rw [show (-X : Polynomial ℚ) = (-1) * X by ring_nf, mul_pow]
      ring_nf
    · exact hf
    · rw [show (-X : Polynomial ℚ) = (-1) * X by ring_nf, mul_pow]
      ring_nf

/-- The determinant order is the sum of the two torsion lengths, independent of the extension. -/
theorem twoTorsionPresentation_det (a b : ℕ) (f : Polynomial ℚ) :
    (twoTorsionPresentation a b f).det = X ^ (a + b) := by
  rw [twoTorsionPresentation, Matrix.det_fin_two]
  simp [pow_add]

/-- With an order-one second lane, FE semilinearity says exactly that the extension polynomial is
even under `X |-> -X`. -/
theorem twoTorsionFECondition_one_iff_even (f : Polynomial ℚ) :
    TwoTorsionFECondition 1 f ↔ f.comp (-X) = f := by
  simp [TwoTorsionFECondition]

/-- For an order-one second lane, row splitting is equivalent to vanishing of the constant
coefficient of the extension polynomial. -/
theorem twoTorsionPresentation_rowSplit_iff_coeff_zero (a : ℕ) (f : Polynomial ℚ) :
    (∃ U : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        twoTorsionPresentation a 1 f = U * twoTorsionSplitPresentation a 1) ↔
      f.coeff 0 = 0 := by
  constructor
  · rintro ⟨U, hU⟩
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) => (M 0 1).coeff 0) hU
    simpa [twoTorsionSplitPresentation, twoTorsionPresentation, Matrix.mul_apply,
      Fin.sum_univ_two] using h01
  · intro hcoeff
    obtain ⟨g, hg⟩ := Polynomial.X_dvd_iff.mpr hcoeff
    refine ⟨upperShearRowGauge g, ?_⟩
    rw [twoTorsionPresentation, twoTorsionSplitPresentation, twoTorsionPresentation,
      upperShearRowGauge, Matrix.mul_fin_two]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hg]
    ring

/-- **Constant-term classification.**  In the order-one two-torsion family, an extension is both
FE-semilinear and row-nonsplit exactly when its polynomial is even with nonzero constant term. -/
theorem feTwoTorsionExtension_criterion (a : ℕ) (f : Polynomial ℚ) :
    (FESemilinearIntertwines feCoefficientParity (twoTorsionSourceFEParity a 1)
        (twoTorsionPresentation a 1 f) ∧
      ¬ ∃ U : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        twoTorsionPresentation a 1 f = U * twoTorsionSplitPresentation a 1) ↔
      (f.comp (-X) = f ∧ f.coeff 0 ≠ 0) := by
  rw [twoTorsionPresentation_feSemilinear_iff, twoTorsionFECondition_one_iff_even]
  rw [not_congr (twoTorsionPresentation_rowSplit_iff_coeff_zero a f)]

/-- The canonical constant extension of an order-`m` lane by an order-one lane. -/
def feUnitTwoTorsionExtension (m : ℕ) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  twoTorsionPresentation m 1 1

/-- The constant extension is FE-semilinear because the second torsion length is odd. -/
theorem feUnitTwoTorsionExtension_feSemilinear (m : ℕ) :
    FESemilinearIntertwines feCoefficientParity (twoTorsionSourceFEParity m 1)
      (feUnitTwoTorsionExtension m) := by
  rw [feUnitTwoTorsionExtension, twoTorsionPresentation_feSemilinear_iff]
  simp [TwoTorsionFECondition]

theorem feUnitTwoTorsionExtension_det (m : ℕ) :
    (feUnitTwoTorsionExtension m).det = X ^ (m + 1) := by
  exact twoTorsionPresentation_det m 1 1

/-- The two-torsion unit extension is not a target-row transform of the split presentation. -/
theorem feUnitTwoTorsionExtension_not_row_split (m : ℕ) :
    ¬ ∃ U : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
      feUnitTwoTorsionExtension m = U * twoTorsionSplitPresentation m 1 := by
  rintro ⟨U, hU⟩
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) => (M 0 1).coeff 0) hU
  simp [feUnitTwoTorsionExtension, twoTorsionSplitPresentation, twoTorsionPresentation,
    Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- **Genuine two-sided non-splitting.**  For positive `m`, the unit extension is not even a
two-sided polynomial transform of the split two-torsion presentation. -/
theorem feUnitTwoTorsionExtension_not_twoSided_split {m : ℕ} (hm : 0 < m) :
    ¬ ∃ U V : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
      feUnitTwoTorsionExtension m = U * twoTorsionSplitPresentation m 1 * V := by
  rintro ⟨U, V, hUV⟩
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) => Polynomial.eval 0 (M 0 1)) hUV
  simp [feUnitTwoTorsionExtension, twoTorsionSplitPresentation, twoTorsionPresentation,
    Matrix.mul_apply, Fin.sum_univ_two, Polynomial.eval_add, Polynomial.eval_mul] at h01
  rw [zero_pow (by omega : m ≠ 0)] at h01
  norm_num at h01

/-- Local-coordinate reflection preserves the extension residue. -/
theorem twoTorsionExtensionResidue_reflection (f : Polynomial ℚ) :
    (f.comp (-X)).coeff 0 = f.coeff 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp]
  simp

/-- Row splitting is invariant under the local-coordinate reflection. -/
theorem twoTorsionPresentation_rowSplit_reflection_iff (a : ℕ) (f : Polynomial ℚ) :
    (∃ U : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        twoTorsionPresentation a 1 (f.comp (-X)) =
          U * twoTorsionSplitPresentation a 1) ↔
      ∃ U : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        twoTorsionPresentation a 1 f = U * twoTorsionSplitPresentation a 1 := by
  rw [twoTorsionPresentation_rowSplit_iff_coeff_zero,
    twoTorsionPresentation_rowSplit_iff_coeff_zero,
    twoTorsionExtensionResidue_reflection]

/-- The unit class is simultaneously FE-semilinear and genuinely two-sided nonsplit. -/
theorem feUnitTwoTorsionExtension_equivariant_and_nonsplit {m : ℕ} (hm : 0 < m) :
    FESemilinearIntertwines feCoefficientParity (twoTorsionSourceFEParity m 1)
        (feUnitTwoTorsionExtension m) ∧
      ¬ ∃ U V : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        feUnitTwoTorsionExtension m = U * twoTorsionSplitPresentation m 1 * V :=
  ⟨feUnitTwoTorsionExtension_feSemilinear m,
    feUnitTwoTorsionExtension_not_twoSided_split hm⟩

end RHTower

namespace GaloisForLFunctions.RHTower

open Complex Matrix Polynomial

/-- The canonical local FE-Witt block read from the gauge-invariant constant extension residue. -/
def twoTorsionExtensionKreinGram (f : Polynomial ℚ) : Matrix (Fin 2) (Fin 2) ℂ :=
  weldFEKreinGram (f.coeff 0 : ℝ)

/-- The extension block is Krein-nonnegative exactly when the constant extension residue vanishes. -/
theorem twoTorsionExtensionKreinGram_kreinNonneg_iff (f : Polynomial ℚ) :
    _root_.RHTower.KreinNonneg (twoTorsionExtensionKreinGram f) ↔ f.coeff 0 = 0 := by
  rw [twoTorsionExtensionKreinGram, weldFEKreinGram_kreinNonneg_iff]
  norm_cast

/-- The local FE-Witt block is blind to paired-germ coordinate reflection. -/
theorem twoTorsionExtensionKreinGram_reflection (f : Polynomial ℚ) :
    twoTorsionExtensionKreinGram (f.comp (-X)) = twoTorsionExtensionKreinGram f := by
  rw [twoTorsionExtensionKreinGram, twoTorsionExtensionKreinGram,
    _root_.RHTower.twoTorsionExtensionResidue_reflection]

/-- Row splitting of an order-one two-torsion extension is equivalent to nonnegativity of its
canonical FE-Witt block. -/
theorem twoTorsionPresentation_rowSplit_iff_kreinNonneg (a : ℕ) (f : Polynomial ℚ) :
    (∃ U : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        _root_.RHTower.twoTorsionPresentation a 1 f =
          U * _root_.RHTower.twoTorsionSplitPresentation a 1) ↔
      _root_.RHTower.KreinNonneg (twoTorsionExtensionKreinGram f) := by
  calc
    (∃ U : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        _root_.RHTower.twoTorsionPresentation a 1 f =
          U * _root_.RHTower.twoTorsionSplitPresentation a 1) ↔ f.coeff 0 = 0 :=
      _root_.RHTower.twoTorsionPresentation_rowSplit_iff_coeff_zero a f
    _ ↔ _root_.RHTower.KreinNonneg (twoTorsionExtensionKreinGram f) :=
      (twoTorsionExtensionKreinGram_kreinNonneg_iff f).symm

/-- **Extension-to-Witt activation.**  The genuine extension is row-nonsplit exactly when its
canonical FE-Witt block has a negative direction. -/
theorem twoTorsionPresentation_rowNonsplit_iff_not_kreinNonneg (a : ℕ) (f : Polynomial ℚ) :
    (¬ ∃ U : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        _root_.RHTower.twoTorsionPresentation a 1 f =
          U * _root_.RHTower.twoTorsionSplitPresentation a 1) ↔
      ¬_root_.RHTower.KreinNonneg (twoTorsionExtensionKreinGram f) :=
  not_congr (twoTorsionPresentation_rowSplit_iff_kreinNonneg a f)

end GaloisForLFunctions.RHTower
