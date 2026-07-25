import GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzLattice
import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleDenominator
import GaloisForLFunctions.RHTower.CCMRationalWeightedShiftTraceClass
import GaloisForLFunctions.RHTower.CCMRationalAdelicBruhatSimpleTensorReal
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Trace-class CCM restriction on the rational adelic algebraic tensor core

Finite-adele common denominators and archimedean Schwartz lattice decay imply absolute
summability of every rational orbit coming from the algebraic Bruhat tensor core. The resulting
CCM weighted shifts on `ℓ²(ℚˣ)` are trace class.

This is a fixed-base theorem. It does not assert strong-Schwartz parameter decay, LF completion,
positivity, a zero spectrum, or the Riemann hypothesis.
-/

noncomputable section

open scoped RestrictedProduct algebraMap

namespace GaloisForLFunctions
namespace RHTower

/-- Right translation of a finite Bruhat function by a finite idele. -/
def ccmRationalFiniteBruhatMulRight
    (φ : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) :
    CCMRationalFiniteBruhatSchwartz :=
  ⟨LocallyConstant.comap
      ⟨fun x => x * (b : CCMRationalFiniteAdele),
        continuous_mul_const _⟩ φ.1,
    φ.2.comp_homeomorph
      (ContinuousAddEquiv.mulRight b).toHomeomorph⟩

@[simp]
theorem ccmRationalFiniteBruhatMulRight_apply
    (φ : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (x : CCMRationalFiniteAdele) :
    (ccmRationalFiniteBruhatMulRight φ b).1 x = φ.1 (x * b) := by
  rfl

/-- A compactly supported locally constant finite-adele function is globally norm bounded. -/
theorem ccmRationalFiniteBruhat_exists_norm_bound
    (φ : CCMRationalFiniteBruhatSchwartz) :
    ∃ C : ℝ, ∀ x, ‖φ.1 x‖ ≤ C :=
  φ.1.continuous.bounded_above_of_compact_support φ.2

/-- Right translation by a finite idele preserves common-denominator confinement. -/
theorem ccmRationalFiniteBruhatMulRight_exists_integerDenominator
    (φ : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ q : ℚ,
      φ.1 (algebraMap ℚ CCMRationalFiniteAdele q * b) ≠ 0 →
        algebraMap ℤ ℚ d * q ∈ (algebraMap ℤ ℚ).range := by
  simpa only [ccmRationalFiniteBruhatMulRight_apply] using
    ccmRationalFiniteBruhat_exists_integerDenominator
      (ccmRationalFiniteBruhatMulRight φ b)

/-- Rational orbit evaluation of one archimedean/finite adelic pure tensor. -/
def ccmRationalAdelicBruhatPureTensorOrbit
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ)
    (q : ℚ) : ℂ :=
  f (bInf * (q : ℝ)) *
    φ.1 (algebraMap ℚ CCMRationalFiniteAdele q * b)

/-- Every fixed-base rational orbit of an adelic Bruhat pure tensor is absolutely summable. -/
theorem ccmRationalAdelicBruhatPureTensorOrbit_summable
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    Summable (fun q : ℚ =>
      ‖ccmRationalAdelicBruhatPureTensorOrbit f φ bInf b q‖) := by
  classical
  obtain ⟨C, hC⟩ := ccmRationalFiniteBruhat_exists_norm_bound φ
  obtain ⟨d, hd, hden⟩ :=
    ccmRationalFiniteBruhatMulRight_exists_integerDenominator φ b
  let S : Set ℚ :=
    {q | φ.1 (algebraMap ℚ CCMRationalFiniteAdele q * b) ≠ 0}
  choose n hn using fun q : S => hden q.1 q.2
  have hn_injective : Function.Injective n := by
    intro q r hnr
    apply Subtype.ext
    have hdQ : algebraMap ℤ ℚ d ≠ 0 := by
      simpa using (Int.cast_ne_zero.mpr hd : (d : ℚ) ≠ 0)
    apply mul_left_cancel₀ hdQ
    calc
      algebraMap ℤ ℚ d * q.1 = algebraMap ℤ ℚ (n q) := (hn q).symm
      _ = algebraMap ℤ ℚ (n r) := by rw [hnr]
      _ = algebraMap ℤ ℚ d * r.1 := hn r
  let a : ℝ := bInf / (d : ℝ)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have ha : a ≠ 0 := div_ne_zero hbInf hdR
  have harg (q : S) :
      bInf * (q.1 : ℝ) = a * (n q : ℝ) := by
    have hreal : (n q : ℝ) = (d : ℝ) * (q.1 : ℝ) := by
      exact_mod_cast hn q
    dsimp [a]
    rw [hreal]
    field_simp
  have harch :
      Summable (fun q : S => ‖f (bInf * (q.1 : ℝ))‖) := by
    have hs :=
      (ccmRationalArchimedeanSchwartz_lattice_summable f ha).comp_injective
        hn_injective
    exact hs.congr fun q => by
      simp only [Function.comp_apply]
      rw [harg q]
  have hsub :
      Summable (fun q : S =>
        ‖ccmRationalAdelicBruhatPureTensorOrbit f φ bInf b q.1‖) := by
    apply Summable.of_nonneg_of_le
      (fun q => norm_nonneg _)
      (fun q => ?_)
      (harch.mul_right C)
    rw [ccmRationalAdelicBruhatPureTensorOrbit, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hC _) (norm_nonneg _)
  have hind :
      Summable (S.indicator
        (fun q : ℚ =>
          ‖ccmRationalAdelicBruhatPureTensorOrbit f φ bInf b q‖)) :=
    summable_subtype_iff_indicator.mp hsub
  exact hind.congr fun q => by
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq]
      have hφ :
          φ.1 (algebraMap ℚ CCMRationalFiniteAdele q * b) = 0 := by
        simpa [S] using hq
      simp [ccmRationalAdelicBruhatPureTensorOrbit, hφ]

/-- `ℚˣ` coefficient of a fixed-base adelic pure-tensor orbit. -/
def ccmRationalAdelicBruhatPureTensorOrbitCoefficient
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ)
    (q : CCMRationalUnit) : ℂ :=
  ccmRationalAdelicBruhatPureTensorOrbit f φ bInf b (q : ℚ)

theorem ccmRationalAdelicBruhatPureTensorOrbitCoefficient_summable
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    Summable (fun q : CCMRationalUnit =>
      ‖ccmRationalAdelicBruhatPureTensorOrbitCoefficient f φ bInf b q‖) :=
  (ccmRationalAdelicBruhatPureTensorOrbit_summable f φ hbInf b).comp_injective
    Units.val_injective

def ccmRationalAdelicBruhatPureTensorOrbitCoefficientLOneBound
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) : ℝ :=
  ccmRationalMoritaCoefficientLOneBound
    (ccmRationalAdelicBruhatPureTensorOrbitCoefficient f φ bInf b)

theorem ccmRationalAdelicBruhatPureTensorOrbitCoefficientLOneBound_nonneg
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) :
    0 ≤ ccmRationalAdelicBruhatPureTensorOrbitCoefficientLOneBound
      f φ bInf b :=
  ccmRationalMoritaCoefficientLOneBound_nonneg _

theorem ccmRationalAdelicBruhatPureTensorOrbitCoefficient_norm_le_lOneBound
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    ∀ q,
      ‖ccmRationalAdelicBruhatPureTensorOrbitCoefficient f φ bInf b q‖ ≤
        ccmRationalAdelicBruhatPureTensorOrbitCoefficientLOneBound
          f φ bInf b :=
  ccmRationalMoritaCoefficient_norm_le_lOneBound
    (ccmRationalAdelicBruhatPureTensorOrbitCoefficient_summable
      f φ hbInf b)

/-- Actual trace-class candidate for one adelic pure-tensor CCM monomial. -/
def ccmRationalAdelicBruhatPureTensorWeightedShift
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ)
    (k : CCMRationalUnit) :
    CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert :=
  ccmRationalMoritaWeightedShift
    (ccmRationalAdelicBruhatPureTensorOrbitCoefficient f φ bInf b) k
    (ccmRationalAdelicBruhatPureTensorOrbitCoefficientLOneBound
      f φ bInf b)
    (ccmRationalAdelicBruhatPureTensorOrbitCoefficientLOneBound_nonneg
      f φ bInf b)
    (ccmRationalAdelicBruhatPureTensorOrbitCoefficient_norm_le_lOneBound
      f φ hbInf b)

theorem ccmRationalAdelicBruhatPureTensorWeightedShift_isTraceClass
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ)
    (k : CCMRationalUnit) :
    (ccmRationalAdelicBruhatPureTensorWeightedShift
      f φ hbInf b k).IsTraceClass := by
  apply ccmRationalMoritaWeightedShift_isTraceClass_of_summable
  exact ccmRationalAdelicBruhatPureTensorOrbitCoefficient_summable
    f φ hbInf b

/-- Bilinear evaluation of the algebraic adelic Bruhat tensor core on one rational orbit. -/
def ccmRationalAdelicBruhatTensorOrbitBilinear
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) (q : ℚ) :
    CCMRationalArchimedeanSchwartz →ₗ[ℂ]
      CCMRationalFiniteBruhatSchwartz →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun φ =>
        f (bInf * (q : ℝ)) *
          φ.1 (algebraMap ℚ CCMRationalFiniteAdele q * b)
      map_add' := by
        intro φ ψ
        simp [mul_add]
      map_smul' := by
        intro z φ
        simp
        ring }
  map_add' := by
    intro f g
    ext φ
    simp [add_mul]
  map_smul' := by
    intro z f
    ext φ
    simp
    ring

/-- Fixed-base rational orbit evaluation of an arbitrary algebraic adelic Bruhat tensor. -/
def ccmRationalAdelicBruhatTensorOrbit
    (t : CCMRationalAdelicBruhatSimpleTensor)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) (q : ℚ) : ℂ :=
  TensorProduct.lift
    (ccmRationalAdelicBruhatTensorOrbitBilinear bInf b q) t

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbit_tmul
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) (q : ℚ) :
    ccmRationalAdelicBruhatTensorOrbit (f ⊗ₜ[ℂ] φ) bInf b q =
      ccmRationalAdelicBruhatPureTensorOrbit f φ bInf b q := by
  rfl

/-- Every fixed-base orbit of the full algebraic adelic Bruhat tensor core is `ℓ¹(ℚ)`. -/
theorem ccmRationalAdelicBruhatTensorOrbit_summable
    (t : CCMRationalAdelicBruhatSimpleTensor)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    Summable (fun q : ℚ =>
      ‖ccmRationalAdelicBruhatTensorOrbit t bInf b q‖) := by
  induction t using TensorProduct.induction_on with
  | zero =>
      simp [ccmRationalAdelicBruhatTensorOrbit]
  | tmul f φ =>
      simpa only [ccmRationalAdelicBruhatTensorOrbit_tmul] using
        ccmRationalAdelicBruhatPureTensorOrbit_summable f φ hbInf b
  | add x y hx hy =>
      apply summable_norm_iff.mpr
      have hadd :=
        (summable_norm_iff.mp hx).add (summable_norm_iff.mp hy)
      exact hadd.congr fun q => by
        simp [ccmRationalAdelicBruhatTensorOrbit]

/-- `ℚˣ` coefficient of an arbitrary algebraic adelic Bruhat tensor orbit. -/
def ccmRationalAdelicBruhatTensorOrbitCoefficient
    (t : CCMRationalAdelicBruhatSimpleTensor)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ)
    (q : CCMRationalUnit) : ℂ :=
  ccmRationalAdelicBruhatTensorOrbit t bInf b (q : ℚ)

theorem ccmRationalAdelicBruhatTensorOrbitCoefficient_summable
    (t : CCMRationalAdelicBruhatSimpleTensor)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    Summable (fun q : CCMRationalUnit =>
      ‖ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b q‖) :=
  (ccmRationalAdelicBruhatTensorOrbit_summable t hbInf b).comp_injective
    Units.val_injective

def ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound
    (t : CCMRationalAdelicBruhatSimpleTensor)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) : ℝ :=
  ccmRationalMoritaCoefficientLOneBound
    (ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b)

theorem ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound_nonneg
    (t : CCMRationalAdelicBruhatSimpleTensor)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) :
    0 ≤ ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound
      t bInf b :=
  ccmRationalMoritaCoefficientLOneBound_nonneg _

theorem ccmRationalAdelicBruhatTensorOrbitCoefficient_norm_le_lOneBound
    (t : CCMRationalAdelicBruhatSimpleTensor)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) :
    ∀ q,
      ‖ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b q‖ ≤
        ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound
          t bInf b :=
  ccmRationalMoritaCoefficient_norm_le_lOneBound
    (ccmRationalAdelicBruhatTensorOrbitCoefficient_summable
      t hbInf b)

/-- Actual fixed-base CCM weighted shift attached to an arbitrary algebraic Bruhat tensor. -/
def ccmRationalAdelicBruhatTensorWeightedShift
    (t : CCMRationalAdelicBruhatSimpleTensor)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ)
    (k : CCMRationalUnit) :
    CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert :=
  ccmRationalMoritaWeightedShift
    (ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b) k
    (ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound t bInf b)
    (ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound_nonneg
      t bInf b)
    (ccmRationalAdelicBruhatTensorOrbitCoefficient_norm_le_lOneBound
      t hbInf b)

/--
Every fixed-base rational CCM monomial from the full algebraic adelic Bruhat tensor core is
trace class.
-/
theorem ccmRationalAdelicBruhatTensorWeightedShift_isTraceClass
    (t : CCMRationalAdelicBruhatSimpleTensor)
    {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ)
    (k : CCMRationalUnit) :
    (ccmRationalAdelicBruhatTensorWeightedShift
      t hbInf b k).IsTraceClass := by
  apply ccmRationalMoritaWeightedShift_isTraceClass_of_summable
  exact ccmRationalAdelicBruhatTensorOrbitCoefficient_summable
    t hbInf b

end RHTower
end GaloisForLFunctions
