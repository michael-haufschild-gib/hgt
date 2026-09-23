import GaloisForLFunctions.RHTower.SelbergMaassParseval
import GaloisForLFunctions.RHTower.SelbergMaassUnipotentPaths
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

/-!
# Exact unipotent Fourier filtering of the original Maass source

The literal normalized Fourier integral intertwines integer translation with the standard
character of the actual congruence residue ring. Complete upper-unipotent averaging therefore
keeps precisely indices divisible by the level; its complementary projection keeps the other
indices. Parseval identifies the complete arithmetic block variance with exactly that original
coefficient mass, including every deck coordinate and every zero of the source.

All source identities use the original congruence Maass object and its actual deck action.
No lift, spectral estimate, numerical truncation, or bound on path length is assumed. The
comparison of these exact channels with the physical full-domain gradient is a further target.
-/

open Complex MeasureTheory Set UpperHalfPlane
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassUnipotentFourier
open _root_.RHTower SelbergMaassMean SelbergMaassFourier
noncomputable section

/-- The literal exponential kernel turns addition into multiplication. -/
theorem kernel_add (w : ℝ) (n : ℤ) (x t : ℝ) :
    deningerFourierKernel w n (x+t) =
      deningerFourierKernel w n x * deningerFourierKernel w n t := by
  simp only [deningerFourierKernel, ← Complex.exp_add, Complex.ofReal_add]
  congr 1
  ring

/-- The normalized integer-frequency kernel has its full stated period. -/
theorem kernel_periodic {w : ℝ} (hw : w ≠ 0) (n : ℤ) :
    Function.Periodic (deningerFourierKernel w n) w := by
  intro x
  rw [kernel_add, deningerFourierKernel_periodic w hw n]
  simp [deningerFourierKernel]

/-- Change of variables gives the exact phase of a periodic Fourier coefficient. -/
theorem coefficient_shift {w : ℝ} (hw : w ≠ 0) (n : ℤ) {F : ℝ → ℂ}
    (hp : Function.Periodic F w) (t : ℝ) :
    deningerFourierCoeff w (fun x => F (x+t)) n =
      deningerFourierKernel w n (-t) * deningerFourierCoeff w F n := by
  have he (x : ℝ) : deningerFourierKernel w n x * F (x+t) =
      deningerFourierKernel w n (-t) *
        (deningerFourierKernel w n (x+t) * F (x+t)) := by
    rw [← mul_assoc, ← kernel_add]
    congr 2
    ring
  have hper := (kernel_periodic hw n).mul hp
  unfold deningerFourierCoeff
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_add_right
    (fun x => deningerFourierKernel w n x * F x) t]
  have hi := hper.intervalIntegral_add_eq t 0
  simp only [zero_add, Pi.mul_apply] at hi ⊢
  rw [add_comm w t, hi]
  ring

/-- The original integral phase is the standard character of the actual residue ring. -/
theorem kernel_neg_integer (N : ℕ) (n j : ℤ) :
    deningerFourierKernel (N+1 : ℕ) n (-(j : ℝ)) =
      ZMod.stdAddChar ((n*j : ℤ) : ZMod (N+1)) := by
  rw [ZMod.stdAddChar_coe, deningerFourierKernel]
  congr 1
  push_cast
  ring

/-- Complete residue summation retains precisely the trivial character. -/
theorem residue_character_sum (N : ℕ) (n : ℤ) :
    ∑ j : ZMod (N+1), ZMod.stdAddChar ((n : ZMod (N+1))*j) =
      if (n : ZMod (N+1))=0 then (N+1 : ℂ) else 0 := by
  simpa only [mul_comm, ZMod.card, Nat.cast_ite, Nat.cast_zero, Nat.cast_add, Nat.cast_one] using
    AddChar.sum_mulShift (n : ZMod (N+1)) (ZMod.isPrimitive_stdAddChar (N+1))

open SelbergMaassCongruenceTrace SelbergMaassSourceCurrents SelbergMaassCuspTransport
open SelbergMaassUnipotentBlocks SelbergMaassUnipotentPaths
open GaloisForLFunctions.HTGeometry.FiniteRingSl2

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- The original arithmetic upper action is literal horizontal translation. -/
theorem field_upper_shift (q : Deck N) (j : ℤ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    field N f (q * QuotientGroup.mk (upper j)) (point x y) =
      field N f q (point (x+j) y) := by
  change (quotientForm N f (q*QuotientGroup.mk (upper j))).1.1 (ofComplex (point x y)) = _
  rw [quotientForm_mul, translate_apply, upper_smul_eq_point]
  have hc := coe_ofComplex_point x hy
  have hre : (ofComplex (point x y)).re = x := by
    change ((ofComplex (point x y) : ℍ) : ℂ).re = x
    rw [hc]
    simp [point]
  have him : (ofComplex (point x y)).im = y := by
    change ((ofComplex (point x y) : ℍ) : ℂ).im = y
    rw [hc]
    simp [point]
  rw [hre,him]
  rfl

/-- Original deck coefficients transform by the exact integer-translation character. -/
theorem coefficient_upper_shift (q : Deck N) (j n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (N+1 : ℕ) n (field N f (q*QuotientGroup.mk (upper j))) y =
      ZMod.stdAddChar ((n*j : ℤ) : ZMod (N+1)) *
        maassCoefficient N (quotientForm N f q) n y := by
  unfold coefficient
  have he : (fun x => field N f (q*QuotientGroup.mk (upper j)) (point x y)) =
      (fun x => field N f q (point (x+j) y)) :=
    funext (fun x => field_upper_shift N f q j x hy)
  rw [he, coefficient_shift (w := (N+1 : ℕ)) (by positivity) n
    (F := fun x => field N f q (point x y))
    (fun x => maass_periodic N (quotientForm N f q) x hy) (j : ℝ), kernel_neg_integer]
  rfl

/-- Each actual finite upper-block element acts by its residue character. -/
theorem coefficient_upperBlock (q : Deck N) (j : Multiplicative (ZMod (N+1)))
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (N+1 : ℕ) n (field N f (q*upperBlock N j)) y =
      ZMod.stdAddChar ((n : ZMod (N+1))*j.toAdd) *
        maassCoefficient N (quotientForm N f q) n y := by
  rw [upperBlock_eq_mk, coefficient_upper_shift N f q _ n hy]
  simp

private theorem kernel_continuous (w : ℝ) (n : ℤ) :
    Continuous (deningerFourierKernel w n) :=
  continuous_iff_continuousAt.mpr (fun x => (deningerFourierKernel_hasDerivAt w n x).continuousAt)

private theorem coefficient_const_mul (w : ℝ) (n : ℤ) (c : ℂ) (F : ℂ → ℂ) (y : ℝ) :
    coefficient w n (fun z => c * F z) y = c * coefficient w n F y := by
  unfold coefficient deningerFourierCoeff
  simp only [mul_left_comm (deningerFourierKernel w n _) c,
    intervalIntegral.integral_const_mul]
  ring

private theorem coefficient_finite_sum {ι : Type*} [Fintype ι] (w : ℝ) (n : ℤ)
    (F : ι → ℂ → ℂ) (hf : ∀ i, ContinuousOn (F i) {z : ℂ | 0 < z.im})
    {y : ℝ} (hy : 0 < y) :
    coefficient w n (fun z => ∑ i, F i z) y = ∑ i, coefficient w n (F i) y := by
  unfold coefficient deningerFourierCoeff
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum
    (f := fun i x => deningerFourierKernel w n x * F i (point x y))
    (fun i _ => ((kernel_continuous w n).mul (slice_continuous (hf i) hy)).intervalIntegrable _ _)]
  rw [Finset.mul_sum]

private theorem coefficient_sub (w : ℝ) (n : ℤ) (F H : ℂ → ℂ)
    (hf : ContinuousOn F {z : ℂ | 0 < z.im})
    (hh : ContinuousOn H {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    coefficient w n (fun z => F z-H z) y = coefficient w n F y-coefficient w n H y := by
  unfold coefficient deningerFourierCoeff
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub
    (f := fun x => deningerFourierKernel w n x * F (point x y))
    (g := fun x => deningerFourierKernel w n x * H (point x y))
    (((kernel_continuous w n).mul (slice_continuous hf hy)).intervalIntegrable _ _)
    (((kernel_continuous w n).mul (slice_continuous hh hy)).intervalIntegrable _ _)]
  ring

/-- The actual coordinate of the complete upper-unipotent average, in the original chart. -/
def upperAverageField (q : Deck N) (z : ℂ) : ℂ :=
  ((N+1 : ℕ) : ℂ)⁻¹ * ∑ j : Multiplicative (ZMod (N+1)), field N f (q*upperBlock N j) z

/-- The discarded original source field, retaining every coordinate and its zeros. -/
def upperComplementField (q : Deck N) (z : ℂ) : ℂ :=
  field N f q z-upperAverageField N f q z

/-- The finite projection preserves the original upper-half-plane continuity. -/
theorem upperAverageField_continuous (q : Deck N) :
    ContinuousOn (upperAverageField N f q) {z : ℂ | 0 < z.im} :=
  continuousOn_const.mul (continuousOn_finsetSum _
    (fun j _ => (quotientForm N f (q*upperBlock N j)).2.2.1.1.continuousOn))

/-- The literal discarded field remains continuous, including its zeros. -/
theorem upperComplementField_continuous (q : Deck N) :
    ContinuousOn (upperComplementField N f q) {z : ℂ | 0 < z.im} :=
  (quotientForm N f q).2.2.1.1.continuousOn.sub (upperAverageField_continuous N f q)

/-- Complete unipotent averaging is the exact divisibility filter on literal source coefficients. -/
theorem coefficient_upperAverageField (q : Deck N) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (N+1 : ℕ) n (upperAverageField N f q) y =
      if (N+1 : ℤ) ∣ n then maassCoefficient N (quotientForm N f q) n y else 0 := by
  classical
  unfold upperAverageField
  rw [coefficient_const_mul, coefficient_finite_sum _ _ (fun j => field N f (q*upperBlock N j))
    (fun j => (quotientForm N f (q*upperBlock N j)).2.2.1.1.continuousOn) hy]
  simp_rw [coefficient_upperBlock N f q _ n hy]
  rw [← Finset.sum_mul]
  have he : (∑ j : Multiplicative (ZMod (N+1)),
      ZMod.stdAddChar ((n : ZMod (N+1))*j.toAdd)) =
      ∑ j : ZMod (N+1), ZMod.stdAddChar ((n : ZMod (N+1))*j) :=
    Equiv.sum_comp Multiplicative.toAdd (fun j : ZMod (N+1) => ZMod.stdAddChar ((n : ZMod (N+1))*j))
  rw [he, residue_character_sum]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_add, Nat.cast_one]
  split_ifs with hn
  · have hN : ((N+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    simp only [Nat.cast_add, Nat.cast_one] at hN ⊢
    rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  · simp

/-- The complementary block keeps exactly the nondivisible frequency channels. -/
theorem coefficient_upperComplementField (q : Deck N) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (N+1 : ℕ) n (upperComplementField N f q) y =
      if (N+1 : ℤ) ∣ n then 0 else maassCoefficient N (quotientForm N f q) n y := by
  classical
  unfold upperComplementField
  rw [coefficient_sub _ _ (field N f q) (upperAverageField N f q)
    (quotientForm N f q).2.2.1.1.continuousOn (upperAverageField_continuous N f q) hy,
    coefficient_upperAverageField N f q n hy]
  change maassCoefficient N (quotientForm N f q) n y -
    (if (N+1 : ℤ) ∣ n then _ else 0) = _
  split_ifs <;> simp

/-- Parseval for the literal discarded source field, without an estimate or frequency truncation. -/
theorem upperComplement_mass_hasSum (q : Deck N) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => if (N+1 : ℤ) ∣ n then 0 else
      normSq (maassCoefficient N (quotientForm N f q) n y))
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        normSq (upperComplementField N f q (point x y))) := by
  have h := SelbergMaassParseval.coefficient_mass_hasSum (N+1 : ℕ) (by positivity)
    (upperComplementField_continuous N f q) hy
  simp_rw [coefficient_upperComplementField N f q _ hy] at h
  simpa only [apply_ite normSq, map_zero] using h

open SelbergMaassCongruenceAverage GaloisForLFunctions.HTGeometry FiniteRegularBlocks
open HTGeometry.ConstraintRelativity

/-- The spectral-filter field is literally the already-constructed arithmetic block projection. -/
theorem upperAverageField_eq_blockAverage (q : Deck N) (z : ℍ) :
    upperAverageField N f q (z : ℂ) =
      blockAverage (upperBlock N) (sourceVector N f z) q := by
  unfold blockAverage reynolds
  change _ = (Fintype.card (Multiplicative (ZMod (N+1))) : ℂ)⁻¹ *
    (∑ j : Multiplicative (ZMod (N+1)), finiteRegularUnitary (upperBlock N j) (sourceVector N f z)) q
  simp only [WithLp.ofLp_sum, Finset.sum_apply, finiteRegularUnitary_apply]
  have hc : Fintype.card (Multiplicative (ZMod (N+1))) = N+1 := by
    rw [Fintype.card_congr Multiplicative.toAdd, ZMod.card]
  rw [hc]
  simp [upperAverageField,field,sourceVector]

/-- Exact arithmetic block variance is the mass of the literal complementary source fields. -/
theorem upperComplement_norm_sq (z : ℍ) :
    ‖sourceVector N f z-blockAverage (upperBlock N) (sourceVector N f z)‖^(2 : ℕ) =
      ∑ q : Deck N, normSq (upperComplementField N f q (z : ℂ)) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro q _
  rw [Complex.sq_norm]
  congr 1
  change (sourceVector N f z) q-(blockAverage (upperBlock N) (sourceVector N f z)) q =
    field N f q (z : ℂ)-upperAverageField N f q (z : ℂ)
  rw [upperAverageField_eq_blockAverage]
  simp [sourceVector, field]

/-- The complete original upper-block variance has an exact physical Fourier mass formula. -/
theorem upperBlock_variance_hasSum {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => if (N+1 : ℤ) ∣ n then 0 else
      ∑ q : Deck N, normSq (maassCoefficient N (quotientForm N f q) n y))
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ‖sourceVector N f (ofComplex (point x y))-
          blockAverage (upperBlock N) (sourceVector N f (ofComplex (point x y)))‖^(2 : ℕ)) := by
  classical
  have h := hasSum_sum (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => upperComplement_mass_hasSum N f q hy)
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero] at h
  rw [← Finset.mul_sum] at h
  have hi := intervalIntegral.integral_finsetSum (μ := volume)
    (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => (Complex.continuous_normSq.comp
      (slice_continuous (upperComplementField_continuous N f q) hy)).intervalIntegrable
        (0 : ℝ) (N+1 : ℕ))
  simp only [Function.comp_def] at hi
  rw [← hi] at h
  have he (x : ℝ) :
      (∑ q : Deck N, normSq (upperComplementField N f q (point x y))) =
      ‖sourceVector N f (ofComplex (point x y))-
        blockAverage (upperBlock N) (sourceVector N f (ofComplex (point x y)))‖^(2 : ℕ) := by
    rw [upperComplement_norm_sq, coe_ofComplex_point x hy]
  simp_rw [he] at h
  exact h

/-- The literal original Fourier vector in the complete deck representation. -/
def coefficientVector (n : ℤ) (y : ℝ) : EuclideanSpace ℂ (Deck N) :=
  WithLp.toLp 2 (fun q => maassCoefficient N (quotientForm N f q) n y)

/-- Original coefficients occupy the exact unipotent character eigenspace in the actual deck group. -/
theorem coefficientVector_upperBlock (j : Multiplicative (ZMod (N+1))) (n : ℤ)
    {y : ℝ} (hy : 0 < y) :
    finiteRegularUnitary (upperBlock N j) (coefficientVector N f n y) =
      ZMod.stdAddChar ((n : ZMod (N+1))*j.toAdd) • coefficientVector N f n y := by
  ext q
  exact coefficient_upperBlock N f q j n hy

end
end GaloisForLFunctions.RHTower.SelbergMaassUnipotentFourier
