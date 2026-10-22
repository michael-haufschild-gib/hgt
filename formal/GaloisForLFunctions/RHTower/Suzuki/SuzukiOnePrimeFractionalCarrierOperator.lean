import GaloisForLFunctions.RHTower.Suzuki.SuzukiOnePrimeFractionalCarrier
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Bounded operators on the one-prime fractional carrier

The scalar energy estimate for the `κ = 2/3` valuation shifts is promoted here to literal bounded
operators on complex `ℓ²(ℤ)`.  Their operator norms have degree `2/3`, and their composition is the
exact valuation group law.  This is the operator carrier required before Gamma-resolvent transport
can be assembled.
-/

open scoped ENNReal

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complex rank-one fractional carrier. -/
abbrev SuzukiOnePrimeFractionalCarrier : Type :=
  lp (fun _ : Fin 1 → ℤ => ℂ) 2

private theorem summable_norm_sq_suzukiOnePrimeFractionalCarrier
    (f : SuzukiOnePrimeFractionalCarrier) :
    Summable fun ν : Fin 1 → ℤ => ‖(f : (Fin 1 → ℤ) → ℂ) ν‖ ^ 2 := by
  have h := (memℓp_gen_iff (E := fun _ : Fin 1 → ℤ => ℂ)
    (f := (f : (Fin 1 → ℤ) → ℂ)) (p := 2) (by norm_num)).mp (lp.memℓp f)
  refine h.congr fun ν => ?_
  rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

private theorem memℓp_suzukiOnePrimeFractionalOrbitShift
    (s : Fin 1 → ℤ) (f : SuzukiOnePrimeFractionalCarrier) :
    Memℓp (fun ν : Fin 1 → ℤ =>
      (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν : ℂ) * f (ν + s)) 2 := by
  have hZ : Summable fun ν : Fin 1 → ℤ => ‖f ν‖ ^ 2 :=
    summable_norm_sq_suzukiOnePrimeFractionalCarrier f
  have hshift : Summable fun ν : Fin 1 → ℤ => ‖f (ν + s)‖ ^ 2 :=
    summable_sq_comp_add hZ s
  let M : ℝ := (1 + (orbitLength s : ℝ)) ^ (2 / 3 : ℝ)
  have hdom : Summable fun ν : Fin 1 → ℤ => M ^ 2 * ‖f (ν + s)‖ ^ 2 :=
    hshift.mul_left _
  have hsum : Summable fun ν : Fin 1 → ℤ =>
      (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν * ‖f (ν + s)‖) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun ν => sq_nonneg _) (fun ν => ?_) hdom
    have hratio := abs_fractionalPolynomialOrbitShiftRatio_le
      (κ := (2 / 3 : ℝ)) (by norm_num) s ν
    have hsq : |fractionalPolynomialOrbitShiftRatio (2 / 3) s ν| ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hratio 2
    calc
      (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν * ‖f (ν + s)‖) ^ 2 =
          |fractionalPolynomialOrbitShiftRatio (2 / 3) s ν| ^ 2 * ‖f (ν + s)‖ ^ 2 := by
        rw [mul_pow, sq_abs]
      _ ≤ M ^ 2 * ‖f (ν + s)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  apply memℓp_gen
  refine hsum.congr fun ν => ?_
  rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp only [mul_pow, sq_abs]

/-- Rank-one fractional valuation shift as a complex linear map. -/
def suzukiOnePrimeFractionalOrbitShiftLM (s : Fin 1 → ℤ) :
    SuzukiOnePrimeFractionalCarrier →ₗ[ℂ] SuzukiOnePrimeFractionalCarrier where
  toFun f := ⟨fun ν =>
    (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν : ℂ) * f (ν + s),
      memℓp_suzukiOnePrimeFractionalOrbitShift s f⟩
  map_add' f g := by
    refine lp.ext (funext fun ν => ?_)
    change (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν : ℂ) *
        ((f + g : SuzukiOnePrimeFractionalCarrier) : (Fin 1 → ℤ) → ℂ) (ν + s) =
      (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν : ℂ) * f (ν + s) +
        (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν : ℂ) * g (ν + s)
    simp only [lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c f := by
    refine lp.ext (funext fun ν => ?_)
    change (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν : ℂ) *
        ((c • f : SuzukiOnePrimeFractionalCarrier) : (Fin 1 → ℤ) → ℂ) (ν + s) =
      c * ((fractionalPolynomialOrbitShiftRatio (2 / 3) s ν : ℂ) * f (ν + s))
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

@[simp] theorem suzukiOnePrimeFractionalOrbitShiftLM_apply
    (s : Fin 1 → ℤ) (f : SuzukiOnePrimeFractionalCarrier) (ν : Fin 1 → ℤ) :
    suzukiOnePrimeFractionalOrbitShiftLM s f ν =
      (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν : ℂ) * f (ν + s) := rfl

/-- Pointwise norm bound before completion to a bounded operator. -/
theorem norm_suzukiOnePrimeFractionalOrbitShiftLM_le
    (s : Fin 1 → ℤ) (f : SuzukiOnePrimeFractionalCarrier) :
    ‖suzukiOnePrimeFractionalOrbitShiftLM s f‖ ≤
      (1 + (orbitLength s : ℝ)) ^ (2 / 3 : ℝ) * ‖f‖ := by
  have hZ : Summable fun ν : Fin 1 → ℤ => ‖f ν‖ ^ 2 :=
    summable_norm_sq_suzukiOnePrimeFractionalCarrier f
  have henergy := tsum_sq_fractionalPolynomialOrbitWeightedShift_le s hZ
  have hsquare : ‖suzukiOnePrimeFractionalOrbitShiftLM s f‖ ^ 2 ≤
      ((1 + (orbitLength s : ℝ)) ^ (2 / 3 : ℝ)) ^ 2 * ‖f‖ ^ 2 := by
    have hout : ‖suzukiOnePrimeFractionalOrbitShiftLM s f‖ ^ 2 =
        ∑' ν : Fin 1 → ℤ, ‖suzukiOnePrimeFractionalOrbitShiftLM s f ν‖ ^ 2 := by
      simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num)
        (suzukiOnePrimeFractionalOrbitShiftLM s f)
    have hin : ‖f‖ ^ 2 = ∑' ν : Fin 1 → ℤ, ‖f ν‖ ^ 2 := by
      simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) f
    rw [hout, hin]
    simpa [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, norm_mul, Complex.norm_real, mul_pow, sq_abs] using henergy
  have hleft : 0 ≤ ‖suzukiOnePrimeFractionalOrbitShiftLM s f‖ := norm_nonneg _
  have hright : 0 ≤ (1 + (orbitLength s : ℝ)) ^ (2 / 3 : ℝ) * ‖f‖ := by positivity
  nlinarith [hsquare]

/-- Rank-one fractional valuation shift as a literal bounded operator on complex `ℓ²`. -/
def suzukiOnePrimeFractionalOrbitShiftCLM (s : Fin 1 → ℤ) :
    SuzukiOnePrimeFractionalCarrier →L[ℂ] SuzukiOnePrimeFractionalCarrier :=
  LinearMap.mkContinuous (suzukiOnePrimeFractionalOrbitShiftLM s)
    ((1 + (orbitLength s : ℝ)) ^ (2 / 3 : ℝ))
    (norm_suzukiOnePrimeFractionalOrbitShiftLM_le s)

@[simp] theorem suzukiOnePrimeFractionalOrbitShiftCLM_apply
    (s : Fin 1 → ℤ) (f : SuzukiOnePrimeFractionalCarrier) (ν : Fin 1 → ℤ) :
    suzukiOnePrimeFractionalOrbitShiftCLM s f ν =
      (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν : ℂ) * f (ν + s) := rfl

/-- The operator norm has the exact polynomial degree required by the Gamma window. -/
theorem norm_suzukiOnePrimeFractionalOrbitShiftCLM_le (s : Fin 1 → ℤ) :
    ‖suzukiOnePrimeFractionalOrbitShiftCLM s‖ ≤
      (1 + (orbitLength s : ℝ)) ^ (2 / 3 : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Exact bounded-operator group law. -/
theorem suzukiOnePrimeFractionalOrbitShiftCLM_comp
    (s t : Fin 1 → ℤ) :
    (suzukiOnePrimeFractionalOrbitShiftCLM s).comp
        (suzukiOnePrimeFractionalOrbitShiftCLM t) =
      suzukiOnePrimeFractionalOrbitShiftCLM (s + t) := by
  ext f ν
  simp only [ContinuousLinearMap.comp_apply,
    suzukiOnePrimeFractionalOrbitShiftCLM_apply]
  have hc :
      (fractionalPolynomialOrbitShiftRatio (2 / 3) s ν : ℂ) *
          (fractionalPolynomialOrbitShiftRatio (2 / 3) t (ν + s) : ℂ) =
        (fractionalPolynomialOrbitShiftRatio (2 / 3) (s + t) ν : ℂ) := by
    exact_mod_cast fractionalPolynomialOrbitShiftRatio_cocycle (2 / 3) s t ν
  rw [← mul_assoc, hc, add_assoc]

end

end RHTower
