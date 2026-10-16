import GaloisForLFunctions.RHTower.DeningerMeyerExponentialSolvability

/-! # Intrinsic nonlinear exponentiation of Meyer cohomology

Exponential corrections are independent of the original source representative.
The proof factors their difference through the entire Xi quotient of an
actual boundary, then uses global source-native Xi synthesis.
-/

open Complex
namespace RHTower
noncomputable section

local notation "V" => DeningerMeyerStrongLogTarget
local notation "Q" => DeningerMeyerStrongLogCohomology
local notation "N" => LinearMap.range deningerMeyerStrongLogSumLM

theorem deningerMeyerSourceExp_congr {g h : V}
    (hgh : (Submodule.Quotient.mk g : Q) = Submodule.Quotient.mk h) :
    (Submodule.Quotient.mk (deningerMeyerSourceExp g) : Q) =
      Submodule.Quotient.mk (deningerMeyerSourceExp h) := by
  obtain ⟨f, hf⟩ := (Submodule.Quotient.eq N).mp hgh
  obtain ⟨H, hH, hdiv⟩ := deningerMeyerBoundary_entireQuotient f
  simp only [hf, Submodule.coe_sub, deningerMeyerStrongLogMellin_sub] at hdiv
  have hg := (deningerMeyerStrongLogMellin_entireRegular g).differentiable
  have hh := (deningerMeyerStrongLogMellin_entireRegular h).differentiable
  apply (Submodule.Quotient.eq N).mpr
  apply deningerMeyerXiDivision_has_cap _
    ((hH.mul hh.cexp).mul
      ((deningerEntire_dslope Complex.differentiable_exp 0).comp (hg.sub hh)))
  intro s
  simp only [Submodule.coe_sub, deningerMeyerStrongLogMellin_sub, deningerMeyerSourceExp_mellin,
    Pi.mul_apply, Function.comp_apply, Pi.sub_apply]
  have hm := sub_smul_dslope Complex.exp 0
    (deningerMeyerStrongLogMellin g s-deningerMeyerStrongLogMellin h s)
  simp only [sub_zero, smul_eq_mul, Complex.exp_zero] at hm
  have he : Complex.exp (deningerMeyerStrongLogMellin g s) =
      Complex.exp (deningerMeyerStrongLogMellin h s) *
        Complex.exp (deningerMeyerStrongLogMellin g s-deningerMeyerStrongLogMellin h s) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc Complex.exp (deningerMeyerStrongLogMellin g s)-1 -
        (Complex.exp (deningerMeyerStrongLogMellin h s)-1)
      = Complex.exp (deningerMeyerStrongLogMellin h s) *
          (Complex.exp (deningerMeyerStrongLogMellin g s-deningerMeyerStrongLogMellin h s)-1) := by
        rw [he]; ring
    _ = _ := by rw [← hm, hdiv]; ring

/-- Entire convolution exponentiation, intrinsically defined on actual middle cohomology. -/
def deningerMeyerCohomologyExp : Q → Q :=
  Quotient.lift (fun g => Submodule.Quotient.mk (deningerMeyerSourceExp g))
    (fun _ _ h => deningerMeyerSourceExp_congr (Quotient.sound h))

@[simp] theorem deningerMeyerCohomologyExp_mk (g : V) :
    deningerMeyerCohomologyExp (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (deningerMeyerSourceExp g) := rfl

@[simp] theorem deningerMeyerCohomologyExp_zero : deningerMeyerCohomologyExp 0 = 0 := by
  change deningerMeyerCohomologyExp (Submodule.Quotient.mk (0 : V)) = 0
  rw [deningerMeyerCohomologyExp_mk, deningerMeyerSourceExp_zero]
  rfl

theorem deningerMeyerCohomologyExp_add (u v : Q) :
    deningerMeyerCohomologyExp (u+v) =
      deningerMeyerCohomologyExp u + deningerMeyerCohomologyExp v +
        deningerMeyerCohomologyConvolution (deningerMeyerCohomologyExp u)
          (deningerMeyerCohomologyExp v) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h =>
      rw [← Submodule.Quotient.mk_add]
      rw [deningerMeyerCohomologyExp_mk, deningerMeyerSourceExp_add]
      simp only [deningerMeyerCohomologyExp_mk,
        Submodule.Quotient.mk_add, deningerMeyerCohomologyConvolution_mk]

/-- The exponential supplies invertible multipliers of actual cohomology. -/
def deningerMeyerCohomologyGauge (u : Q) : Module.End ℂ Q :=
  LinearMap.id + deningerMeyerCohomologyConvolution (deningerMeyerCohomologyExp u)

@[simp] theorem deningerMeyerCohomologyGauge_mk (g : V) :
    deningerMeyerCohomologyGauge (Submodule.Quotient.mk g) =
      deningerMeyerCohomologySourceGauge g := by
  apply LinearMap.ext
  intro u
  induction u using Submodule.Quotient.induction_on with
  | H h =>
    change Submodule.Quotient.mk h +
      deningerMeyerCohomologyConvolution (deningerMeyerCohomologyExp (Submodule.Quotient.mk g))
        (Submodule.Quotient.mk h) = Submodule.Quotient.mk (deningerMeyerSourceGauge g h)
    simp only [deningerMeyerCohomologyExp_mk, deningerMeyerCohomologyConvolution_mk,
      deningerMeyerSourceGauge_apply, Submodule.Quotient.mk_add]

/-- Global nonlinear convolution gauges are bijective on the entire original quotient. -/
theorem deningerMeyerCohomologyGauge_bijective (u : Q) :
    Function.Bijective (deningerMeyerCohomologyGauge u) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    rw [deningerMeyerCohomologyGauge_mk]
    exact (deningerMeyerCohomologySourceGaugeEquiv g).bijective

end
end RHTower
