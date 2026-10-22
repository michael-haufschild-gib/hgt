import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerSourceConvolution

/-! # Convolution on actual Meyer middle cohomology

The product is induced by literal source convolution. In particular its
well-definedness is paid in the original Poisson complex, not postulated
from the spectral recipient.
-/

namespace RHTower
noncomputable section

local notation "V" => DeningerMeyerStrongLogTarget
local notation "Q" => DeningerMeyerStrongLogCohomology
local notation "N" => LinearMap.range deningerMeyerStrongLogSumLM

private def convLeft (g : V) : Q →ₗ[ℂ] Q :=
  (N).liftQ ((N).mkQ.comp (deningerMeyerSourceConvolutionLM g)) (by
    rintro _ ⟨f, rfl⟩
    change Submodule.Quotient.mk
      (deningerMeyerSourceConvolution g (deningerMeyerStrongLogSumLM f)) = (0 : Q)
    rw [Submodule.Quotient.mk_eq_zero]
    exact deningerMeyerSourceConvolution_boundary g f)

private def convSourceLeft : V →ₗ[ℂ] Q →ₗ[ℂ] Q where
  toFun := convLeft
  map_add' g h := by
    apply LinearMap.ext
    intro u
    induction u using Submodule.Quotient.induction_on with
    | H k =>
      change (N).mkQ (deningerMeyerSourceConvolutionLM (g+h) k) =
        (N).mkQ (deningerMeyerSourceConvolutionLM g k) +
          (N).mkQ (deningerMeyerSourceConvolutionLM h k)
      rw [map_add, LinearMap.add_apply, map_add]
  map_smul' c g := by
    apply LinearMap.ext
    intro u
    induction u using Submodule.Quotient.induction_on with
    | H k =>
      change (N).mkQ (deningerMeyerSourceConvolutionLM (c • g) k) =
        c • (N).mkQ (deningerMeyerSourceConvolutionLM g k)
      rw [map_smul, LinearMap.smul_apply, map_smul]

/-- The actual Poisson quotient carries the original convolution product. -/
def deningerMeyerCohomologyConvolution : Q →ₗ[ℂ] Q →ₗ[ℂ] Q :=
  (N).liftQ convSourceLeft (by
    rintro _ ⟨f, rfl⟩
    apply LinearMap.ext
    intro u
    induction u using Submodule.Quotient.induction_on with
    | H g =>
      change Submodule.Quotient.mk
        (deningerMeyerSourceConvolution (deningerMeyerStrongLogSumLM f) g) = (0 : Q)
      rw [deningerMeyerSourceConvolution_comm, Submodule.Quotient.mk_eq_zero]
      exact deningerMeyerSourceConvolution_boundary g f)

@[simp] theorem deningerMeyerCohomologyConvolution_mk (g h : V) :
    deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g) (Submodule.Quotient.mk h) =
      Submodule.Quotient.mk (deningerMeyerSourceConvolution g h) := rfl

theorem deningerMeyerCohomologyConvolution_comm (u v : Q) :
    deningerMeyerCohomologyConvolution u v = deningerMeyerCohomologyConvolution v u := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h => simp only [deningerMeyerCohomologyConvolution_mk, deningerMeyerSourceConvolution_comm g h]

theorem deningerMeyerCohomologyConvolution_assoc (u v w : Q) :
    deningerMeyerCohomologyConvolution (deningerMeyerCohomologyConvolution u v) w =
      deningerMeyerCohomologyConvolution u (deningerMeyerCohomologyConvolution v w) := by
  induction u using Submodule.Quotient.induction_on with
  | H f =>
    induction v using Submodule.Quotient.induction_on with
    | H g =>
      induction w using Submodule.Quotient.induction_on with
      | H h => simp only [deningerMeyerCohomologyConvolution_mk, deningerMeyerSourceConvolution_assoc]

end
end RHTower
