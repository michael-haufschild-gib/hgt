import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveLogarithmicForms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedOriginTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalExteriorTraceIdentity

/-! Specialization of the residue of a traced logarithmic volume form. -/

noncomputable section

open KaehlerDifferential GaloisForLFunctions.HTGeometry GlobalTheory.CechDR
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k F K L : Type} [Field k] [Field F] [Field K] [Field L]
  [Algebra k F] [Algebra k K] [Algebra k L] [Algebra F K] [Algebra F L] [Algebra K L]
  [IsScalarTower k F K] [IsScalarTower k F L] [IsScalarTower k K L] [IsScalarTower F K L]
  {d : ℕ} {x : Fin (d + 1) → F}

theorem pullbackDR_vol0 :
    pullbackDR (IsScalarTower.toAlgHom k K L) (vol0 k K x) = vol0 k L x := by
  unfold vol0
  rw [pullbackDR_wedge]
  congr 1
  funext j
  rw [algHomKaehlerMap_smul, algHomKaehlerMap_D, map_inv₀]
  change (algebraMap K L (algebraMap F K (x j.succ / x 0)))⁻¹ •
      D k L (algebraMap K L (algebraMap F K (x j.succ / x 0))) = _
  rw [← IsScalarTower.algebraMap_apply F K L]

variable [Module.Finite F K] [Module.Finite K L] [Algebra.Etale K L]

/-- Trace down the tower on a logarithmic volume form agrees with field
trace of its coefficient. -/
theorem traceDR_vol0_coefficient (τ : DR k K →ₗ[K] K) (hτ : IsTop (x := x) τ) (b : L) :
    Algebra.trace F K (τ (traceDR k K L (b • vol0 k L x))) = Algebra.trace F L b := by
  rw [← pullbackDR_vol0 (k := k) (K := K), traceDR_smul_pullback,
    map_smul, hτ.1, smul_eq_mul, mul_one, Algebra.trace_trace]

/-- The residue of a traced logarithmic volume form with a regular
coefficient is the sum of its coefficient values on the origin fibre. -/
theorem IsFinCover.residue_traceDR_origin [IsAlgClosed k] (hL : IsFinCover k L x)
    [IsReduced ((rB k L x {0}) ⧸ originIdeal k L x)]
    (ρ : F →ₗ[k] k) (hρ : IsRes x ρ) (τ : DR k K →ₗ[K] K) (hτ : IsTop (x := x) τ)
    (b : rB k L x {0}) :
    ρ (Algebra.trace F K (τ (traceDR k K L ((b : L) • vol0 k L x)))) =
      ∑ᶠ e : OriginFibrePoint k L x, e.1 b := by
  rw [traceDR_vol0_coefficient τ hτ]
  exact hL.residue_trace_origin ρ hρ b

end GlobalTheory.PD
