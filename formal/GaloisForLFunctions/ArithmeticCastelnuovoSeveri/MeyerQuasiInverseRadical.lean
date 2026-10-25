import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PositiveMeyerDegreesCanForgetClasses
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionInverseSource

/-!
# Actual quasi-inversion and the Meyer trace radical

A genuine class has a quasi-inverse exactly when its Mellin values avoid -1 at
every Xi point. Requiring every product of a class to have a quasi-inverse
therefore detects exactly the ordinary trace radical. All inverse kernels are
actual all-weight sources; no completion or continuity premise is introduced.
-/

noncomputable section
open Complex RHTower
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Quasi-regularity in the literal nonunital source convolution algebra. -/
def MeyerQuasiRegular (u : DeningerMeyerStrongLogCohomology) : Prop :=
  ∃ v : DeningerMeyerStrongLogCohomology,
    u + v + deningerMeyerCohomologyConvolution u v = 0

/-- Actual source inversion has precisely the Xi-value obstruction. -/
theorem meyerQuasiRegular_iff_values (u : DeningerMeyerStrongLogCohomology) :
    MeyerQuasiRegular u ↔ ∀ rho : XiDivisorSupport, 1 + meyerPointDegree rho u ≠ 0 := by
  constructor
  · rintro ⟨v, hv⟩ rho hz
    have he := congrArg (meyerPointDegree rho) hv
    rw [map_add, map_add, meyerPointDegree_product, map_zero] at he
    have hp : (1 + meyerPointDegree rho u) * (1 + meyerPointDegree rho v) = 1 := by
      linear_combination he
    rw [hz, zero_mul] at hp
    exact zero_ne_one hp
  · induction u using Submodule.Quotient.induction_on with
    | H g =>
      intro hg
      obtain ⟨h, hh⟩ := exists_deningerMeyerSourceQuasiInverse g hg
      refine ⟨Submodule.Quotient.mk h, ?_⟩
      rw [deningerMeyerCohomologyConvolution_mk]
      change (LinearMap.range deningerMeyerStrongLogSumLM).mkQ g +
        (LinearMap.range deningerMeyerStrongLogSumLM).mkQ h +
        (LinearMap.range deningerMeyerStrongLogSumLM).mkQ (deningerMeyerSourceConvolution g h) = 0
      rw [← map_add, ← map_add]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hh

/-- The universal quasi-inverse condition for the nonunital radical. -/
def MeyerQuasiRadical (u : DeningerMeyerStrongLogCohomology) : Prop :=
  ∀ v : DeningerMeyerStrongLogCohomology,
    MeyerQuasiRegular (deningerMeyerCohomologyConvolution u v)

/-- Universal product inversion sees values, whereas principal equivalence sees every lower jet. -/
theorem meyerQuasiRadical_iff_values_zero (u : DeningerMeyerStrongLogCohomology) :
    MeyerQuasiRadical u ↔ ∀ rho : XiDivisorSupport, meyerPointDegree rho u = 0 := by
  constructor
  · intro hu rho
    by_contra hz
    let v : DeningerMeyerStrongLogCohomology :=
      (- (meyerPointDegree rho u)⁻¹) • Submodule.Quotient.mk (meyerPointSource rho)
    have h := (meyerQuasiRegular_iff_values _).mp (hu v) rho
    apply h
    rw [meyerPointDegree_product]
    have hv : meyerPointDegree rho v = -(meyerPointDegree rho u)⁻¹ := by
      simp only [v, map_smul, meyerPointDegree_mk, meyerPointSource_values,
        if_pos rfl, smul_eq_mul, mul_one]
    rw [hv, mul_neg, mul_inv_cancel₀ hz, add_neg_cancel]
  · intro hu v
    apply (meyerQuasiRegular_iff_values _).mpr
    intro rho
    rw [meyerPointDegree_product, hu rho, zero_mul, add_zero]
    exact one_ne_zero

/-- The ordinary trace radical is exactly the universal actual quasi-inverse radical. -/
theorem meyerQuasiRadical_mk_iff_trace_radical (g : DeningerMeyerStrongLogTarget) :
    MeyerQuasiRadical (Submodule.Quotient.mk g) ↔
      ∀ h : DeningerMeyerStrongLogTarget, meyerSourceTrace g h = 0 := by
  rw [meyerQuasiRadical_iff_values_zero]
  simp only [meyerPointDegree_mk]
  exact (meyerSourceTrace_radical_iff_values_zero g).symm

/-- The genuine source algebra has zero quasi-inverse radical exactly when the Xi divisor is simple. -/
theorem meyerQuasiRadical_eq_zero_iff_simple :
    (∀ u : DeningerMeyerStrongLogCohomology, MeyerQuasiRadical u ↔ u = 0) ↔
      ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  rw [← meyerSourceTrace_radical_eq_boundary_iff_simple]
  constructor
  · intro h g
    exact (meyerQuasiRadical_mk_iff_trace_radical g).symm.trans
      ((h (Submodule.Quotient.mk g)).trans (Submodule.Quotient.mk_eq_zero (LinearMap.range deningerMeyerStrongLogSumLM)))
  · intro h u
    induction u using Submodule.Quotient.induction_on with
    | H g =>
      exact (meyerQuasiRadical_mk_iff_trace_radical g).trans
        ((h g).trans (Submodule.Quotient.mk_eq_zero (LinearMap.range deningerMeyerStrongLogSumLM)).symm)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerQuasiRegular_iff_values
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerQuasiRadical_iff_values_zero
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerQuasiRadical_mk_iff_trace_radical
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerQuasiRadical_eq_zero_iff_simple
