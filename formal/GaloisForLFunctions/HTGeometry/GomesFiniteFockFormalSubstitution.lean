import GaloisForLFunctions.HTGeometry.GomesFiniteFockFormalSeries
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Finite clock evaluation respects based formal substitution

The augmentation ideal is the natural carrier of formal changes of clock.
Its elements evaluate to nilpotent matrices, so substitution terminates exactly
at the existing jet horizon. No analytic convergence hypothesis is required.
-/

noncomputable section
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Based formal clock coordinates form the existing constant-coefficient augmentation ideal. -/
abbrev GomesBasedFormalSeries := RingHom.ker (PowerSeries.constantCoeff : PowerSeries ℂ →+* ℂ)

/-- Every based symbol has exactly the required zero constant coefficient. -/
theorem gomesBasedFormalSeries_constantCoeff (G : GomesBasedFormalSeries) :
    PowerSeries.constantCoeff G.val = 0 := RingHom.mem_ker.mp G.property

/-- Every based symbol can be substituted formally. -/
theorem gomesBasedFormalSeries_hasSubst (G : GomesBasedFormalSeries) : PowerSeries.HasSubst G.val :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (gomesBasedFormalSeries_constantCoeff G)

/-- Every based formal symbol vanishes to the horizon power under actual finite clock evaluation. -/
theorem gomesFiniteFockFormalHom_based_pow (N : ℕ) (G : GomesBasedFormalSeries) :
    gomesFiniteFockFormalHom N G.val ^ N = 0 := by
  obtain ⟨Q, hQ⟩ := PowerSeries.X_dvd_iff.mpr (gomesBasedFormalSeries_constantCoeff G)
  rw [← map_pow, hQ, mul_pow, map_mul, map_pow, gomesFiniteFockFormalHom_X,
    fockShiftMatrix_nilpotent, zero_mul]

/-- After finite evaluation, substitution is precisely polynomial evaluation of the truncated outer symbol. -/
theorem gomesFiniteFockFormalHom_subst (N : ℕ) (F : PowerSeries ℂ) (G : GomesBasedFormalSeries) :
    gomesFiniteFockFormalHom N (F.subst G.val) =
      Polynomial.aeval (gomesFiniteFockFormalHom N G.val) (PowerSeries.trunc N F) := by
  have hg := gomesBasedFormalSeries_hasSubst G
  have hs := congrArg (fun P : PowerSeries ℂ => gomesFiniteFockFormalHom N (P.subst G.val))
    (PowerSeries.eq_X_pow_mul_shift_add_trunc N F)
  rw [PowerSeries.subst_add hg, PowerSeries.subst_mul hg, PowerSeries.subst_pow hg,
    PowerSeries.subst_X hg, map_add, map_mul, map_pow, gomesFiniteFockFormalHom_based_pow,
    zero_mul, zero_add, PowerSeries.subst_coe hg] at hs
  simpa only [Polynomial.aeval_algHom, AlgHom.comp_apply] using hs

/-- Two based coordinates are indistinguishable by all substituted symbols exactly when their finite matrices agree. -/
theorem gomesFiniteFockFormalHom_subst_eq_iff (N : ℕ) (G H : GomesBasedFormalSeries) :
    (∀ F : PowerSeries ℂ,
      gomesFiniteFockFormalHom N (F.subst G.val) = gomesFiniteFockFormalHom N (F.subst H.val)) ↔
      gomesFiniteFockFormalHom N G.val = gomesFiniteFockFormalHom N H.val := by
  constructor
  · intro h
    simpa only [PowerSeries.subst_X (gomesBasedFormalSeries_hasSubst G),
      PowerSeries.subst_X (gomesBasedFormalSeries_hasSubst H)] using h PowerSeries.X
  · intro h F
    rw [gomesFiniteFockFormalHom_subst, gomesFiniteFockFormalHom_subst, h]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
