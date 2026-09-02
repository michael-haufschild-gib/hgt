import GaloisForLFunctions.RHTower.CliffordMultiplicity

/-!
# Clifford successor-doubling multiplicity mismatch

The Clifford doubling functor adds two generators by replacing `V` with `V × V`.  It therefore
doubles dimension.  At a Xi zero, a Clifford model must instead keep generalized-eigenspace
dimension equal to the same fixed analytic order.  Consequently the named doubling construction
cannot upgrade a level-`k` exact multiplicity model to level `k+1`: at every zero it has twice the
required multiplicity.  The corpus only supplies the reverse restriction map.
-/

open Complex Module

namespace RHTower

noncomputable section

/-- The public Clifford doubling functor doubles underlying dimension. -/
theorem finrank_anticommSpace_double_eq_two_mul
    {k m : ℕ} (S : AnticommSpace k m) :
    finrank ℂ S.double.V = 2 * finrank ℂ S.V := by
  change finrank ℂ (S.V × S.V) = 2 * finrank ℂ S.V
  rw [finrank_prod]
  omega

/-- Doubling cannot preserve any positive target dimension. -/
theorem finrank_anticommSpace_double_ne_target_of_exact
    {k m n : ℕ} (S : AnticommSpace k m) (hn : n ≠ 0)
    (hexact : finrank ℂ S.V = n) :
    finrank ℂ S.double.V ≠ n := by
  rw [finrank_anticommSpace_double_eq_two_mul, hexact]
  omega

/-- At a Xi zero, the doubled Clifford space cannot remain an exact model of that zero's
unchanged analytic multiplicity. -/
theorem finrank_anticommSpace_double_ne_xi_order
    {rho : ℂ} (hzero : xi rho = 0) {k m : ℕ} (S : AnticommSpace k m)
    (hexact : finrank ℂ S.V = (analyticOrderAt xi rho).toNat) :
    finrank ℂ S.double.V ≠ (analyticOrderAt xi rho).toNat :=
  finrank_anticommSpace_double_ne_target_of_exact S
    (xi_order_toNat_ne_zero hzero) hexact

end

end RHTower
