import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphic
import GaloisForLFunctions.HTGeometry.BesselOrderRiccatiBaseField
import GaloisForLFunctions.HTGeometry.HolderShiftElimination

/-!
# Rational Riccati obstruction for the Bessel order recurrence

The companion equation for the order recurrence is

`sigma^(2 : ℕ) y - c (X + 1) sigma y - y = 0`,

so its Riccati equation is `u * sigma u - c (X + 1) * u - 1 = 0` over `ℂ(X)`.
This module proves unconditionally that the Riccati equation has no rational solution whenever
`c != 0`.  The proof is denominator-theoretic: in a reduced presentation `u = p / q`, the shifted
denominator divides `p`; after cancellation the residual factor divides both `p` and `q`, hence is
a unit.  The remaining identity then has degree `deg q + 1` on one side and at most `deg q` on the
other.

This is the exact irreducibility obstruction for the rank-two Bessel difference module.  It does
not assert the still-missing parameterized Picard--Vessiot classification theorem.
-/

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

open Polynomial

/-- Polynomial denominator form of the rational Riccati obstruction. -/
theorem orderBesselRiccatiPolynomial_no_solution
    {c : ℂ} (hc : c ≠ 0) {p q : Polynomial ℂ} (hq : q ≠ 0)
    (hco : IsCoprime p q)
    (h : p * p.comp (X + C 1) -
        (C c * (X + C 1)) * p * q.comp (X + C 1) -
        q * q.comp (X + C 1) = 0) : False := by
  exact FieldShift.orderBesselRiccatiPolynomial_no_solution hc hq hco h

/-- The Bessel Riccati equation has no solution in `ℂ(X)` for any nonzero slope. -/
theorem orderBesselRiccati_no_ratFunc_solution {c : ℂ} (hc : c ≠ 0) :
    ¬ ∃ u : RatFunc ℂ,
      u * ratShift u -
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (C c * (X + C 1)) * u - 1 = 0 := by
  rintro ⟨u, huRic⟩
  let p := u.num
  let q := u.denom
  have hq : q ≠ 0 := u.denom_ne_zero
  have hco : IsCoprime p q := u.isCoprime_num_denom
  have hqK : algebraMap (Polynomial ℂ) (RatFunc ℂ) q ≠ 0 := fun hzero =>
    hq (RatFunc.algebraMap_injective ℂ (by rw [hzero, map_zero]))
  have hqs : q.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hq
  have hqsK : algebraMap (Polynomial ℂ) (RatFunc ℂ) (q.comp (X + C 1)) ≠ 0 :=
    fun hzero => hqs (RatFunc.algebraMap_injective ℂ (by rw [hzero, map_zero]))
  have hratio : algebraMap (Polynomial ℂ) (RatFunc ℂ) p /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) q = u := RatFunc.num_div_denom u
  have hshift : ratShift u =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X + C 1)) /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (q.comp (X + C 1)) := by
    rw [← hratio, map_div₀, ratShift_algebraMap, ratShift_algebraMap]
  have hcross : p * p.comp (X + C 1) -
      (C c * (X + C 1)) * p * q.comp (X + C 1) -
      q * q.comp (X + C 1) = 0 := by
    apply RatFunc.algebraMap_injective ℂ
    simp only [map_sub, map_mul, map_zero]
    rw [hshift, ← hratio] at huRic
    field_simp [hqK, hqsK] at huRic
    simp only [map_mul] at huRic
    linear_combination huRic
  exact orderBesselRiccatiPolynomial_no_solution hc hq hco hcross

/-- Physical specialization `c = 2 / s`: positive argument makes the Bessel Riccati obstruction
nondegenerate. -/
theorem modifiedBesselOrderRiccati_no_ratFunc_solution
    {s : ℝ} (hs : 0 < s) :
    ¬ ∃ u : RatFunc ℂ,
      u * ratShift u -
        algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (C (2 / (s : ℂ)) * (X + C 1)) * u - 1 = 0 := by
  apply orderBesselRiccati_no_ratFunc_solution
  exact div_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt hs)

end

end HTGeometry
end GaloisForLFunctions
