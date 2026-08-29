import GaloisForLFunctions.HTGeometry.MahlerTraceCard
import GaloisForLFunctions.HTGeometry.GeometricKallenLehmannHypertranscendence

/-!
# The spectral zeta function of the ultrametric spectrum

The same spectrum whose heat trace is hypertranscendental has a spectral zeta function that is a
*rational* function of `u = p^(-s)`:

```text
ζ_p(u) = (p−2) + (p−1)²·u/(1 − p·u).
```

Being an element of the coefficient field, it is differentially algebraic — the observation
fracture between the thermal and the Dirichlet reporter.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-- The Dirichlet coefficients of the reduced spectrum. -/
def zetaCoeff (p : ℕ) (n : ℕ) : k :=
  if n = 0 then ((p : k)) - 2 else (((p : k)) - 1) ^ 2 * ((p : k)) ^ (n - 1)

/-- The spectral zeta function as a series in `u = p^(-s)`. -/
def zetaSeries (p : ℕ) : LaurentSeries k :=
  HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk (zetaCoeff (k := k) p))

theorem coeff_zetaSeries (p : ℕ) (n : ℤ) :
    (zetaSeries (k := k) p).coeff n = if n < 0 then 0 else zetaCoeff p n.natAbs :=
  coeff_ofPowerSeries_mk (zetaCoeff (k := k) p) n

/-- The closed rational form of the spectral zeta function. -/
def zetaRat (p : ℕ) : RatFunc k :=
  algebraMap k (RatFunc k) (((p : k)) - 2)
    + algebraMap k (RatFunc k) ((((p : k)) - 1) ^ 2) * RatFunc.X
      * (1 - algebraMap k (RatFunc k) ((p : k)) * RatFunc.X)⁻¹

theorem oneSubPX_ne_zero (p : ℕ) :
    (1 - algebraMap k (RatFunc k) ((p : k)) * (RatFunc.X : RatFunc k)) ≠ 0 := by
  intro h
  have h2 := congrArg (algebraMap (RatFunc k) (LaurentSeries k)) h
  rw [map_sub, map_one, map_mul, algebraMap_const_laurentSeries, algebraMap_ratFuncX,
    laurentCoord, map_zero] at h2
  have h3 := congrArg (fun x : LaurentSeries k => x.coeff 0) h2
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_one, HahnSeries.coeff_zero,
    HahnSeries.single_mul_single, zero_add, mul_one] at h3
  rw [if_pos trivial, HahnSeries.coeff_single_of_ne (by norm_num : (0 : ℤ) ≠ 1), sub_zero] at h3
  exact one_ne_zero h3

set_option maxHeartbeats 1000000 in
/-- **The Dirichlet reporter is rational**: the spectral zeta series is the expansion of a
rational function of `u = p^(-s)`. -/
theorem zetaSeries_eq_algebraMap [CharZero k] (p : ℕ) (hp : 1 < p) :
    zetaSeries (k := k) p = algebraMap (RatFunc k) (LaurentSeries k) (zetaRat p) := by
  have hunit : (1 - HahnSeries.single (1 : ℤ) ((p : k)) : LaurentSeries k)
      = algebraMap (RatFunc k) (LaurentSeries k)
        (1 - algebraMap k (RatFunc k) ((p : k)) * RatFunc.X) := by
    rw [map_sub, map_one, map_mul, algebraMap_const_laurentSeries, algebraMap_ratFuncX,
      laurentCoord,
      show (HahnSeries.single (0 : ℤ) ((p : k)) : LaurentSeries k) * HahnSeries.single 1 1
        = HahnSeries.single 1 ((p : k)) from by
      rw [HahnSeries.single_mul_single, zero_add, mul_one]]
  have hne : (1 - HahnSeries.single (1 : ℤ) ((p : k)) : LaurentSeries k) ≠ 0 := by
    rw [hunit]
    intro hz
    exact oneSubPX_ne_zero p
      ((injective_iff_map_eq_zero (algebraMap (RatFunc k) (LaurentSeries k))).mp
        (algebraMap (RatFunc k) (LaurentSeries k)).injective _ hz)
  refine mul_left_cancel₀ hne ?_
  have hprod : (1 - HahnSeries.single (1 : ℤ) ((p : k)) : LaurentSeries k) * zetaSeries (k := k) p
      = HahnSeries.C (((p : k)) - 2) * (1 - HahnSeries.single (1 : ℤ) ((p : k)))
        + HahnSeries.C ((((p : k)) - 1) ^ 2) * HahnSeries.single (1 : ℤ) 1 := by
    refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
    rw [sub_mul, one_mul, HahnSeries.coeff_sub, HahnSeries.coeff_single_mul,
      HahnSeries.coeff_add, coeff_C_mul_hahn, coeff_C_mul_hahn, HahnSeries.coeff_sub,
      HahnSeries.coeff_one, HahnSeries.coeff_single, HahnSeries.coeff_single,
      coeff_zetaSeries, coeff_zetaSeries]
    by_cases h0 : n < 0
    · have e1 : ¬ (n = 0) := by omega
      have e2 : ¬ (n = 1) := by omega
      have e3 : (n - 1 : ℤ) < 0 := by omega
      simp [h0, e1, e2, e3]
    · by_cases h1 : n = 0
      · subst h1
        have e3 : ((0 : ℤ) - 1 : ℤ) < 0 := by omega
        simp [h0, e3, zetaCoeff]
      · by_cases h2 : n = 1
        · subst h2
          have e3 : ¬ ((1 : ℤ) - 1 < 0) := by omega
          simp only [if_neg h0, if_neg e3, if_neg h1, if_pos rfl, zetaCoeff]
          norm_num
          ring
        · have e3 : ¬ ((n : ℤ) - 1 < 0) := by omega
          have hnat : n.natAbs - 1 = ((n - 1).natAbs - 1) + 1 := by omega
          simp only [if_neg h0, if_neg e3, if_neg h1, if_neg h2, zetaCoeff,
            if_neg (show ¬ n.natAbs = 0 by omega),
            if_neg (show ¬ (n - 1).natAbs = 0 by omega)]
          rw [hnat, pow_succ]
          ring
  rw [hprod, hunit, ← map_mul]
  have hcancel : (1 - algebraMap k (RatFunc k) ((p : k)) * (RatFunc.X : RatFunc k)) * zetaRat p
      = algebraMap k (RatFunc k) (((p : k)) - 2)
          * (1 - algebraMap k (RatFunc k) ((p : k)) * RatFunc.X)
        + algebraMap k (RatFunc k) ((((p : k)) - 1) ^ 2) * RatFunc.X := by
    have hden : (1 - algebraMap k (RatFunc k) ((p : k)) * (RatFunc.X : RatFunc k)) ≠ 0 :=
      oneSubPX_ne_zero p
    rw [zetaRat, mul_add]
    field_simp
  rw [hcancel, map_add, map_mul, map_mul, algebraMap_const_laurentSeries,
    algebraMap_const_laurentSeries, algebraMap_ratFuncX, laurentCoord, ← hunit,
    HahnSeries.C_apply, HahnSeries.C_apply]

/-- **The Dirichlet reporter is differentially algebraic**, being an element of the coefficient
field, while the thermal reporter is hypertranscendental. -/
theorem differentialAlgebraicOver_zetaSeries [CharZero k] (p : ℕ) (hp : 1 < p) :
    letI := innerOrdinaryDifferential (k := k)
    DifferentialAlgebraicOver (RatFunc k) (zetaSeries (k := k) p) := by
  letI := innerOrdinaryDifferential (k := k)
  rw [zetaSeries_eq_algebraMap p hp]
  exact differentialAlgebraicOver_algebraMap _

end

end GaloisForLFunctions.HTGeometry
