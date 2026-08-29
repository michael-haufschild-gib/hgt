import GaloisForLFunctions.HTGeometry.QDifferenceInhomogeneousHT

/-!
# The geometric Källén–Lehmann response is hypertranscendental

The response of the geometric spectrum obeys `R - a R(bz) = (1-a)/(1-z)`.  The inhomogeneity is a
cotangent model plus a constant, so the first-order inhomogeneous `q`-difference criterion applies
whenever the two multipliers are multiplicatively independent.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Multiplicative Polynomial

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

theorem algebraMap_eq_toRF_C (x : k) : algebraMap k (RatFunc k) x = toRF (Polynomial.C x) := by
  rw [toRF, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- The cotangent model differs from a constant by a simple pole. -/
theorem cotModel_sub_const (c : k) :
    cotModel c - algebraMap k (RatFunc k) c
      = algebraMap k (RatFunc k) (2 * c) / toRF (linFac k) := by
  have hlin : toRF (linFac k) ≠ 0 := RatFunc.algebraMap_ne_zero linFac_ne_zero
  rw [cotModel, algebraMap_eq_toRF_C, algebraMap_eq_toRF_C, eq_div_iff hlin, sub_mul,
    div_mul_cancel₀ _ hlin, ← map_mul, ← map_sub]
  congr 1
  rw [linFac]
  simp only [map_mul, map_ofNat, Polynomial.C_1, mul_one]
  ring

/-- The simple pole `w/(1-X)` is a cotangent model plus a constant. -/
theorem oneSubInv_eq_cotModel_add_const [CharZero k] (w : k) :
    algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X)
      = cotModel (-(w / 2)) + algebraMap k (RatFunc k) (w / 2) := by
  have hlin : toRF (linFac k) ≠ 0 := RatFunc.algebraMap_ne_zero linFac_ne_zero
  have hneg : toRF (Polynomial.C (1 : k) - Polynomial.X) = -toRF (linFac k) := by
    rw [← map_neg]
    congr 1
    rw [linFac]
    ring
  have h := cotModel_sub_const (-(w / 2))
  have h2 : (2 : k) * -(w / 2) = -w := by ring
  rw [h2] at h
  have hsum : cotModel (-(w / 2)) + algebraMap k (RatFunc k) (w / 2)
      = algebraMap k (RatFunc k) (-w) / toRF (linFac k) := by
    rw [← h, map_neg]
    ring
  rw [hneg, div_neg, hsum, map_neg, neg_div]

/-! ## The geometric series realization -/

theorem coeff_ofPowerSeries_mk (f : ℕ → k) (n : ℤ) :
    (HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk f)).coeff n
      = if n < 0 then 0 else f n.natAbs := by
  rw [PowerSeries.coeff_coe]
  by_cases h : n < 0
  · simp [h]
  · simp [h]

theorem algebraMap_linFacInv (w : k) :
    algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X))
      = HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk (fun _ => w)) := by
  have hne : toRF (Polynomial.C (1 : k) - Polynomial.X) ≠ 0 := by
    refine RatFunc.algebraMap_ne_zero ?_
    intro h
    have := congrArg (fun p : Polynomial k => p.coeff 1) h
    simp at this
  have himg : algebraMap (RatFunc k) (LaurentSeries k) (toRF (Polynomial.C 1 - Polynomial.X))
      = 1 - HahnSeries.single 1 1 := by
    have hcoe : algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C 1 - Polynomial.X))
        = HahnSeries.ofPowerSeries ℤ k
          ((Polynomial.C 1 - Polynomial.X : Polynomial k) : PowerSeries k) :=
      (RatFunc.coe_coe _).symm
    rw [toRF, hcoe]
    refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
    rw [PowerSeries.coeff_coe, HahnSeries.coeff_sub, HahnSeries.coeff_one,
      HahnSeries.coeff_single]
    by_cases h : n < 0
    · simp [h, (by omega : n ≠ 0), (by omega : n ≠ 1)]
    · have hnat : ((Polynomial.C 1 - Polynomial.X : Polynomial k) : PowerSeries k) = 1 - PowerSeries.X := by
        push_cast
        simp
      rw [if_neg h, hnat]
      by_cases h0 : n = 0
      · subst h0; simp
      · by_cases h1 : n = 1
        · subst h1; simp
        · have : n.natAbs ≠ 0 := by omega
          have h1' : n.natAbs ≠ 1 := by omega
          simp [h0, h1, this, h1', PowerSeries.coeff_X]
  have hmul : (1 - HahnSeries.single (1 : ℤ) (1 : k))
      * HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk (fun _ => w))
      = HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk (fun n => if n = 0 then w else 0)) := by
    refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
    rw [sub_mul, one_mul, coeff_ofPowerSeries_mk, coeff_ofPowerSeries_mk]
    sorry
  sorry

end

end GaloisForLFunctions.HTGeometry
