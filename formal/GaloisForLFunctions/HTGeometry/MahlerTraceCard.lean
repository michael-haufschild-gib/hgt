import GaloisForLFunctions.HTGeometry.MahlerTraceGerm

/-!
# The reduced trace over the rational function field

The rational function field `k(w)` sits inside the two-variable perfect base as the level-zero
layer, compatibly with the Euler derivation.  Hypertranscendence over the larger base therefore
descends to hypertranscendence over `k(w)`, which is the statement of the thermal Mahler theorem.
Rigidity of the Mahler constraint and irrationality of its solution are recorded as well.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-- The level-zero embedding of `k(w)` into the perfect base. -/
def kwToPerfect (p : ℕ) (hp : 1 < p) : RatFunc k →+* perfectBase (k := k) p hp :=
  RingHom.codRestrict (ratFuncToHahn : RatFunc k →+* HahnSeries ℚ k) (perfectBase p hp)
    (ratFuncToHahn_mem_perfectBase p hp)

@[simp]
theorem kwToPerfect_coe (p : ℕ) (hp : 1 < p) (r : RatFunc k) :
    ((kwToPerfect p hp r : perfectBase (k := k) p hp) : HahnSeries ℚ k) = ratFuncToHahn r := rfl

/-- `k(w)` acts on the two-variable perfect base through the level-zero embedding. -/
@[reducible] def kwBaseAlgebra (p : ℕ) (hp : 1 < p) : Algebra (RatFunc k) (MahlerPBase k p hp) :=
  ((algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp)).comp (kwToPerfect p hp)).toAlgebra

/-- `k(w)` acts on the Mahler ambient through the base. -/
@[reducible] def kwAmbientAlgebra [CharZero k] (p : ℕ) (hp : 1 < p) :
    Algebra (RatFunc k) (MahlerAmbient k) :=
  (((mahlerPEmbed k p hp).comp
    ((algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp)).comp
      (kwToPerfect p hp)))).toAlgebra

theorem kwToPerfect_eulerOp [CharZero k] (p : ℕ) (hp : 1 < p) (r : RatFunc k) :
    kwToPerfect p hp (ratFuncEulerOp r) = perfectBaseDeriv p hp (kwToPerfect p hp r) := by
  refine Subtype.ext ?_
  show ratFuncToHahn (ratFuncEulerOp r) = hahnQEuler (ratFuncToHahn r)
  exact ratFuncToHahn_eulerOp r

set_option maxHeartbeats 1000000 in
theorem kwBase_differential_compat [CharZero k] (p : ℕ) (hp : 1 < p) (r : RatFunc k) :
    letI := perfectAlgebra (k := k) p hp
    letI := perfectDifferential (k := k) p hp
    letI := kwBaseAlgebra (k := k) p hp
    letI := cylinderDifferential (1 : k)
    (twoCylinderDifferential (0 : perfectBase (k := k) p hp)).deriv
        (algebraMap (RatFunc k) (MahlerPBase k p hp) r)
      = algebraMap (RatFunc k) (MahlerPBase k p hp)
        ((cylinderDifferential (1 : k)).deriv r) := by
  letI := perfectAlgebra (k := k) p hp
  letI := perfectDifferential (k := k) p hp
  letI := kwBaseAlgebra (k := k) p hp
  letI := cylinderDifferential (1 : k)
  show twoCylDerivation (0 : perfectBase (k := k) p hp)
      (algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp) (kwToPerfect p hp r))
    = algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp)
      (kwToPerfect p hp ((cylinderDifferential (1 : k)).deriv r))
  rw [twoCylDerivation_algebraMap_const, cylinderDifferential_deriv,
    cylDeriv_one_eq_ratFuncEulerOp, kwToPerfect_eulerOp]
  rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The reduced one-particle trace of the `p`-adic Neumann-to-Dirichlet spectrum is
hypertranscendental over `k(w)` for the Euler derivation `w d/dw`**, for every `p ≥ 2`. -/
theorem hypertranscendentalOver_traceSeries_kw [CharZero k] (p : ℕ) (hp : 1 < p) :
    letI := cylinderDifferential (1 : k)
    letI := mahlerDifferential (k := k)
    letI := kwAmbientAlgebra (k := k) p hp
    HypertranscendentalOver (RatFunc k)
      (HahnSeries.C (traceSeries (k := k) p hp) : MahlerAmbient k) := by
  letI := perfectAlgebra (k := k) p hp
  letI := perfectDifferential (k := k) p hp
  letI := kwBaseAlgebra (k := k) p hp
  letI := kwAmbientAlgebra (k := k) p hp
  letI := mahlerPEmbedAlgebra (k := k) p hp
  letI := cylinderDifferential (1 : k)
  letI := mahlerDifferential (k := k)
  haveI : IsScalarTower (RatFunc k) (MahlerPBase k p hp) (MahlerAmbient k) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hbig := hypertranscendentalOver_traceSeries_euler (k := k) p hp
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton] at hbig
  exact hbig.restrictScalars
    (algebraMap (RatFunc k) (MahlerPBase k p hp)).injective

/-- **Rigidity of the thermal Mahler constraint**: it has a unique solution. -/
theorem traceSeries_unique [CharZero k] (p : ℕ) (hp : 1 < p) (V : HahnSeries ℚ k)
    (hV : V = HahnSeries.C (((p : k)) - 2) * wSeries k + (wSeries k) ^ p
      + HahnSeries.C ((p : k)) * mahlerHom p (by omega) V) :
    V = traceSeries (k := k) p hp := by
  have hU := traceSeries_mahler_equation (k := k) p hp
  have hY : mahlerHom p (by omega : 0 < p) (V - traceSeries (k := k) p hp)
      = HahnSeries.C (((p : k))⁻¹) * (V - traceSeries (k := k) p hp) := by
    have hpk : ((p : k)) ≠ 0 := by
      have : (0 : ℕ) < p := by omega
      exact Nat.cast_ne_zero.mpr this.ne'
    have hdiff : V - traceSeries (k := k) p hp
        = HahnSeries.C ((p : k))
          * mahlerHom p (by omega) (V - traceSeries (k := k) p hp) := by
      rw [map_sub, mul_sub]
      linear_combination hV - hU
    have hinv : (HahnSeries.C (((p : k))⁻¹) : HahnSeries ℚ k) * HahnSeries.C ((p : k)) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hpk, map_one]
    calc mahlerHom p (by omega : 0 < p) (V - traceSeries (k := k) p hp)
        = 1 * mahlerHom p (by omega) (V - traceSeries (k := k) p hp) := by rw [one_mul]
      _ = (HahnSeries.C (((p : k))⁻¹) * HahnSeries.C ((p : k)))
          * mahlerHom p (by omega) (V - traceSeries (k := k) p hp) := by rw [hinv]
      _ = HahnSeries.C (((p : k))⁻¹)
          * (HahnSeries.C ((p : k)) * mahlerHom p (by omega) (V - traceSeries (k := k) p hp)) := by
        ring
      _ = HahnSeries.C (((p : k))⁻¹) * (V - traceSeries (k := k) p hp) := by rw [← hdiff]
  have hne : ((p : k))⁻¹ ≠ 1 := by
    intro hcon
    have hpk : ((p : k)) ≠ 0 := by
      have : (0 : ℕ) < p := by omega
      exact Nat.cast_ne_zero.mpr this.ne'
    have hp1 : ((p : k)) = 1 := by
      field_simp at hcon
      linear_combination -hcon
    have h2 : ((p : ℕ) : k) = ((1 : ℕ) : k) := by push_cast; exact hp1
    have := Nat.cast_injective (R := k) h2
    omega
  have := eq_zero_of_mahlerHom_eq_smul hp hne hY
  linear_combination this

/-- **The reduced trace is not a rational function.** -/
theorem traceSeries_not_ratFunc [CharZero k] (p : ℕ) (hp : 1 < p) (r : RatFunc k) :
    ratFuncToHahn r ≠ traceSeries (k := k) p hp := by
  intro hr
  have hU := traceSeries_mahler_equation (k := k) p hp
  rw [← hr] at hU
  have hw : ratFuncToHahn (RatFunc.X : RatFunc k) = wSeries k := wCoord_coe (k := k) p hp
  have hL : ratFuncToHahn (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C ((p : k)))
        * ratFuncPow p (by omega) r - r)
      = HahnSeries.C ((p : k)) * mahlerHom p (by omega) (ratFuncToHahn r) - ratFuncToHahn r := by
    rw [map_sub, map_mul, ratFuncToHahn_pow p hp,
      show (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C ((p : k))))
        = algebraMap k (RatFunc k) ((p : k)) from (RatFunc.algebraMap_C _), ratFuncToHahn_const]
  have hR : ratFuncToHahn (algebraMap (Polynomial k) (RatFunc k)
        (Polynomial.C (-(((p : k)) - 2)) * Polynomial.X ^ (p ^ (0 : ℕ))
          + Polynomial.C (-1 : k) * Polynomial.X ^ (p ^ (0 + 1 : ℕ))))
      = -(HahnSeries.C (((p : k)) - 2)) * wSeries k
        + (-1 : HahnSeries ℚ k) * (wSeries k) ^ p := by
    rw [show (algebraMap (Polynomial k) (RatFunc k)
          (Polynomial.C (-(((p : k)) - 2)) * Polynomial.X ^ (p ^ (0 : ℕ))
            + Polynomial.C (-1 : k) * Polynomial.X ^ (p ^ (0 + 1 : ℕ))))
        = algebraMap k (RatFunc k) (-(((p : k)) - 2)) * (RatFunc.X : RatFunc k) ^ (p ^ (0 : ℕ))
          + algebraMap k (RatFunc k) (-1 : k) * (RatFunc.X : RatFunc k) ^ (p ^ (0 + 1 : ℕ))
        from by
      rw [map_add, map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_C,
        RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      rfl]
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ratFuncToHahn_const, ratFuncToHahn_const,
      hw, pow_zero, pow_one, pow_one, map_neg, map_neg, map_one]
  have heq : ratFuncToHahn (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C ((p : k)))
        * ratFuncPow p (by omega) r - r)
      = ratFuncToHahn (algebraMap (Polynomial k) (RatFunc k)
        (Polynomial.C (-(((p : k)) - 2)) * Polynomial.X ^ (p ^ (0 : ℕ))
          + Polynomial.C (-1 : k) * Polynomial.X ^ (p ^ (0 + 1 : ℕ)))) := by
    rw [hL, hR]
    linear_combination -hU
  have hkey := (ratFuncToHahn : RatFunc k →+* HahnSeries ℚ k).injective heq
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  refine no_ratFunc_mahler_solution (k := k) (p := p) (n := 0) hp hpk ?_ r hkey
  intro hcon
  have hp1 : ((p : k)) - 1 ≠ 0 := by
    intro h1
    have hp1' : ((p : k)) = 1 := by linear_combination h1
    have h2 : ((p : ℕ) : k) = ((1 : ℕ) : k) := by push_cast; exact hp1'
    have := Nat.cast_injective (R := k) h2
    omega
  refine hp1 ?_
  have h2 : (((p : k)) - 1) ^ 2 = 0 := by linear_combination -hcon
  exact (pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp h2

end

end GaloisForLFunctions.HTGeometry
