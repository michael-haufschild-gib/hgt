import GaloisForLFunctions.HTGeometry.MahlerHahnModel
import GaloisForLFunctions.HTGeometry.QDifferenceEulerCompat

/-!
# The rational base of the Mahler model

The two-variable rational field `k(w)(h)` embeds into `k((w^ℚ))((h))` by expanding the first
coordinate in Hahn series and the second in Laurent series.  The Mahler substitution `w ↦ w^p`
together with `h ↦ p⁻¹h` is the restriction of the ambient operator.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-- The coefficient embedding of `k(w)` into Hahn series with rational exponents. -/
def ratFuncToHahn : RatFunc k →+* HahnSeries ℚ k :=
  (laurentToHahn : LaurentSeries k →+* HahnSeries ℚ k).comp
    (algebraMap (RatFunc k) (LaurentSeries k))

theorem ratFuncToHahn_const (c : k) :
    ratFuncToHahn (algebraMap k (RatFunc k) c) = HahnSeries.C c := by
  rw [ratFuncToHahn, RingHom.coe_comp, Function.comp_apply, algebraMap_const_laurentSeries,
    laurentToHahn]
  show HahnSeries.embDomain _ (HahnSeries.single (0 : ℤ) c) = HahnSeries.C c
  rw [HahnSeries.embDomain_single, HahnSeries.C_apply]
  norm_num

theorem ratFuncToHahn_pow (p : ℕ) (hp : 1 < p) (r : RatFunc k) :
    ratFuncToHahn (ratFuncPow p (by omega) r) = mahlerHom p (by omega) (ratFuncToHahn r) := by
  show laurentToHahn (algebraMap (RatFunc k) (LaurentSeries k) (ratFuncPow p (by omega) r))
    = mahlerHom p (by omega)
      (laurentToHahn (algebraMap (RatFunc k) (LaurentSeries k) r))
  rw [← ramify_algebraMap p (by omega), laurentToHahn_ramify p hp]

/-- The two-variable rational base of a Mahler equation. -/
abbrev MahlerBase (k : Type*) [Field k] := RatFunc (RatFunc k)

theorem ratFuncPow_injective' (p : ℕ) (hp : 1 < p) :
    Function.Injective (ratFuncPow (k := k) p (by omega)) :=
  RatFunc.map_injective (R := k) (S := k) (polyPow (k := k) p)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyPow_injective (by omega)))
    (polyPow_injective (by omega))

/-- The Mahler substitution on the base: `w ↦ w^p`, `h ↦ p⁻¹ h`. -/
def mahlerBaseDilation [CharZero k] (p : ℕ) (hp : 1 < p) : MahlerBase k →+* MahlerBase k :=
  ratFuncTwist (ratFuncPow p (by omega)) (ratFuncPow_injective' p hp)
    (algebraMap k (RatFunc k) (((p : k))⁻¹))
    (by
      have hpk : ((p : k)) ≠ 0 := by
        have : (0 : ℕ) < p := by omega
        exact Nat.cast_ne_zero.mpr this.ne'
      simpa using inv_ne_zero hpk)

/-- The Hahn expansion of the two-variable rational base. -/
def mahlerEmbed (k : Type*) [Field k] : MahlerBase k →+* MahlerAmbient k :=
  (hahnMapRingHom (ratFuncToHahn : RatFunc k →+* HahnSeries ℚ k)).comp
    (algebraMap (RatFunc (RatFunc k)) (LaurentSeries (RatFunc k)))

/-- **The base substitution is the restriction of the ambient one.** -/
theorem mahlerEmbed_mahlerBaseDilation [CharZero k] (p : ℕ) (hp : 1 < p) (x : MahlerBase k) :
    mahlerEmbed k (mahlerBaseDilation p hp x) = mahlerDilation p hp (mahlerEmbed k x) := by
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  have hχ : ∀ n : ℤ,
      ratFuncToHahn ((laurentChar (algebraMap k (RatFunc k) (((p : k))⁻¹))
          (by simpa using inv_ne_zero hpk)) (Multiplicative.ofAdd n) : RatFunc k)
        = ((laurentChar (HahnSeries.C (((p : k))⁻¹) : HahnSeries ℚ k)
            (C_inv_natCast_ne_zero hp)) (Multiplicative.ofAdd n) : HahnSeries ℚ k) := by
    intro n
    rw [laurentChar_apply, laurentChar_apply, map_zpow₀, ratFuncToHahn_const]
  simp only [mahlerEmbed, RingHom.coe_comp, Function.comp_apply, mahlerBaseDilation,
    mahlerDilation, hahnTwistHom_apply]
  rw [algebraMap_ratFuncTwist, hahnTwistHom_apply,
    hahnMapRingHom_hahnTwist ratFuncToHahn (ratFuncPow p (by omega)) (mahlerHom p (by omega))
      _ _ (fun r => ratFuncToHahn_pow p hp r) hχ]

/-! ## The Euler operator through the Hahn embedding -/

theorem laurentToHahn_innerEuler [CharZero k] (f : LaurentSeries k) :
    laurentToHahn (innerEuler f) = hahnQEuler (laurentToHahn f) := by
  refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
  by_cases hγ : ∃ n : ℤ, ((n : ℚ)) = γ
  · obtain ⟨n, rfl⟩ := hγ
    rw [coeff_hahnQEuler, coeff_laurentToHahn, coeff_laurentToHahn, coeff_innerEuler]
    congr 1
    push_cast
    ring
  · push Not at hγ
    rw [coeff_hahnQEuler, coeff_laurentToHahn_of_not_int _ hγ,
      coeff_laurentToHahn_of_not_int _ hγ, mul_zero]

/-- **The Euler operator of `k(w)` is the Hahn grading.** -/
theorem ratFuncToHahn_eulerOp [CharZero k] (r : RatFunc k) :
    ratFuncToHahn (ratFuncEulerOp r) = hahnQEuler (ratFuncToHahn r) := by
  show laurentToHahn (algebraMap (RatFunc k) (LaurentSeries k) (ratFuncEulerOp r))
    = hahnQEuler (laurentToHahn (algebraMap (RatFunc k) (LaurentSeries k) r))
  rw [algebraMap_ratFuncEulerOp, laurentToHahn_innerEuler]

/-! ## The base derivation through the embedding -/

theorem coeff_mahlerEmbed_algebraMap (P : Polynomial (RatFunc k)) (n : ℤ) :
    (mahlerEmbed k (algebraMap (Polynomial (RatFunc k)) (MahlerBase k) P)).coeff n
      = if n < 0 then 0 else ratFuncToHahn (P.coeff n.natAbs) := by
  rw [mahlerEmbed, RingHom.coe_comp, Function.comp_apply, coeff_hahnMapRingHom,
    coeff_algebraMap_polynomial]
  by_cases h : n < 0
  · simp [h]
  · simp [h]

set_option maxHeartbeats 1000000 in
/-- **The base derivation is the restriction of the ambient one**, on polynomials in the twisting
coordinate. -/
theorem mahlerEmbed_twoCylDerivation_algebraMap [CharZero k] (P : Polynomial (RatFunc k)) :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    mahlerEmbed k (twoCylDerivation (algebraMap k (RatFunc k) 0)
        (algebraMap (Polynomial (RatFunc k)) (MahlerBase k) P))
      = mahlerAmbientDeriv
        (mahlerEmbed k (algebraMap (Polynomial (RatFunc k)) (MahlerBase k) P)) := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  rw [twoCylDerivation_algebraMap]
  simp only [map_zero, zero_mul, add_zero]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_mahlerEmbed_algebraMap, coeff_mahlerAmbientDeriv, coeff_mahlerEmbed_algebraMap]
  by_cases h : n < 0
  · simp [h]
  · rw [if_neg h, if_neg h, coeffDeriv_coeff, cylinderDifferential_deriv,
      cylDeriv_one_eq_ratFuncEulerOp, ratFuncToHahn_eulerOp]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The base derivation of `k(w)(h)` is the restriction of the derivation of the Mahler
ambient.** -/
theorem mahlerEmbed_twoCylDerivation [CharZero k] (x : MahlerBase k) :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    mahlerEmbed k (twoCylDerivation (algebraMap k (RatFunc k) 0) x)
      = mahlerAmbientDeriv (mahlerEmbed k x) := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  refine RatFunc.induction_on (P := fun x =>
    mahlerEmbed k (twoCylDerivation (algebraMap k (RatFunc k) 0) x)
      = mahlerAmbientDeriv (mahlerEmbed k x)) x ?_
  intro p q hq
  have hqne : algebraMap (Polynomial (RatFunc k)) (MahlerBase k) q ≠ 0 := by
    simpa using RatFunc.algebraMap_ne_zero hq
  have hFq : (algebraMap (Polynomial (RatFunc k)) (MahlerBase k) p /
      algebraMap (Polynomial (RatFunc k)) (MahlerBase k) q)
      * algebraMap (Polynomial (RatFunc k)) (MahlerBase k) q
      = algebraMap (Polynomial (RatFunc k)) (MahlerBase k) p := div_mul_cancel₀ _ hqne
  set F : MahlerBase k := algebraMap (Polynomial (RatFunc k)) (MahlerBase k) p /
    algebraMap (Polynomial (RatFunc k)) (MahlerBase k) q with hFdef
  have h1 := congrArg (mahlerEmbed k)
    (twoCylDerivation_leibniz (algebraMap k (RatFunc k) 0) F
      (algebraMap (Polynomial (RatFunc k)) (MahlerBase k) q))
  rw [hFq] at h1
  simp only [map_add, map_mul] at h1
  rw [mahlerEmbed_twoCylDerivation_algebraMap, mahlerEmbed_twoCylDerivation_algebraMap] at h1
  have h2 := mahlerAmbientDeriv_leibniz (mahlerEmbed k F)
    (mahlerEmbed k (algebraMap (Polynomial (RatFunc k)) (MahlerBase k) q))
  rw [← map_mul, hFq] at h2
  have hemb : mahlerEmbed k (algebraMap (Polynomial (RatFunc k)) (MahlerBase k) q) ≠ 0 := by
    intro h
    exact hqne ((injective_iff_map_eq_zero (mahlerEmbed k)).mp (mahlerEmbed k).injective _ h)
  refine mul_left_cancel₀ hemb ?_
  linear_combination h2 - h1

end

end GaloisForLFunctions.HTGeometry
