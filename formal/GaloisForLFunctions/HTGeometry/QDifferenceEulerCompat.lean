import GaloisForLFunctions.HTGeometry.QDifferenceRatFuncEmbedding
import GaloisForLFunctions.HTGeometry.DoubleSineOrbitResidueObstruction
import GaloisForLFunctions.HTGeometry.TwoCylinderDifferential

/-!
# The Euler operator under Laurent expansion

The Euler operator `z d/dz` of `k(z)` becomes the grading `zⁿ ↦ n zⁿ` of `k((z))`.  Both are
derivations over `k`, so the identity only has to be checked on polynomials and then transported
across a quotient by cancelling the image of the denominator.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Multiplicative Polynomial

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

theorem coeff_algebraMap_polynomial (p : Polynomial k) (n : ℤ) :
    (algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap (Polynomial k) (RatFunc k) p)).coeff n
      = if n < 0 then 0 else p.coeff n.natAbs := by
  have hcoe : algebraMap (RatFunc k) (LaurentSeries k)
      (algebraMap (Polynomial k) (RatFunc k) p)
      = HahnSeries.ofPowerSeries ℤ k ((p : Polynomial k) : PowerSeries k) :=
    (RatFunc.coe_coe _).symm
  rw [hcoe, coeff_ofPowerSeries_polynomial]

/-- The Euler operator of a polynomial is the Laurent grading. -/
theorem algebraMap_ratFuncEulerOp_polynomial (p : Polynomial k) :
    algebraMap (RatFunc k) (LaurentSeries k)
        (ratFuncEulerOp (algebraMap (Polynomial k) (RatFunc k) p))
      = innerEuler (algebraMap (RatFunc k) (LaurentSeries k)
          (algebraMap (Polynomial k) (RatFunc k) p)) := by
  have hop : ratFuncEulerOp (algebraMap (Polynomial k) (RatFunc k) p)
      = algebraMap (Polynomial k) (RatFunc k) (Polynomial.X * Polynomial.derivative p) := by
    rw [ratFuncEulerOp, ratFuncDerivative_algebraMap, map_mul]
  rw [hop]
  ext n
  rw [coeff_algebraMap_polynomial, coeff_innerEuler, coeff_algebraMap_polynomial]
  by_cases h : n < 0
  · simp [h]
  · rw [if_neg h, if_neg h]
    by_cases h0 : n = 0
    · subst h0
      simp [Polynomial.mul_coeff_zero]
    · have hnat : n.natAbs = (n.natAbs - 1) + 1 := by omega
      rw [hnat, Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      have hsucc : ((n.natAbs - 1 : ℕ) : k) + 1 = (n : k) := by
        have h2 : ((n.natAbs - 1 : ℕ) : ℤ) + 1 = n := by omega
        exact_mod_cast congrArg (fun t : ℤ => (t : k)) h2
      rw [hsucc]
      ring

/-- **The Euler operator of `k(z)` is the Laurent grading of `k((z))`.** -/
theorem algebraMap_ratFuncEulerOp (f : RatFunc k) :
    algebraMap (RatFunc k) (LaurentSeries k) (ratFuncEulerOp f)
      = innerEuler (algebraMap (RatFunc k) (LaurentSeries k) f) := by
  have hleib : ∀ x y : RatFunc k, ratFuncEulerOp (x * y)
      = ratFuncEulerOp x * y + x * ratFuncEulerOp y := by
    intro x y
    rw [ratFuncEulerOp, ratFuncEulerOp, ratFuncEulerOp, Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  refine RatFunc.induction_on (P := fun f =>
    algebraMap (RatFunc k) (LaurentSeries k) (ratFuncEulerOp f)
      = innerEuler (algebraMap (RatFunc k) (LaurentSeries k) f)) f ?_
  intro p s hs
  set ψ := algebraMap (RatFunc k) (LaurentSeries k) with hψ
  set F : RatFunc k := algebraMap (Polynomial k) (RatFunc k) p /
    algebraMap (Polynomial k) (RatFunc k) s with hF
  have hsne : algebraMap (Polynomial k) (RatFunc k) s ≠ 0 := by
    simpa using RatFunc.algebraMap_ne_zero hs
  have hFs : F * algebraMap (Polynomial k) (RatFunc k) s
      = algebraMap (Polynomial k) (RatFunc k) p := by
    rw [hF, div_mul_cancel₀ _ hsne]
  have h1 := congrArg ψ (hleib F (algebraMap (Polynomial k) (RatFunc k) s))
  rw [hFs, map_add, map_mul, map_mul, algebraMap_ratFuncEulerOp_polynomial,
    algebraMap_ratFuncEulerOp_polynomial] at h1
  have h2 : innerEuler (ψ F * ψ (algebraMap (Polynomial k) (RatFunc k) s))
      = innerEuler (ψ F) * ψ (algebraMap (Polynomial k) (RatFunc k) s)
        + ψ F * innerEuler (ψ (algebraMap (Polynomial k) (RatFunc k) s)) :=
    innerEuler_leibniz _ _
  rw [← map_mul, hFs] at h2
  have hψs : ψ (algebraMap (Polynomial k) (RatFunc k) s) ≠ 0 := by
    simpa [hψ] using hsne
  exact mul_right_cancel₀ hψs (add_right_cancel (h1.symm.trans h2))

/-! ## The two-variable comparison -/

/-- The coordinate `h` of the ambient field. -/
def hCoord (k : Type*) [Field k] : QLaurent k := HahnSeries.single 1 1

theorem qDerivation_C (s : k) (x : LaurentSeries k) :
    qDerivation s (HahnSeries.C x : QLaurent k) = HahnSeries.C (innerEuler x) := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_qDerivation]
  by_cases h : n = 0
  · subst h; simp [HahnSeries.C_apply]
  · simp [HahnSeries.C_apply, h]

theorem qDerivation_hCoord (s : k) :
    qDerivation s (hCoord k) = HahnSeries.C (HahnSeries.C s) * hCoord k := by
  have hrhs : (HahnSeries.C (HahnSeries.C s) : QLaurent k) * hCoord k
      = HahnSeries.single 1 (HahnSeries.C s) := by
    rw [hCoord, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hrhs]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_qDerivation, hCoord]
  by_cases h : n = 1
  · subst h
    rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same,
      show innerEuler (1 : LaurentSeries k) = 0 from hahnGrade_one _, zero_add,
      HahnSeries.C_apply, HahnSeries.C_apply, mul_one, one_smul]
  · rw [HahnSeries.coeff_single_of_ne h, HahnSeries.coeff_single_of_ne h]
    simp

theorem qEmbed_algebraMap_coeff (c : RatFunc k) :
    qEmbed k (algebraMap (RatFunc k) (QBase k) c)
      = HahnSeries.C (algebraMap (RatFunc k) (LaurentSeries k) c) := by
  rw [qEmbed, RingHom.coe_comp, Function.comp_apply, algebraMap_const_laurentSeries]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_hahnMapRingHom]
  by_cases h : n = 0
  · subst h; simp [HahnSeries.C_apply]
  · simp [HahnSeries.C_apply, h]

theorem qEmbed_X :
    qEmbed k (algebraMap (Polynomial (RatFunc k)) (QBase k) Polynomial.X) = hCoord k := by
  have hX : algebraMap (Polynomial (RatFunc k)) (QBase k) Polynomial.X = RatFunc.X :=
    RatFunc.algebraMap_X
  rw [hX, qEmbed, RingHom.coe_comp, Function.comp_apply]
  have hcoe : algebraMap (QBase k) (LaurentSeries (RatFunc k)) RatFunc.X
      = HahnSeries.single 1 1 := RatFunc.coe_X
  rw [hcoe, hCoord]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_hahnMapRingHom]
  by_cases h : n = 1
  · subst h; simp
  · simp [h]

theorem cylDeriv_one_eq_ratFuncEulerOp (y : RatFunc k) :
    cylDeriv (1 : k) y = ratFuncEulerOp y := by
  rw [cylDeriv, map_one, one_mul]

theorem coeff_qEmbed_algebraMap (P : Polynomial (RatFunc k)) (n : ℤ) :
    (qEmbed k (algebraMap (Polynomial (RatFunc k)) (QBase k) P)).coeff n
      = if n < 0 then 0
        else algebraMap (RatFunc k) (LaurentSeries k) (P.coeff n.natAbs) := by
  rw [qEmbed, RingHom.coe_comp, Function.comp_apply, coeff_hahnMapRingHom,
    coeff_algebraMap_polynomial]
  by_cases h : n < 0
  · simp [h]
  · simp [h]

theorem coeff_hCoord_mul (Q : QLaurent k) (m : ℤ) :
    (hCoord k * Q).coeff (m + 1) = Q.coeff m := by
  rw [hCoord, mul_comm, HahnSeries.coeff_mul_single_add, mul_one]

/-- **The two-variable derivation of the base is the restriction of the ambient one**, on
polynomials in the second coordinate. -/
theorem qEmbed_twoCylDerivation_algebraMap (s : k) (P : Polynomial (RatFunc k)) :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    qEmbed k (twoCylDerivation (algebraMap k (RatFunc k) s)
        (algebraMap (Polynomial (RatFunc k)) (QBase k) P))
      = qDerivation s (qEmbed k (algebraMap (Polynomial (RatFunc k)) (QBase k) P)) := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  rw [twoCylDerivation_algebraMap, map_add, map_mul, map_mul, qEmbed_algebraMap_coeff,
    qEmbed_X, algebraMap_const_laurentSeries]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [HahnSeries.coeff_add, coeff_qDerivation, mul_assoc, coeff_C_mul_hahn,
    coeff_qEmbed_algebraMap, coeff_qEmbed_algebraMap]
  have hshift : (hCoord k * qEmbed k (algebraMap (Polynomial (RatFunc k)) (QBase k)
        (Polynomial.derivative P))).coeff n
      = (qEmbed k (algebraMap (Polynomial (RatFunc k)) (QBase k)
          (Polynomial.derivative P))).coeff (n - 1) := by
    have := coeff_hCoord_mul (k := k)
      (qEmbed k (algebraMap (Polynomial (RatFunc k)) (QBase k) (Polynomial.derivative P))) (n - 1)
    rwa [sub_add_cancel] at this
  rw [hshift, coeff_qEmbed_algebraMap]
  by_cases hneg : n < 0
  · rw [if_pos hneg, if_pos (by omega : n - 1 < 0), if_pos hneg]
    simp
  · rw [if_neg hneg, if_neg hneg]
    by_cases hz : n = 0
    · subst hz
      rw [if_pos (by norm_num : (0 : ℤ) - 1 < 0)]
      simp only [Int.natAbs_zero, coeffDeriv_coeff, mul_zero, zero_smul, map_zero, add_zero]
      rw [cylinderDifferential_deriv, cylDeriv_one_eq_ratFuncEulerOp, algebraMap_ratFuncEulerOp]
      simp
    · have hnat : n.natAbs = (n - 1).natAbs + 1 := by omega
      have hcast : ((((n - 1).natAbs : ℕ) : k) + 1) = (n : k) := by
        have h2 : (((n - 1).natAbs : ℕ) : ℤ) + 1 = n := by omega
        exact_mod_cast congrArg (fun t : ℤ => (t : k)) h2
      have hCn : (HahnSeries.C ((n : k)) : LaurentSeries k)
          = (((n - 1).natAbs : ℕ) : LaurentSeries k) + 1 := by
        rw [← hcast, map_add, map_natCast, map_one]
      rw [if_neg (by omega : ¬ (n - 1 < 0)), coeffDeriv_coeff, cylinderDifferential_deriv,
        cylDeriv_one_eq_ratFuncEulerOp, algebraMap_ratFuncEulerOp, hnat,
        Polynomial.coeff_derivative, map_mul, map_add, map_natCast, map_one, ← hCn]
      have hCs : (HahnSeries.single (0 : ℤ) s : LaurentSeries k) = HahnSeries.C s :=
        (HahnSeries.C_apply s).symm
      have hCns : (HahnSeries.C ((n • s : k)) : LaurentSeries k)
          = HahnSeries.C ((n : k)) * HahnSeries.C s := by
        rw [zsmul_eq_mul, map_mul]
      rw [hCs, hCns]
      ring

set_option maxHeartbeats 1000000 in
/-- **The two-variable derivation of `k(z)(h)` is the restriction of the derivation of
`k((z))((h))`.** -/
theorem qEmbed_twoCylDerivation (s : k) (x : QBase k) :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    qEmbed k (twoCylDerivation (algebraMap k (RatFunc k) s) x)
      = qDerivation s (qEmbed k x) := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  refine RatFunc.induction_on (P := fun x =>
    qEmbed k (twoCylDerivation (algebraMap k (RatFunc k) s) x)
      = qDerivation s (qEmbed k x)) x ?_
  intro p q hq
  have hqne : algebraMap (Polynomial (RatFunc k)) (QBase k) q ≠ 0 := by
    simpa using RatFunc.algebraMap_ne_zero hq
  have hFq : (algebraMap (Polynomial (RatFunc k)) (QBase k) p /
      algebraMap (Polynomial (RatFunc k)) (QBase k) q)
      * algebraMap (Polynomial (RatFunc k)) (QBase k) q
      = algebraMap (Polynomial (RatFunc k)) (QBase k) p := div_mul_cancel₀ _ hqne
  set F : QBase k := algebraMap (Polynomial (RatFunc k)) (QBase k) p /
    algebraMap (Polynomial (RatFunc k)) (QBase k) q with hFdef
  have h1 := congrArg (qEmbed k)
    (twoCylDerivation_leibniz (algebraMap k (RatFunc k) s) F
      (algebraMap (Polynomial (RatFunc k)) (QBase k) q))
  rw [hFq] at h1
  simp only [map_add, map_mul] at h1
  rw [qEmbed_twoCylDerivation_algebraMap, qEmbed_twoCylDerivation_algebraMap] at h1
  have h2 := qDerivation_leibniz s (qEmbed k F)
    (qEmbed k (algebraMap (Polynomial (RatFunc k)) (QBase k) q))
  rw [← map_mul, hFq] at h2
  have hemb : qEmbed k (algebraMap (Polynomial (RatFunc k)) (QBase k) q) ≠ 0 := by
    intro h
    exact hqne ((injective_iff_map_eq_zero (qEmbed k)).mp (qEmbed k).injective _ h)
  refine mul_left_cancel₀ hemb ?_
  linear_combination h2 - h1

end

end GaloisForLFunctions.HTGeometry
