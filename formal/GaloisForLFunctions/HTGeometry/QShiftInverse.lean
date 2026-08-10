import GaloisForLFunctions.HTGeometry.QShiftField
import GaloisForLFunctions.HTGeometry.GammaShiftEigenrelation

/-!
# The inverse q-shift and the q-Gamma degree obstruction

The q-shift `f(z,u) ↦ f(z+1, q·u)` of `ℂ(z,u)` is an automorphism: the inverse shifts the
coefficients back by `z ↦ z−1` and scales the variable by `q⁻¹`.  Against it the multiplier
`M = (1−u)/(1−q)` of Jackson's functional equation carries a degree obstruction — no nonzero
element of `ℂ(z,u)` satisfies `σ(r) = Mᵉ·r` with `e ≥ 1`, because the shift preserves the
`u`-degree while `Mᵉ` raises it by `e`.
-/

namespace GaloisForLFunctions.HTGeometry

set_option maxSynthPendingDepth 4

open Polynomial nonZeroDivisors

noncomputable section

/-! ## The inverse shift -/

theorem ratShiftInv_const (t : ℂ) :
    GaloisForLFunctions.ratShiftInv (algebraMap ℂ (RatFunc ℂ) t)
      = algebraMap ℂ (RatFunc ℂ) t := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) t,
    Polynomial.algebraMap_eq, GaloisForLFunctions.ratShiftInv_algebraMap, Polynomial.C_comp]

/-- The polynomial-level inverse q-shift: coefficients shift by `z ↦ z−1`, the variable scales
by `q⁻¹`. -/
def qShiftPolyMapInv (q : RealEulerNome) : Polynomial (RatFunc ℂ) →+* Polynomial (RatFunc ℂ) :=
  (Polynomial.eval₂RingHom Polynomial.C (Polynomial.C (qConst q)⁻¹ * Polynomial.X)).comp
    (Polynomial.mapRingHom GaloisForLFunctions.ratShiftInv)

theorem qShiftPolyMapInv_apply (q : RealEulerNome) (p : Polynomial (RatFunc ℂ)) :
    qShiftPolyMapInv q p
      = (p.map GaloisForLFunctions.ratShiftInv).comp
          (Polynomial.C (qConst q)⁻¹ * Polynomial.X) := rfl

theorem qShiftPolyMapInv_ne_zero (q : RealEulerNome) {p : Polynomial (RatFunc ℂ)} (hp : p ≠ 0) :
    qShiftPolyMapInv q p ≠ 0 := by
  have hinv : (qConst q)⁻¹ ≠ 0 := inv_ne_zero (qConst_ne_zero q)
  rw [qShiftPolyMapInv_apply]
  have hmap : p.map GaloisForLFunctions.ratShiftInv ≠ 0 := by
    intro h0
    exact hp (Polynomial.map_injective _
      (GaloisForLFunctions.ratShiftInv).injective (by rw [h0, Polynomial.map_zero]))
  intro h0
  have hlead : ((p.map GaloisForLFunctions.ratShiftInv).comp
      (Polynomial.C (qConst q)⁻¹ * Polynomial.X)).leadingCoeff = 0 := by
    rw [h0, Polynomial.leadingCoeff_zero]
  rw [Polynomial.leadingCoeff_comp (by
    rw [Polynomial.natDegree_C_mul_X _ hinv]
    exact one_ne_zero)] at hlead
  have hlc : (Polynomial.C (qConst q)⁻¹ * Polynomial.X : Polynomial (RatFunc ℂ)).leadingCoeff
      = (qConst q)⁻¹ := by
    rw [Polynomial.leadingCoeff_C_mul_X]
  rw [hlc] at hlead
  rcases mul_eq_zero.mp hlead with h | h
  · exact hmap (Polynomial.leadingCoeff_eq_zero.mp h)
  · exact hinv (pow_eq_zero_iff'.mp h).1

/-- The polynomial-level inverse q-shift, landing in the field. -/
def qShiftCompHomInv (q : RealEulerNome) : Polynomial (RatFunc ℂ) →+* RatFunc (RatFunc ℂ) :=
  (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))).comp (qShiftPolyMapInv q)

theorem qShiftCompHomInv_apply (q : RealEulerNome) (p : Polynomial (RatFunc ℂ)) :
    qShiftCompHomInv q p
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMapInv q p) := rfl

theorem qShiftCompHomInv_mem_nonZeroDivisors (q : RealEulerNome) :
    (Polynomial (RatFunc ℂ))⁰ ≤ (RatFunc (RatFunc ℂ))⁰.comap (qShiftCompHomInv q) := by
  intro p hp
  rw [Submonoid.mem_comap]
  refine mem_nonZeroDivisors_of_ne_zero ?_
  have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
  rw [qShiftCompHomInv_apply]
  intro h0
  exact qShiftPolyMapInv_ne_zero q hp0
    (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))

/-- **The inverse q-shift** `f(z, u) ↦ f(z−1, q⁻¹·u)`. -/
def qShiftInv (q : RealEulerNome) : RatFunc (RatFunc ℂ) →+* RatFunc (RatFunc ℂ) :=
  RatFunc.liftRingHom (qShiftCompHomInv q) (qShiftCompHomInv_mem_nonZeroDivisors q)

theorem qShiftInv_algebraMap (q : RealEulerNome) (p : Polynomial (RatFunc ℂ)) :
    qShiftInv q (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p)
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMapInv q p) := by
  simp [qShiftInv, qShiftCompHomInv_apply]

theorem qShiftPolyMapInv_qShiftPolyMap (q : RealEulerNome) (p : Polynomial (RatFunc ℂ)) :
    qShiftPolyMapInv q (qShiftPolyMap q p) = p := by
  have hhom : (qShiftPolyMapInv q).comp (qShiftPolyMap q) = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, qShiftPolyMap_apply, Polynomial.map_C, Polynomial.C_comp,
        qShiftPolyMapInv_apply, Polynomial.map_C, Polynomial.C_comp, RingHom.id_apply,
        GaloisForLFunctions.ratShiftInv_ratShift]
    · rw [RingHom.comp_apply, qShiftPolyMap_apply, Polynomial.map_X, Polynomial.X_comp,
        qShiftPolyMapInv_apply, RingHom.id_apply]
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.mul_comp,
        Polynomial.C_comp, Polynomial.X_comp]
      have hconst : GaloisForLFunctions.ratShiftInv (qConst q) = qConst q := by
        rw [qConst, ratShiftInv_const]
      rw [hconst, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ (qConst_ne_zero q),
        map_one, one_mul]
  have := RingHom.congr_fun hhom p
  rwa [RingHom.comp_apply, RingHom.id_apply] at this

theorem qShiftPolyMap_qShiftPolyMapInv (q : RealEulerNome) (p : Polynomial (RatFunc ℂ)) :
    qShiftPolyMap q (qShiftPolyMapInv q p) = p := by
  have hhom : (qShiftPolyMap q).comp (qShiftPolyMapInv q) = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, qShiftPolyMapInv_apply, Polynomial.map_C, Polynomial.C_comp,
        qShiftPolyMap_apply, Polynomial.map_C, Polynomial.C_comp, RingHom.id_apply,
        GaloisForLFunctions.ratShift_ratShiftInv]
    · rw [RingHom.comp_apply, qShiftPolyMapInv_apply, Polynomial.map_X, Polynomial.X_comp,
        qShiftPolyMap_apply, RingHom.id_apply]
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.mul_comp,
        Polynomial.C_comp, Polynomial.X_comp]
      have hconst : GaloisForLFunctions.ratShift (qConst q)⁻¹ = (qConst q)⁻¹ := by
        rw [qConst, ← map_inv₀, GaloisForLFunctions.ratShift_const]
      rw [hconst, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ (qConst_ne_zero q),
        map_one, one_mul]
  have := RingHom.congr_fun hhom p
  rwa [RingHom.comp_apply, RingHom.id_apply] at this

theorem qShiftInv_qShift (q : RealEulerNome) (f : RatFunc (RatFunc ℂ)) :
    qShiftInv q (qShift q f) = f := by
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [map_div₀, map_div₀, qShift_algebraMap, qShift_algebraMap, qShiftInv_algebraMap,
    qShiftInv_algebraMap, qShiftPolyMapInv_qShiftPolyMap, qShiftPolyMapInv_qShiftPolyMap,
    RatFunc.num_div_denom]

theorem qShift_qShiftInv (q : RealEulerNome) (f : RatFunc (RatFunc ℂ)) :
    qShift q (qShiftInv q f) = f := by
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [map_div₀, map_div₀, qShiftInv_algebraMap, qShiftInv_algebraMap, qShift_algebraMap,
    qShift_algebraMap, qShiftPolyMap_qShiftPolyMapInv, qShiftPolyMap_qShiftPolyMapInv,
    RatFunc.num_div_denom]

/-! ## The multiplier of Jackson's functional equation -/

/-- The nonzero constant `1 − q`, as a scalar of the two-variable field. -/
def qOneSub (q : RealEulerNome) : RatFunc ℂ :=
  algebraMap ℂ (RatFunc ℂ) (((1 - q.val : ℝ) : ℂ))

theorem qOneSub_ne_zero (q : RealEulerNome) : qOneSub q ≠ 0 := by
  intro h0
  exact q.one_sub_complex_ne_zero
    ((algebraMap ℂ (RatFunc ℂ)).injective (h0.trans (map_zero _).symm))

/-- The polynomial numerator `(1 − u)/(1 − q)` of Jackson's multiplier. -/
def qMultPoly (q : RealEulerNome) : Polynomial (RatFunc ℂ) :=
  Polynomial.C (qOneSub q)⁻¹ * (1 - Polynomial.X)

/-- **Jackson's multiplier** `(1 − u)/(1 − q)` inside `ℂ(z,u)`. -/
def qMult (q : RealEulerNome) : RatFunc (RatFunc ℂ) :=
  algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qMultPoly q)

theorem one_sub_X_ne_zero : (1 - Polynomial.X : Polynomial (RatFunc ℂ)) ≠ 0 := by
  intro h0
  have hco := congrArg (fun p => Polynomial.coeff p 1) h0
  simp [Polynomial.coeff_one] at hco

theorem qMultPoly_ne_zero (q : RealEulerNome) : qMultPoly q ≠ 0 :=
  mul_ne_zero (fun h0 => (inv_ne_zero (qOneSub_ne_zero q))
    (Polynomial.C_eq_zero.mp h0)) one_sub_X_ne_zero

theorem natDegree_one_sub_X :
    (1 - Polynomial.X : Polynomial (RatFunc ℂ)).natDegree = 1 := by
  have hneg : (1 - Polynomial.X : Polynomial (RatFunc ℂ))
      = -(Polynomial.X - Polynomial.C 1) := by
    rw [map_one]
    ring
  rw [hneg, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]

theorem natDegree_qMultPoly (q : RealEulerNome) : (qMultPoly q).natDegree = 1 := by
  rw [qMultPoly, Polynomial.natDegree_C_mul (inv_ne_zero (qOneSub_ne_zero q)),
    natDegree_one_sub_X]

theorem qMult_ne_zero (q : RealEulerNome) : qMult q ≠ 0 := by
  rw [qMult]
  intro h0
  exact qMultPoly_ne_zero q
    (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))

/-- **The q-Gamma degree obstruction**: no nonzero element of `ℂ(z,u)` satisfies
`r(z+1, q·u) = ((1−u)/(1−q))ᵉ·r(z,u)` with `e ≥ 1` — the shift preserves `u`-degrees, and the
multiplier raises them. -/
theorem qShift_eq_qMult_pow_mul_eq_zero (q : RealEulerNome) {r : RatFunc (RatFunc ℂ)} {e : ℕ}
    (he : 1 ≤ e) (h : qShift q r = qMult q ^ e * r) : r = 0 := by
  by_contra hr
  set P := r.num with hP_def
  set Q := r.denom with hQ_def
  have hP : P ≠ 0 := RatFunc.num_ne_zero hr
  have hQ : Q ≠ 0 := r.denom_ne_zero
  have hQK : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) Q ≠ 0 :=
    fun h0 => hQ (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))
  have hσQK : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMap q Q) ≠ 0 :=
    fun h0 => qShiftPolyMap_ne_zero q hQ
      (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))
  have hrepr : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) P
      / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) Q = r :=
    RatFunc.num_div_denom r
  have hcross : qShiftPolyMap q P * Q = qMultPoly q ^ e * P * qShiftPolyMap q Q := by
    apply RatFunc.algebraMap_injective (RatFunc ℂ)
    have hshift : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMap q P)
        / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMap q Q)
        = qMult q ^ e * (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) P
            / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) Q) := by
      rw [← qShift_algebraMap, ← qShift_algebraMap, ← map_div₀, hrepr, h]
    rw [div_eq_iff hσQK] at hshift
    rw [map_mul, map_mul, map_mul, map_pow, hshift, qMult]
    field_simp
  have hdeg := congrArg Polynomial.natDegree hcross
  rw [Polynomial.natDegree_mul (qShiftPolyMap_ne_zero q hP) hQ,
    Polynomial.natDegree_mul (mul_ne_zero (pow_ne_zero e (qMultPoly_ne_zero q)) hP)
      (qShiftPolyMap_ne_zero q hQ),
    Polynomial.natDegree_mul (pow_ne_zero e (qMultPoly_ne_zero q)) hP,
    Polynomial.natDegree_pow, natDegree_qMultPoly,
    qShiftPolyMap_natDegree, qShiftPolyMap_natDegree] at hdeg
  omega

end

end GaloisForLFunctions.HTGeometry
