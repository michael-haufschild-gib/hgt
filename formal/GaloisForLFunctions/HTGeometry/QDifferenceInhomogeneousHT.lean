import GaloisForLFunctions.HTGeometry.QDifferenceOstrowski
import GaloisForLFunctions.HTGeometry.SimplePoleEulerCombination
import GaloisForLFunctions.HTGeometry.DoubleSineCylinderHypertranscendence

/-!
# Hypertranscendence of a first-order inhomogeneous `q`-difference equation

A Laurent series `R` with `R - a·R(bz) = r`, where `r` is a rational function with a single pole
on the multiplicative orbit of that pole, is differentially transcendental over `k(z)`.

The homogeneous equation `σ y = a⁻¹ y` has no rational solution, so the equation is untwisted in
the two-variable Laurent field `k((z))((h))`, where `h` is a formal solution: `u = R h⁻¹` is an
additive primitive with increment `-r h⁻¹` in the base `k(z)(h)`.  The derivation is chosen with
`δ h = 0`, so the differential jets of the increment are the Euler jets of `r` divided by `h`, and
a telescoping relation for them descends — by comparing the `h⁰` Laurent coefficients — to a
twisted dilation coboundary equation for `r` over `k(z)`, which the orbit obstruction forbids.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Multiplicative

open scoped RatFunc

open scoped Differential

noncomputable section

variable {k : Type*} [Field k]

/-- The dilation of a series constant in `h`. -/
theorem qDilation_C (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (v : LaurentSeries k) :
    qDilation a b ha hb (HahnSeries.C v) = HahnSeries.C (innerDilation b hb v) := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_qDilation]
  by_cases h : n = 0
  · subst h; simp [HahnSeries.C_apply]
  · simp [HahnSeries.C_apply, h]

/-- The inverse of the coordinate `h`. -/
def hCoordInv (k : Type*) [Field k] : QLaurent k := HahnSeries.single (-1) 1

theorem hCoord_mul_hCoordInv : hCoord k * hCoordInv k = 1 := by
  rw [hCoord, hCoordInv, HahnSeries.single_mul_single, mul_one]
  norm_num

theorem qDilation_hCoordInv (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) :
    qDilation a b ha hb (hCoordInv k)
      = HahnSeries.C (HahnSeries.C a) * hCoordInv k := by
  have hrhs : (HahnSeries.C (HahnSeries.C a) : QLaurent k) * hCoordInv k
      = HahnSeries.single (-1) (HahnSeries.C a) := by
    rw [hCoordInv, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hrhs]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_qDilation, hCoordInv]
  by_cases h : n = -1
  · subst h
    rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same, map_one, mul_one,
      ← map_zpow₀, inv_zpow, ← zpow_neg, neg_neg, zpow_one]
  · rw [HahnSeries.coeff_single_of_ne h, HahnSeries.coeff_single_of_ne h, map_zero, mul_zero]

theorem qEmbed_hCoordInv : qEmbed k (RatFunc.X⁻¹) = hCoordInv k := by
  have hX : qEmbed k RatFunc.X = hCoord k := by
    have := qEmbed_X (k := k)
    rwa [RatFunc.algebraMap_X] at this
  have hne : (RatFunc.X : QBase k) ≠ 0 := RatFunc.X_ne_zero
  have hmul : qEmbed k (RatFunc.X⁻¹) * hCoord k = 1 := by
    rw [← hX, ← map_mul, inv_mul_cancel₀ hne, map_one]
  have hmul' : hCoordInv k * hCoord k = 1 := by
    rw [mul_comm]; exact hCoord_mul_hCoordInv
  have hcancel : qEmbed k (RatFunc.X⁻¹) * hCoord k = hCoordInv k * hCoord k := by
    rw [hmul, hmul']
  refine mul_right_cancel₀ ?_ hcancel
  intro h
  rw [h, mul_zero] at hmul'
  exact zero_ne_one hmul'

/-! ## The jets of the increment -/

theorem algebraMap_ratFunc_qBase (w : RatFunc k) :
    algebraMap (RatFunc k) (QBase k) w
      = algebraMap (Polynomial (RatFunc k)) (QBase k) (Polynomial.C w) := by
  rw [IsScalarTower.algebraMap_apply (RatFunc k) (Polynomial (RatFunc k)) (QBase k),
    Polynomial.algebraMap_eq]

theorem coeffDeriv_C_ratFunc (w : RatFunc k) :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    coeffDeriv (Polynomial.C w) = Polynomial.C (ratFuncEulerOp w) := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  refine Polynomial.ext fun n => ?_
  rw [coeffDeriv_coeff, Polynomial.coeff_C, Polynomial.coeff_C]
  by_cases h : n = 0
  · subst h
    simp [cylinderDifferential_deriv, cylDeriv]
  · simp [h, cylinderDifferential_deriv, cylDeriv, ratFuncEulerOp]

theorem coeffDeriv_X_ratFunc :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    coeffDeriv (Polynomial.X : Polynomial (RatFunc k)) = 0 := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  refine Polynomial.ext fun n => ?_
  rw [coeffDeriv_coeff, Polynomial.coeff_zero, Polynomial.coeff_X]
  by_cases h : 1 = n
  · rw [if_pos h, cylinderDifferential_deriv, cylDeriv, ratFuncEulerOp, map_one,
      Derivation.map_one_eq_zero, mul_zero, mul_zero]
  · rw [if_neg h, cylinderDifferential_deriv, cylDeriv, ratFuncEulerOp, map_zero, mul_zero,
      mul_zero]

theorem twoCylDerivation_zero_algebraMap (w : RatFunc k) :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    twoCylDerivation (algebraMap k (RatFunc k) 0) (algebraMap (RatFunc k) (QBase k) w)
      = algebraMap (RatFunc k) (QBase k) (ratFuncEulerOp w) := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  rw [algebraMap_ratFunc_qBase, twoCylDerivation_algebraMap, coeffDeriv_C_ratFunc]
  simp only [map_zero, zero_mul, add_zero]
  rw [algebraMap_ratFunc_qBase]

theorem twoCylDerivation_zero_X :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    twoCylDerivation (algebraMap k (RatFunc k) 0) (RatFunc.X : QBase k) = 0 := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  have hX : (RatFunc.X : QBase k)
      = algebraMap (Polynomial (RatFunc k)) (QBase k) Polynomial.X := RatFunc.algebraMap_X.symm
  rw [hX, twoCylDerivation_algebraMap, coeffDeriv_X_ratFunc]
  simp only [map_zero, zero_mul, add_zero]

theorem twoCylDerivation_zero_X_inv :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    twoCylDerivation (algebraMap k (RatFunc k) 0) ((RatFunc.X : QBase k)⁻¹) = 0 := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  have hne : (RatFunc.X : QBase k) ≠ 0 := RatFunc.X_ne_zero
  have hmul : (RatFunc.X : QBase k) * (RatFunc.X : QBase k)⁻¹ = 1 := mul_inv_cancel₀ hne
  have hone : twoCylDerivation (algebraMap k (RatFunc k) 0) (1 : QBase k) = 0 := by
    have hl := twoCylDerivation_leibniz (algebraMap k (RatFunc k) 0) (1 : QBase k) 1
    rw [mul_one] at hl
    simp only [one_mul] at hl
    have h0 : (0 : QBase k) + twoCylDerivation (algebraMap k (RatFunc k) 0) (1 : QBase k)
        = twoCylDerivation (algebraMap k (RatFunc k) 0) (1 : QBase k)
          + twoCylDerivation (algebraMap k (RatFunc k) 0) (1 : QBase k) := by
      rw [zero_add]; exact hl
    exact (add_right_cancel h0).symm
  have h := congrArg (twoCylDerivation (algebraMap k (RatFunc k) 0)) hmul
  rw [twoCylDerivation_leibniz, hone, twoCylDerivation_zero_X, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hne

/-- The differential jets of `w/h` for the derivation with `δ h = 0` are the Euler jets of `w`
divided by `h`. -/
theorem differentialJet_algebraMap_mul_XInv (w : RatFunc k) (n : ℕ) :
    letI := qBaseDifferential (0 : k)
    differentialJet n (algebraMap (RatFunc k) (QBase k) w * (RatFunc.X : QBase k)⁻¹)
      = algebraMap (RatFunc k) (QBase k) (ratFuncEulerOp^[n] w) * (RatFunc.X : QBase k)⁻¹ := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  letI := qBaseDifferential (0 : k)
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      have hstep : (algebraMap (RatFunc k) (QBase k) w * (RatFunc.X : QBase k)⁻¹)′
          = algebraMap (RatFunc k) (QBase k) (ratFuncEulerOp w) * (RatFunc.X : QBase k)⁻¹ := by
        rw [twoCylinderDifferential_deriv, twoCylDerivation_leibniz, twoCylDerivation_zero_X_inv,
          twoCylDerivation_zero_algebraMap, mul_zero, zero_add, mul_comm]
      rw [show differentialJet (n + 1)
            (algebraMap (RatFunc k) (QBase k) w * (RatFunc.X : QBase k)⁻¹)
          = differentialJet n ((algebraMap (RatFunc k) (QBase k) w * (RatFunc.X : QBase k)⁻¹)′)
          from Function.iterate_succ_apply _ _ _,
        hstep, ih, Function.iterate_succ_apply]

/-- A nonzero constant-coefficient jet character of `w/h` is a nonzero Euler combination of `w`
divided by `h`. -/
theorem exists_eulerCombination_of_jetCombination (c : (Unit × ℕ) →₀ k) (hc : c ≠ 0)
    (w : RatFunc k) :
    letI := qBaseDifferential (0 : k)
    ∃ (α : ℕ → k) (N : ℕ), α N ≠ 0 ∧
      Finsupp.linearCombination (QBase k)
        (fun p : Unit × ℕ => differentialJet p.2
          (algebraMap (RatFunc k) (QBase k) w * (RatFunc.X : QBase k)⁻¹))
        (Finsupp.mapRange (algebraMap k (QBase k)) (map_zero _) c)
        = algebraMap (RatFunc k) (QBase k) (eulerCombination α N w)
            * (RatFunc.X : QBase k)⁻¹ := by
  classical
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  letI := qBaseDifferential (0 : k)
  have hsne : (c.support.image Prod.snd).Nonempty := by
    obtain ⟨p, hp⟩ := Finsupp.support_nonempty_iff.mpr hc
    exact ⟨p.2, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  refine ⟨fun i => c ((), i), (c.support.image Prod.snd).max' hsne, ?_, ?_⟩
  · show c ((), (c.support.image Prod.snd).max' hsne) ≠ 0
    obtain ⟨p, hp, hp2⟩ := Finset.mem_image.mp (Finset.max'_mem _ hsne)
    have hpeq : ((), (c.support.image Prod.snd).max' hsne) = p :=
      Prod.ext (Subsingleton.elim _ _) hp2.symm
    rw [hpeq]
    exact Finsupp.mem_support_iff.mp hp
  · rw [Finsupp.linearCombination_apply, Finsupp.sum,
      Finsupp.support_mapRange_of_injective (map_zero _) c (algebraMap k (QBase k)).injective]
    simp only [Finsupp.mapRange_apply, smul_eq_mul, differentialJet_algebraMap_mul_XInv,
      ← mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    have hmap : ∀ i : ℕ, algebraMap (RatFunc k) (QBase k)
        (toRF (Polynomial.C (c ((), i))) * ratFuncEulerOp^[i] w)
        = algebraMap k (QBase k) (c ((), i))
          * algebraMap (RatFunc k) (QBase k) (ratFuncEulerOp^[i] w) := by
      intro i
      have hc0 : algebraMap (RatFunc k) (QBase k) (toRF (Polynomial.C (c ((), i))))
          = algebraMap k (QBase k) (c ((), i)) := by
        rw [toRF, ← Polynomial.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k),
          ← IsScalarTower.algebraMap_apply k (RatFunc k) (QBase k)]
      rw [map_mul, hc0]
    rw [eulerCombination, map_sum]
    simp only [hmap]
    rw [sum_unitProd c.support (fun p : Unit × ℕ => algebraMap k (QBase k) (c p)
      * algebraMap (RatFunc k) (QBase k) (ratFuncEulerOp^[p.2] w))]
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' _ n hn))
    · intro n _ hn
      have : c ((), n) = 0 := by
        by_contra hne
        exact hn (Finset.mem_image.mpr ⟨((), n), Finsupp.mem_support_iff.mpr hne, rfl⟩)
      simp [this]

/-! ## The absence of a telescoper -/

theorem ratFuncTwist_X (φ : RatFunc k →+* RatFunc k) (hφ : Function.Injective φ)
    (q : RatFunc k) (hq : q ≠ 0) :
    ratFuncTwist φ hφ q hq (RatFunc.X : QBase k)
      = algebraMap (RatFunc k) (QBase k) q * RatFunc.X := by
  have hX : (RatFunc.X : QBase k)
      = algebraMap (Polynomial (RatFunc k)) (QBase k) Polynomial.X := RatFunc.algebraMap_X.symm
  have hdiv : (RatFunc.X : QBase k)
      = algebraMap (Polynomial (RatFunc k)) (QBase k) Polynomial.X /
        algebraMap (Polynomial (RatFunc k)) (QBase k) 1 := by
    rw [map_one, div_one, hX]
  rw [hdiv, ratFuncTwist_div]
  simp only [map_one, div_one, polyTwist_apply, Polynomial.map_X,
    polyScale_X, map_mul]
  congr 1

/-- **No constant-coefficient jet character of the increment `-r/h` is a dilation coboundary in
the base**, when `r` is a cotangent model plus a constant. -/
theorem no_jetTelescoper_cotModel [CharZero k] (a b : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → b ^ n ≠ 1) (cc γ₀ : k) (hcc : cc ≠ 0) :
    letI := qBaseDifferential (0 : k)
    ∀ c : (Unit × ℕ) →₀ k, c ≠ 0 → ∀ y : QBase k,
      qBaseDilation a b ha hb y - y ≠
        Finsupp.linearCombination (QBase k)
          (fun p : Unit × ℕ => differentialJet p.2
            (algebraMap (RatFunc k) (QBase k)
              (-(cotModel cc + algebraMap k (RatFunc k) γ₀)) * (RatFunc.X : QBase k)⁻¹))
          (Finsupp.mapRange (algebraMap k (QBase k)) (map_zero _) c) := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  letI := qBaseDifferential (0 : k)
  intro c hc y heq
  obtain ⟨α, N, hαN, hcomb⟩ := exists_eulerCombination_of_jetCombination c hc
    (-(cotModel cc + algebraMap k (RatFunc k) γ₀))
  rw [hcomb] at heq
  have hXne : (RatFunc.X : QBase k) ≠ 0 := RatFunc.X_ne_zero
  have hXX : (RatFunc.X : QBase k)⁻¹ * RatFunc.X = 1 := inv_mul_cancel₀ hXne
  have hmul : qBaseDilation a b ha hb y * RatFunc.X - y * RatFunc.X
      = algebraMap (RatFunc k) (QBase k)
        (eulerCombination α N (-(cotModel cc + algebraMap k (RatFunc k) γ₀))) := by
    have h := congrArg (fun t : QBase k => t * (RatFunc.X : QBase k)) heq
    simpa [sub_mul, mul_assoc, hXX] using h
  have hainv : algebraMap (RatFunc k) (QBase k) (algebraMap k (RatFunc k) a)
      * algebraMap (RatFunc k) (QBase k) (algebraMap k (RatFunc k) a⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
  have key : algebraMap (RatFunc k) (QBase k) (algebraMap k (RatFunc k) a)
      * qBaseDilation a b ha hb (y * RatFunc.X) - y * RatFunc.X
      = algebraMap (RatFunc k) (QBase k)
        (eulerCombination α N (-(cotModel cc + algebraMap k (RatFunc k) γ₀))) := by
    rw [← hmul, map_mul, qBaseDilation, ratFuncTwist_X]
    have : algebraMap (RatFunc k) (QBase k) (algebraMap k (RatFunc k) a)
        * (qBaseDilation a b ha hb y
          * (algebraMap (RatFunc k) (QBase k) (algebraMap k (RatFunc k) a⁻¹) * RatFunc.X))
        = (algebraMap (RatFunc k) (QBase k) (algebraMap k (RatFunc k) a)
          * algebraMap (RatFunc k) (QBase k) (algebraMap k (RatFunc k) a⁻¹))
          * (qBaseDilation a b ha hb y * RatFunc.X) := by ring
    rw [show (ratFuncTwist ((ratFuncScale b hb : RatFunc k →ₐ[k] RatFunc k) :
        RatFunc k →+* RatFunc k) (ratFuncScale_injective b hb)
        (algebraMap k (RatFunc k) a⁻¹) (by simpa using inv_ne_zero ha)) y
        = qBaseDilation a b ha hb y from rfl, this, hainv, one_mul]
  obtain ⟨m₀, hm₀⟩ := exists_twistedCoboundary_of_ratFuncTwist
    ((ratFuncScale b hb : RatFunc k →ₐ[k] RatFunc k) : RatFunc k →+* RatFunc k)
    (ratFuncScale_injective b hb) (algebraMap k (RatFunc k) a⁻¹) (by simpa using inv_ne_zero ha)
    (algebraMap k (RatFunc k) a)
    (eulerCombination α N (-(cotModel cc + algebraMap k (RatFunc k) γ₀))) (y * RatFunc.X) key
  refine not_twistedDilationTelescoped_eulerCombination_cotModel b a cc (α 0 * γ₀) hb ha hcc
    hqtor α N hαN ⟨-m₀, ?_⟩
  rw [eulerCombination_neg, eulerCombination_add, eulerCombination_algebraMap] at hm₀
  have hcoe : ((ratFuncScale b hb : RatFunc k →ₐ[k] RatFunc k) : RatFunc k →+* RatFunc k) m₀
      = ratFuncScale b hb m₀ := rfl
  rw [hcoe] at hm₀
  rw [map_neg]
  linear_combination hm₀

/-! ## The shift identity and the transfer -/

theorem algebraMap_k_laurentSeries (c : k) :
    algebraMap k (LaurentSeries k) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]
  simp

/-- The differential structure of `k((z))` with `δ z = z`. -/
@[reducible] def innerDifferential : Differential (LaurentSeries k) :=
  hahnDifferential (Int.castAddHom k)

theorem innerDifferential_deriv (v : LaurentSeries k) :
    letI := innerDifferential (k := k)
    v′ = innerEuler v := rfl

/-- **The twisted primitive of a first-order inhomogeneous `q`-difference equation is an additive
primitive**: dividing by the formal solution `h` of the homogeneous equation turns the equation
into a shift by the base element `-r/h`. -/
theorem qDilation_C_mul_hCoordInv (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (R : LaurentSeries k)
    (r : RatFunc k)
    (hR : R - algebraMap k (LaurentSeries k) a * innerDilation b hb R
      = algebraMap (RatFunc k) (LaurentSeries k) r) :
    qDilation a b ha hb (HahnSeries.C R * hCoordInv k)
      = HahnSeries.C R * hCoordInv k
        + qEmbed k (algebraMap (RatFunc k) (QBase k) (-r) * (RatFunc.X : QBase k)⁻¹) := by
  have hstep : algebraMap k (LaurentSeries k) a * innerDilation b hb R
      = R - algebraMap (RatFunc k) (LaurentSeries k) r := by
    rw [← hR]; ring
  rw [map_mul, qDilation_C, qDilation_hCoordInv, map_mul, qEmbed_algebraMap_coeff,
    qEmbed_hCoordInv, map_neg]
  have hcm : (HahnSeries.C (innerDilation b hb R) : QLaurent k)
      * (HahnSeries.C (HahnSeries.C a) * hCoordInv k)
      = HahnSeries.C (algebraMap k (LaurentSeries k) a * innerDilation b hb R)
        * hCoordInv k := by
    rw [algebraMap_k_laurentSeries, map_mul]
    ring
  rw [hcm, hstep, map_sub]
  simp only [map_neg]
  ring

theorem differentialJet_C (s : k) (v : LaurentSeries k) (n : ℕ) :
    letI := innerDifferential (k := k)
    letI := qDifferential s
    differentialJet n (HahnSeries.C v : QLaurent k) = HahnSeries.C (differentialJet n v) := by
  letI := innerDifferential (k := k)
  letI := qDifferential s
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, ih, differentialJet_succ]
      exact qDerivation_C s _

set_option maxHeartbeats 1000000 in
/-- **Hypertranscendence of a first-order inhomogeneous `q`-difference equation.**  If the
multipliers are multiplicatively independent and the inhomogeneity is a cotangent model plus a
constant, every Laurent solution of `R - a R(bz) = r` is differentially transcendental over
`k(z)` for the Euler derivation. -/
theorem hypertranscendentalOver_of_qDifference_cotModel [CharZero k]
    (a b : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hind : ∀ m n : ℤ, b ^ m = a ^ n → m = 0 ∧ n = 0)
    (cc γ₀ : k) (hcc : cc ≠ 0) (R : LaurentSeries k)
    (hR : R - algebraMap k (LaurentSeries k) a * innerDilation b hb R
      = algebraMap (RatFunc k) (LaurentSeries k)
        (cotModel cc + algebraMap k (RatFunc k) γ₀)) :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    letI := innerDifferential (k := k)
    HypertranscendentalOver (RatFunc k) R := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  letI := innerDifferential (k := k)
  letI := qBaseDifferential (0 : k)
  letI := qDifferential (0 : k)
  letI := qEmbedAlgebra (k := k)
  letI : Algebra (RatFunc k) (QLaurent k) :=
    ((HahnSeries.C : LaurentSeries k →+* QLaurent k).comp
      (algebraMap (RatFunc k) (LaurentSeries k))).toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq (R := RatFunc k) (S := QBase k) (A := QLaurent k)
    fun w => (qEmbed_algebraMap_coeff w).symm
  haveI : DifferentialAlgebra (QBase k) (QLaurent k) :=
    ⟨fun x => (qEmbed_twoCylDerivation 0 x).symm⟩
  haveI : CharZero (QLaurent k) :=
    charZero_of_injective_algebraMap (algebraMap k (QLaurent k)).injective
  have hqtor : ∀ n : ℤ, n ≠ 0 → b ^ n ≠ 1 := by
    intro n hn h
    exact hn (hind n 0 (by simpa using h)).1
  have hu := differentialIndependent_of_qDifference_primitive a b 0 ha hb hind
    (HahnSeries.C R * hCoordInv k)
    (algebraMap (RatFunc k) (QBase k) (-(cotModel cc + algebraMap k (RatFunc k) γ₀))
      * (RatFunc.X : QBase k)⁻¹)
    (qDilation_C_mul_hCoordInv a b ha hb R _ hR)
    (no_jetTelescoper_cotModel a b ha hb hqtor cc γ₀ hcc)
  have hmem : (HahnSeries.C R : QLaurent k) * hCoordInv k
      ∈ differentialAdjoin (QBase k) ({(HahnSeries.C R : QLaurent k)} : Set (QLaurent k)) := by
    have h1 : (HahnSeries.C R : QLaurent k)
        ∈ differentialAdjoin (QBase k) ({(HahnSeries.C R : QLaurent k)} : Set (QLaurent k)) :=
      subset_differentialAdjoin (QBase k) _ rfl
    have h2 : hCoordInv k
        ∈ differentialAdjoin (QBase k) ({(HahnSeries.C R : QLaurent k)} : Set (QLaurent k)) := by
      have : hCoordInv k = algebraMap (QBase k) (QLaurent k) ((RatFunc.X : QBase k)⁻¹) :=
        qEmbed_hCoordInv.symm
      rw [this]
      exact IntermediateField.algebraMap_mem _ _
    exact mul_mem h1 h2
  have hCR : HypertranscendentalOver (QBase k) (HahnSeries.C R : QLaurent k) := by
    intro hDA
    exact differentialAlgebraicOver_of_mem_differentialAdjoin_singleton hDA hmem hu
  have hCRsmall : HypertranscendentalOver (RatFunc k) (HahnSeries.C R : QLaurent k) := fun hDA =>
    hCR (differentialAlgebraicOver_mono hDA)
  intro hDAR
  refine hCRsmall ?_
  intro hindep
  refine hDAR ?_
  have hcomp : (fun p : Unit × ℕ => differentialJet p.2 (HahnSeries.C R : QLaurent k))
      = (HahnSeries.C : LaurentSeries k →+* QLaurent k) ∘
        (fun p : Unit × ℕ => differentialJet p.2 R) := by
    funext p
    exact differentialJet_C 0 R p.2
  rw [DifferentialIndependent, hcomp] at hindep
  exact hindep.of_comp
    ({ (HahnSeries.C : LaurentSeries k →+* QLaurent k) with
        commutes' := fun _ => rfl } : LaurentSeries k →ₐ[RatFunc k] QLaurent k)

end

end GaloisForLFunctions.HTGeometry
