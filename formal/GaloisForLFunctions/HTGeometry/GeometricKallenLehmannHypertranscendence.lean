import GaloisForLFunctions.HTGeometry.QDifferenceInhomogeneousHT
import GaloisForLFunctions.HTGeometry.RamifiedLaurentTransfer
import GaloisForLFunctions.HTGeometry.MultiplicativeDependenceRoot
import GaloisForLFunctions.HTGeometry.GeometricKallenLehmannResponse

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

/-- The simple pole `w/(1-X)` is a cotangent model plus a constant. -/
theorem oneSubInv_eq_cotModel_add_const [CharZero k] (w : k) :
    algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X)
      = cotModel (-(w / 2)) + algebraMap k (RatFunc k) (w / 2) := by
  have hlin : toRF (linFac k) ≠ 0 := RatFunc.algebraMap_ne_zero linFac_ne_zero
  have hneg : toRF (Polynomial.C (1 : k) - Polynomial.X) = -toRF (linFac k) := by
    rw [← map_neg]
    congr 1
    rw [linFac]
    ring_nf
  have h := cotModel_sub_const (-(w / 2))
  have h2 : (2 : k) * -(w / 2) = -w := by ring
  rw [h2] at h
  have hsum : cotModel (-(w / 2)) + algebraMap k (RatFunc k) (w / 2)
      = algebraMap k (RatFunc k) (-w) / toRF (linFac k) := by
    rw [← h, map_neg]
    ring_nf
  rw [hneg, div_neg, hsum, map_neg, neg_div]

/-! ## The Laurent solution of the inhomogeneous equation -/

/-- The coefficientwise solution of `R - a R(bz) = ρ`. -/
def qDifferenceSolution (a b : k) (ρ : LaurentSeries k) : LaurentSeries k where
  coeff m := ρ.coeff m / (1 - a * b ^ m)
  isPWO_support' := by
    refine ρ.isPWO_support.mono ?_
    intro m hm
    simp only [Function.mem_support] at hm ⊢
    intro h
    exact hm (by simp [h])

@[simp]
theorem coeff_qDifferenceSolution (a b : k) (ρ : LaurentSeries k) (m : ℤ) :
    (qDifferenceSolution a b ρ).coeff m = ρ.coeff m / (1 - a * b ^ m) := rfl

/-- **Every Laurent series is the defect of a first-order inhomogeneous `q`-difference
equation**, as soon as no `a bᵐ` equals one; the solution is then unique. -/
theorem qDifferenceSolution_spec (a b : k) (hb : b ≠ 0) (ρ : LaurentSeries k)
    (hres : ∀ m : ℤ, 1 - a * b ^ m ≠ 0) :
    qDifferenceSolution a b ρ
        - algebraMap k (LaurentSeries k) a * innerDilation b hb (qDifferenceSolution a b ρ)
      = ρ := by
  refine HahnSeries.coeff_inj.mp (funext fun m => ?_)
  rw [HahnSeries.coeff_sub, algebraMap_k_laurentSeries, coeff_C_mul_hahn, coeff_innerDilation,
    coeff_qDifferenceSolution]
  field_simp
  rw [mul_div_assoc, div_self (hres m), mul_one]

theorem qDifferenceSolution_unique (a b : k) (hb : b ≠ 0) (ρ R : LaurentSeries k)
    (hres : ∀ m : ℤ, 1 - a * b ^ m ≠ 0)
    (hR : R - algebraMap k (LaurentSeries k) a * innerDilation b hb R = ρ) :
    R = qDifferenceSolution a b ρ := by
  refine HahnSeries.coeff_inj.mp (funext fun m => ?_)
  have h := congrArg (fun x : LaurentSeries k => x.coeff m) hR
  simp only [HahnSeries.coeff_sub, algebraMap_k_laurentSeries, coeff_C_mul_hahn,
    coeff_innerDilation] at h
  rw [coeff_qDifferenceSolution, eq_div_iff (hres m), ← h]
  ring_nf

/-- The multiplicative independence of the multipliers rules out every resonance. -/
theorem no_resonance_of_multIndependent {a b : k} (ha : a ≠ 0)
    (hind : ∀ m n : ℤ, b ^ m = a ^ n → m = 0 ∧ n = 0) (m : ℤ) : 1 - a * b ^ m ≠ 0 := by
  intro h
  have hbm : b ^ m = a ^ (-1 : ℤ) := by
    have ha' : a ≠ 0 := ha
    field_simp
    linear_combination -h
  exact absurd (hind m (-1) hbm).2 (by norm_num)

/-! ## The hypertranscendence of the geometric response -/

/-- **The response of a geometric spectrum is hypertranscendental.**  For multiplicatively
independent multipliers, the unique Laurent solution of `R - a R(bz) = w/(1-z)` with `w ≠ 0` is
differentially transcendental over `k(z)`. -/
theorem hypertranscendentalOver_qDifferenceSolution [CharZero k] (a b w : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hw : w ≠ 0)
    (hind : ∀ m n : ℤ, b ^ m = a ^ n → m = 0 ∧ n = 0) :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    letI := innerDifferential (k := k)
    HypertranscendentalOver (RatFunc k)
      (qDifferenceSolution a b (algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X)))) := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  letI := innerDifferential (k := k)
  refine hypertranscendentalOver_of_qDifference_cotModel a b ha hb hind (-(w / 2)) (w / 2)
    (by simpa using hw) _ ?_
  rw [qDifferenceSolution_spec a b hb _ (no_resonance_of_multIndependent ha hind),
    ← oneSubInv_eq_cotModel_add_const w]

/-! ## The Euclidean propagator -/

/-- The Euclidean momentum propagator as a germ at infinity, in the variable `w = 1/s`:
`G(w) = -w R(-w)`, which is the identity `G(-1/z) = -z R(z)` read in the reciprocal coordinate. -/
def propagatorGerm (R : LaurentSeries k) : LaurentSeries k :=
  -(HahnSeries.single 1 1 : LaurentSeries k) * innerDilation (-1) (by norm_num) R

/-- **The propagator germ satisfies the reciprocal `q`-difference equation.**  Reciprocal inversion
turns the multiplier `a` into `a/b` and reflects the inhomogeneity. -/
theorem propagatorGerm_equation (a b : k) (hb : b ≠ 0) (r : RatFunc k)
    (R : LaurentSeries k)
    (hR : R - algebraMap k (LaurentSeries k) a * innerDilation b hb R
      = algebraMap (RatFunc k) (LaurentSeries k) r) :
    propagatorGerm R
        - algebraMap k (LaurentSeries k) (a / b) * innerDilation b hb (propagatorGerm R)
      = algebraMap (RatFunc k) (LaurentSeries k)
        (-(RatFunc.X : RatFunc k) * ratFuncScale (-1) (by norm_num : (-1 : k) ≠ 0) r) := by
  have hmone : (-1 : k) ≠ 0 := by norm_num
  have hrefl := congrArg (innerDilation (-1) hmone) hR
  rw [map_sub, map_mul, innerDilation_innerDilation, algebraMap_k_laurentSeries,
    innerDilation_C, ← algebraMap_k_laurentSeries, ← algebraMap_ratFuncScale] at hrefl
  have hdil : innerDilation b hb (propagatorGerm R)
      = algebraMap k (LaurentSeries k) b
        * (-(HahnSeries.single 1 1 : LaurentSeries k)
          * innerDilation (-1 * b) (by simpa using mul_ne_zero hmone hb) R) := by
    rw [propagatorGerm, map_mul, map_neg, innerDilation_single_one, innerDilation_innerDilation,
      algebraMap_k_laurentSeries]
    ring_nf
  rw [hdil, propagatorGerm]
  have hbne : algebraMap k (LaurentSeries k) b ≠ 0 := by
    simpa [algebraMap_k_laurentSeries] using C_ne_zero_of_ne_zero hb
  have hab : algebraMap k (LaurentSeries k) (a / b) * algebraMap k (LaurentSeries k) b
      = algebraMap k (LaurentSeries k) a := by
    rw [← map_mul, div_mul_cancel₀ _ hb]
  have hX : (HahnSeries.single 1 1 : LaurentSeries k)
      = algebraMap (RatFunc k) (LaurentSeries k) RatFunc.X := RatFunc.coe_X.symm
  calc -(HahnSeries.single 1 1 : LaurentSeries k) * innerDilation (-1) hmone R
        - algebraMap k (LaurentSeries k) (a / b) * (algebraMap k (LaurentSeries k) b
          * (-(HahnSeries.single 1 1 : LaurentSeries k)
            * innerDilation (-1 * b) (by simpa using mul_ne_zero hmone hb) R))
      = -(HahnSeries.single 1 1 : LaurentSeries k)
          * (innerDilation (-1) hmone R
            - algebraMap k (LaurentSeries k) a
              * innerDilation (-1 * b) (by simpa using mul_ne_zero hmone hb) R) := by
        rw [← mul_assoc, hab]
        ring_nf
    _ = -(HahnSeries.single 1 1 : LaurentSeries k)
          * algebraMap (RatFunc k) (LaurentSeries k) (ratFuncScale (-1) hmone r) := by
        rw [hrefl]
    _ = algebraMap (RatFunc k) (LaurentSeries k)
          (-(RatFunc.X : RatFunc k) * ratFuncScale (-1) hmone r) := by
        rw [hX, map_mul, map_neg]

theorem propagator_inhomogeneity_eq (w : k) :
    -(RatFunc.X : RatFunc k) * ratFuncScale (-1) (by norm_num : (-1 : k) ≠ 0)
        (algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X))
      = toRF (-(Polynomial.C w) * Polynomial.X)
        / (toRF (Polynomial.X - Polynomial.C (-1 : k)) * toRF 1) := by
  have hmone : (-1 : k) ≠ 0 := by norm_num
  have hX : (RatFunc.X : RatFunc k) = toRF Polynomial.X := RatFunc.algebraMap_X.symm
  have hscale : ratFuncScale (-1) hmone
      (algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X))
      = algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 + Polynomial.X) := by
    rw [algebraMap_eq_toRF_C, ratFuncScale_div]
    congr 1
    · congr 1
      rw [polyScale_eq_comp, Polynomial.C_comp]
    · congr 1
      rw [polyScale_eq_comp]
      simp [Polynomial.sub_comp]
  rw [hscale, show toRF (1 : Polynomial k) = 1 from map_one _, mul_one,
    show toRF (Polynomial.X - Polynomial.C (-1 : k)) = toRF (Polynomial.C 1 + Polynomial.X) from by
      congr 1
      rw [Polynomial.C_neg, Polynomial.C_1]
      ring,
    show toRF (-(Polynomial.C w) * Polynomial.X)
        = -(algebraMap k (RatFunc k) w) * (RatFunc.X : RatFunc k) from by
      rw [hX, algebraMap_eq_toRF_C,
        show toRF (-(Polynomial.C w) * Polynomial.X)
          = toRF (-(Polynomial.C w)) * toRF Polynomial.X from map_mul _ _ _,
        show toRF (-(Polynomial.C w)) = -toRF (Polynomial.C w) from map_neg _ _]]
  ring_nf

/-- **The Euclidean propagator of the geometric spectrum is hypertranscendental.**  Reciprocal
inversion turns the response equation into the same shape with multiplier `a/b` and a reflected
simple pole, so the criterion applies again. -/
theorem hypertranscendentalOver_propagatorGerm [CharZero k] (a b w : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hw : w ≠ 0)
    (hind : ∀ m n : ℤ, b ^ m = a ^ n → m = 0 ∧ n = 0) (R : LaurentSeries k)
    (hR : R - algebraMap k (LaurentSeries k) a * innerDilation b hb R
      = algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X))) :
    letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
    letI := innerDifferential (k := k)
    HypertranscendentalOver (RatFunc k) (propagatorGerm R) := by
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  letI := innerDifferential (k := k)
  have hab : a / b ≠ 0 := div_ne_zero ha hb
  have hind' : ∀ m n : ℤ, b ^ m = (a / b) ^ n → m = 0 ∧ n = 0 := by
    intro m n h
    have hbn : b ^ (m + n) = a ^ n := by
      rw [zpow_add₀ hb, h, div_zpow]
      field_simp
    obtain ⟨h1, h2⟩ := hind (m + n) n hbn
    exact ⟨by omega, h2⟩
  have hqtor : ∀ n : ℤ, n ≠ 0 → b ^ n ≠ 1 := by
    intro n hn h
    exact hn (hind n 0 (by simpa using h)).1
  refine hypertranscendentalOver_of_qDifference_simplePole (a / b) b hab hb hind' (-1)
    (by norm_num) (-(Polynomial.C w) * Polynomial.X) 1 (by simp) ?_ ?_ _ ?_
  · simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_X]
    simpa using hw
  · intro n hn
    refine regularAt_simplePoleQuotient _ _ _ _ ?_ (by simp)
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add]
    intro h
    refine hqtor n hn ?_
    have h1 : (-1 : k) * b ^ n = (-1 : k) * 1 := by
      rw [mul_one]
      linear_combination h
    exact mul_left_cancel₀ (by norm_num : (-1 : k) ≠ 0) h1
  · rw [← propagator_inhomogeneity_eq w]
    exact propagatorGerm_equation a b hb _ R hR

/-! ## The response of a geometric spectrum, for every multiplier pair -/

theorem complex_zpow_real_ne_one {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≠ 1) (n : ℤ) (hn : n ≠ 0) :
    ((β : ℂ)) ^ n ≠ 1 := by
  intro h
  have hreal : (β : ℝ) ^ n = 1 := by
    have hcast : (((β : ℝ) ^ n : ℝ) : ℂ) = 1 := by
      push_cast
      exact h
    exact_mod_cast hcast
  have hlog := congrArg Real.log hreal
  rw [Real.log_zpow, Real.log_one] at hlog
  have hlogβ : Real.log β ≠ 0 := by
    intro hz
    exact hβ₁ (by
      have := Real.exp_log hβ₀
      rw [hz, Real.exp_zero] at this
      exact this.symm)
  rcases mul_eq_zero.mp hlog with h' | h'
  · exact hn (by exact_mod_cast h')
  · exact hlogβ h'

/-- **The response of a geometric Källén--Lehmann spectrum is hypertranscendental, for every pair
of multipliers in `(0,1)`.**  Either the multipliers are multiplicatively independent, and the
two-variable model applies, or both are powers of a common positive real, and the ramified
one-variable model applies. -/
theorem hypertranscendentalOver_geometricResponse (a b : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (R : LaurentSeries ℂ)
    (hbC : ((b : ℂ)) ≠ 0)
    (hR : R - algebraMap ℂ (LaurentSeries ℂ) ((a : ℂ)) * innerDilation ((b : ℂ)) hbC R
      = algebraMap (RatFunc ℂ) (LaurentSeries ℂ)
        (algebraMap ℂ (RatFunc ℂ) ((1 - a : ℝ) : ℂ)
          / toRF (Polynomial.C 1 - Polynomial.X))) :
    letI : Differential (RatFunc ℂ) := cylinderDifferential (1 : ℂ)
    letI := innerDifferential (k := ℂ)
    HypertranscendentalOver (RatFunc ℂ) R := by
  letI : Differential (RatFunc ℂ) := cylinderDifferential (1 : ℂ)
  letI := innerDifferential (k := ℂ)
  have haC : ((a : ℂ)) ≠ 0 := by
    simpa using ne_of_gt ha₀
  have hwC : ((1 - a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by intro h; linarith [sub_eq_zero.mp h])
  rcases multIndependent_or_commonRoot ha₀ ha₁ hb₀ hb₁ with hind | ⟨β, p, q, hβ₀, hq, hβq, hβp⟩
  · refine hypertranscendentalOver_of_qDifference_simplePole ((a : ℂ)) ((b : ℂ)) haC hbC ?_ 1
      one_ne_zero (-(Polynomial.C ((1 - a : ℝ) : ℂ))) 1 (by simp) ?_ ?_ R ?_
    · intro m n hmn
      refine hind m n ?_
      have hcast : (((b : ℝ) ^ m : ℝ) : ℂ) = (((a : ℝ) ^ n : ℝ) : ℂ) := by
        push_cast
        exact hmn
      exact_mod_cast hcast
    · simp only [Polynomial.eval_neg, Polynomial.eval_C, neg_ne_zero]
      exact hwC
    · intro n hn
      refine regularAt_simplePoleQuotient _ _ _ _ ?_ (by simp)
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, one_mul]
      intro h
      refine complex_zpow_real_ne_one hb₀ (by linarith) n hn ?_
      linear_combination h
    · rw [hR]
      congr 1
      rw [algebraMap_eq_toRF_C]
      rw [show (Polynomial.C 1 - Polynomial.X : Polynomial ℂ)
          = -(Polynomial.X - Polynomial.C 1) from by ring,
        show toRF (-(Polynomial.X - Polynomial.C 1) : Polynomial ℂ)
          = -toRF (Polynomial.X - Polynomial.C 1) from map_neg _ _,
        show toRF (1 : Polynomial ℂ) = 1 from map_one _, mul_one,
        show toRF (-(Polynomial.C ((1 - a : ℝ) : ℂ)) : Polynomial ℂ)
          = -toRF (Polynomial.C ((1 - a : ℝ) : ℂ)) from map_neg _ _]
      field_simp
  · have hβC : ((β : ℂ)) ≠ 0 := by simpa using ne_of_gt hβ₀
    have hβ₁ : β ≠ 1 := by
      intro h
      rw [h, one_pow] at hβq
      linarith
    have hbeq : ((b : ℂ)) = ((β : ℂ)) ^ q := by
      rw [← hβq]
      push_cast
      ring
    have haeq : ((a : ℂ)) = ((β : ℂ)) ^ p := by
      rw [← hβp]
      push_cast
      ring
    refine hypertranscendentalOver_of_ramifiedMonomialTwist ((β : ℂ)) hβC ?_ p q hq
      (((1 - a : ℝ) : ℂ)) hwC R ?_
    · intro n hn
      exact complex_zpow_real_ne_one hβ₀ hβ₁ n hn
    · have hgen : ∀ (c : ℂ) (hc : c ≠ 0), c = ((β : ℂ)) ^ q →
          (R - algebraMap ℂ (LaurentSeries ℂ) ((a : ℂ)) * innerDilation c hc R
            = algebraMap (RatFunc ℂ) (LaurentSeries ℂ)
              (algebraMap ℂ (RatFunc ℂ) ((1 - a : ℝ) : ℂ)
                / toRF (Polynomial.C 1 - Polynomial.X))) →
          R - algebraMap ℂ (LaurentSeries ℂ) (((β : ℂ)) ^ p)
              * innerDilation (((β : ℂ)) ^ q) (pow_ne_zero q hβC) R
            = algebraMap (RatFunc ℂ) (LaurentSeries ℂ)
              (algebraMap ℂ (RatFunc ℂ) ((1 - a : ℝ) : ℂ)
                / toRF (Polynomial.C 1 - Polynomial.X)) := by
        rintro c hc rfl h
        rw [← haeq]
        exact h
      exact hgen _ hbC hbeq hR

/-! ## The propagator for every multiplier pair -/

theorem innerDilation_propagatorGerm (R : LaurentSeries k) :
    innerDilation (-1) (by norm_num : (-1 : k) ≠ 0) (propagatorGerm R)
      = (HahnSeries.single 1 1 : LaurentSeries k) * R := by
  have hgen : ∀ (c : k) (hc : c ≠ 0), c = 1 → innerDilation c hc R = R := by
    rintro c hc rfl
    refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
    rw [coeff_innerDilation, one_zpow, one_mul]
  rw [propagatorGerm, map_mul, map_neg, innerDilation_single_one, innerDilation_innerDilation,
    hgen _ _ (by ring),
    show (HahnSeries.C (-1 : k) : LaurentSeries k) = -1 from by
      rw [map_neg, map_one]]
  ring

/-- **Hypertranscendence of the response gives hypertranscendence of the propagator.**  Reciprocal
inversion is a dilation followed by multiplication by the coordinate, and both preserve
differential transcendence over `k(z)`. -/
theorem hypertranscendentalOver_propagatorGerm_of_response [CharZero k] {R : LaurentSeries k}
    (hR : @HypertranscendentalOver (RatFunc k) (LaurentSeries k) _ _ _
      (innerDifferential (k := k)) R) :
    @HypertranscendentalOver (RatFunc k) (LaurentSeries k) _ _ _
      (innerDifferential (k := k)) (propagatorGerm R) := by
  letI := innerDifferential (k := k)
  letI : Differential (RatFunc k) := cylinderDifferential (1 : k)
  haveI := IsScalarTower.of_algebraMap_eq (R := k) (S := RatFunc k) (A := LaurentSeries k)
    fun c => by
      rw [algebraMap_k_laurentSeries]
      exact (algebraMap_const_laurentSeries c).symm
  haveI : DifferentialAlgebra (RatFunc k) (LaurentSeries k) :=
    ⟨fun y => by
      rw [innerDifferential_deriv, cylinderDifferential_deriv, cylDeriv_one_eq_ratFuncEulerOp,
        algebraMap_ratFuncEulerOp]⟩
  haveI : CharZero (LaurentSeries k) :=
    charZero_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective
  intro hDA
  refine hR ?_
  have h1 := differentialAlgebraicOver_innerDilation (-1) (by norm_num : (-1 : k) ≠ 0) hDA
  rw [innerDilation_propagatorGerm] at h1
  have hprod : ((HahnSeries.single 1 1 : LaurentSeries k) * R)
      * algebraMap (RatFunc k) (LaurentSeries k) (RatFunc.X : RatFunc k)⁻¹ = R := by
    rw [algebraMap_ratFuncX_inv]
    have hone : (HahnSeries.single (1 : ℤ) (1 : k) : LaurentSeries k)
        * HahnSeries.single (-1) 1 = 1 := by
      rw [HahnSeries.single_mul_single]
      norm_num
    calc (HahnSeries.single (1 : ℤ) (1 : k) * R) * HahnSeries.single (-1) 1
        = (HahnSeries.single (1 : ℤ) (1 : k) * HahnSeries.single (-1) 1) * R := by ring
      _ = R := by rw [hone, one_mul]
  have hmem : R ∈ differentialAdjoin (RatFunc k)
      ({(HahnSeries.single 1 1 : LaurentSeries k) * R} : Set (LaurentSeries k)) := by
    have h2 := mul_mem (subset_differentialAdjoin (RatFunc k)
      ({(HahnSeries.single 1 1 : LaurentSeries k) * R} : Set (LaurentSeries k)) rfl)
      (IntermediateField.algebraMap_mem
        (differentialAdjoin (RatFunc k)
          ({(HahnSeries.single 1 1 : LaurentSeries k) * R} : Set (LaurentSeries k)))
        (RatFunc.X : RatFunc k)⁻¹)
    rwa [hprod] at h2
  exact differentialAlgebraicOver_of_mem_differentialAdjoin_singleton h1 hmem

/-! ## The rational inhomogeneity as a geometric series -/

theorem algebraMap_polynomial_laurent_coeff (p : Polynomial k) (n : ℤ) :
    (algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap (Polynomial k) (RatFunc k) p)).coeff n
      = if n < 0 then 0 else p.coeff n.natAbs :=
  coeff_algebraMap_polynomial p n

theorem coeff_ofPowerSeries_mk (f : ℕ → k) (n : ℤ) :
    (HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk f)).coeff n
      = if n < 0 then 0 else f n.natAbs := by
  rw [PowerSeries.coeff_coe]
  by_cases h : n < 0
  · simp [h]
  · simp [h]

theorem algebraMap_oneSubX :
    algebraMap (RatFunc k) (LaurentSeries k)
        (toRF (Polynomial.C 1 - Polynomial.X : Polynomial k))
      = 1 - HahnSeries.single 1 1 := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [toRF, algebraMap_polynomial_laurent_coeff, HahnSeries.coeff_sub, HahnSeries.coeff_one,
    HahnSeries.coeff_single]
  by_cases hneg : n < 0
  · rw [if_pos hneg, if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ n = 1)]
    ring
  · rw [if_neg hneg]
    by_cases h0 : n = 0
    · subst h0
      simp [Polynomial.coeff_sub, Polynomial.coeff_X]
    · by_cases h1 : n = 1
      · subst h1
        simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one]
      · have hn0 : n.natAbs ≠ 0 := by omega
        have hn1 : n.natAbs ≠ 1 := by omega
        simp [h0, h1, Polynomial.coeff_sub, Polynomial.coeff_X, hn0,
          Ne.symm hn1, Polynomial.coeff_one]

theorem oneSubX_mul_geometric (w : k) :
    (1 - HahnSeries.single 1 1 : LaurentSeries k)
        * HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun _ => w)
      = HahnSeries.C w := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [sub_mul, one_mul, HahnSeries.coeff_sub, coeff_ofPowerSeries_mk,
    show ((HahnSeries.single (1 : ℤ) (1 : k) : LaurentSeries k)
        * HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun _ => w)).coeff n
      = (HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun _ => w)).coeff (n - 1) from by
      have := HahnSeries.coeff_mul_single_add (a := n - 1) (b := 1)
        (r := (1 : k)) (x := HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun _ => w))
      rw [sub_add_cancel, mul_one] at this
      rw [mul_comm]
      exact this,
    coeff_ofPowerSeries_mk, HahnSeries.C_apply, HahnSeries.coeff_single]
  by_cases hneg : n < 0
  · rw [if_pos hneg, if_pos (by omega : n - 1 < 0), if_neg (by omega : ¬ n = 0)]
    ring
  · by_cases h0 : n = 0
    · subst h0
      norm_num
    · have h1 : ¬ (n - 1 < 0) := by omega
      rw [if_neg hneg, if_neg h1, if_neg h0]
      simp

theorem algebraMap_oneSubInv_eq_geometric (w : k) :
    algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X))
      = HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun _ => w) := by
  have hne : toRF (Polynomial.C 1 - Polynomial.X : Polynomial k) ≠ 0 := by
    refine RatFunc.algebraMap_ne_zero ?_
    intro h
    have hcoeff := congrArg (fun p : Polynomial k => p.coeff 1) h
    simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one] at hcoeff
  have himg : (1 - HahnSeries.single 1 1 : LaurentSeries k) ≠ 0 := by
    rw [← algebraMap_oneSubX]
    intro hzero
    exact hne ((map_eq_zero_iff _ (algebraMap (RatFunc k) (LaurentSeries k)).injective).mp hzero)
  refine mul_right_cancel₀ himg ?_
  rw [mul_comm (HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun _ => w)),
    oneSubX_mul_geometric, ← algebraMap_oneSubX, ← map_mul, div_mul_cancel₀ _ hne,
    algebraMap_const_laurentSeries, HahnSeries.C_apply]

/-! ## The corpus's geometric response as a complex Laurent series -/

/-- The response of the geometric Källén--Lehmann spectrum, as a complex Laurent series. -/
def geometricResponseLaurent (a b : ℝ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ
    (PowerSeries.map (algebraMap ℝ ℂ) (_root_.HTGeometry.geometricKallenLehmannResponse a b))

theorem coeff_geometricResponseLaurent (a b : ℝ) (n : ℤ) :
    (geometricResponseLaurent a b).coeff n
      = if n < 0 then 0 else ((_root_.HTGeometry.geometricKallenLehmannMoment a b n.natAbs : ℝ) : ℂ) := by
  rw [geometricResponseLaurent, PowerSeries.coeff_coe]
  by_cases h : n < 0
  · simp [h]
  · simp [h, PowerSeries.coeff_map, _root_.HTGeometry.geometricKallenLehmannResponse]

/-- **The complex response satisfies the exact self-similarity constraint.** -/
theorem geometricResponseLaurent_equation (a b : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hb₀ : 0 < b)
    (hb₁ : b < 1) (hbC : ((b : ℂ)) ≠ 0) :
    geometricResponseLaurent a b
        - algebraMap ℂ (LaurentSeries ℂ) ((a : ℂ))
          * innerDilation ((b : ℂ)) hbC (geometricResponseLaurent a b)
      = algebraMap (RatFunc ℂ) (LaurentSeries ℂ)
        (algebraMap ℂ (RatFunc ℂ) ((1 - a : ℝ) : ℂ) / toRF (Polynomial.C 1 - Polynomial.X)) := by
  rw [algebraMap_oneSubInv_eq_geometric]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [HahnSeries.coeff_sub, algebraMap_k_laurentSeries, coeff_C_mul_hahn, coeff_innerDilation,
    coeff_geometricResponseLaurent]
  rw [coeff_ofPowerSeries_mk]
  by_cases h : n < 0
  · simp [h]
  · rw [if_neg h, if_neg h]
    have hres : (1 : ℝ) - a * b ^ n.natAbs ≠ 0 := by
      have hble : b ^ n.natAbs ≤ 1 := pow_le_one₀ (le_of_lt hb₀) (le_of_lt hb₁)
      have hpos : 0 < b ^ n.natAbs := pow_pos hb₀ _
      nlinarith
    have hresC : (((1 - a * b ^ n.natAbs : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hres
    have hbz : ((b : ℂ)) ^ n = (((b ^ n.natAbs : ℝ) : ℂ)) := by
      have hn : ((n.natAbs : ℕ) : ℤ) = n := Int.natAbs_of_nonneg (by omega)
      calc ((b : ℂ)) ^ n = ((b : ℂ)) ^ ((n.natAbs : ℕ) : ℤ) := by rw [hn]
        _ = ((b : ℂ)) ^ (n.natAbs : ℕ) := zpow_natCast _ _
        _ = (((b ^ n.natAbs : ℝ) : ℂ)) := by push_cast; ring
    rw [_root_.HTGeometry.geometricKallenLehmannMoment, hbz]
    rw [show (((1 - a) / (1 - a * b ^ n.natAbs) : ℝ) : ℂ)
        = ((1 - a : ℝ) : ℂ) / ((1 - a * b ^ n.natAbs : ℝ) : ℂ) from by push_cast; ring]
    field_simp
    push_cast
    ring

/-! ## The card's statements -/

/-- **The mass-resolvent response of a geometric Källén--Lehmann spectrum is hypertranscendental
over `ℂ(z)`**, for every pair of multipliers in `(0,1)`, for the Euler derivation. -/
theorem hypertranscendentalOver_geometricResponseLaurent (a b : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) :
    letI : Differential (RatFunc ℂ) := cylinderDifferential (1 : ℂ)
    letI := innerDifferential (k := ℂ)
    HypertranscendentalOver (RatFunc ℂ) (geometricResponseLaurent a b) := by
  have hbC : ((b : ℂ)) ≠ 0 := by simpa using ne_of_gt hb₀
  exact hypertranscendentalOver_geometricResponse a b ha₀ ha₁ hb₀ hb₁ _ hbC
    (geometricResponseLaurent_equation a b ha₀ ha₁ hb₀ hb₁ hbC)

/-- The same conclusion for the ordinary derivation, which is the card's statement. -/
theorem hypertranscendentalOver_geometricResponseLaurent_ordinary (a b : ℝ) (ha₀ : 0 < a)
    (ha₁ : a < 1) (hb₀ : 0 < b) (hb₁ : b < 1) :
    letI := ratFuncOrdinaryDifferential (k := ℂ)
    letI := innerOrdinaryDifferential (k := ℂ)
    HypertranscendentalOver (RatFunc ℂ) (geometricResponseLaurent a b) :=
  hypertranscendentalOver_ordinary_of_euler
    (hypertranscendentalOver_geometricResponseLaurent a b ha₀ ha₁ hb₀ hb₁)

/-- **The Euclidean momentum propagator of the geometric spectrum is hypertranscendental**, for
every pair of multipliers in `(0,1)`, for both derivations. -/
theorem hypertranscendentalOver_geometricPropagator (a b : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) :
    letI : Differential (RatFunc ℂ) := cylinderDifferential (1 : ℂ)
    letI := innerDifferential (k := ℂ)
    HypertranscendentalOver (RatFunc ℂ) (propagatorGerm (geometricResponseLaurent a b)) :=
  hypertranscendentalOver_propagatorGerm_of_response
    (hypertranscendentalOver_geometricResponseLaurent a b ha₀ ha₁ hb₀ hb₁)

/-- The propagator statement for the ordinary derivation. -/
theorem hypertranscendentalOver_geometricPropagator_ordinary (a b : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) :
    letI := ratFuncOrdinaryDifferential (k := ℂ)
    letI := innerOrdinaryDifferential (k := ℂ)
    HypertranscendentalOver (RatFunc ℂ) (propagatorGerm (geometricResponseLaurent a b)) :=
  hypertranscendentalOver_ordinary_of_euler
    (hypertranscendentalOver_geometricPropagator a b ha₀ ha₁ hb₀ hb₁)

end

end GaloisForLFunctions.HTGeometry
