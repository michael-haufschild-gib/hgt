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
  ring

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

set_option maxHeartbeats 1000000 in
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
theorem propagatorGerm_equation (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (r : RatFunc k)
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
    ring
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
        ring
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
  ring

set_option maxHeartbeats 1000000 in
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
    exact propagatorGerm_equation a b ha hb _ R hR

end

end GaloisForLFunctions.HTGeometry
