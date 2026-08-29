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

end

end GaloisForLFunctions.HTGeometry
