import GaloisForLFunctions.HTGeometry.TwistedRatFuncLaurent

/-!
# The two-variable Laurent model of a `q`-difference field

The field `k((z))((h))` carries the dilation `z ↦ b z`, `h ↦ a⁻¹ h` and the derivation with
`δ z = z`, `δ h = s h`.  Its invariants are computed by the multiplicative relations between `a`
and `b`: if `bᵐ = aⁿ` forces `m = n = 0`, the only invariant Laurent series are the constants.

This is the ambient difference-differential field in which a first-order inhomogeneous
`q`-difference equation with constant multiplier `a` can be untwisted: the extra coordinate `h`
is a formal solution of the homogeneous equation, and dividing by it turns the inhomogeneous
equation into an additive one.  The constant invariant field is what the differential Ostrowski
criterion requires of its ambient field.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Multiplicative

noncomputable section

variable {k : Type*} [Field k]

/-! ## The one-variable layer -/

/-- The dilation `f(z) ↦ f(b z)` of `k((z))`. -/
def innerDilation (b : k) (hb : b ≠ 0) : LaurentSeries k →+* LaurentSeries k :=
  hahnTwistHom (RingHom.id k) (laurentChar b hb)

@[simp]
theorem coeff_innerDilation (b : k) (hb : b ≠ 0) (f : LaurentSeries k) (n : ℤ) :
    (innerDilation b hb f).coeff n = b ^ n * f.coeff n := by
  simp [innerDilation]

/-- The Euler derivation `z d/dz` of `k((z))`. -/
def innerEuler : LaurentSeries k →+ LaurentSeries k := hahnGradeHom (Int.castAddHom k)

@[simp]
theorem coeff_innerEuler (f : LaurentSeries k) (n : ℤ) :
    (innerEuler f).coeff n = (n : k) * f.coeff n := rfl

theorem innerEuler_leibniz (x y : LaurentSeries k) :
    innerEuler (x * y) = innerEuler x * y + x * innerEuler y :=
  hahnGrade_mul (Int.castAddHom k) x y

theorem coeff_C_mul (c : k) (x : LaurentSeries k) (n : ℤ) :
    ((HahnSeries.C c : LaurentSeries k) * x).coeff n = c * x.coeff n := by
  rw [mul_comm, HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero, mul_comm]

theorem innerEuler_C_mul (c : k) (x : LaurentSeries k) :
    innerEuler ((HahnSeries.C c : LaurentSeries k) * x)
      = (HahnSeries.C c : LaurentSeries k) * innerEuler x := by
  ext n
  rw [coeff_innerEuler, coeff_C_mul, coeff_C_mul, coeff_innerEuler]
  ring

theorem innerDilation_C (b : k) (hb : b ≠ 0) (c : k) :
    innerDilation b hb (HahnSeries.C c : LaurentSeries k) = HahnSeries.C c := by
  ext n
  rw [coeff_innerDilation]
  by_cases h : n = 0
  · subst h; simp
  · simp [HahnSeries.C_apply, h]

theorem innerDilation_innerEuler (b : k) (hb : b ≠ 0) (f : LaurentSeries k) :
    innerDilation b hb (innerEuler f) = innerEuler (innerDilation b hb f) := by
  ext n
  rw [coeff_innerDilation, coeff_innerEuler, coeff_innerEuler, coeff_innerDilation]
  ring

/-! ## The two-variable field -/

/-- The two-variable Laurent field `k((z))((h))`. -/
abbrev QLaurent (k : Type*) [Field k] := LaurentSeries (LaurentSeries k)

theorem C_ne_zero_of_ne_zero {c : k} (hc : c ≠ 0) : (HahnSeries.C c : LaurentSeries k) ≠ 0 := by
  intro h
  have := congrArg (fun x : LaurentSeries k => x.coeff 0) h
  simp only [HahnSeries.C_apply, HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at this
  exact hc this

/-- The dilation `z ↦ b z`, `h ↦ a⁻¹ h` of `k((z))((h))`. -/
def qDilation (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) : QLaurent k →+* QLaurent k :=
  hahnTwistHom (innerDilation b hb)
    (laurentChar (HahnSeries.C a⁻¹ : LaurentSeries k) (C_ne_zero_of_ne_zero (inv_ne_zero ha)))

@[simp]
theorem coeff_qDilation (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (f : QLaurent k) (n : ℤ) :
    (qDilation a b ha hb f).coeff n
      = (HahnSeries.C a⁻¹ : LaurentSeries k) ^ n * innerDilation b hb (f.coeff n) := by
  simp [qDilation]

theorem coeff_coeff_qDilation (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (f : QLaurent k) (n m : ℤ) :
    ((qDilation a b ha hb f).coeff n).coeff m = a ^ (-n) * (b ^ m * (f.coeff n).coeff m) := by
  rw [coeff_qDilation, ← map_zpow₀, coeff_C_mul, coeff_innerDilation, inv_zpow, ← zpow_neg]

/-- **The invariants of the two-variable dilation are the constants**, exactly when the multiplier
pair is multiplicatively independent. -/
theorem exists_C_C_of_qDilation_eq_self (a b : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hind : ∀ m n : ℤ, b ^ m = a ^ n → m = 0 ∧ n = 0)
    {f : QLaurent k} (hf : qDilation a b ha hb f = f) :
    ∃ c : k, f = HahnSeries.C (HahnSeries.C c) := by
  have key : ∀ n m : ℤ, (f.coeff n).coeff m ≠ 0 → b ^ m = a ^ n := by
    intro n m hne
    have h := congrArg (fun x : QLaurent k => (x.coeff n).coeff m) hf
    simp only [coeff_coeff_qDilation] at h
    have hstep : a ^ (-n) * b ^ m = 1 :=
      mul_right_cancel₀ hne (by rw [one_mul]; linear_combination h)
    have h2 := congrArg (fun t : k => a ^ n * t) hstep
    simp only [mul_one] at h2
    rw [← mul_assoc, ← zpow_add₀ ha, add_neg_cancel, zpow_zero, one_mul] at h2
    exact h2
  have vanish : ∀ n m : ℤ, n ≠ 0 ∨ m ≠ 0 → (f.coeff n).coeff m = 0 := by
    intro n m hnm
    by_contra hne
    rcases hnm with hn | hm
    · exact hn (hind m n (key n m hne)).2
    · exact hm (hind m n (key n m hne)).1
  refine ⟨(f.coeff 0).coeff 0, ?_⟩
  ext n m
  by_cases hn : n = 0
  · subst hn
    by_cases hm : m = 0
    · subst hm; simp [HahnSeries.C_apply]
    · rw [vanish 0 m (Or.inr hm)]
      simp [HahnSeries.C_apply, hm]
  · rw [vanish n m (Or.inl hn)]
    simp [HahnSeries.C_apply, hn]

/-! ## The derivation -/

/-- The outer grading `hⁿ ↦ n s hⁿ`. -/
def outerGrade (s : k) : ℤ →+ LaurentSeries k :=
  (HahnSeries.C : k →+* LaurentSeries k).toAddMonoidHom.comp (zmultiplesHom k s)

@[simp]
theorem outerGrade_apply (s : k) (n : ℤ) :
    outerGrade s n = (HahnSeries.C (n • s) : LaurentSeries k) := rfl

/-- The derivation of `k((z))((h))` with `δ z = z` and `δ h = s h`. -/
def qDerivation (s : k) : QLaurent k →+ QLaurent k :=
  hahnCoeffMapHom innerEuler + hahnGradeHom (outerGrade s)

theorem coeff_qDerivation (s : k) (f : QLaurent k) (n : ℤ) :
    (qDerivation s f).coeff n
      = innerEuler (f.coeff n) + (HahnSeries.C (n • s) : LaurentSeries k) * f.coeff n := rfl

theorem qDerivation_leibniz (s : k) (x y : QLaurent k) :
    qDerivation s (x * y) = qDerivation s x * y + x * qDerivation s y := by
  simp only [qDerivation, AddMonoidHom.add_apply, hahnCoeffMapHom_apply, hahnGradeHom_apply,
    hahnCoeffMap_leibniz innerEuler innerEuler_leibniz, hahnGrade_mul]
  ring

/-- The differential structure of `k((z))((h))` with `δ z = z` and `δ h = s h`. -/
@[reducible] def qDifferential (s : k) : Differential (QLaurent k) := by
  letI : Algebra ℤ (QLaurent k) := Ring.toIntAlgebra _
  exact ⟨Derivation.mk' (qDerivation s).toIntLinearMap (by
    intro x y
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul, qDerivation_leibniz]
    ring)⟩

theorem innerDilation_C_mul (b : k) (hb : b ≠ 0) (c : k) (x : LaurentSeries k) :
    innerDilation b hb ((HahnSeries.C c : LaurentSeries k) * x)
      = (HahnSeries.C c : LaurentSeries k) * innerDilation b hb x := by
  rw [map_mul, innerDilation_C]

/-- **The dilation commutes with the derivation.** -/
theorem qDilation_qDerivation (a b s : k) (ha : a ≠ 0) (hb : b ≠ 0) (f : QLaurent k) :
    qDilation a b ha hb (qDerivation s f) = qDerivation s (qDilation a b ha hb f) := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_qDilation, coeff_qDerivation, coeff_qDerivation, coeff_qDilation, ← map_zpow₀,
    map_add, innerDilation_innerEuler, innerDilation_C_mul, innerEuler_C_mul]
  ring

/-- The constants are fixed by the dilation. -/
@[simp]
theorem qDilation_C_C (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (c : k) :
    qDilation a b ha hb (HahnSeries.C (HahnSeries.C c)) = HahnSeries.C (HahnSeries.C c) := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  refine HahnSeries.coeff_inj.mp (funext fun m => ?_)
  rw [coeff_coeff_qDilation]
  by_cases hn : n = 0
  · subst hn
    by_cases hm : m = 0
    · subst hm; simp [HahnSeries.C_apply]
    · simp [HahnSeries.C_apply, hm]
  · simp [HahnSeries.C_apply, hn]

theorem innerDilation_innerDilation (c d : k) (hc : c ≠ 0) (hd : d ≠ 0) (f : LaurentSeries k) :
    innerDilation c hc (innerDilation d hd f) = innerDilation (c * d) (mul_ne_zero hc hd) f := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_innerDilation, coeff_innerDilation, coeff_innerDilation, mul_zpow, mul_assoc]

theorem innerDilation_single_one (c : k) (hc : c ≠ 0) :
    innerDilation c hc (HahnSeries.single 1 1 : LaurentSeries k)
      = HahnSeries.C c * HahnSeries.single 1 1 := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_innerDilation, coeff_C_mul]
  by_cases h : n = 1
  · subst h; simp
  · rw [HahnSeries.coeff_single_of_ne h, mul_zero, mul_zero]

end

end GaloisForLFunctions.HTGeometry
