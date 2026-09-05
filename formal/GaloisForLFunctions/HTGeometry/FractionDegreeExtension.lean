import GaloisForLFunctions.HTGeometry.DegreeDeterminantNonCancellation

/-!
# Extending a degree function to the fraction field

A degree function on a domain extends uniquely to its fraction field by `deg(a/b) = deg a − deg b`.
Well-definedness is cross-multiplication, multiplicativity is the product of representations, and
subadditivity is the common denominator.  The extension is again a degree function, so all the
determinant criteria apply to matrices of rational functions.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CommRing A] [IsDomain A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

omit [IsDomain A] in
theorem algebraMap_fractionRing_ne_zero_of_ne_zero {b : A} (hb : b ≠ 0) :
    algebraMap A K b ≠ 0 :=
  fun h => hb (IsFractionRing.injective A K (by rw [map_zero]; exact h))

/-- The integer value of a degree function at a nonzero element. -/
def degZ (d : A → WithBot ℤ) (a : A) : ℤ := (d a).unbotD 0

omit [IsDomain A] in
theorem coe_degZ {d : A → WithBot ℤ} (hd : IsDegree d) {a : A} (ha : a ≠ 0) :
    ((degZ d a : ℤ) : WithBot ℤ) = d a := by
  rcases hda : d a with _ | v
  · exact absurd hda (hd.ne_bot ha)
  · simp only [degZ, hda]
    rfl

theorem degZ_mul {d : A → WithBot ℤ} (hd : IsDegree d) {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    degZ d (a * b) = degZ d a + degZ d b := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have h := hd.map_mul a b
  rw [← coe_degZ hd hab, ← coe_degZ hd ha, ← coe_degZ hd hb] at h
  exact_mod_cast h

open scoped Classical in
/-- The extension of a degree function to the fraction field. -/
def fracDeg (d : A → WithBot ℤ) (x : K) : WithBot ℤ :=
  if x = 0 then ⊥
  else (((degZ d (IsLocalization.sec (nonZeroDivisors A) x).1
      - degZ d ((IsLocalization.sec (nonZeroDivisors A) x).2 : A) : ℤ) : WithBot ℤ))

omit [IsDomain A] in
@[simp] theorem fracDeg_zero (d : A → WithBot ℤ) : fracDeg (K := K) d 0 = ⊥ := by
  simp [fracDeg]

omit [IsDomain A] in
theorem fracDeg_ne_bot (d : A → WithBot ℤ) {x : K} (hx : x ≠ 0) : fracDeg d x ≠ ⊥ := by
  classical
  simp [fracDeg, hx]

/-- **Well-definedness.**  Any representation computes the extended degree. -/
theorem fracDeg_eq {d : A → WithBot ℤ} (hd : IsDegree d) {x : K} {a b : A}
    (ha : a ≠ 0) (hb : b ≠ 0) (hrep : x * algebraMap A K b = algebraMap A K a) :
    fracDeg d x = ((degZ d a - degZ d b : ℤ) : WithBot ℤ) := by
  classical
  have hbK : algebraMap A K b ≠ 0 := algebraMap_fractionRing_ne_zero_of_ne_zero hb
  have hx : x ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrep
    exact ha (IsFractionRing.injective A K (by simpa using hrep.symm))
  have hs := IsLocalization.sec_spec (nonZeroDivisors A) x
  have hb0 : ((IsLocalization.sec (nonZeroDivisors A) x).2 : A) ≠ 0 :=
    nonZeroDivisors.coe_ne_zero _
  have hb0K : algebraMap A K ((IsLocalization.sec (nonZeroDivisors A) x).2 : A) ≠ 0 :=
    algebraMap_fractionRing_ne_zero_of_ne_zero hb0
  have ha0 : (IsLocalization.sec (nonZeroDivisors A) x).1 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hs
    rcases mul_eq_zero.mp hs with h | h
    · exact hx h
    · exact hb0K h
  have hcross : algebraMap A K ((IsLocalization.sec (nonZeroDivisors A) x).1 * b)
      = algebraMap A K (a * ((IsLocalization.sec (nonZeroDivisors A) x).2 : A)) := by
    rw [map_mul, map_mul, ← hs, ← hrep]
    ring
  have hcross' : (IsLocalization.sec (nonZeroDivisors A) x).1 * b
      = a * ((IsLocalization.sec (nonZeroDivisors A) x).2 : A) :=
    IsFractionRing.injective A K hcross
  have hZ := congrArg (degZ d) hcross'
  rw [degZ_mul hd ha0 hb, degZ_mul hd ha hb0] at hZ
  rw [fracDeg, if_neg hx]
  congr 1
  omega

theorem fracDeg_algebraMap {d : A → WithBot ℤ} (hd : IsDegree d) (a : A) :
    fracDeg (K := K) d (algebraMap A K a) = d a := by
  classical
  by_cases ha : a = 0
  · subst ha
    rw [map_zero, fracDeg_zero]
    exact ((hd.eq_bot 0).mpr rfl).symm
  · have h1 : degZ d (1 : A) = 0 := by
      have h := hd.map_one
      rw [← coe_degZ hd (one_ne_zero (α := A))] at h
      exact_mod_cast h
    rw [fracDeg_eq hd ha one_ne_zero (by simp), h1, sub_zero, coe_degZ hd ha]

/-- **The extension is a degree function.** -/
theorem isDegree_fracDeg {d : A → WithBot ℤ} (hd : IsDegree d) :
    IsDegree (fracDeg (K := K) d) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · intro h
      by_contra hx
      exact fracDeg_ne_bot d hx h
    · intro h; subst h; simp
  · intro x y
    by_cases hx : x = 0
    · subst hx; simp
    by_cases hy : y = 0
    · subst hy; simp
    obtain ⟨a, b, hb, hab⟩ : ∃ a b : A, b ≠ 0 ∧ x * algebraMap A K b = algebraMap A K a := by
      refine ⟨(IsLocalization.sec (nonZeroDivisors A) x).1,
        ((IsLocalization.sec (nonZeroDivisors A) x).2 : A), nonZeroDivisors.coe_ne_zero _,
        IsLocalization.sec_spec (nonZeroDivisors A) x⟩
    obtain ⟨c, e, he, hce⟩ : ∃ c e : A, e ≠ 0 ∧ y * algebraMap A K e = algebraMap A K c := by
      refine ⟨(IsLocalization.sec (nonZeroDivisors A) y).1,
        ((IsLocalization.sec (nonZeroDivisors A) y).2 : A), nonZeroDivisors.coe_ne_zero _,
        IsLocalization.sec_spec (nonZeroDivisors A) y⟩
    have ha : a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hab
      rcases mul_eq_zero.mp hab with h | h
      · exact hx h
      · exact algebraMap_fractionRing_ne_zero_of_ne_zero hb h
    have hc : c ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hce
      rcases mul_eq_zero.mp hce with h | h
      · exact hy h
      · exact algebraMap_fractionRing_ne_zero_of_ne_zero he h
    have hmul : (x * y) * algebraMap A K (b * e) = algebraMap A K (a * c) := by
      rw [map_mul, map_mul]
      calc x * y * (algebraMap A K b * algebraMap A K e)
          = (x * algebraMap A K b) * (y * algebraMap A K e) := by ring
        _ = algebraMap A K a * algebraMap A K c := by rw [hab, hce]
    have hZ : degZ d (a * c) - degZ d (b * e)
        = (degZ d a - degZ d b) + (degZ d c - degZ d e) := by
      rw [degZ_mul hd ha hc, degZ_mul hd hb he]
      ring
    rw [fracDeg_eq hd (mul_ne_zero ha hc) (mul_ne_zero hb he) hmul,
      fracDeg_eq hd ha hb hab, fracDeg_eq hd hc he hce, hZ]
    exact WithBot.coe_add _ _
  · intro x y
    by_cases hxy : x + y = 0
    · rw [hxy]; simp
    by_cases hx : x = 0
    · subst hx; simp
    by_cases hy : y = 0
    · subst hy; simp
    obtain ⟨a, b, hb, hab⟩ : ∃ a b : A, b ≠ 0 ∧ x * algebraMap A K b = algebraMap A K a :=
      ⟨(IsLocalization.sec (nonZeroDivisors A) x).1,
        ((IsLocalization.sec (nonZeroDivisors A) x).2 : A), nonZeroDivisors.coe_ne_zero _,
        IsLocalization.sec_spec (nonZeroDivisors A) x⟩
    obtain ⟨c, e, he, hce⟩ : ∃ c e : A, e ≠ 0 ∧ y * algebraMap A K e = algebraMap A K c :=
      ⟨(IsLocalization.sec (nonZeroDivisors A) y).1,
        ((IsLocalization.sec (nonZeroDivisors A) y).2 : A), nonZeroDivisors.coe_ne_zero _,
        IsLocalization.sec_spec (nonZeroDivisors A) y⟩
    have ha : a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hab
      rcases mul_eq_zero.mp hab with h | h
      · exact hx h
      · exact algebraMap_fractionRing_ne_zero_of_ne_zero hb h
    have hc : c ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hce
      rcases mul_eq_zero.mp hce with h | h
      · exact hy h
      · exact algebraMap_fractionRing_ne_zero_of_ne_zero he h
    have hsum : (x + y) * algebraMap A K (b * e) = algebraMap A K (a * e + c * b) := by
      rw [map_add, map_mul, map_mul, map_mul]
      calc (x + y) * (algebraMap A K b * algebraMap A K e)
          = (x * algebraMap A K b) * algebraMap A K e
            + (y * algebraMap A K e) * algebraMap A K b := by ring
        _ = algebraMap A K a * algebraMap A K e + algebraMap A K c * algebraMap A K b := by
            rw [hab, hce]
    have hnum : a * e + c * b ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hsum
      rcases mul_eq_zero.mp hsum with h | h
      · exact hxy h
      · exact algebraMap_fractionRing_ne_zero_of_ne_zero (mul_ne_zero hb he) h
    rw [fracDeg_eq hd hnum (mul_ne_zero hb he) hsum, fracDeg_eq hd ha hb hab,
      fracDeg_eq hd hc he hce, degZ_mul hd hb he]
    have hbound : d (a * e + c * b) ≤ max (d (a * e)) (d (c * b)) := hd.map_add_le _ _
    rw [← coe_degZ hd hnum, ← coe_degZ hd (mul_ne_zero ha he),
      ← coe_degZ hd (mul_ne_zero hc hb), degZ_mul hd ha he, degZ_mul hd hc hb] at hbound
    have hZ : degZ d (a * e + c * b) ≤ max (degZ d a + degZ d e) (degZ d c + degZ d b) := by
      exact_mod_cast hbound
    rcases le_total (degZ d a + degZ d e) (degZ d c + degZ d b) with hcase | hcase
    · rw [max_eq_right hcase] at hZ
      refine le_trans ?_ (le_max_right _ _)
      exact_mod_cast (by omega : degZ d (a * e + c * b) - (degZ d b + degZ d e)
        ≤ degZ d c - degZ d e)
    · rw [max_eq_left hcase] at hZ
      refine le_trans ?_ (le_max_left _ _)
      exact_mod_cast (by omega : degZ d (a * e + c * b) - (degZ d b + degZ d e)
        ≤ degZ d a - degZ d b)

end GaloisForLFunctions.HTGeometry

end
