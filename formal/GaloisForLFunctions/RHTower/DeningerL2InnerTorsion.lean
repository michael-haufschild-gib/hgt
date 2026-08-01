import GaloisForLFunctions.RHTower.DeningerL2InnerAdditive

/-!
# The `L²` inner product vanishes on torsion

A root of unity has absolute value one at every place, so its Kummer function is identically zero
and its inner product with anything vanishes.  This is the property that lets the form descend to
the Kummer group `𝒢 = Q̄ˣ/μ_∞`.

* `deningerPlace_eq_one_of_isOfFinOrder` : a root of unity has value one at every place.
* `deningerL2Inner_torsion_left`, `deningerL2Inner_torsion_right` : the inner product vanishes.
* `deningerAbsL2Inner_torsion_left` : the same for the absolute inner product.
-/

namespace RHTower

open NumberField Module

open scoped IntermediateField

section Torsion

variable {K : Type*} [Field K] [NumberField K]

private theorem deningerPosPow_eq_one {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : n ≠ 0)
    (h : t ^ n = 1) : t = 1 := by
  have hlog : (n : ℝ) * Real.log t = 0 := by rw [← Real.log_pow, h, Real.log_one]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hzero := (mul_eq_zero.mp hlog).resolve_left hn'
  have hexp := congrArg Real.exp hzero
  rwa [Real.exp_log ht, Real.exp_zero] at hexp

omit [NumberField K] in
/-- **A root of unity has value one at every infinite place.** -/
theorem deningerInfinitePlace_eq_one_of_isOfFinOrder {x : K} (hx : x ≠ 0) (h : IsOfFinOrder x)
    (v : InfinitePlace K) : v x = 1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  refine deningerPosPow_eq_one (InfinitePlace.pos_iff.mpr hx) hn.ne' ?_
  rw [← map_pow, hpow, map_one]

/-- **A root of unity has value one at every finite place.** -/
theorem deningerFinitePlace_eq_one_of_isOfFinOrder {x : K} (hx : x ≠ 0) (h : IsOfFinOrder x)
    (w : FinitePlace K) : w x = 1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  refine deningerPosPow_eq_one (FinitePlace.pos_iff.mpr hx) hn.ne' ?_
  rw [← map_pow, hpow, map_one]

/-- **The inner product vanishes on torsion.** -/
theorem deningerL2Inner_torsion_left {x : K} (hx : x ≠ 0) (h : IsOfFinOrder x) (y : K) :
    deningerL2Inner x y = 0 := by
  rw [deningerL2Inner]
  have harch : (∑ v : InfinitePlace K, (v.mult : ℝ) * (Real.log (v x) * Real.log (v y))) = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [deningerInfinitePlace_eq_one_of_isOfFinOrder hx h v, Real.log_one, zero_mul, mul_zero]
  have hfin : (∑ᶠ w : FinitePlace K,
      (Real.log (w x) * Real.log (w y)) / (deningerPlaceDegree w : ℝ)) = 0 := by
    have hzero : (fun w : FinitePlace K =>
        (Real.log (w x) * Real.log (w y)) / (deningerPlaceDegree w : ℝ)) = fun _ => (0 : ℝ) := by
      funext w
      rw [deningerFinitePlace_eq_one_of_isOfFinOrder hx h w, Real.log_one, zero_mul, zero_div]
    rw [hzero, finsum_zero]
  rw [harch, hfin, add_zero]

/-- **The inner product vanishes on torsion in the second argument.** -/
theorem deningerL2Inner_torsion_right {y : K} (hy : y ≠ 0) (h : IsOfFinOrder y) (x : K) :
    deningerL2Inner x y = 0 := by
  rw [deningerL2Inner_comm, deningerL2Inner_torsion_left hy h]

end Torsion

section AbsoluteTorsion

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

omit [Algebra.IsAlgebraic ℚ F] in
/-- Finite order transfers to a subfield element. -/
theorem deningerIntermediate_isOfFinOrder {E : IntermediateField ℚ F} {α : F} (hα : α ∈ E)
    (h : IsOfFinOrder α) : IsOfFinOrder (⟨α, hα⟩ : E) := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  refine Subtype.ext ?_
  show ((⟨α, hα⟩ : E) ^ n : F) = 1
  rw [← hpow]

/-- **The absolute inner product vanishes on roots of unity.** -/
theorem deningerAbsL2Inner_torsion_left {α β : F} (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : IsOfFinOrder α) : deningerAbsL2Inner α β = 0 := by
  have hαm : α ∈ (ℚ⟮α, β⟯ : IntermediateField ℚ F) :=
    IntermediateField.subset_adjoin ℚ {α, β} (by simp)
  have hβm : β ∈ (ℚ⟮α, β⟯ : IntermediateField ℚ F) :=
    IntermediateField.subset_adjoin ℚ {α, β} (by simp)
  rw [deningerAbsL2Inner_intermediateField (ℚ⟮α, β⟯ : IntermediateField ℚ F) hαm hβm hα hβ,
    deningerNormalizedL2Inner,
    deningerL2Inner_torsion_left (deningerIntermediate_ne_zero hαm hα)
      (deningerIntermediate_isOfFinOrder hαm h), zero_div]

end AbsoluteTorsion

end RHTower
