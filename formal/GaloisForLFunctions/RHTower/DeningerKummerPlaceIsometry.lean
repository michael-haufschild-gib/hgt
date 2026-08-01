import GaloisForLFunctions.RHTower.DeningerHeightZeroKummer

/-!
# The Kummer place isometry

For a field with admissible absolute values, the function `f_α(v) = log ‖α‖_v` on the place space
has total variation exactly twice the logarithmic height of `α`.  The mechanism is the pointwise
identity `|log t| = 2 log⁺ t - log t` together with the product formula, which kills the signed
sum and leaves twice the positive part — and the sum of the positive parts *is* the logarithmic
height.

Combined with the height-zero theorem this makes the Kummer class map injective modulo torsion in
the place model: `f_α` vanishes identically exactly when `α` is a root of unity.

* `deningerLogProductFormula` : the product formula in logarithmic form.
* `deningerKummerL1Norm_eq_two_mul_logHeight` : the isometry `‖f_α‖₁ = 2 h(α)`.
* `deningerKummerL1Norm_eq_zero_iff` : injectivity of the Kummer class map.
* `deningerAllPlaces_one_isOfFinOrder` : an element of absolute value one at every place is a root
  of unity.
-/

namespace RHTower

open Height AdmissibleAbsValues Real Function

section PlaceIsometry

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- The pointwise identity `|log t| = 2 log⁺ t - log t`, valid for every nonnegative `t`. -/
theorem deningerAbsLog_eq {t : ℝ} (ht : 0 ≤ t) :
    |Real.log t| = 2 * Real.posLog t - Real.log t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp [Real.posLog]
  · rcases le_or_gt 1 t with h1 | h1
    · rw [Real.posLog_eq_log_max_one ht, max_eq_right h1, abs_of_nonneg (Real.log_nonneg h1)]
      ring
    · rw [Real.posLog_eq_log_max_one ht, max_eq_left h1.le, Real.log_one,
        abs_of_nonpos (Real.log_nonpos hpos.le h1.le)]
      ring

omit [AdmissibleAbsValues K] in
/-- The multiset form of the pointwise identity. -/
private theorem deningerSumMapAbsLog (s : Multiset (AbsoluteValue K ℝ)) (x : K) :
    (s.map fun v => |Real.log (v x)|).sum
      = 2 * (s.map fun v => Real.posLog (v x)).sum - (s.map fun v => Real.log (v x)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, deningerAbsLog_eq (a.nonneg x)]
    ring

/-- **The product formula in logarithmic form.**  The signed sum of the logarithms of all absolute
values of a nonzero element vanishes. -/
theorem deningerLogProductFormula {x : K} (hx : x ≠ 0) :
    (archAbsVal.map fun v : AbsoluteValue K ℝ => Real.log (v x)).sum
      + ∑ᶠ v : nonarchAbsVal, Real.log (v.val x) = 0 := by
  have hpf := AdmissibleAbsValues.product_formula (K := K) hx
  have hprodne : (Multiset.map (fun v : AbsoluteValue K ℝ => v x) archAbsVal).prod
      * ∏ᶠ v : nonarchAbsVal, v.val x ≠ 0 := by
    rw [hpf]; exact one_ne_zero
  have hposA : ∀ a ∈ Multiset.map (fun v : AbsoluteValue K ℝ => v x) archAbsVal, a ≠ 0 := by
    intro a ha
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (v.pos hx).ne'
  have hposN : ∀ v : nonarchAbsVal (K := K), 0 < v.val x := fun v =>
    v.val.pos hx
  have hlog := congrArg Real.log hpf
  rw [Real.log_mul (left_ne_zero_of_mul hprodne) (right_ne_zero_of_mul hprodne),
    Real.log_multiset_prod hposA, Real.log_finprod hposN, Real.log_one, Multiset.map_map] at hlog
  exact hlog

/-- The total variation of `f_α` over the place space: the `L¹` norm of the Kummer class. -/
noncomputable def deningerKummerL1Norm (x : K) : ℝ :=
  (archAbsVal.map fun v : AbsoluteValue K ℝ => |Real.log (v x)|).sum
    + ∑ᶠ v : nonarchAbsVal, |Real.log (v.val x)|

/-- **The Kummer place isometry.**  The total variation of `f_α(v) = log ‖α‖_v` over the place
space is twice the logarithmic height of `α`. -/
theorem deningerKummerL1Norm_eq_two_mul_logHeight {x : K} (hx : x ≠ 0) :
    deningerKummerL1Norm x = 2 * Height.logHeight₁ x := by
  classical
  have hfin : HasFiniteMulSupport (fun v : nonarchAbsVal => v.val x) :=
    AdmissibleAbsValues.hasFiniteMulSupport hx
  set S : Finset (nonarchAbsVal (K := K)) := hfin.toFinset with hS
  have hmemS : ∀ v : nonarchAbsVal (K := K),
      v.val x ≠ 1 → v ∈ S := by
    intro v hv
    simpa [hS, Function.mulSupport] using hv
  have hsub : ∀ g : ℝ → ℝ, g 1 = 0 →
      Function.support (fun v : nonarchAbsVal => g (v.val x)) ⊆ (S : Set _) := by
    intro g hg v hv
    by_contra hvS
    apply hv
    show g (v.val x) = 0
    have hone : v.val x = 1 := by
      by_contra hne
      exact hvS (Finset.mem_coe.mpr (hmemS v hne))
    rw [hone, hg]
  have habs := hsub (fun t => |Real.log t|) (by simp)
  have hpos := hsub Real.posLog (by simp [Real.posLog])
  have hlg := hsub Real.log (by simp)
  rw [deningerKummerL1Norm, Height.logHeight₁_eq, deningerSumMapAbsLog,
    finsum_eq_finsetSum_of_support_subset _ habs,
    finsum_eq_finsetSum_of_support_subset _ hpos]
  have hfinsum : ∑ v ∈ S, |Real.log (v.val x)|
      = 2 * ∑ v ∈ S, Real.posLog (v.val x)
        - ∑ v ∈ S, Real.log (v.val x) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ =>
      deningerAbsLog_eq (v.val.nonneg x)
  rw [hfinsum]
  have hprod := deningerLogProductFormula hx
  rw [finsum_eq_finsetSum_of_support_subset _ hlg] at hprod
  linarith

end PlaceIsometry

section NumberFieldModel

variable {K : Type*} [Field K] [NumberField K]

/-- **Injectivity of the Kummer class map in the place model.**  The function `f_α` has vanishing
total variation exactly when `α` is a root of unity. -/
theorem deningerKummerL1Norm_eq_zero_iff {x : K} (hx : x ≠ 0) :
    deningerKummerL1Norm x = 0 ↔ IsOfFinOrder x := by
  rw [deningerKummerL1Norm_eq_two_mul_logHeight hx, mul_eq_zero,
    ← deningerLogHeightZero_iff_isOfFinOrder hx]
  constructor
  · intro h
    exact h.resolve_left two_ne_zero
  · intro h
    exact Or.inr h

/-- **An element of absolute value one at every place is a root of unity.** -/
theorem deningerAllPlaces_one_isOfFinOrder {x : K} (hx : x ≠ 0)
    (harch : ∀ v ∈ (archAbsVal : Multiset (AbsoluteValue K ℝ)), v x = 1)
    (hnon : ∀ v : nonarchAbsVal (K := K), v.val x = 1) : IsOfFinOrder x := by
  refine (deningerKummerL1Norm_eq_zero_iff hx).mp ?_
  have harch' : (archAbsVal.map fun v : AbsoluteValue K ℝ => |Real.log (v x)|).sum = 0 := by
    refine Multiset.sum_eq_zero ?_
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp ha
    rw [harch v hv, Real.log_one, abs_zero]
  have hnon' : ∑ᶠ v : nonarchAbsVal (K := K),
      |Real.log (v.val x)| = 0 := by
    have : (fun v : nonarchAbsVal (K := K) => |Real.log (v.val x)|)
        = fun _ => (0 : ℝ) := by
      funext v
      rw [hnon v, Real.log_one, abs_zero]
    rw [this, finsum_zero]
  rw [deningerKummerL1Norm, harch', hnon', add_zero]

end NumberFieldModel

end RHTower
