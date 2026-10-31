import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge
import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision

/-!
# Unit-window increments of the horizontal collision charge

Write `O(T) = xiHorizontalCollisionCharge T` for the multiplicity-weighted number of ordered pairs
of distinct ξ-zeros with `0 < Re < 1`, `0 ≤ Im < T` sharing an ordinate. `O` is cumulative and
monotone; a bound `sup_T O(T) < ∞` means that only finitely many zeros lie off the critical line
(`index_exit_first_rung_tfae`). The quantity attached to a single unit window is the increment

`ΔO(T) = O(T + 1) − O(T)`.

Let `W(T)` be the ξ-zeros with `0 < Re < 1`, `T ≤ Im < T + 1`, `n(T)` their total multiplicity and
`n_off(T)` its off-line part.

* `xiCollisionIncrement_eq`: `ΔO(T) = Σ_{ρ ∈ W(T)} m_ρ (H(Im ρ) − m_ρ)`, `H` the multiplicity of the
  full horizontal fibre.
* `xiUnitWindowOffLineOrder_le_increment`, `xiCollisionIncrement_le_two_mul`:
  `n_off(T) ≤ ΔO(T) ≤ 2 n(T) n_off(T)`. A fibre in `W(T)` lies in `W(T)`; a critical zero meets
  only off-line zeros in its fibre, an off-line zero meets at most `n(T)` copies.
* `exists_xiCollisionIncrement_le_log_sq`: unconditionally `ΔO(T) ≤ C log² T` for large `T`, from
  the local count `n(T) ≤ C log T`; summed, `O(n) ≤ A + C n log²(n + 1)`
  (`exists_xiHorizontalCollisionCharge_nat_le`).
* `tendsto_lineOrder_div_totalOrder_of_bounded_increment`: if `ΔO` is bounded, then the critical
  proportion `N₀(T)/N(T)` of the windows tends to `1`. Bounded increments bound the off-line count
  linearly, `n_off ≤ M(T + 1)`, against `N(T) ≍ T log T`.
-/

set_option autoImplicit false

open Complex Filter Topology Set
open scoped BigOperators
open _root_.RHTower

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ## The unit window and the increment formula -/

/-- ξ-zeros of the open strip with ordinate in `[T, T + 1)`. -/
def xiUnitWindowZeros (T : ℝ) : Finset ℂ :=
  (stripZeros_finite (T + 1)).toFinset.filter (fun ρ => T ≤ ρ.im)

theorem mem_xiUnitWindowZeros {T : ℝ} {ρ : ℂ} :
    ρ ∈ xiUnitWindowZeros T ↔ ρ ∈ (stripZeros_finite (T + 1)).toFinset ∧ T ≤ ρ.im :=
  Finset.mem_filter

/-- The part of the height-`T + 1` window below `T` is the height-`T` window. -/
theorem stripZeros_filter_not_le_eq (T : ℝ) :
    (stripZeros_finite (T + 1)).toFinset.filter (fun ρ => ¬ T ≤ ρ.im) =
      (stripZeros_finite T).toFinset := by
  ext ρ
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, not_le]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3, _⟩, hz⟩, hlt⟩
    exact ⟨⟨h1, h2, h3, hlt⟩, hz⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, hz⟩
    exact ⟨⟨⟨h1, h2, h3, by linarith⟩, hz⟩, h4⟩

/-- Sums over the height-`T + 1` window split into the height-`T` window and the unit window. -/
theorem sum_stripZeros_add_one (T : ℝ) (f : ℂ → ℕ) :
    ∑ ρ ∈ (stripZeros_finite (T + 1)).toFinset, f ρ =
      ∑ ρ ∈ (stripZeros_finite T).toFinset, f ρ + ∑ ρ ∈ xiUnitWindowZeros T, f ρ := by
  rw [← Finset.sum_filter_add_sum_filter_not (stripZeros_finite (T + 1)).toFinset
    (fun ρ => T ≤ ρ.im) f, stripZeros_filter_not_le_eq, add_comm]
  rfl

/-- Summand of the collision charge at a zero `ρ`: `m_ρ (H(Im ρ) − m_ρ)`. -/
def xiCollisionTerm (ρ : ℂ) : ℕ :=
  (analyticOrderAt xi ρ).toNat * (xiHorizontalMultiplicity ρ.im - (analyticOrderAt xi ρ).toNat)

/-- Increment of the collision charge across the unit window `[T, T + 1)`. -/
def xiCollisionIncrement (T : ℝ) : ℕ :=
  xiHorizontalCollisionCharge (T + 1) - xiHorizontalCollisionCharge T

theorem xiHorizontalCollisionCharge_add_one (T : ℝ) :
    xiHorizontalCollisionCharge (T + 1) =
      xiHorizontalCollisionCharge T + ∑ ρ ∈ xiUnitWindowZeros T, xiCollisionTerm ρ := by
  unfold xiHorizontalCollisionCharge
  exact sum_stripZeros_add_one T xiCollisionTerm

/-- **Increment formula.** `ΔO(T)` is the collision summand summed over the unit window only. -/
theorem xiCollisionIncrement_eq (T : ℝ) :
    xiCollisionIncrement T = ∑ ρ ∈ xiUnitWindowZeros T, xiCollisionTerm ρ := by
  unfold xiCollisionIncrement
  rw [xiHorizontalCollisionCharge_add_one]
  omega

/-- Total multiplicity `n(T)` of the unit window. -/
def xiUnitWindowOrder (T : ℝ) : ℕ :=
  ∑ ρ ∈ xiUnitWindowZeros T, (analyticOrderAt xi ρ).toNat

/-- Off-line multiplicity `n_off(T)` of the unit window. -/
def xiUnitWindowOffLineOrder (T : ℝ) : ℕ :=
  ∑ ρ ∈ (xiUnitWindowZeros T).filter (fun ρ => ρ.re ≠ 1 / 2), (analyticOrderAt xi ρ).toNat

theorem xiUnitWindowOffLineOrder_le_order (T : ℝ) :
    xiUnitWindowOffLineOrder T ≤ xiUnitWindowOrder T :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-! ## The two-sided increment bound -/

/-- **Lower bound.** Every off-line copy of the unit window pays at least one unit of increment. -/
theorem xiUnitWindowOffLineOrder_le_increment (T : ℝ) :
    xiUnitWindowOffLineOrder T ≤ xiCollisionIncrement T := by
  rw [xiCollisionIncrement_eq]
  calc xiUnitWindowOffLineOrder T
      ≤ ∑ ρ ∈ (xiUnitWindowZeros T).filter (fun ρ => ρ.re ≠ 1 / 2), xiCollisionTerm ρ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        obtain ⟨hW, hoff⟩ := Finset.mem_filter.mp hρ
        exact xi_order_le_horizontalCollisionTerm_of_offLine (mem_xiUnitWindowZeros.mp hW).1 hoff
    _ ≤ ∑ ρ ∈ xiUnitWindowZeros T, xiCollisionTerm ρ :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The full horizontal fibre through a unit-window zero lies in the unit window. -/
theorem mem_xiUnitWindowZeros_of_fibre {T : ℝ} {ρ z : ℂ} (hT : T ≤ ρ.im)
    (hz : z ∈ (stripZeros_finite (T + 1)).toFinset.filter (fun z => z.im = ρ.im)) :
    z ∈ xiUnitWindowZeros T := by
  obtain ⟨hzS, hzim⟩ := Finset.mem_filter.mp hz
  exact mem_xiUnitWindowZeros.mpr ⟨hzS, by rw [hzim]; exact hT⟩

/-- Pointwise bound: a critical zero collides only with off-line zeros of its window, an
off-line zero with at most `n(T)` copies. -/
theorem xiCollisionTerm_le {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ xiUnitWindowZeros T) :
    xiCollisionTerm ρ ≤
      (analyticOrderAt xi ρ).toNat * xiUnitWindowOffLineOrder T +
        (if ρ.re ≠ 1 / 2 then (analyticOrderAt xi ρ).toNat * xiUnitWindowOrder T else 0) := by
  obtain ⟨hS, hT⟩ := mem_xiUnitWindowZeros.mp hρ
  by_cases hre : ρ.re = 1 / 2
  · rw [if_neg (not_not.mpr hre), add_zero]
    unfold xiCollisionTerm
    rw [horizontalMultiplicity_sub_order_eq_sum_same_im_erase hS]
    apply Nat.mul_le_mul_left
    apply Finset.sum_le_sum_of_subset
    intro z hz
    obtain ⟨hzne, hzF⟩ := Finset.mem_erase.mp hz
    refine Finset.mem_filter.mpr ⟨mem_xiUnitWindowZeros_of_fibre hT hzF, fun hzre => hzne ?_⟩
    exact Complex.ext (hzre.trans hre.symm) (Finset.mem_filter.mp hzF).2
  · rw [if_pos hre]
    have hH : xiHorizontalMultiplicity ρ.im ≤ xiUnitWindowOrder T := by
      rw [xiHorizontalMultiplicity, stripHeightFinset_eq_stripZeros_filter_im hS]
      exact Finset.sum_le_sum_of_subset fun z hz => mem_xiUnitWindowZeros_of_fibre hT hz
    unfold xiCollisionTerm
    exact (Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans hH)).trans (Nat.le_add_left _ _)

/-- **Upper bound.** `ΔO(T) ≤ 2 n(T) n_off(T)`. -/
theorem xiCollisionIncrement_le_two_mul (T : ℝ) :
    xiCollisionIncrement T ≤ 2 * (xiUnitWindowOrder T * xiUnitWindowOffLineOrder T) := by
  rw [xiCollisionIncrement_eq]
  calc ∑ ρ ∈ xiUnitWindowZeros T, xiCollisionTerm ρ
      ≤ ∑ ρ ∈ xiUnitWindowZeros T,
          ((analyticOrderAt xi ρ).toNat * xiUnitWindowOffLineOrder T +
            (if ρ.re ≠ 1 / 2 then (analyticOrderAt xi ρ).toNat * xiUnitWindowOrder T else 0)) :=
        Finset.sum_le_sum fun ρ hρ => xiCollisionTerm_le hρ
    _ = xiUnitWindowOrder T * xiUnitWindowOffLineOrder T +
          xiUnitWindowOffLineOrder T * xiUnitWindowOrder T := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_filter, ← Finset.sum_mul]
        rfl
    _ = 2 * (xiUnitWindowOrder T * xiUnitWindowOffLineOrder T) := by ring

/-! ## The unconditional size of an increment -/

/-- **Local count.** `n(T) ≤ C log T` for large `T`: the zero copies over the unit window all lie
within height `1` of `T`. -/
theorem exists_xiUnitWindowOrder_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, (xiUnitWindowOrder T : ℝ) ≤ C * Real.log T := by
  classical
  obtain ⟨C, hC, hev⟩ := exists_card_near_xi_zeros_le
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with T hT
  have hzero : ∀ ρ ∈ xiUnitWindowZeros T, xi ρ = 0 := fun ρ hρ =>
    ((Set.Finite.mem_toFinset _).mp (mem_xiUnitWindowZeros.mp hρ).1).2
  let fib : {ρ // ρ ∈ xiUnitWindowZeros T} → Finset XiZeroCopy := fun ρ =>
    xiZeroCopyFiber ⟨ρ.1, mem_xi_divisor_support_of_eq_zero (hzero ρ.1 ρ.2)⟩
  have hdisj : ((xiUnitWindowZeros T).attach : Set {ρ // ρ ∈ xiUnitWindowZeros T}).PairwiseDisjoint
      fib := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro q hqa hqb
    apply hab
    apply Subtype.ext
    have h := (mem_xiZeroCopyFiber.mp hqa).symm.trans (mem_xiZeroCopyFiber.mp hqb)
    exact congrArg (fun r : XiDivisorSupport => (r : ℂ)) h
  have hcard : ((xiUnitWindowZeros T).attach.biUnion fib).card = xiUnitWindowOrder T := by
    rw [Finset.card_biUnion hdisj]
    unfold xiUnitWindowOrder
    rw [← Finset.sum_attach (xiUnitWindowZeros T) (fun ρ => (analyticOrderAt xi ρ).toNat)]
    exact Finset.sum_congr rfl fun ρ _ => card_xiZeroCopyFiber_eq_order_toNat _
  have hnear : ∀ q ∈ (xiUnitWindowZeros T).attach.biUnion fib, |(q.1 : ℂ).im - T| ≤ 1 := by
    intro q hq
    obtain ⟨ρ, _, hqρ⟩ := Finset.mem_biUnion.mp hq
    have hq1 : (q.1 : ℂ) = ρ.1 := by
      rw [mem_xiZeroCopyFiber.mp hqρ]
    obtain ⟨hS, hTle⟩ := mem_xiUnitWindowZeros.mp ρ.2
    have hlt : ρ.1.im < T + 1 := ((Set.Finite.mem_toFinset _).mp hS).1.2.2.2
    rw [hq1, abs_le]
    constructor <;> linarith
  have h := hT _ hnear
  rw [hcard] at h
  exact h

/-- **Unconditional increment bound.** `ΔO(T) ≤ C log² T` for large `T`. -/
theorem exists_xiCollisionIncrement_le_log_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (xiCollisionIncrement T : ℝ) ≤ C * Real.log T ^ 2 := by
  obtain ⟨C, hC, hev⟩ := exists_xiUnitWindowOrder_le_log
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  filter_upwards [hev] with T hT
  have hnat : xiCollisionIncrement T ≤ 2 * (xiUnitWindowOrder T * xiUnitWindowOrder T) :=
    (xiCollisionIncrement_le_two_mul T).trans
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (xiUnitWindowOffLineOrder_le_order T)))
  have hreal : (xiCollisionIncrement T : ℝ) ≤
      2 * ((xiUnitWindowOrder T : ℝ) * xiUnitWindowOrder T) := by
    exact_mod_cast hnat
  have hn0 : (0 : ℝ) ≤ xiUnitWindowOrder T := Nat.cast_nonneg _
  calc (xiCollisionIncrement T : ℝ)
      ≤ 2 * ((xiUnitWindowOrder T : ℝ) * xiUnitWindowOrder T) := hreal
    _ ≤ 2 * ((C * Real.log T) * (C * Real.log T)) := by
        gcongr
        exact hn0.trans hT
    _ = 2 * C ^ 2 * Real.log T ^ 2 := by ring

/-- Charge at the next unit height: `O(T + 1) = O(T) + ΔO(T)`. -/
theorem xiHorizontalCollisionCharge_add_one_eq_add_increment (T : ℝ) :
    xiHorizontalCollisionCharge (T + 1) =
      xiHorizontalCollisionCharge T + xiCollisionIncrement T := by
  rw [xiCollisionIncrement_eq, xiHorizontalCollisionCharge_add_one]

/-- **Unconditional cumulative bound.** `O(n) ≤ A + C n log²(n + 1)` at natural heights. -/
theorem exists_xiHorizontalCollisionCharge_nat_le :
    ∃ A C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (xiHorizontalCollisionCharge n : ℝ) ≤ A + C * n * Real.log ((n : ℝ) + 1) ^ 2 := by
  obtain ⟨C, hC, hev⟩ := exists_xiCollisionIncrement_le_log_sq
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  set k₀ : ℕ := ⌈max T₁ 1⌉₊ with hk₀
  refine ⟨xiHorizontalCollisionCharge k₀, C, hC, fun n => ?_⟩
  have hk₀T : max T₁ 1 ≤ (k₀ : ℝ) := Nat.le_ceil _
  have hbase : ∀ n : ℕ, n ≤ k₀ →
      (xiHorizontalCollisionCharge n : ℝ) ≤ xiHorizontalCollisionCharge k₀ := fun n hn => by
    exact_mod_cast xiHorizontalCollisionCharge_mono (by exact_mod_cast hn)
  have hlogsq : ∀ x y : ℝ, 1 ≤ x → x ≤ y → Real.log x ^ 2 ≤ Real.log y ^ 2 := fun x y hx hxy =>
    pow_le_pow_left₀ (Real.log_nonneg hx) (Real.log_le_log (by linarith) hxy) 2
  induction n with
  | zero =>
    have h0 := hbase 0 (Nat.zero_le _)
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero] at h0 ⊢
    exact h0
  | succ m ih =>
    have hnn : 0 ≤ C * ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1 + 1) ^ 2 := by positivity
    push_cast
    by_cases hm : m + 1 ≤ k₀
    · have h := hbase (m + 1) hm
      push_cast at h
      linarith
    · have hkm : k₀ ≤ m := by omega
      have hmT : T₁ ≤ (m : ℝ) :=
        (le_max_left _ _).trans (hk₀T.trans (by exact_mod_cast hkm))
      have hm1 : (1 : ℝ) ≤ m := (le_max_right _ _).trans (hk₀T.trans (by exact_mod_cast hkm))
      have hinc := hT₁ (m : ℝ) hmT
      have hstep := xiHorizontalCollisionCharge_add_one_eq_add_increment (m : ℝ)
      have hstepR : (xiHorizontalCollisionCharge ((m : ℝ) + 1) : ℝ) =
          xiHorizontalCollisionCharge (m : ℝ) + xiCollisionIncrement (m : ℝ) := by
        exact_mod_cast hstep
      have hl1 := hlogsq (m : ℝ) ((m : ℝ) + 1 + 1) hm1 (by linarith)
      have hl2 := hlogsq ((m : ℝ) + 1) ((m : ℝ) + 1 + 1) (by linarith) (by linarith)
      have hm0 : (0 : ℝ) ≤ m := by linarith
      rw [hstepR]
      nlinarith [mul_le_mul_of_nonneg_left hl2 (mul_nonneg hC.le hm0),
        mul_le_mul_of_nonneg_left hl1 hC.le]

/-! ## Bounded increments give critical density one -/

theorem xiStripWindowOffLineOrder_add_one (T : ℝ) :
    xiStripWindowOffLineOrder (T + 1) =
      xiStripWindowOffLineOrder T + xiUnitWindowOffLineOrder T := by
  unfold xiStripWindowOffLineOrder xiUnitWindowOffLineOrder
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  exact sum_stripZeros_add_one T _

theorem xiStripWindowOffLineOrder_zero : xiStripWindowOffLineOrder 0 = 0 := by
  unfold xiStripWindowOffLineOrder
  apply Finset.sum_eq_zero
  intro ρ hρ
  have h := ((Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hρ).1).1
  exact absurd h.2.2.2 (not_lt.mpr h.2.2.1)

theorem xiStripWindowOffLineOrder_mono {T U : ℝ} (h : T ≤ U) :
    xiStripWindowOffLineOrder T ≤ xiStripWindowOffLineOrder U := by
  unfold xiStripWindowOffLineOrder
  exact Finset.sum_le_sum_of_subset
    (Finset.filter_subset_filter _ (stripZeros_toFinset_mono h))

/-- Increments bounded by `M` bound the off-line order of the height-`n` window by `M n`. -/
theorem xiStripWindowOffLineOrder_nat_le {M : ℕ} (hM : ∀ T : ℝ, xiCollisionIncrement T ≤ M)
    (n : ℕ) : xiStripWindowOffLineOrder n ≤ M * n := by
  induction n with
  | zero => simp [xiStripWindowOffLineOrder_zero]
  | succ k ih =>
    have h := xiStripWindowOffLineOrder_add_one (k : ℝ)
    have h2 := (xiUnitWindowOffLineOrder_le_increment (k : ℝ)).trans (hM k)
    push_cast
    rw [h, Nat.mul_add_one]
    exact Nat.add_le_add ih h2

/-- The zero count `N(T)` is at most the strip order of height `T + 1`. -/
theorem xiZeroCount_le_xiStripWindowTotalOrder {T : ℝ} (hT : 0 ≤ T) :
    xiZeroCount T ≤ (xiStripWindowTotalOrder (T + 1) : ℤ) := by
  classical
  rw [xiZeroCount_eq_pos_sum hT]
  have hinj : Set.InjOn (fun ρ : XiDivisorSupport => (ρ : ℂ)) ↑(xiSupportsPos T) :=
    fun a _ b _ h => Subtype.ext h
  have hsub : (xiSupportsPos T).image (fun ρ : XiDivisorSupport => (ρ : ℂ)) ⊆
      (stripZeros_finite (T + 1)).toFinset := by
    intro z hz
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨habs, hpos⟩ := mem_xiSupportsPos.mp hρ
    have hzero := xi_eq_zero_of_mem_divisor_support ρ
    have hstrip :=
      (CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
        (CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_of_xi_eq_zero hzero)).2
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨hstrip.1, hstrip.2, hpos.le, ?_⟩, hzero⟩
    linarith [(abs_le.mp habs).2]
  unfold xiStripWindowTotalOrder
  push_cast
  calc ∑ ρ ∈ xiSupportsPos T, (xiSupportMultiplicity ρ : ℤ)
      = ∑ z ∈ (xiSupportsPos T).image (fun ρ : XiDivisorSupport => (ρ : ℂ)),
          ((analyticOrderAt xi z).toNat : ℤ) := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl fun ρ _ => by
          rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat]
    _ ≤ ∑ z ∈ (stripZeros_finite (T + 1)).toFinset, ((analyticOrderAt xi z).toNat : ℤ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _

/-- **Bounded increments give density one.** If every unit window carries collision increment at
most `M`, the critical-line proportion of the strip windows tends to `1`. -/
theorem tendsto_lineOrder_div_totalOrder_of_bounded_increment {M : ℕ}
    (hM : ∀ T : ℝ, xiCollisionIncrement T ≤ M) :
    Tendsto (fun T : ℝ => (xiStripWindowLineOrder T : ℝ) / xiStripWindowTotalOrder T)
      atTop (𝓝 1) := by
  obtain ⟨T₀, hT₀4, hclose⟩ := exists_xiZeroCount_close (1 / (4 * Real.pi)) (by positivity)
  have hpi := Real.pi_pos
  -- off-line order grows at most linearly
  have hoff : ∀ T : ℝ, 0 ≤ T → (xiStripWindowOffLineOrder T : ℝ) ≤ M * (T + 1) := by
    intro T hT
    have h12 := (xiStripWindowOffLineOrder_mono (Nat.le_ceil T)).trans
      (xiStripWindowOffLineOrder_nat_le hM ⌈T⌉₊)
    have h3 : (⌈T⌉₊ : ℝ) ≤ T + 1 := (Nat.ceil_lt_add_one hT).le
    have h4 : (xiStripWindowOffLineOrder T : ℝ) ≤ M * ⌈T⌉₊ := by exact_mod_cast h12
    exact h4.trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _))
  -- total order grows like `T log T`
  have htot : ∀ T : ℝ, T₀ + 1 ≤ T →
      (T - 1) * Real.log (T - 1) / (4 * Real.pi) ≤ xiStripWindowTotalOrder T := by
    intro T hT
    have hc := (abs_le.mp (hclose (T - 1) (by linarith))).1
    have hle := xiZeroCount_le_xiStripWindowTotalOrder (T := T - 1) (by linarith)
    rw [sub_add_cancel] at hle
    have hleR : (xiZeroCount (T - 1) : ℝ) ≤ xiStripWindowTotalOrder T := by exact_mod_cast hle
    have heq : 1 / (2 * Real.pi) * ((T - 1) * Real.log (T - 1)) -
        1 / (4 * Real.pi) * ((T - 1) * Real.log (T - 1)) =
          (T - 1) * Real.log (T - 1) / (4 * Real.pi) := by
      field_simp
      ring
    linarith
  have hsub1 : Tendsto (fun T : ℝ => T - 1) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-1) tendsto_id).congr fun T => by
      simp [sub_eq_add_neg]
  have hg : Tendsto (fun T : ℝ => 8 * Real.pi * M / Real.log (T - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hsub1)
  have hlarge : ∀ T : ℝ, max (T₀ + 1) 4 ≤ T →
      0 < Real.log (T - 1) ∧ 0 < (xiStripWindowTotalOrder T : ℝ) := by
    intro T hT
    have hT1 : T₀ + 1 ≤ T := (le_max_left _ _).trans hT
    have hT4 : 4 ≤ T := (le_max_right _ _).trans hT
    have hlog : 0 < Real.log (T - 1) := Real.log_pos (by linarith)
    exact ⟨hlog, (div_pos (mul_pos (by linarith) hlog) (by positivity)).trans_le (htot T hT1)⟩
  have hratio : Tendsto
      (fun T : ℝ => (xiStripWindowOffLineOrder T : ℝ) / xiStripWindowTotalOrder T)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun T => by positivity) ?_ hg
    filter_upwards [eventually_ge_atTop (max (T₀ + 1) 4)] with T hT
    have hT1 : T₀ + 1 ≤ T := (le_max_left _ _).trans hT
    have hT4 : 4 ≤ T := (le_max_right _ _).trans hT
    obtain ⟨hlog, htotpos⟩ := hlarge T hT
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    rw [div_le_div_iff₀ htotpos hlog]
    calc (xiStripWindowOffLineOrder T : ℝ) * Real.log (T - 1)
        ≤ M * (T + 1) * Real.log (T - 1) := by
          gcongr
          exact hoff T (by linarith)
      _ ≤ 8 * Real.pi * M * ((T - 1) * Real.log (T - 1) / (4 * Real.pi)) := by
          have hrw : 8 * Real.pi * M * ((T - 1) * Real.log (T - 1) / (4 * Real.pi)) =
              2 * M * (T - 1) * Real.log (T - 1) := by
            field_simp
            ring
          rw [hrw]
          nlinarith [mul_nonneg (mul_nonneg hM0 hlog.le) (by linarith : (0 : ℝ) ≤ T - 3)]
      _ ≤ 8 * Real.pi * M * xiStripWindowTotalOrder T := by
          gcongr
          exact htot T hT1
  have hev : ∀ᶠ T : ℝ in atTop,
      1 - (xiStripWindowOffLineOrder T : ℝ) / xiStripWindowTotalOrder T =
        (xiStripWindowLineOrder T : ℝ) / xiStripWindowTotalOrder T := by
    filter_upwards [eventually_ge_atTop (max (T₀ + 1) 4)] with T hT
    have hpos := (hlarge T hT).2
    rw [sub_eq_iff_eq_add, ← add_div, ← Nat.cast_add, ← xiStripWindowTotalOrder_eq_line_add_offLine,
      div_self hpos.ne']
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hratio
  rw [sub_zero] at hlim
  exact hlim.congr' hev

end GaloisForLFunctions.ConjugateDiagonalGeometry

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.xiCollisionIncrement_eq
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.xiUnitWindowOffLineOrder_le_increment
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.xiCollisionIncrement_le_two_mul
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_xiCollisionIncrement_le_log_sq
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_xiHorizontalCollisionCharge_nat_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_lineOrder_div_totalOrder_of_bounded_increment
