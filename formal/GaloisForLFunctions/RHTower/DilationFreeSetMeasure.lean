import Mathlib

/-!
# Sets without integer-ratio lags are short

Let `S ⊆ ℝ` be measurable and `L > 0`.  If `S ∩ (S − mL)` is null for every integer `m ≥ 1`, then
`|S| ≤ L`: translating the slices `S ∩ [jL, (j+1)L)` back into `[0, L)` gives almost disjoint sets.

With `L = log 2` this applies to every *dilation-free* set (no two points of `S` differ by `log n`,
`n ≥ 2`), since the lags `m log 2 = log 2^m` are among the `log n`.  In the multiplicative variable:
a set of positive reals containing no two points in an integer ratio has logarithmic measure at most
`log 2`, with equality for the windows `[a, 2a)`.

Consequently a nonnegative function whose autocorrelation vanishes at every lag `log n`, `n ≥ 2`
(a nonnegative prime-blind test), is supported, up to a null set, on a set of measure at most
`log 2` (`volume_pos_le_log_two_of_primeBlind`).
-/

open MeasureTheory Set

namespace RHTower.DilationFree

/-- **Lag-free sets are short.** If `S ∩ (S − mL)` is null for all `m ≥ 1`, then `|S| ≤ L`. -/
theorem volume_le_of_null_inter_shift {S : Set ℝ} (hS : MeasurableSet S) {L : ℝ} (hL : 0 < L)
    (h : ∀ m : ℕ, 1 ≤ m → volume (S ∩ (fun x => x + (m : ℝ) * L) ⁻¹' S) = 0) :
    volume S ≤ ENNReal.ofReal L := by
  -- slices and their translates into `[0, L)`
  set Sj : ℤ → Set ℝ := fun j => S ∩ Ico ((j : ℝ) * L) (((j : ℝ) + 1) * L) with hSj
  set Fj : ℤ → Set ℝ := fun j => (fun z => z + (j : ℝ) * L) ⁻¹' Sj j with hFj
  have hSjm : ∀ j, MeasurableSet (Sj j) := fun j => hS.inter measurableSet_Ico
  have hFjm : ∀ j, MeasurableSet (Fj j) := fun j => (hSjm j).preimage (measurable_add_const _)
  -- `S` is the disjoint union of its slices
  have hcover : S = ⋃ j : ℤ, Sj j := by
    ext x; constructor
    · intro hx
      refine mem_iUnion.mpr ⟨⌊x / L⌋, hx, ?_, ?_⟩
      · have := Int.floor_le (x / L)
        calc (⌊x / L⌋ : ℝ) * L ≤ (x / L) * L := by gcongr
          _ = x := by field_simp
      · have := Int.lt_floor_add_one (x / L)
        calc x = (x / L) * L := by field_simp
          _ < ((⌊x / L⌋ : ℝ) + 1) * L := by gcongr
    · intro hx; obtain ⟨j, hj⟩ := mem_iUnion.mp hx; exact hj.1
  have hdisjS : Pairwise (Function.onFun Disjoint Sj) := by
    intro j k hjk
    refine Set.disjoint_left.mpr (fun x hxj hxk => hjk ?_)
    have h1 := hxj.2; have h2 := hxk.2
    have a1 : (j : ℝ) < (k : ℝ) + 1 := by
      have : (j : ℝ) * L < ((k : ℝ) + 1) * L := lt_of_le_of_lt h1.1 h2.2
      exact lt_of_mul_lt_mul_right this hL.le
    have a2 : (k : ℝ) < (j : ℝ) + 1 := by
      have : (k : ℝ) * L < ((j : ℝ) + 1) * L := lt_of_le_of_lt h2.1 h1.2
      exact lt_of_mul_lt_mul_right this hL.le
    have b1 : j < k + 1 := by exact_mod_cast a1
    have b2 : k < j + 1 := by exact_mod_cast a2
    omega
  have hvolS : volume S = ∑' j : ℤ, volume (Sj j) := by
    conv_lhs => rw [hcover]
    exact measure_iUnion hdisjS hSjm
  have hvolF : ∀ j, volume (Fj j) = volume (Sj j) := fun j =>
    measure_preimage_add_right volume _ _
  -- the translates are almost disjoint
  have hdisjF : Pairwise (Function.onFun (AEDisjoint volume) Fj) := by
    have key : ∀ j k : ℤ, j < k → AEDisjoint volume (Fj j) (Fj k) := by
      intro j k hjk
      obtain ⟨m, hm⟩ : ∃ m : ℕ, k = j + m := ⟨(k - j).toNat, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hnull := h m hm1
      -- `Fj j ∩ Fj k` maps into `S ∩ (S − mL)` under `z ↦ z + jL`
      have hsub : Fj j ∩ Fj k ⊆
          (fun z => z + (j : ℝ) * L) ⁻¹' (S ∩ (fun x => x + (m : ℝ) * L) ⁻¹' S) := by
        intro z hz
        refine ⟨hz.1.1, ?_⟩
        have := hz.2.1
        simp only [mem_preimage] at this ⊢
        have e : z + (j : ℝ) * L + (m : ℝ) * L = z + (k : ℝ) * L := by
          rw [hm]; push_cast; ring
        rw [e]; exact this
      show volume (Fj j ∩ Fj k) = 0
      refine measure_mono_null hsub ?_
      rw [measure_preimage_add_right]; exact hnull
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h' | h'
    · exact key j k h'
    · exact (key k j h').symm
  have hFsub : (⋃ j : ℤ, Fj j) ⊆ Ico 0 L := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    have := hj.2
    simp only [mem_Ico] at this ⊢
    constructor
    · nlinarith [this.1]
    · nlinarith [this.2]
  calc volume S = ∑' j : ℤ, volume (Sj j) := hvolS
    _ = ∑' j : ℤ, volume (Fj j) := by simp_rw [hvolF]
    _ = volume (⋃ j : ℤ, Fj j) :=
        (measure_iUnion₀ hdisjF (fun j => (hFjm j).nullMeasurableSet)).symm
    _ ≤ volume (Ico (0 : ℝ) L) := measure_mono hFsub
    _ = ENNReal.ofReal L := by rw [Real.volume_Ico, sub_zero]

/-- **Dilation-free sets have measure at most `log 2`.** If `S ∩ (S − log n)` is null for every
integer `n ≥ 2`, then `|S| ≤ log 2`. -/
theorem volume_le_log_two_of_dilationFree {S : Set ℝ} (hS : MeasurableSet S)
    (h : ∀ n : ℕ, 2 ≤ n → volume (S ∩ (fun x => x + Real.log n) ⁻¹' S) = 0) :
    volume S ≤ ENNReal.ofReal (Real.log 2) := by
  refine volume_le_of_null_inter_shift hS (Real.log_pos (by norm_num)) (fun m hm => ?_)
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have := h (2 ^ m) h2m
  have e : Real.log ((2 ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log 2 := by
    push_cast; rw [Real.log_pow]
  rw [e] at this; exact this

/-- A vanishing autocorrelation of a nonnegative function at lag `a` makes its positivity set
almost disjoint from its translate by `−a`. -/
theorem volume_inter_shift_eq_zero_of_autocorrelation_eq_zero {g : ℝ → ℝ}
    (hg0 : ∀ x, 0 ≤ g x) {a : ℝ} (hint : Integrable (fun x => g (x + a) * g x))
    (hzero : ∫ x, g (x + a) * g x = 0) :
    volume ({x | 0 < g x} ∩ (fun x => x + a) ⁻¹' {x | 0 < g x}) = 0 := by
  have hnn : 0 ≤ fun x => g (x + a) * g x := fun x => mul_nonneg (hg0 _) (hg0 _)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp hzero
  refine measure_mono_null (fun x hx => ?_) (ae_iff.mp hae)
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage] at hx
  simp only [Set.mem_setOf_eq, Pi.zero_apply]
  exact (mul_pos hx.2 hx.1).ne'

/-- **Nonnegative prime-blind functions are short.**  If `g ≥ 0` and its autocorrelation
`∫ g(x + log n) g(x) dx` vanishes for every integer `n ≥ 2`, then `{g > 0}` has measure at most
`log 2`. -/
theorem volume_pos_le_log_two_of_primeBlind {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hint : ∀ n : ℕ, 2 ≤ n → Integrable (fun x => g (x + Real.log n) * g x))
    (hblind : ∀ n : ℕ, 2 ≤ n → ∫ x, g (x + Real.log n) * g x = 0) :
    volume {x | 0 < g x} ≤ ENNReal.ofReal (Real.log 2) :=
  volume_le_log_two_of_dilationFree (measurableSet_lt measurable_const hg) (fun n hn =>
    volume_inter_shift_eq_zero_of_autocorrelation_eq_zero hg0 (hint n hn) (hblind n hn))

end RHTower.DilationFree
