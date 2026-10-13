import Mathlib

/-!
# Finitely many cosines are simultaneously bounded away from `1` at arbitrarily large times

**Theorem** (`exists_ge_forall_cos_le`).  For finitely many nonzero frequencies `λ_i`
(`n` of them) and every `U`, there is `u ≥ U` with `cos(λ_i u) ≤ cos(π/(4(n+1)))` for all `i`.

Proof.  On a window `[U, U+T]` the set where `cos(λ u) > cos a` lies in the intervals
`|λ u − 2πm| < a`, of total length `≤ (|λ|T/(2π) + 5)(2a/|λ|) = Ta/π + 10a/|λ|`.  With
`a = π/(4(n+1))` the union over `i` has length `< T` once `T` is large, so the window contains a
good point.
-/

open MeasureTheory Set Real

noncomputable section

namespace RHTower

/-- One frequency: the times in `[U, U + T]` with `cos(λu) > cos a` lie in short intervals. -/
theorem subset_iUnion_Ioo_of_cos_gt {l a U T u : ℝ} (hl : 0 < l) (ha : 0 < a) (haπ : a ≤ π)
    (hu : u ∈ Icc U (U + T)) (hcos : Real.cos a < Real.cos (l * u)) :
    u ∈ ⋃ m ∈ Finset.Icc (⌊l * U / (2 * π)⌋ - 1) (⌈l * (U + T) / (2 * π)⌉ + 1),
      Ioo ((2 * π * m - a) / l) ((2 * π * m + a) / l) := by
  have hπ := Real.pi_pos
  set x := l * u / (2 * π) with hx
  set m := round x with hm
  have hxm := abs_sub_round x
  have hlu : l * u - 2 * π * m = 2 * π * (x - m) := by rw [hx]; field_simp
  have habs : |l * u - 2 * π * m| ≤ π := by
    rw [hlu, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    nlinarith [hxm]
  have hc : Real.cos (l * u) = Real.cos |l * u - 2 * π * m| := by
    rw [Real.cos_abs, show l * u - 2 * π * m = l * u - (m : ℝ) * (2 * π) by ring,
      Real.cos_sub_int_mul_two_pi]
  have hlt : |l * u - 2 * π * m| < a := by
    by_contra hge
    push Not at hge
    have := Real.cos_le_cos_of_nonneg_of_le_pi ha.le habs hge
    rw [← hc] at this
    linarith
  rw [abs_lt] at hlt
  have hu1 := hu.1
  have hu2 := hu.2
  have hmlo : ⌊l * U / (2 * π)⌋ - 1 ≤ m := by
    have h1 : (⌊l * U / (2 * π)⌋ : ℝ) ≤ l * U / (2 * π) := Int.floor_le _
    have h2 : l * U / (2 * π) ≤ x := by
      rw [hx]; apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
    have h3 : x - 1 / 2 ≤ m := by have := (abs_le.mp hxm).2; linarith
    have : ((⌊l * U / (2 * π)⌋ - 1 : ℤ) : ℝ) ≤ m := by push_cast; linarith
    exact_mod_cast this
  have hmhi : m ≤ ⌈l * (U + T) / (2 * π)⌉ + 1 := by
    have h1 : l * (U + T) / (2 * π) ≤ (⌈l * (U + T) / (2 * π)⌉ : ℝ) := Int.le_ceil _
    have h2 : x ≤ l * (U + T) / (2 * π) := by
      rw [hx]; apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
    have h3 : (m : ℝ) ≤ x + 1 / 2 := by have := (abs_le.mp hxm).1; linarith
    have : (m : ℝ) ≤ ((⌈l * (U + T) / (2 * π)⌉ + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  refine mem_iUnion₂.mpr ⟨m, Finset.mem_Icc.mpr ⟨hmlo, hmhi⟩, ?_, ?_⟩
  · rw [div_lt_iff₀ hl]; linarith
  · rw [lt_div_iff₀ hl]; linarith

/-- The volume of those intervals. -/
theorem volume_iUnion_Ioo_le {l a U T : ℝ} (hl : 0 < l) (ha : 0 < a) (hT : 0 ≤ T) :
    volume (⋃ m ∈ Finset.Icc (⌊l * U / (2 * π)⌋ - 1) (⌈l * (U + T) / (2 * π)⌉ + 1),
      Ioo ((2 * π * m - a) / l) ((2 * π * m + a) / l)) ≤
        ENNReal.ofReal ((l * T / (2 * π) + 5) * (2 * a / l)) := by
  have hπ := Real.pi_pos
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hvol : ∀ m : ℤ, volume (Ioo ((2 * π * m - a) / l) ((2 * π * m + a) / l)) =
      ENNReal.ofReal (2 * a / l) := by
    intro m; rw [Real.volume_Ioo]; congr 1; field_simp; ring
  simp_rw [hvol]
  rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
  have hcard : (((⌈l * (U + T) / (2 * π)⌉ + 1 + 1 - (⌊l * U / (2 * π)⌋ - 1)).toNat : ℕ) : ℝ) ≤
      l * T / (2 * π) + 5 := by
    have h1 : (⌈l * (U + T) / (2 * π)⌉ : ℝ) < l * (U + T) / (2 * π) + 1 := Int.ceil_lt_add_one _
    have h2 : l * U / (2 * π) - 1 < (⌊l * U / (2 * π)⌋ : ℝ) := by
      have := Int.lt_floor_add_one (l * U / (2 * π)); linarith
    have hnn : 0 ≤ ⌈l * (U + T) / (2 * π)⌉ + 1 + 1 - (⌊l * U / (2 * π)⌋ - 1) := by
      have h3 : (⌊l * U / (2 * π)⌋ : ℝ) ≤ l * U / (2 * π) := Int.floor_le _
      have h4 : l * U / (2 * π) ≤ l * (U + T) / (2 * π) := by
        apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
      have h5 : l * (U + T) / (2 * π) ≤ (⌈l * (U + T) / (2 * π)⌉ : ℝ) := Int.le_ceil _
      have : (0 : ℝ) ≤ ((⌈l * (U + T) / (2 * π)⌉ + 1 + 1 - (⌊l * U / (2 * π)⌋ - 1) : ℤ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    rw [show (((⌈l * (U + T) / (2 * π)⌉ + 1 + 1 - (⌊l * U / (2 * π)⌋ - 1)).toNat : ℕ) : ℝ) =
      ((⌈l * (U + T) / (2 * π)⌉ + 1 + 1 - (⌊l * U / (2 * π)⌋ - 1) : ℤ) : ℝ) by
        rw [← Int.toNat_of_nonneg hnn]; norm_cast]
    push_cast
    have : l * (U + T) / (2 * π) - l * U / (2 * π) = l * T / (2 * π) := by field_simp; ring
    linarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **Simultaneous avoidance.** -/
theorem exists_ge_forall_cos_le {ι : Type*} [Fintype ι] (l : ι → ℝ) (hl : ∀ i, l i ≠ 0)
    (U : ℝ) : ∃ u, U ≤ u ∧ ∀ i, Real.cos (l i * u) ≤
      Real.cos (π / (4 * (Fintype.card ι + 1))) := by
  have hπ := Real.pi_pos
  set n := Fintype.card ι
  set a := π / (4 * (n + 1)) with ha
  have ha0 : 0 < a := by positivity
  have haπ : a ≤ π := by
    rw [ha, div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  set S := ∑ i, 1 / |l i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  set U' := max U 0
  set T := 14 * a * S + 1 with hT
  have hT0 : 0 < T := by positivity
  by_contra hno
  push Not at hno
  have hcover : Icc U' (U' + T) ⊆ ⋃ i, ⋃ m ∈ Finset.Icc (⌊|l i| * U' / (2 * π)⌋ - 1)
      (⌈|l i| * (U' + T) / (2 * π)⌉ + 1),
        Ioo ((2 * π * m - a) / |l i|) ((2 * π * m + a) / |l i|) := by
    intro u hu
    have hU'u : U ≤ u := le_trans (le_max_left _ _) hu.1
    obtain ⟨i, hi⟩ := hno u hU'u
    have hu0 : 0 ≤ u := le_trans (le_max_right _ _) hu.1
    have hcos : Real.cos (|l i| * u) = Real.cos (l i * u) := by
      rw [← Real.cos_abs (l i * u), abs_mul, abs_of_nonneg hu0]
    refine mem_iUnion.mpr ⟨i, subset_iUnion_Ioo_of_cos_gt (abs_pos.mpr (hl i)) ha0 haπ
      hu (by rw [hcos]; exact hi)⟩
  have hvol := measure_mono (μ := volume) hcover
  rw [Real.volume_Icc, show U' + T - U' = T by ring] at hvol
  have hsum := hvol.trans (measure_iUnion_fintype_le volume _)
  have hbound : ∑ i, volume (⋃ m ∈ Finset.Icc (⌊|l i| * U' / (2 * π)⌋ - 1)
      (⌈|l i| * (U' + T) / (2 * π)⌉ + 1),
        Ioo ((2 * π * m - a) / |l i|) ((2 * π * m + a) / |l i|)) ≤
      ENNReal.ofReal (∑ i, (|l i| * T / (2 * π) + 5) * (2 * a / |l i|)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have := abs_pos.mpr (hl i); positivity)]
    exact Finset.sum_le_sum fun i _ =>
      volume_iUnion_Ioo_le (abs_pos.mpr (hl i)) ha0 hT0.le
  have hlt : ∑ i, (|l i| * T / (2 * π) + 5) * (2 * a / |l i|) < T := by
    have hterm : ∀ i, (|l i| * T / (2 * π) + 5) * (2 * a / |l i|) =
        T * a / π + 10 * a * (1 / |l i|) := by
      intro i
      have := abs_pos.mpr (hl i)
      field_simp; ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    have hna : (n : ℝ) * (T * a / π) ≤ T / 4 := by
      rw [ha]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : (n : ℝ) * (T * (π / (4 * (n + 1))) / π) = T / 4 * (n / (n + 1)) := by
        field_simp
      rw [this]
      have : (n : ℝ) / (n + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    have : 10 * a * S < 3 * T / 4 := by rw [hT]; nlinarith
    linarith
  have := hsum.trans hbound
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  linarith

end RHTower
