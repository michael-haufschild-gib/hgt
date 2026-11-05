import Mathlib
import GaloisForLFunctions.ArithmeticDiscreteness.RealSatakeAnglesDefeatPolynomialRepulsion

/-!
# Generic Satake angles repel at polynomial scale

The failure of `RealSatakeAnglesDefeatPolynomialRepulsion` is exceptional. For Lebesgue-almost
every `x ∈ [0, 1]` the inhomogeneous forms `kξ − j ∓ x` (`ξ = log 3/log 2`) stay above `c/k²`
(`ae_inhomogeneous_gap`): the points within `(k+1)^{−2}` of `(k+1)ξ ∓ ℤ` have measure
`≤ 20/(k+1)²` (`volume_badSet_le`), a summable sequence, so by Borel–Cantelli almost every `x`
lies in only finitely many of them; the finitely many small `k` are handled by excluding the
countable set `ξℕ ± ℤ`.

So polynomial repulsion of the real pure carriers holds for almost every Satake angle; it fails on
a null set of Liouville-type angles, and integrality of the local data (Kronecker torsion) is a
certificate that the angle is not of that type.
-/

open MeasureTheory Filter Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The bad set at step `k`: points `x ∈ [0, 1]` with `(k+1)ξ ∓ x` within `(k+1)^{−2}` of an
integer. -/
def badSet (ξ : ℝ) (k : ℕ) : Set ℝ :=
  {x | x ∈ Icc (0 : ℝ) 1 ∧ ∃ j : ℤ, (|((k : ℝ) + 1) * ξ - j - x| < 1 / ((k : ℝ) + 1) ^ 2 ∨
    |((k : ℝ) + 1) * ξ - j + x| < 1 / ((k : ℝ) + 1) ^ 2)}

theorem volume_badSet_le (ξ : ℝ) (k : ℕ) :
    volume (badSet ξ k) ≤ ENNReal.ofReal (20 / ((k : ℝ) + 1) ^ 2) := by
  classical
  set c : ℝ := ((k : ℝ) + 1) * ξ with hc
  set r : ℝ := 1 / ((k : ℝ) + 1) ^ 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    nlinarith
  set S : Finset ℤ := Finset.Icc (⌊c⌋ - 2) (⌊c⌋ + 2) with hS
  have hsub : badSet ξ k ⊆ ⋃ j ∈ S, (Ioo (c - j - r) (c - j + r) ∪ Ioo (j - c - r) (j - c + r)) := by
    rintro x ⟨⟨hx0, hx1⟩, j, hj⟩
    have hfl := Int.floor_le c
    have hfl' := Int.lt_floor_add_one c
    refine mem_iUnion₂.mpr ⟨j, ?_, ?_⟩
    · rw [hS, Finset.mem_Icc]
      rcases hj with h | h
      · obtain ⟨h1, h2⟩ := abs_lt.mp h
        have hlo : (⌊c⌋ : ℝ) - 3 < j := by linarith
        have hhi : (j : ℝ) < ⌊c⌋ + 2 := by linarith
        constructor
        · have : ⌊c⌋ - 3 < j := by exact_mod_cast hlo
          omega
        · have : j < ⌊c⌋ + 2 := by exact_mod_cast hhi
          omega
      · obtain ⟨h1, h2⟩ := abs_lt.mp h
        have hlo : (⌊c⌋ : ℝ) - 2 < j := by linarith
        have hhi : (j : ℝ) < ⌊c⌋ + 3 := by linarith
        constructor
        · have : ⌊c⌋ - 2 < j := by exact_mod_cast hlo
          omega
        · have : j < ⌊c⌋ + 3 := by exact_mod_cast hhi
          omega
    · rcases hj with h | h
      · obtain ⟨h1, h2⟩ := abs_lt.mp h
        exact Or.inl ⟨by linarith, by linarith⟩
      · obtain ⟨h1, h2⟩ := abs_lt.mp h
        exact Or.inr ⟨by linarith, by linarith⟩
  have hcard : S.card = 5 := by rw [hS, Int.card_Icc]; omega
  calc volume (badSet ξ k)
      ≤ volume (⋃ j ∈ S, (Ioo (c - j - r) (c - j + r) ∪ Ioo (j - c - r) (j - c + r))) :=
        measure_mono hsub
    _ ≤ ∑ j ∈ S, volume (Ioo (c - j - r) (c - j + r) ∪ Ioo (j - c - r) (j - c + r)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ S, ENNReal.ofReal (4 * r) := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (measure_union_le _ _).trans ?_
        rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_add (by linarith) (by linarith)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (20 / ((k : ℝ) + 1) ^ 2) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat,
          ← ENNReal.ofReal_ofNat 5, ← ENNReal.ofReal_mul (by norm_num), hr]
        congr 1; ring

theorem tsum_volume_badSet_ne_top (ξ : ℝ) : ∑' k, volume (badSet ξ k) ≠ ⊤ := by
  have hsum : Summable fun k : ℕ => 20 / ((k : ℝ) + 1) ^ 2 := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    have h' := h.mul_left 20
    refine h'.congr fun k => ?_
    push_cast; ring
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun k => volume_badSet_le ξ k)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
  exact ENNReal.ofReal_ne_top

/-- **Almost every `x ∈ [0, 1]` is badly approximable by `ξℕ ± ℤ`.** For almost every `x` with
`0 ≤ x ≤ 1` there is `c > 0` with `c/(k+1)² ≤ |(k+1)ξ − j ∓ x|` for all `k ∈ ℕ`, `j ∈ ℤ`. -/
theorem ae_inhomogeneous_gap (ξ : ℝ) :
    ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → ∃ c > 0, ∀ k : ℕ, ∀ j : ℤ,
      c / ((k : ℝ) + 1) ^ 2 ≤ |((k : ℝ) + 1) * ξ - j - x| ∧
        c / ((k : ℝ) + 1) ^ 2 ≤ |((k : ℝ) + 1) * ξ - j + x| := by
  classical
  -- the countable exceptional set `ξℕ ± ℤ`
  set E : Set ℝ := ⋃ k : ℕ, ⋃ j : ℤ, ({((k : ℝ) + 1) * ξ - j} ∪ {(j : ℝ) - ((k : ℝ) + 1) * ξ})
    with hE
  have hEc : E.Countable :=
    countable_iUnion fun k => countable_iUnion fun j => (countable_singleton _).union
      (countable_singleton _)
  have hE0 : ∀ᵐ x : ℝ, x ∉ E := (measure_eq_zero_iff_ae_notMem).mp (hEc.measure_zero volume)
  filter_upwards [ae_eventually_notMem (tsum_volume_badSet_ne_top ξ), hE0] with x hx hxE hxI
  obtain ⟨K, hK⟩ := eventually_atTop.mp hx
  -- the gap of `(k+1)ξ ∓ x` to the integers, positive off `E`
  set g : ℕ → ℝ := fun k =>
    min |((k : ℝ) + 1) * ξ - x - round (((k : ℝ) + 1) * ξ - x)|
      |((k : ℝ) + 1) * ξ + x - round (((k : ℝ) + 1) * ξ + x)| with hg
  have hgpos : ∀ k, 0 < g k := by
    intro k
    refine lt_min (abs_pos.mpr fun h0 => hxE ?_) (abs_pos.mpr fun h0 => hxE ?_)
    · refine mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨round (((k : ℝ) + 1) * ξ - x), Or.inl ?_⟩⟩
      rw [mem_singleton_iff]; linarith
    · refine mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨round (((k : ℝ) + 1) * ξ + x), Or.inr ?_⟩⟩
      rw [mem_singleton_iff]; linarith
  have hglow : ∀ k : ℕ, ∀ j : ℤ, g k ≤ |((k : ℝ) + 1) * ξ - j - x| ∧
      g k ≤ |((k : ℝ) + 1) * ξ - j + x| := by
    intro k j
    constructor
    · refine (min_le_left _ _).trans ?_
      have := round_le (((k : ℝ) + 1) * ξ - x) j
      rwa [show ((k : ℝ) + 1) * ξ - x - j = ((k : ℝ) + 1) * ξ - j - x by ring] at this
    · refine (min_le_right _ _).trans ?_
      have := round_le (((k : ℝ) + 1) * ξ + x) j
      rwa [show ((k : ℝ) + 1) * ξ + x - j = ((k : ℝ) + 1) * ξ - j + x by ring] at this
  -- `c = ∏_{k<K} min 1 ((k+1)² g k)`
  set φ : ℕ → ℝ := fun k => min 1 (((k : ℝ) + 1) ^ 2 * g k) with hφ
  have hφpos : ∀ k, 0 < φ k := fun k => lt_min one_pos (by have := hgpos k; positivity)
  have hφle : ∀ k, φ k ≤ 1 := fun k => min_le_left _ _
  set c : ℝ := ∏ k ∈ Finset.range K, φ k with hc
  have hc0 : 0 < c := Finset.prod_pos fun k _ => hφpos k
  have hc1 : c ≤ 1 := Finset.prod_le_one (fun k _ => (hφpos k).le) fun k _ => hφle k
  have hck : ∀ k < K, c ≤ ((k : ℝ) + 1) ^ 2 * g k := by
    intro k hk
    have hmem : k ∈ Finset.range K := Finset.mem_range.mpr hk
    rw [hc, ← Finset.mul_prod_erase _ _ hmem]
    have hrest : ∏ i ∈ (Finset.range K).erase k, φ i ≤ 1 :=
      Finset.prod_le_one (fun i _ => (hφpos i).le) fun i _ => hφle i
    calc φ k * ∏ i ∈ (Finset.range K).erase k, φ i ≤ φ k * 1 :=
          mul_le_mul_of_nonneg_left hrest (hφpos k).le
      _ ≤ ((k : ℝ) + 1) ^ 2 * g k := by rw [mul_one]; exact min_le_right _ _
  refine ⟨c, hc0, fun k j => ?_⟩
  have hk2 : 0 < ((k : ℝ) + 1) ^ 2 := by positivity
  by_cases hkK : K ≤ k
  · -- not in the bad set: the gap is at least `1/(k+1)²`
    have hnot := hK k hkK
    have hb : ¬ (|((k : ℝ) + 1) * ξ - j - x| < 1 / ((k : ℝ) + 1) ^ 2 ∨
        |((k : ℝ) + 1) * ξ - j + x| < 1 / ((k : ℝ) + 1) ^ 2) := fun h => hnot ⟨hxI, j, h⟩
    push Not at hb
    have hcd : c / ((k : ℝ) + 1) ^ 2 ≤ 1 / ((k : ℝ) + 1) ^ 2 :=
      div_le_div_of_nonneg_right hc1 hk2.le
    exact ⟨hcd.trans hb.1, hcd.trans hb.2⟩
  · push Not at hkK
    have h := hck k hkK
    have hcd : c / ((k : ℝ) + 1) ^ 2 ≤ g k := by rw [div_le_iff₀ hk2]; linarith
    exact ⟨hcd.trans (hglow k j).1, hcd.trans (hglow k j).2⟩

/-! ### The zeros of the real pure carrier -/

open Complex in
/-- **The zeros of `(1 − 2^{−s})(1 − 2cos θ · 3^{−s} + 3^{−2s})`** are the points `iy` with
`y = 2πk/log 2` or `y = (εθ + 2πj)/log 3`, `ε = ±1`. -/
theorem realPureCarrier_zero_ordinate (θ : ℝ) {s : ℂ} (hs : realPureCarrier θ s = 0) :
    ∃ y : ℝ, s = (y : ℂ) * I ∧ ((∃ k : ℤ, y = 2 * Real.pi * k / Real.log 2) ∨
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∃ j : ℤ, y = (ε * θ + 2 * Real.pi * j) / Real.log 3) := by
  have hl3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hl3c : ((Real.log 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl3
  unfold realPureCarrier at hs
  rcases mul_eq_zero.mp hs with h1 | h2
  · have h1' : 1 - ((2 : ℕ) : ℂ) ^ (-s) = 0 := by push_cast; exact h1
    obtain ⟨k, rfl⟩ := (one_sub_cpow_neg_eq_zero_iff (by norm_num) s).mp h1'
    exact ⟨2 * Real.pi * k / Real.log 2, by simp [colPt], Or.inl ⟨k, by ring⟩⟩
  · -- `1 − 2cos θ w + w² = (w − e^{iθ})(w − e^{−iθ})`
    set w := (3 : ℂ) ^ (-s) with hw
    have hcos : ((2 * Real.cos θ : ℝ) : ℂ) = Complex.exp (θ * I) + Complex.exp (-(θ * I)) := by
      push_cast; rw [← Complex.ofReal_cos, ← neg_mul, ← Complex.two_cos]; push_cast; ring
    have hprod : Complex.exp (θ * I) * Complex.exp (-(θ * I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hfac : (w - Complex.exp (θ * I)) * (w - Complex.exp (-(θ * I))) = 0 := by
      rw [hcos] at h2; linear_combination h2 + hprod
    have hsolve : ∀ φ : ℝ, w = Complex.exp (φ * I) →
        ∃ j : ℤ, s = (((-φ + 2 * Real.pi * j) / Real.log 3 : ℝ) : ℂ) * I := by
      intro φ hφ
      rw [hw, cpow_def_of_ne_zero (by norm_num), show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_log (by norm_num)] at hφ
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hφ
      refine ⟨-n, ?_⟩
      push_cast
      field_simp
      linear_combination -hn
    rcases mul_eq_zero.mp hfac with h | h
    · obtain ⟨j, hj⟩ := hsolve θ (sub_eq_zero.mp h)
      exact ⟨_, hj, Or.inr ⟨-1, Or.inr rfl, j, by push_cast; ring⟩⟩
    · obtain ⟨j, hj⟩ := hsolve (-θ) (by rw [sub_eq_zero.mp h]; push_cast; ring_nf)
      exact ⟨_, hj, Or.inr ⟨1, Or.inl rfl, j, by push_cast; ring⟩⟩

/-- The mixed distance is an inhomogeneous linear form. -/
theorem mixed_ordinate_sub (x : ℝ) (k j ε : ℤ) :
    2 * Real.pi * k / Real.log 2 - (ε * (2 * Real.pi * x) + 2 * Real.pi * j) / Real.log 3 =
      2 * Real.pi / Real.log 3 * (k * (Real.log 3 / Real.log 2) - j - ε * x) := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hl3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp
  ring

open Complex in
/-- **Generic Satake angles repel at polynomial scale.** For almost every `x ∈ [0, 1]` there is
`C > 0` such that, with `θ = 2πx`, distinct zeros of the pure carrier
`(1 − 2^{−s})(1 − 2cos θ · 3^{−s} + 3^{−2s})` of height at most `T ≥ 1` are at distance
`≥ C/T²`. -/
theorem ae_realPureCarrier_repulsion :
    ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → ∃ C > 0, ∀ T : ℝ, 1 ≤ T → ∀ ρ ρ' : ℂ,
      realPureCarrier (2 * Real.pi * x) ρ = 0 → realPureCarrier (2 * Real.pi * x) ρ' = 0 →
        |ρ.im| ≤ T → |ρ'.im| ≤ T → ρ ≠ ρ' → C / T ^ 2 ≤ ‖ρ - ρ'‖ := by
  set ξ := Real.log 3 / Real.log 2 with hξ
  -- the countable set `x ∈ ½ℤ`
  have hhalf : ∀ᵐ x : ℝ, x ∉ ⋃ m : ℤ, ({(m : ℝ) / 2} : Set ℝ) :=
    (measure_eq_zero_iff_ae_notMem).mp
      ((countable_iUnion fun _ => countable_singleton _).measure_zero volume)
  filter_upwards [ae_inhomogeneous_gap ξ, hhalf] with x hgap hx2 hxI
  obtain ⟨c, hc0, hc⟩ := hgap hxI
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  -- `d = dist(2x, ℤ) > 0`
  set d : ℝ := |2 * x - round (2 * x)| with hd
  have hd0 : 0 < d := by
    refine abs_pos.mpr fun h0 => hx2 (mem_iUnion.mpr ⟨round (2 * x), ?_⟩)
    rw [mem_singleton_iff]; linarith
  have hdle : ∀ m : ℤ, d ≤ |2 * x + m| := fun m => by
    have := round_le (2 * x) (-m); push_cast at this; rwa [sub_neg_eq_add] at this
  -- the mixed gap
  have hmixed : ∀ k j ε : ℤ, (ε = 1 ∨ ε = -1) →
      min (d / 2) (c / ((k : ℝ) ^ 2 + 1)) ≤ |(k : ℝ) * ξ - j - ε * x| := by
    intro k j ε hε
    rcases lt_trichotomy k 0 with hk | hk | hk
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, -k = (n : ℤ) + 1 := ⟨(-k - 1).toNat, by omega⟩
      have hkr : (k : ℝ) = -((n : ℝ) + 1) := by
        have : ((-k : ℤ) : ℝ) = ((n : ℤ) + 1 : ℤ) := by rw [hn]
        push_cast at this; linarith
      have hcd : c / ((k : ℝ) ^ 2 + 1) ≤ c / ((n : ℝ) + 1) ^ 2 := by
        rw [hkr, neg_sq]
        exact div_le_div_of_nonneg_left hc0.le (by positivity) (by linarith)
      refine (min_le_right _ _).trans (hcd.trans ?_)
      rw [hkr]
      rcases hε with rfl | rfl
      · have e : -((n : ℝ) + 1) * ξ - j - ((1 : ℤ) : ℝ) * x =
            -(((n : ℝ) + 1) * ξ - ((-j : ℤ) : ℝ) + x) := by push_cast; ring
        rw [e, abs_neg]; exact (hc n (-j)).2
      · have e : -((n : ℝ) + 1) * ξ - j - ((-1 : ℤ) : ℝ) * x =
            -(((n : ℝ) + 1) * ξ - ((-j : ℤ) : ℝ) - x) := by push_cast; ring
        rw [e, abs_neg]; exact (hc n (-j)).1
    · have hk0 : (k : ℝ) = 0 := by exact_mod_cast hk
      rw [hk0, zero_mul, zero_sub]
      refine (min_le_left _ _).trans ?_
      rcases hε with rfl | rfl
      · have e : -(j : ℝ) - ((1 : ℤ) : ℝ) * x = -(2 * x + ((2 * j : ℤ) : ℝ)) / 2 := by
          push_cast; ring
        rw [e, abs_div, abs_neg, abs_two]; linarith [hdle (2 * j)]
      · have e : -(j : ℝ) - ((-1 : ℤ) : ℝ) * x = (2 * x + ((-(2 * j) : ℤ) : ℝ)) / 2 := by
          push_cast; ring
        rw [e, abs_div, abs_two]; linarith [hdle (-(2 * j))]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
      have hkr : (k : ℝ) = (n : ℝ) + 1 := by rw [hn]; push_cast; ring
      have hcd : c / ((k : ℝ) ^ 2 + 1) ≤ c / ((n : ℝ) + 1) ^ 2 := by
        rw [hkr]; exact div_le_div_of_nonneg_left hc0.le (by positivity) (by linarith)
      refine (min_le_right _ _).trans (hcd.trans ?_)
      rw [hkr]
      rcases hε with rfl | rfl
      · have e : ((n : ℝ) + 1) * ξ - j - ((1 : ℤ) : ℝ) * x = ((n : ℝ) + 1) * ξ - j - x := by
          push_cast; ring
        rw [e]; exact (hc n j).1
      · have e : ((n : ℝ) + 1) * ξ - j - ((-1 : ℤ) : ℝ) * x = ((n : ℝ) + 1) * ξ - j + x := by
          push_cast; ring
        rw [e]; exact (hc n j).2
  -- constants
  set B : ℝ := 2 * Real.pi / Real.log 2 with hB
  set A : ℝ := 2 * Real.pi / Real.log 3 with hA
  have hB0 : 0 < B := by positivity
  have hA0 : 0 < A := by positivity
  set K : ℝ := 1 / B ^ 2 + 1 with hK
  have hK0 : 0 < K := by positivity
  set m : ℝ := min (d / 2) (c / K) with hm
  have hm0 : 0 < m := lt_min (by positivity) (by positivity)
  refine ⟨min B (min A (min (A * d) (A * m))), lt_min hB0 (lt_min hA0 (lt_min (by positivity)
    (by positivity))), fun T hT ρ ρ' hρ hρ' hT1 hT2 hne => ?_⟩
  have hT0 : 0 < T := by linarith
  have hT2' : 1 ≤ T ^ 2 := by nlinarith
  have hCT : ∀ v : ℝ, 0 ≤ v → min B (min A (min (A * d) (A * m))) ≤ v →
      min B (min A (min (A * d) (A * m))) / T ^ 2 ≤ v := fun v hv h =>
    (div_le_self (lt_min hB0 (lt_min hA0 (lt_min (by positivity) (by positivity)))).le hT2').trans h
  obtain ⟨y, rfl, hy⟩ := realPureCarrier_zero_ordinate _ hρ
  obtain ⟨y', rfl, hy'⟩ := realPureCarrier_zero_ordinate _ hρ'
  have hyne : y ≠ y' := fun h => hne (by rw [h])
  have hnorm : ‖(y : ℂ) * I - (y' : ℂ) * I‖ = |y - y'| := by
    rw [← sub_mul, ← ofReal_sub, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  have him : ∀ z : ℝ, |((z : ℂ) * I).im| = |z| := fun z => by simp
  rw [him] at hT1 hT2
  rw [hnorm]
  -- the mixed case, in either order
  have hmix : ∀ (k j ε : ℤ), (ε = 1 ∨ ε = -1) → |2 * Real.pi * k / Real.log 2| ≤ T →
      min B (min A (min (A * d) (A * m))) / T ^ 2 ≤
        |2 * Real.pi * k / Real.log 2 - (ε * (2 * Real.pi * x) + 2 * Real.pi * j) / Real.log 3| := by
    intro k j ε hε hkT
    rw [mixed_ordinate_sub, ← hξ, abs_mul, abs_of_pos hA0]
    have hkb : B * |(k : ℝ)| ≤ T := by
      have e : 2 * Real.pi * k / Real.log 2 = B * k := by rw [hB]; ring
      rw [e, abs_mul, abs_of_pos hB0] at hkT; exact hkT
    have hk2 : (k : ℝ) ^ 2 + 1 ≤ T ^ 2 * K := by
      have h1 : |(k : ℝ)| ≤ T / B := by rw [le_div_iff₀ hB0]; linarith [hkb]
      have h2 : (k : ℝ) ^ 2 ≤ (T / B) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h3 : (T / B) ^ 2 = T ^ 2 * (1 / B ^ 2) := by ring
      rw [hK]; nlinarith
    have hlow := hmixed k j ε hε
    have hmT : m / T ^ 2 ≤ min (d / 2) (c / ((k : ℝ) ^ 2 + 1)) := by
      refine le_min ((div_le_self (by positivity) hT2').trans (min_le_left _ _)) ?_
      calc m / T ^ 2 ≤ (c / K) / T ^ 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = c / (T ^ 2 * K) := by rw [div_div, mul_comm]
        _ ≤ c / ((k : ℝ) ^ 2 + 1) := div_le_div_of_nonneg_left hc0.le (by positivity) hk2
    calc min B (min A (min (A * d) (A * m))) / T ^ 2 ≤ A * m / T ^ 2 :=
          div_le_div_of_nonneg_right ((min_le_right _ _).trans ((min_le_right _ _).trans
            (min_le_right _ _))) (by positivity)
      _ = A * (m / T ^ 2) := by ring
      _ ≤ A * |(k : ℝ) * ξ - j - ε * x| :=
          mul_le_mul_of_nonneg_left (hmT.trans hlow) hA0.le
  rcases hy with ⟨k, rfl⟩ | ⟨ε, hε, j, rfl⟩ <;> rcases hy' with ⟨k', rfl⟩ | ⟨ε', hε', j', rfl⟩
  · -- two column points
    have hkk : k ≠ k' := fun h => hyne (by rw [h])
    refine hCT _ (abs_nonneg _) ((min_le_left _ _).trans ?_)
    have : 2 * Real.pi * k / Real.log 2 - 2 * Real.pi * k' / Real.log 2 = B * (k - k') := by
      rw [hB]; ring
    rw [this, abs_mul, abs_of_pos hB0]
    have : (1 : ℝ) ≤ |(k : ℝ) - k'| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkk)
    nlinarith
  · exact hmix k j' ε' hε' hT1
  · rw [abs_sub_comm]; exact hmix k' j ε hε hT2
  · -- two points of the second factor
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl
    · have hjj : j ≠ j' := fun h => hyne (by rw [h])
      refine hCT _ (abs_nonneg _) ((min_le_right _ _).trans ((min_le_left _ _).trans ?_))
      have : (((1 : ℤ) : ℝ) * (2 * Real.pi * x) + 2 * Real.pi * j) / Real.log 3 -
          (((1 : ℤ) : ℝ) * (2 * Real.pi * x) + 2 * Real.pi * j') / Real.log 3 = A * (j - j') := by
        rw [hA]; push_cast; ring
      rw [this, abs_mul, abs_of_pos hA0]
      have : (1 : ℝ) ≤ |(j : ℝ) - j'| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hjj)
      nlinarith
    · refine hCT _ (abs_nonneg _) ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_left _ _).trans ?_)))
      have : (((1 : ℤ) : ℝ) * (2 * Real.pi * x) + 2 * Real.pi * j) / Real.log 3 -
          (((-1 : ℤ) : ℝ) * (2 * Real.pi * x) + 2 * Real.pi * j') / Real.log 3 =
            A * (2 * x + ((j - j' : ℤ) : ℝ)) := by
        rw [hA]; push_cast; ring
      rw [this, abs_mul, abs_of_pos hA0]
      exact mul_le_mul_of_nonneg_left (hdle _) hA0.le
    · refine hCT _ (abs_nonneg _) ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_left _ _).trans ?_)))
      have : (((-1 : ℤ) : ℝ) * (2 * Real.pi * x) + 2 * Real.pi * j) / Real.log 3 -
          (((1 : ℤ) : ℝ) * (2 * Real.pi * x) + 2 * Real.pi * j') / Real.log 3 =
            -(A * (2 * x + ((j' - j : ℤ) : ℝ))) := by
        rw [hA]; push_cast; ring
      rw [this, abs_neg, abs_mul, abs_of_pos hA0]
      exact mul_le_mul_of_nonneg_left (hdle _) hA0.le
    · have hjj : j ≠ j' := fun h => hyne (by rw [h])
      refine hCT _ (abs_nonneg _) ((min_le_right _ _).trans ((min_le_left _ _).trans ?_))
      have : (((-1 : ℤ) : ℝ) * (2 * Real.pi * x) + 2 * Real.pi * j) / Real.log 3 -
          (((-1 : ℤ) : ℝ) * (2 * Real.pi * x) + 2 * Real.pi * j') / Real.log 3 = A * (j - j') := by
        rw [hA]; push_cast; ring
      rw [this, abs_mul, abs_of_pos hA0]
      have : (1 : ℝ) ≤ |(j : ℝ) - j'| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hjj)
      nlinarith

end GaloisForLFunctions.ArithmeticDiscreteness
