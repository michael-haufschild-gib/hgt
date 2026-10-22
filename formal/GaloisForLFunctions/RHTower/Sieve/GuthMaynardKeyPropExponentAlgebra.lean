import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# The exponent algebra of Guth–Maynard §12

The proof of Proposition 3.1 (Guth–Maynard, §12) ends in the cubic inequality

`|W|³ N^{6σ−3} ⪅ N³ + |W|²N² + TN|W|^{2−1/k} + N²|W|^{2−3/(4k)}T^{1/(2k)} + T²|W|^{3/2}
                + T|W|N^{3−2σ} + T|W|²N^{3/2−σ} + T^{9/8}|W|^{29/16}N^{3/2−σ}`   (`cubicRHS`),

which "rearranges" to (12.1) (`fullBound`):

`|W| ⪅ N^{2−2σ} + N^{5−6σ} + T^{k/(k+1)}N^{(4−6σ)k/(k+1)} + N^{(5−6σ)4k/(4k+3)}T^{2/(4k+3)}
      + T^{4/3}N^{2−4σ} + T^{1/2}N^{3−4σ} + TN^{9/2−7σ} + T^{18/19}N^{72/19−112σ/19}`.

* `le_max_mul_sum_of_rpow_le` is the rearrangement: `x^p ≤ D Σ_i T^{α_i}N^{β_i}x^{e_i}` with
  `p − e_i ≥ 1` gives `x ≤ max(1, |s|D) Σ_i T^{α_i/(p−e_i)} N^{β_i/(p−e_i)}` (one term carries at
  least a `1/|s|` share of the sum; take its `(p − e_i)`-th root).
* `le_fullBound_of_cubic` is (12.1) with the explicit loss `max(1, 8D)`.
* With `k = 4` (more generally: second exponent `j = 4`, third exponent `k ≥ 2`) and
  `T = N^{6/5}`, each of the eight terms of (12.1) is at most `N^{(18−20σ)/5} = T N^{(12−20σ)/5}`
  for `σ ∈ [7/10, 8/10]`: the eight linear comparisons `keyExponent_one_le` …
  `keyExponent_eight_le` (the simplification at `T = N^{6/5}` in §12), assembled in `fullBound_le_keyBound` and
  `le_keyBound_of_cubic`.
-/

set_option autoImplicit false

open Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The monomial rearrangement -/

/-- `t^θ ≤ max(1, t)` for `t ≥ 0`, `θ ∈ [0, 1]`. -/
theorem rpow_le_max_one {t θ : ℝ} (ht : 0 ≤ t) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    t ^ θ ≤ max 1 t := by
  rcases le_total t 1 with h | h
  · exact (Real.rpow_le_one ht h hθ0).trans (le_max_left _ _)
  · exact (Real.rpow_le_rpow_of_exponent_le h hθ1).trans (by rw [Real.rpow_one]; exact le_max_right _ _)

/-- **Monomial rearrangement.**  If `x ≥ 0`, `D ≥ 0`, `T, N > 0`, `1 ≤ p − e_i` and
`x^p ≤ D Σ_{i∈s} T^{α_i} N^{β_i} x^{e_i}`, then
`x ≤ max(1, |s| D) Σ_{i∈s} T^{α_i/(p−e_i)} N^{β_i/(p−e_i)}`. -/
theorem le_max_mul_sum_of_rpow_le {ι : Type*} (s : Finset ι) {x p D T N : ℝ} (α β e : ι → ℝ)
    (hx : 0 ≤ x) (hD : 0 ≤ D) (hT : 0 < T) (hN : 0 < N) (he : ∀ i ∈ s, 1 ≤ p - e i)
    (h : x ^ p ≤ D * ∑ i ∈ s, T ^ α i * N ^ β i * x ^ e i) :
    x ≤ max 1 (s.card * D) * ∑ i ∈ s, T ^ (α i / (p - e i)) * N ^ (β i / (p - e i)) := by
  have hsum0 : 0 ≤ ∑ i ∈ s, T ^ (α i / (p - e i)) * N ^ (β i / (p - e i)) :=
    sum_nonneg fun i _ => by positivity
  have hmax : (1 : ℝ) ≤ max 1 (s.card * D) := le_max_left _ _
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0]; nlinarith
  -- `s` is nonempty since `x^p > 0`
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hpos p
  have hs : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with he' | hne
    · rw [he', sum_empty, mul_zero] at h; linarith
    · exact hne
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  -- one term carries a `1/|s|` share
  have hshare : ∑ i ∈ s, x ^ p / s.card ≤ ∑ i ∈ s, D * (T ^ α i * N ^ β i * x ^ e i) := by
    rw [sum_const, nsmul_eq_mul, ← mul_sum, mul_div_cancel₀ _ hn.ne']
    exact h
  obtain ⟨i, hi, hle⟩ := Finset.exists_le_of_sum_le hs hshare
  have hq : 0 < p - e i := by linarith [he i hi]
  have hxe : 0 < x ^ e i := Real.rpow_pos_of_pos hpos _
  have hTN : 0 ≤ T ^ α i * N ^ β i := by positivity
  -- `x^{p−e_i} ≤ |s| D T^{α_i} N^{β_i}`
  have hpe : x ^ (p - e i) ≤ s.card * D * (T ^ α i * N ^ β i) := by
    rw [Real.rpow_sub hpos, div_le_iff₀ hxe]
    rw [div_le_iff₀ hn] at hle
    nlinarith
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = (p - e i)⁻¹ := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := hθ ▸ inv_nonneg.mpr hq.le
  have hθ1 : θ ≤ 1 := hθ ▸ inv_le_one_of_one_le₀ (he i hi)
  have hroot : x ≤ (s.card * D) ^ θ * (T ^ (α i / (p - e i)) * N ^ (β i / (p - e i))) := by
    calc x = (x ^ (p - e i)) ^ θ := by rw [hθ, Real.rpow_rpow_inv hx hq.ne']
      _ ≤ (s.card * D * (T ^ α i * N ^ β i)) ^ θ :=
          Real.rpow_le_rpow (Real.rpow_nonneg hx _) hpe hθ0
      _ = _ := by
          rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ s.card * D) hTN,
            Real.mul_rpow (Real.rpow_nonneg hT.le (α i)) (Real.rpow_nonneg hN.le (β i)),
            ← Real.rpow_mul hT.le, ← Real.rpow_mul hN.le, hθ, div_eq_mul_inv, div_eq_mul_inv]
  have hterm : T ^ (α i / (p - e i)) * N ^ (β i / (p - e i)) ≤
      ∑ j ∈ s, T ^ (α j / (p - e j)) * N ^ (β j / (p - e j)) :=
    Finset.single_le_sum (f := fun j => T ^ (α j / (p - e j)) * N ^ (β j / (p - e j)))
      (fun j _ => by positivity) hi
  calc x ≤ (s.card * D) ^ θ * (T ^ (α i / (p - e i)) * N ^ (β i / (p - e i))) := hroot
    _ ≤ max 1 (s.card * D) * (T ^ (α i / (p - e i)) * N ^ (β i / (p - e i))) :=
        mul_le_mul_of_nonneg_right (rpow_le_max_one (by positivity) hθ0 hθ1) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hterm (by positivity)

/-! ### The cubic inequality and (12.1) -/

/-- The right-hand side of the cubic inequality for `|W|³ N^{6σ−3}` in the proof of
Proposition 3.1.  `j` and `k` are the exponents of the two `k`-dependent terms of
Proposition 6.1 (`j = k` in the paper). -/
def cubicRHS (W N T σ : ℝ) (j k : ℕ) : ℝ :=
  N ^ (3 : ℝ) + W ^ (2 : ℝ) * N ^ (2 : ℝ) + T * N * W ^ (2 - 1 / (j : ℝ)) +
    N ^ (2 : ℝ) * W ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) + T ^ (2 : ℝ) * W ^ (3 / 2 : ℝ) +
    T * W * N ^ (3 - 2 * σ) + T * W ^ (2 : ℝ) * N ^ (3 / 2 - σ) +
    T ^ (9 / 8 : ℝ) * W ^ (29 / 16 : ℝ) * N ^ (3 / 2 - σ)

/-- The right-hand side of Guth–Maynard (12.1) (`eq:FullBound`), with the exponents `j`, `k`. -/
def fullBound (N T σ : ℝ) (j k : ℕ) : ℝ :=
  N ^ (2 - 2 * σ) + N ^ (5 - 6 * σ) + T ^ ((j : ℝ) / (j + 1)) * N ^ ((4 - 6 * σ) * ((j : ℝ) / (j + 1))) +
    N ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)) +
    T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) + T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) + T * N ^ (9 / 2 - 7 * σ) +
    T ^ (18 / 19 : ℝ) * N ^ (72 / 19 - 112 * σ / 19)

/-- The `T`-exponents, `N`-exponents and `|W|`-exponents of the eight terms of `cubicRHS`. -/
def cubicTExp (k : ℕ) : Fin 8 → ℝ := ![0, 0, 1, 1 / (2 * (k : ℝ)), 2, 1, 1, 9 / 8]
def cubicNExp (σ : ℝ) : Fin 8 → ℝ := ![3, 2, 1, 2, 0, 3 - 2 * σ, 3 / 2 - σ, 3 / 2 - σ]
def cubicWExp (j k : ℕ) : Fin 8 → ℝ :=
  ![0, 2, 2 - 1 / (j : ℝ), 2 - 3 / (4 * (k : ℝ)), 3 / 2, 1, 2, 29 / 16]

theorem cubicRHS_eq_sum (W N T σ : ℝ) (j k : ℕ) :
    cubicRHS W N T σ j k = ∑ i, T ^ cubicTExp k i * N ^ cubicNExp σ i * W ^ cubicWExp j k i := by
  simp only [Fin.sum_univ_eight, cubicTExp, cubicNExp, cubicWExp, Matrix.cons_val, cubicRHS,
    Real.rpow_zero, Real.rpow_one]
  ring

/-- Every term of `cubicRHS` has `|W|`-exponent at most `2`. -/
theorem one_le_three_sub_cubicWExp {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) (i : Fin 8) :
    1 ≤ 3 - cubicWExp j k i := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 0 ≤ 1 / (j : ℝ) := by positivity
  have h2 : 0 ≤ 3 / (4 * (k : ℝ)) := by positivity
  have h3 : 0 ≤ (j : ℝ)⁻¹ := by positivity
  fin_cases i <;> simp [cubicWExp] <;> linarith

/-- The eight terms of (12.1), in the order of `cubicRHS`. -/
theorem sum_root_eq_fullBound (N T σ : ℝ) {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∑ i, T ^ (cubicTExp k i / (3 - cubicWExp j k i)) *
        N ^ ((cubicNExp σ i - (6 * σ - 3)) / (3 - cubicWExp j k i)) = fullBound N T σ j k := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk3 : 4 * (k : ℝ) + 3 ≠ 0 := by positivity
  have hd3 : 3 - (2 - 1 / (j : ℝ)) = ((j : ℝ) + 1) / j := by field_simp; ring
  have hd4 : 3 - (2 - 3 / (4 * (k : ℝ))) = (4 * (k : ℝ) + 3) / (4 * k) := by field_simp; ring
  simp only [Fin.sum_univ_eight, cubicTExp, cubicNExp, cubicWExp, Matrix.cons_val, fullBound]
  have e1 : T ^ ((0 : ℝ) / (3 - 0)) * N ^ ((3 - (6 * σ - 3)) / (3 - 0)) = N ^ (2 - 2 * σ) := by
    rw [zero_div, Real.rpow_zero, one_mul]; congr 1; ring
  have e2 : T ^ ((0 : ℝ) / (3 - 2)) * N ^ ((2 - (6 * σ - 3)) / (3 - 2)) = N ^ (5 - 6 * σ) := by
    rw [zero_div, Real.rpow_zero, one_mul]; congr 1; ring
  have e3 : T ^ ((1 : ℝ) / (3 - (2 - 1 / (j : ℝ)))) * N ^ ((1 - (6 * σ - 3)) / (3 - (2 - 1 / (j : ℝ))))
      = T ^ ((j : ℝ) / (j + 1)) * N ^ ((4 - 6 * σ) * ((j : ℝ) / (j + 1))) := by
    have x3 : (1 : ℝ) / (((j : ℝ) + 1) / j) = j / (j + 1) := by field_simp
    have y3 : (1 - (6 * σ - 3)) / (((j : ℝ) + 1) / j) = (4 - 6 * σ) * (j / (j + 1)) := by
      field_simp; ring
    rw [hd3, x3, y3]
  have e4 : T ^ (1 / (2 * (k : ℝ)) / (3 - (2 - 3 / (4 * (k : ℝ))))) *
      N ^ ((2 - (6 * σ - 3)) / (3 - (2 - 3 / (4 * (k : ℝ))))) =
      N ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3)) := by
    have x4 : 1 / (2 * (k : ℝ)) / ((4 * k + 3) / (4 * k)) = 2 / (4 * k + 3) := by
      field_simp; ring
    have y4 : (2 - (6 * σ - 3)) / ((4 * (k : ℝ) + 3) / (4 * k)) =
        (5 - 6 * σ) * (4 * k / (4 * k + 3)) := by
      field_simp; ring
    rw [mul_comm, hd4, x4, y4]
  have e5 : T ^ ((2 : ℝ) / (3 - 3 / 2)) * N ^ ((0 - (6 * σ - 3)) / (3 - 3 / 2)) =
      T ^ (4 / 3 : ℝ) * N ^ (2 - 4 * σ) := by
    congr 2 <;> ring
  have e6 : T ^ ((1 : ℝ) / (3 - 1)) * N ^ ((3 - 2 * σ - (6 * σ - 3)) / (3 - 1)) =
      T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * σ) := by
    congr 2 <;> ring
  have e7 : T ^ ((1 : ℝ) / (3 - 2)) * N ^ ((3 / 2 - σ - (6 * σ - 3)) / (3 - 2)) =
      T * N ^ (9 / 2 - 7 * σ) := by
    rw [show (1 : ℝ) / (3 - 2) = 1 by norm_num, Real.rpow_one]; congr 2; ring
  have e8 : T ^ ((9 / 8 : ℝ) / (3 - 29 / 16)) * N ^ ((3 / 2 - σ - (6 * σ - 3)) / (3 - 29 / 16)) =
      T ^ (18 / 19 : ℝ) * N ^ (72 / 19 - 112 * σ / 19) := by
    congr 2 <;> ring
  rw [e1, e2, e3, e4, e5, e6, e7, e8]

/-- **Guth–Maynard (12.1).**  If `|W|³ N^{6σ−3} ≤ D · cubicRHS` with `D ≥ 0`, `N, T > 0`,
`j, k ≥ 1`, then `|W| ≤ max(1, 8D) · fullBound`. -/
theorem le_fullBound_of_cubic {W N T σ D : ℝ} {j k : ℕ} (hW : 0 ≤ W) (hN : 0 < N) (hT : 0 < T)
    (hj : 1 ≤ j) (hk : 1 ≤ k) (hD : 0 ≤ D)
    (h : W ^ (3 : ℝ) * N ^ (6 * σ - 3) ≤ D * cubicRHS W N T σ j k) :
    W ≤ max 1 (8 * D) * fullBound N T σ j k := by
  -- divide out `N^{6σ−3}`
  have hsplit : ∀ i, T ^ cubicTExp k i * N ^ cubicNExp σ i * W ^ cubicWExp j k i =
      N ^ (6 * σ - 3) * (T ^ cubicTExp k i * N ^ (cubicNExp σ i - (6 * σ - 3)) *
        W ^ cubicWExp j k i) := fun i => by
    have : N ^ cubicNExp σ i = N ^ (6 * σ - 3) * N ^ (cubicNExp σ i - (6 * σ - 3)) := by
      rw [← Real.rpow_add hN]; congr 1; ring
    rw [this]; ring
  have hN0 : 0 < N ^ (6 * σ - 3) := Real.rpow_pos_of_pos hN _
  have h' : W ^ (3 : ℝ) ≤ D * ∑ i, T ^ cubicTExp k i * N ^ (cubicNExp σ i - (6 * σ - 3)) *
      W ^ cubicWExp j k i := by
    rw [cubicRHS_eq_sum, Finset.sum_congr rfl fun i _ => hsplit i, ← Finset.mul_sum] at h
    exact (mul_le_mul_iff_of_pos_right hN0).mp (by linarith : W ^ (3 : ℝ) * N ^ (6 * σ - 3) ≤
      (D * ∑ i, T ^ cubicTExp k i * N ^ (cubicNExp σ i - (6 * σ - 3)) * W ^ cubicWExp j k i) *
        N ^ (6 * σ - 3))
  have hr := le_max_mul_sum_of_rpow_le Finset.univ (cubicTExp k)
    (fun i => cubicNExp σ i - (6 * σ - 3)) (cubicWExp j k) hW hD hT hN
    (fun i _ => one_le_three_sub_cubicWExp hj hk i) h'
  rw [Finset.card_univ, Fintype.card_fin, sum_root_eq_fullBound N T σ hj hk] at hr
  simpa using hr

/-! ### The eight exponent comparisons (`j = 4`, `k ≥ 2`, `T = N^{6/5}`, `σ ∈ [7/10, 8/10]`)

Each term `T^a N^b` of (12.1) is `N^{6a/5 + b}`; the target is `T N^{(12−20σ)/5} = N^{(18−20σ)/5}`.
The paper takes `j = k = 4`; the fourth comparison holds for every `k ≥ 2` since its slack is
`(10σ − 7)(4k − 6) / (5(4k + 3))`. -/

theorem keyExponent_one_le {σ : ℝ} (h : σ ≤ 8 / 10) : 2 - 2 * σ ≤ (18 - 20 * σ) / 5 := by
  linarith

theorem keyExponent_two_le {σ : ℝ} (h : 7 / 10 ≤ σ) : 5 - 6 * σ ≤ (18 - 20 * σ) / 5 := by
  linarith

theorem keyExponent_three_le {σ : ℝ} (h : 7 / 10 ≤ σ) :
    6 / 5 * (4 / 5) + (4 - 6 * σ) * (4 / 5) ≤ (18 - 20 * σ) / 5 := by
  linarith

theorem keyExponent_four_le {σ k : ℝ} (h : 7 / 10 ≤ σ) (hk : 2 ≤ k) :
    6 / 5 * (2 / (4 * k + 3)) + (5 - 6 * σ) * (4 * k / (4 * k + 3)) ≤ (18 - 20 * σ) / 5 := by
  have hD : 0 < 4 * k + 3 := by linarith
  have e : 6 / 5 * (2 / (4 * k + 3)) + (5 - 6 * σ) * (4 * k / (4 * k + 3)) =
      (12 / 5 + (5 - 6 * σ) * (4 * k)) / (4 * k + 3) := by
    field_simp; ring
  rw [e, div_le_iff₀ hD]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 10 * σ - 7) (by linarith : (0 : ℝ) ≤ 4 * k - 6)]

theorem keyExponent_five_le (σ : ℝ) : 6 / 5 * (4 / 3) + (2 - 4 * σ) ≤ (18 - 20 * σ) / 5 := by
  linarith

theorem keyExponent_six_le (σ : ℝ) : 6 / 5 * (1 / 2) + (3 - 4 * σ) ≤ (18 - 20 * σ) / 5 := by
  linarith

theorem keyExponent_seven_le {σ : ℝ} (h : 7 / 10 ≤ σ) :
    6 / 5 * 1 + (9 / 2 - 7 * σ) ≤ (18 - 20 * σ) / 5 := by
  linarith

theorem keyExponent_eight_le {σ : ℝ} (h : 7 / 10 ≤ σ) :
    6 / 5 * (18 / 19) + (72 / 19 - 112 * σ / 19) ≤ (18 - 20 * σ) / 5 := by
  linarith

/-- `(N^{6/5})^a N^b ≤ N^c` for `N ≥ 1` and `6a/5 + b ≤ c`. -/
theorem monomial_le_of_exponent_le {N a b c : ℝ} (hN : 1 ≤ N) (h : 6 / 5 * a + b ≤ c) :
    (N ^ (6 / 5 : ℝ)) ^ a * N ^ b ≤ N ^ c := by
  have hN0 : 0 < N := by linarith
  rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
  exact Real.rpow_le_rpow_of_exponent_le hN h

/-- **(12.1) at `j = 4`, `k ≥ 2`, `T = N^{6/5}`.**  For `N ≥ 1` and `σ ∈ [7/10, 8/10]` every term
of (12.1) is at most `T N^{(12−20σ)/5}`. -/
theorem fullBound_le_keyBound {N σ : ℝ} {k : ℕ} (hN : 1 ≤ N) (h1 : 7 / 10 ≤ σ) (h2 : σ ≤ 8 / 10)
    (hk : 2 ≤ k) :
    fullBound N (N ^ (6 / 5 : ℝ)) σ 4 k ≤ 8 * (N ^ (6 / 5 : ℝ) * N ^ ((12 - 20 * σ) / 5)) := by
  have hN0 : 0 < N := by linarith
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have htarget : N ^ (6 / 5 : ℝ) * N ^ ((12 - 20 * σ) / 5) = N ^ ((18 - 20 * σ) / 5) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  rw [htarget]
  have hpure : ∀ b : ℝ, b ≤ (18 - 20 * σ) / 5 → N ^ b ≤ N ^ ((18 - 20 * σ) / 5) :=
    fun b hb => Real.rpow_le_rpow_of_exponent_le hN hb
  have t1 := hpure _ (keyExponent_one_le h2)
  have t2 := hpure _ (keyExponent_two_le h1)
  have t3 := monomial_le_of_exponent_le hN (keyExponent_three_le h1)
  have t4 := monomial_le_of_exponent_le hN (keyExponent_four_le h1 hk')
  have t5 := monomial_le_of_exponent_le hN (keyExponent_five_le σ)
  have t6 := monomial_le_of_exponent_le hN (keyExponent_six_le σ)
  have t7 := monomial_le_of_exponent_le hN (keyExponent_seven_le h1)
  have t8 := monomial_le_of_exponent_le hN (keyExponent_eight_le h1)
  rw [Real.rpow_one] at t7
  have e3 : ((4 : ℕ) : ℝ) / ((4 : ℕ) + 1) = 4 / 5 := by norm_num
  unfold fullBound
  rw [e3, mul_comm (N ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))))]
  linarith

/-- **Proposition 3.1 from the cubic inequality.**  If `|W|³ N^{6σ−3} ≤ D · cubicRHS` with
`j = 4`, `k ≥ 2`, `T = N^{6/5}`, `N ≥ 1`, `σ ∈ [7/10, 8/10]` and `D ≥ 0`, then
`|W| ≤ 8 max(1, 8D) · T N^{(12−20σ)/5}`. -/
theorem le_keyBound_of_cubic {W N σ D : ℝ} {k : ℕ} (hW : 0 ≤ W) (hN : 1 ≤ N) (h1 : 7 / 10 ≤ σ)
    (h2 : σ ≤ 8 / 10) (hk : 2 ≤ k) (hD : 0 ≤ D)
    (h : W ^ (3 : ℝ) * N ^ (6 * σ - 3) ≤ D * cubicRHS W N (N ^ (6 / 5 : ℝ)) σ 4 k) :
    W ≤ 8 * max 1 (8 * D) * (N ^ (6 / 5 : ℝ) * N ^ ((12 - 20 * σ) / 5)) := by
  have hN0 : 0 < N := by linarith
  have hb := le_fullBound_of_cubic hW hN0 (Real.rpow_pos_of_pos hN0 _) (by norm_num)
    (by omega) hD h
  have hf := fullBound_le_keyBound hN h1 h2 hk
  have hm : 0 ≤ max 1 (8 * D) := le_trans zero_le_one (le_max_left _ _)
  calc W ≤ max 1 (8 * D) * fullBound N (N ^ (6 / 5 : ℝ)) σ 4 k := hb
    _ ≤ max 1 (8 * D) * (8 * (N ^ (6 / 5 : ℝ) * N ^ ((12 - 20 * σ) / 5))) :=
        mul_le_mul_of_nonneg_left hf hm
    _ = _ := by ring

end

end RHTower.GuthMaynard
