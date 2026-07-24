import GaloisForLFunctions.RHTower.PsiRemainderGainWindow
import GaloisForLFunctions.RHTower.WindowHarmonicSharpBounds

/-!
# The per-block σ-contraction

On a ladder block `(Y, 2QY]`, given the uniform ratio `a` above `x₀ ≤ Y`,
the harmonically weighted remainder mass improves on the trivial bound by
a fixed amount per block:

`∑_{Y < n ≤ 2QY} |R(n)|(1/n − 1/(n+1))
   ≤ a·(log(2QY) − log Y) − (a − ε')·ρ/3 + 6a/Y`,

where `ε' = δ + ρ(log(1/ρ) + 3) + κ ≤ a`: the gain window supplied by
`exists_pointwise_small_window` occupies log-length `≥ ρ/3` (the floor
loss is half the window once `Y ≥ 2/ρ`), carries ratio `ε'` (the additive
junk absorbed by `κ·t`), and the sharp harmonic window bounds price all
three sub-blocks with total boundary error `6a/Y` — summable along a
geometric ladder.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

set_option maxHeartbeats 1000000 in
theorem sigma_block_contraction {a δ ρ κ : ℝ} {Y Q x₀ : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hY1 : 1 ≤ Y) (hQ1 : 1 ≤ Q)
    (hQ : 40 / δ + 2 < Real.log Q)
    (hx₀Y : x₀ ≤ Y) (hYρ : 2 / ρ ≤ (Y : ℝ))
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a)
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t)
    (hjunk : ∀ t : ℕ, Y < t →
      Real.log ((Q * Y : ℕ) : ℝ) + 1 + 2 * Real.sqrt t * Real.log t
        ≤ κ * t) :
    ∑ n ∈ Finset.Ioc Y (2 * Q * Y),
        |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      ≤ a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log Y)
        - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
        + a * (6 / Y) := by
  set ε' : ℝ := δ + ρ * (Real.log (1 / ρ) + 3) + κ with hε'
  have hε'0 : 0 ≤ ε' := by
    have hρlog0 : 0 ≤ Real.log (1 / ρ) :=
      Real.log_nonneg (by
        rw [le_div_iff₀ hρ0, one_mul]
        linarith)
    rw [hε']
    positivity
  -- the gain window
  obtain ⟨m₀, hm₀Y, hm₀QY, hpoint⟩ :=
    exists_pointwise_small_window hδ hρ0 (by linarith) hY1 hQ1 hQ
  set w : ℕ := m₀ + Nat.floor (ρ * m₀) with hw
  have hYR : (2 : ℝ) ≤ ρ * Y := by
    rw [div_le_iff₀ hρ0] at hYρ
    linarith
  have hm₀R : (Y : ℝ) < m₀ := by exact_mod_cast hm₀Y
  have hρm₀2 : (2 : ℝ) ≤ ρ * m₀ := by nlinarith [hYR, hm₀R, hρ0]
  have hfloor_ge : (ρ * m₀) / 2 ≤ (Nat.floor (ρ * m₀) : ℝ) := by
    have h1 : (ρ * m₀) - 1 ≤ (Nat.floor (ρ * m₀) : ℝ) := by
      have := Nat.sub_one_lt_floor (ρ * m₀)
      linarith
    linarith
  have hfloor_le : (Nat.floor (ρ * m₀) : ℝ) ≤ ρ * m₀ :=
    Nat.floor_le (by positivity)
  have hwR_ge : (1 + ρ / 2) * m₀ ≤ (w : ℝ) := by
    rw [hw]
    push_cast
    linarith [hfloor_ge]
  have hwR_le : (w : ℝ) ≤ (1 + ρ) * m₀ := by
    rw [hw]
    push_cast
    linarith [hfloor_le]
  have hm₀w : m₀ ≤ w := by omega
  have hw2QY : w ≤ 2 * Q * Y := by
    have h1 : (w : ℝ) ≤ (3 / 2 : ℝ) * (Q * Y) := by
      have h2 : (m₀ : ℝ) ≤ (Q * Y : ℕ) := by exact_mod_cast hm₀QY
      push_cast at h2 ⊢
      nlinarith [hwR_le, hρ1, h2, hm₀R,
        (by exact_mod_cast hY1 : (1:ℝ) ≤ Y)]
    have h3 : ((3 / 2 : ℝ)) * (Q * Y) ≤ ((2 * Q * Y : ℕ) : ℝ) := by
      push_cast
      nlinarith [(by exact_mod_cast hQ1 : (1:ℝ) ≤ Q),
        (by exact_mod_cast hY1 : (1:ℝ) ≤ Y)]
    exact_mod_cast le_trans h1 h3
  have hm₀1 : 1 ≤ m₀ := by omega
  have hw1 : 1 ≤ w := by omega
  -- pointwise ratio on the three sub-blocks
  have hpart1 : ∀ n ∈ Finset.Ioc Y m₀,
      |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ a * (1 / ((n : ℝ) + 1)) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hR := hratio n (by omega)
    have hnw : (n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        = 1 / ((n : ℝ) + 1) := by
      field_simp
      ring
    have hwpos : (0 : ℝ) ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
      rw [sub_nonneg]
      apply div_le_div_of_nonneg_left one_pos.le hn0
      linarith
    calc |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ (a * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hR hwpos
      _ = a * ((n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by ring
      _ = a * (1 / ((n : ℝ) + 1)) := by rw [hnw]
  have hpart2 : ∀ n ∈ Finset.Ioc m₀ w,
      |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ ε' * (1 / ((n : ℝ) + 1)) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnρ : (n : ℝ) ≤ (1 + ρ) * m₀ := by
      have : (n : ℝ) ≤ w := by exact_mod_cast hn.2
      linarith [hwR_le]
    have hpt := hpoint n (by omega) hnρ
    have hj := hjunk n (by omega)
    have hR : |psiRemainder n| ≤ ε' * n := by
      rw [hε']
      calc |psiRemainder n|
          ≤ (δ + ρ * (Real.log (1 / ρ) + 3)) * n
            + (Real.log ((Q * Y : ℕ) : ℝ) + 1)
            + 2 * Real.sqrt n * Real.log n := by
            linarith [hpt]
        _ ≤ (δ + ρ * (Real.log (1 / ρ) + 3)) * n + κ * n := by
            linarith [hj]
        _ = (δ + ρ * (Real.log (1 / ρ) + 3) + κ) * n := by ring
    have hnw : (n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        = 1 / ((n : ℝ) + 1) := by
      field_simp
      ring
    have hwpos : (0 : ℝ) ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
      rw [sub_nonneg]
      apply div_le_div_of_nonneg_left one_pos.le hn0
      linarith
    calc |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ (ε' * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hR hwpos
      _ = ε' * ((n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by ring
      _ = ε' * (1 / ((n : ℝ) + 1)) := by rw [hnw]
  have hpart3 : ∀ n ∈ Finset.Ioc w (2 * Q * Y),
      |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ a * (1 / ((n : ℝ) + 1)) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hR := hratio n (by omega)
    have hnw : (n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        = 1 / ((n : ℝ) + 1) := by
      field_simp
      ring
    have hwpos : (0 : ℝ) ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
      rw [sub_nonneg]
      apply div_le_div_of_nonneg_left one_pos.le hn0
      linarith
    calc |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ (a * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hR hwpos
      _ = a * ((n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by ring
      _ = a * (1 / ((n : ℝ) + 1)) := by rw [hnw]
  -- split the block
  have hsplit : Finset.Ioc Y (2 * Q * Y)
      = Finset.Ioc Y m₀ ∪ (Finset.Ioc m₀ w ∪ Finset.Ioc w (2 * Q * Y)) := by
    rw [Finset.Ioc_union_Ioc_eq_Ioc hm₀w hw2QY,
      Finset.Ioc_union_Ioc_eq_Ioc (le_of_lt hm₀Y)
        (le_trans hm₀w hw2QY)]
  have hd1 : Disjoint (Finset.Ioc Y m₀)
      (Finset.Ioc m₀ w ∪ Finset.Ioc w (2 * Q * Y)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Ioc] at hx
    rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc] at hx'
    omega
  have hd2 : Disjoint (Finset.Ioc m₀ w) (Finset.Ioc w (2 * Q * Y)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Ioc] at hx hx'
    omega
  rw [hsplit, Finset.sum_union hd1, Finset.sum_union hd2]
  -- price the three parts with the sharp harmonic windows
  have hH1 := abs_le.1 (abs_sum_inv_succ_window_sub_le hY1 (le_of_lt hm₀Y))
  have hH2 := abs_le.1 (abs_sum_inv_succ_window_sub_le hm₀1 hm₀w)
  have hH3 := abs_le.1 (abs_sum_inv_succ_window_sub_le hw1 hw2QY)
  have hb1 : ∑ n ∈ Finset.Ioc Y m₀,
      |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      ≤ a * (Real.log m₀ - Real.log Y + 2 / Y) := by
    calc ∑ n ∈ Finset.Ioc Y m₀,
          |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ ∑ n ∈ Finset.Ioc Y m₀, a * (1 / ((n : ℝ) + 1)) :=
          Finset.sum_le_sum hpart1
      _ = a * ∑ n ∈ Finset.Ioc Y m₀, 1 / ((n : ℝ) + 1) := by
          rw [Finset.mul_sum]
      _ ≤ a * (Real.log m₀ - Real.log Y + 2 / Y) := by
          apply mul_le_mul_of_nonneg_left _ ha.le
          linarith [hH1.2]
  have hb2 : ∑ n ∈ Finset.Ioc m₀ w,
      |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      ≤ ε' * (Real.log w - Real.log m₀ + 2 / m₀) := by
    calc ∑ n ∈ Finset.Ioc m₀ w,
          |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ ∑ n ∈ Finset.Ioc m₀ w, ε' * (1 / ((n : ℝ) + 1)) :=
          Finset.sum_le_sum hpart2
      _ = ε' * ∑ n ∈ Finset.Ioc m₀ w, 1 / ((n : ℝ) + 1) := by
          rw [Finset.mul_sum]
      _ ≤ ε' * (Real.log w - Real.log m₀ + 2 / m₀) := by
          apply mul_le_mul_of_nonneg_left _ hε'0
          linarith [hH2.2]
  have hb3 : ∑ n ∈ Finset.Ioc w (2 * Q * Y),
      |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      ≤ a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log w + 2 / w) := by
    calc ∑ n ∈ Finset.Ioc w (2 * Q * Y),
          |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ ∑ n ∈ Finset.Ioc w (2 * Q * Y), a * (1 / ((n : ℝ) + 1)) :=
          Finset.sum_le_sum hpart3
      _ = a * ∑ n ∈ Finset.Ioc w (2 * Q * Y), 1 / ((n : ℝ) + 1) := by
          rw [Finset.mul_sum]
      _ ≤ a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log w + 2 / w) := by
          apply mul_le_mul_of_nonneg_left _ ha.le
          linarith [hH3.2]
  -- the gain-window log-length is at least `ρ/3`
  have hgainlen : ρ / 3 ≤ Real.log w - Real.log m₀ := by
    have hm₀0 : (0 : ℝ) < m₀ := by exact_mod_cast (by omega : 0 < m₀)
    have h1 : Real.log ((1 + ρ / 2) * m₀) ≤ Real.log w :=
      Real.log_le_log (by positivity) hwR_ge
    rw [Real.log_mul (by positivity) hm₀0.ne'] at h1
    have h2 : ρ / 3 ≤ Real.log (1 + ρ / 2) := by
      have h3 := Real.log_le_sub_one_of_pos
        (x := (1 + ρ / 2)⁻¹) (by positivity)
      rw [Real.log_inv] at h3
      have h4 : (1 + ρ / 2)⁻¹ - 1 = -(ρ / 2) / (1 + ρ / 2) := by
        field_simp
        ring
      rw [h4] at h3
      have h5 : ρ / 3 ≤ (ρ / 2) / (1 + ρ / 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [hρ1, hρ0]
      have h6 : -(ρ / 2) / (1 + ρ / 2) = -(ρ / 2 / (1 + ρ / 2)) := by
        ring
      linarith
    linarith
  -- error terms: `m₀, w > Y`
  have hinvm₀ : 2 / (m₀ : ℝ) ≤ 2 / Y := by
    apply div_le_div_of_nonneg_left (by norm_num)
      (by exact_mod_cast (by omega : 0 < Y))
    exact_mod_cast le_of_lt hm₀Y
  have hinvw : 2 / (w : ℝ) ≤ 2 / Y := by
    apply div_le_div_of_nonneg_left (by norm_num)
      (by exact_mod_cast (by omega : 0 < Y))
    exact_mod_cast (by omega : Y ≤ w)
  have hεa : ε' ≤ a := by rw [hε']; exact hε'a
  have h6Y : a * (6 / Y) = a * (2 / Y) + a * (2 / Y) + a * (2 / Y) := by
    ring
  have hgain_mul : (a - ε') * (ρ / 3) ≤ (a - ε') * (Real.log w - Real.log m₀) :=
    mul_le_mul_of_nonneg_left hgainlen (by linarith)
  have hε2m : ε' * (2 / m₀) ≤ a * (2 / Y) := by
    calc ε' * (2 / (m₀ : ℝ)) ≤ a * (2 / m₀) := by
          apply mul_le_mul_of_nonneg_right hεa (by positivity)
      _ ≤ a * (2 / Y) := by
          apply mul_le_mul_of_nonneg_left hinvm₀ ha.le
  have haw : a * (2 / (w : ℝ)) ≤ a * (2 / Y) :=
    mul_le_mul_of_nonneg_left hinvw ha.le
  have e1 : a * (Real.log (m₀ : ℝ) - Real.log Y + 2 / Y)
      = a * (Real.log (m₀ : ℝ) - Real.log Y) + a * (2 / Y) := by ring
  have e2 : ε' * (Real.log (w : ℝ) - Real.log m₀ + 2 / m₀)
      = ε' * (Real.log (w : ℝ) - Real.log m₀) + ε' * (2 / m₀) := by ring
  have e3 : a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log w + 2 / w)
      = a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log w)
        + a * (2 / w) := by ring
  have e4 : a * (Real.log (m₀ : ℝ) - Real.log Y)
      + a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log w)
      + ε' * (Real.log (w : ℝ) - Real.log m₀)
      = a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log Y)
        - (a - ε') * (Real.log (w : ℝ) - Real.log m₀) := by ring
  linarith [hb1, hb2, hb3, e1, e2, e3, e4, hgain_mul, hε2m, haw, h6Y]

end RHTower
