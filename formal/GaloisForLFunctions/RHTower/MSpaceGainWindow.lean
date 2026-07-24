import GaloisForLFunctions.RHTower.WindowLogHarmonicSharp
import GaloisForLFunctions.RHTower.PsiRemainderGainWindow

/-!
# The m-space gain window

Inside every m-block `(Y, 2QY]` (with fibers above the small-value scale)
sits an interval `(A, B]` — the floor-preimage of a fiber gain window —
of log-length at least `ρ/4` on which the fiber remainder is pointwise
small:

`∀ m ∈ (A, B] : |R(⌊N/m⌋)| ≤ ε'·⌊N/m⌋`,  `ε' = δ + ρ(log(1/ρ)+3) + κ`.

The fiber window `(W₀, Q·W₀]` with `W₀ = ⌊N/(2QY)⌋` supplies the small
point `m₀`; `A = ⌊N/(w₀+1)⌋`, `B = ⌊N/m₀⌋` with `w₀ = m₀ + ⌊ρm₀⌋`, and
the floor losses are absorbed by `Y ≥ 8` and `Y ≥ 8/ρ`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

set_option maxHeartbeats 1000000 in
theorem exists_m_gain_window {δ ρ κ : ℝ} {Q Y N : ℕ}
    (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (_hκ : 0 ≤ κ)
    (hQ1 : 1 ≤ Q) (hQ : 40 / δ + 2 < Real.log Q)
    (hY8 : 8 ≤ Y) (hYρ : 8 / ρ ≤ (Y : ℝ))
    (hN : 8 * Q * Y ≤ N)
    (hWρ : 2 / ρ ≤ ((N / (2 * Q * Y) : ℕ) : ℝ))
    (hjunkf : ∀ t : ℕ, N / (2 * Q * Y) < t →
      Real.log ((Q * (N / (2 * Q * Y)) : ℕ) : ℝ) + 1
        + 2 * Real.sqrt t * Real.log t ≤ κ * t) :
    ∃ A B : ℕ, Y < A ∧ A ≤ B ∧ B ≤ 2 * Q * Y ∧
      ρ / 4 ≤ Real.log B - Real.log A ∧
      ∀ m ∈ Finset.Ioc A B,
        |psiRemainder (N / m)|
          ≤ (δ + ρ * (Real.log (1 / ρ) + 3) + κ) * ((N / m : ℕ) : ℝ) := by
  set W₀ : ℕ := N / (2 * Q * Y) with hW₀
  have hQY0 : 0 < 2 * Q * Y := by positivity
  have hW₀4 : 4 ≤ W₀ := by
    rw [hW₀]
    apply (Nat.le_div_iff_mul_le hQY0).2
    nlinarith [hN]
  have hW₀1 : 1 ≤ W₀ := by omega
  -- the fiber small-value window
  obtain ⟨m₀, hm₀W, hm₀Q, hpoint⟩ :=
    exists_pointwise_small_window hδ hρ0 (by linarith) hW₀1 hQ1 hQ
  set w₀ : ℕ := m₀ + Nat.floor (ρ * m₀) with hw₀
  have hm₀R : (W₀ : ℝ) < m₀ := by exact_mod_cast hm₀W
  have hWρ2 : (2 : ℝ) ≤ ρ * W₀ := by
    rw [div_le_iff₀ hρ0] at hWρ
    linarith
  have hρm₀2 : (2 : ℝ) ≤ ρ * m₀ := by nlinarith [hρ0]
  have hfl_ge : (ρ * m₀) / 2 ≤ (Nat.floor (ρ * m₀) : ℝ) := by
    have h1 : (ρ * m₀) - 1 ≤ (Nat.floor (ρ * m₀) : ℝ) := by
      have := Nat.sub_one_lt_floor (ρ * m₀)
      linarith
    linarith
  have hfl_le : (Nat.floor (ρ * m₀) : ℝ) ≤ ρ * m₀ :=
    Nat.floor_le (by positivity)
  have hw_ge : (1 + ρ / 2) * m₀ ≤ (w₀ : ℝ) := by
    rw [hw₀]
    push_cast
    linarith
  have hw_le : (w₀ : ℝ) ≤ (1 + ρ) * m₀ := by
    rw [hw₀]
    push_cast
    linarith
  have hm₀1 : 1 ≤ m₀ := by omega
  have hm₀0R : (0 : ℝ) < m₀ := by exact_mod_cast (by omega : 0 < m₀)
  -- `m₀ ≤ ⌊N/(2Y)⌋`, hence real `m₀ ≤ N/(2Y)`
  have hm₀N : (m₀ : ℝ) ≤ (N : ℝ) / (2 * Y) := by
    have h1 : m₀ ≤ Q * W₀ := hm₀Q
    have h2 : (Q * W₀) * (2 * Y) ≤ N := by
      have h3 : W₀ * (2 * Q * Y) ≤ N := by
        rw [hW₀]
        exact Nat.div_mul_le_self N (2 * Q * Y)
      calc (Q * W₀) * (2 * Y) = W₀ * (2 * Q * Y) := by ring
        _ ≤ N := h3
    have h4 : (m₀ : ℝ) * (2 * Y) ≤ N := by
      have : m₀ * (2 * Y) ≤ N := le_trans
        (Nat.mul_le_mul_right _ h1) h2
      exact_mod_cast this
    have h5 : (0 : ℝ) < 2 * Y := by
      have : (8 : ℝ) ≤ Y := by exact_mod_cast hY8
      linarith
    rw [le_div_iff₀ h5]
    linarith
  set A : ℕ := N / (w₀ + 1) with hA
  set B : ℕ := N / m₀ with hB
  have hYR : (8 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY8
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  -- 1. `Y < A`
  have hYA : Y < A := by
    have hkey : (Y + 1 : ℝ) * ((w₀ : ℝ) + 1) ≤ N := by
      have h1 : (w₀ : ℝ) ≤ (3 / 2) * m₀ := by nlinarith [hw_le, hρ1, hm₀0R]
      have h2 : (w₀ : ℝ) + 1 ≤ (3 / 4) * (N / Y) + 1 := by
        have h3 : (3 / 2 : ℝ) * m₀ ≤ (3 / 2) * ((N : ℝ) / (2 * Y)) := by
          nlinarith [hm₀N]
        have h4 : (3 / 2 : ℝ) * ((N : ℝ) / (2 * Y)) = (3 / 4) * (N / Y) := by
          field_simp
          ring
        linarith
      have hY0 : (0 : ℝ) < Y := by linarith
      have h5 : ((Y : ℝ) + 1) * ((3 / 4) * ((N : ℝ) / Y) + 1)
          = (3 / 4) * N * (1 + 1 / Y) + Y + 1 := by
        field_simp
        ring
      have h6 : (1 : ℝ) + 1 / Y ≤ 9 / 8 := by
        have : (1 : ℝ) / Y ≤ 1 / 8 := by
          apply div_le_div_of_nonneg_left one_pos.le (by norm_num)
          exact hYR
        linarith
      have h7 : (Y : ℝ) + 1 ≤ (5 / 32) * N := by
        have h8 : (Y : ℝ) ≤ (N : ℝ) / 8 := by
          have h9 : (8 : ℝ) * Y ≤ N := by
            have : 8 * Y ≤ N := by nlinarith [hN, hQ1]
            exact_mod_cast this
          linarith [h9]
        have h10 : (64 : ℝ) ≤ N := by
          have : 64 ≤ N := by nlinarith [hN, hQ1, hY8]
          exact_mod_cast this
        linarith
      have h11 : ((Y:ℝ) + 1) * ((w₀:ℝ) + 1)
          ≤ ((Y:ℝ) + 1) * ((3/4) * ((N:ℝ)/Y) + 1) := by
        apply mul_le_mul_of_nonneg_left h2 (by linarith)
      nlinarith [h11, h5, h6, h7, hNR]
    have hnat : (Y + 1) * (w₀ + 1) ≤ N := by
      have := hkey
      push_cast at this
      exact_mod_cast this
    have : Y + 1 ≤ A := by
      rw [hA]
      exact (Nat.le_div_iff_mul_le (by omega)).2 hnat
    omega
  -- 2. `A ≤ B`
  have hAB : A ≤ B := by
    rw [hA, hB]
    exact Nat.div_le_div_left (by omega) (by omega)
  -- 3. `B ≤ 2QY`
  have hB2QY : B ≤ 2 * Q * Y := by
    have h1 : N < (W₀ + 1) * (2 * Q * Y) := by
      have h2 := Nat.div_add_mod N (2 * Q * Y)
      have h3 := Nat.mod_lt N hQY0
      have h4 : (W₀ + 1) * (2 * Q * Y)
          = 2 * Q * Y * W₀ + 2 * Q * Y := by ring
      rw [hW₀] at *
      omega
    have h5 : N < m₀ * (2 * Q * Y) := by
      have h6 : W₀ + 1 ≤ m₀ := by omega
      have h7 : (W₀ + 1) * (2 * Q * Y) ≤ m₀ * (2 * Q * Y) :=
        Nat.mul_le_mul_right _ h6
      omega
    have h8 : N / m₀ < 2 * Q * Y := by
      rw [Nat.div_lt_iff_lt_mul (show 0 < m₀ by omega)]
      have h9 : m₀ * (2 * Q * Y) = 2 * Q * Y * m₀ := Nat.mul_comm _ _
      omega
    rw [hB]
    omega
  -- 4. gain log-length `ρ/4 ≤ log B − log A`
  have hA1 : 1 ≤ A := by omega
  have hAposR : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hBposR : (0 : ℝ) < B := by
    have : A ≤ B := hAB
    exact_mod_cast (by omega : 0 < B)
  have hgain : ρ / 4 ≤ Real.log B - Real.log A := by
    have hBr : (N : ℝ) / m₀ - 1 ≤ (B : ℝ) := by
      rw [hB]
      have h1 := Nat.div_add_mod N m₀
      have h2 := Nat.mod_lt N (show 0 < m₀ by omega)
      have h3 : (N : ℝ) = (m₀ : ℝ) * ((N / m₀ : ℕ) : ℝ)
          + ((N % m₀ : ℕ) : ℝ) := by
        exact_mod_cast h1.symm
      have h4 : ((N % m₀ : ℕ) : ℝ) < m₀ := by exact_mod_cast h2
      rw [div_sub_one hm₀0R.ne', div_le_iff₀ hm₀0R]
      nlinarith [h3, h4]
    have hAr : (A : ℝ) ≤ (N : ℝ) / (w₀ + 1) := by
      rw [hA]
      have hw₀0 : (0 : ℝ) < (w₀ : ℝ) + 1 := by positivity
      rw [le_div_iff₀ hw₀0]
      have h1 : (N / (w₀ + 1)) * (w₀ + 1) ≤ N :=
        Nat.div_mul_le_self N (w₀ + 1)
      have h2 : ((N / (w₀ + 1) : ℕ) : ℝ) * ((w₀ : ℝ) + 1) ≤ N := by
        exact_mod_cast h1
      exact h2
    have hratio : (1 + 3 * ρ / 8) * (A : ℝ) ≤ (B : ℝ) := by
      have h1 : (1 + 3 * ρ / 8) * (A : ℝ)
          ≤ (1 + 3 * ρ / 8) * ((N : ℝ) / (w₀ + 1)) := by
        apply mul_le_mul_of_nonneg_left hAr (by linarith)
      have h2 : (1 + 3 * ρ / 8) * ((N : ℝ) / (w₀ + 1))
          ≤ (N : ℝ) / m₀ - 1 := by
        have hw₀1R : (0 : ℝ) < (w₀ : ℝ) + 1 := by positivity
        rw [div_sub_one hm₀0R.ne',
          show (1 + 3 * ρ / 8) * ((N : ℝ) / ((w₀ : ℝ) + 1))
            = ((1 + 3 * ρ / 8) * N) / ((w₀ : ℝ) + 1) from by ring,
          div_le_div_iff₀ hw₀1R hm₀0R]
        have hkey : (1 + ρ / 2) * m₀ ≤ (w₀ : ℝ) + 1 := by
          linarith [hw_ge]
        have hm₀N' : (m₀ : ℝ) * (2 * Y) ≤ N := by
          have := hm₀N
          have hY0 : (0 : ℝ) < 2 * Y := by linarith
          rw [le_div_iff₀ hY0] at this
          linarith
        have hYρ' : (8 : ℝ) ≤ ρ * Y := by
          rw [div_le_iff₀ hρ0] at hYρ
          linarith
        have habs : (m₀ : ℝ) * (1 + ρ / 2) ≤ (N : ℝ) * (ρ / 8) := by
          have h5 : (m₀ : ℝ) * (1 + ρ / 2) ≤ (m₀ : ℝ) * (3 / 2) := by
            apply mul_le_mul_of_nonneg_left _ hm₀0R.le
            linarith
          have h6 : (m₀ : ℝ) * (3 / 2) * (ρ * Y) ≤ (N : ℝ) * (ρ / 8)
              * (ρ * Y) := by
            have h7 : (m₀ : ℝ) * (3 / 2) * (ρ * Y)
                ≤ (m₀ : ℝ) * (2 * Y) * ρ := by
              nlinarith [hρ0.le, hm₀0R.le, hYρ', (by linarith : (0:ℝ) ≤ Y)]
            have h8 : (m₀ : ℝ) * (2 * Y) * ρ ≤ (N : ℝ) * ρ := by
              apply mul_le_mul_of_nonneg_right hm₀N' hρ0.le
            have h9 : (N : ℝ) * ρ ≤ (N : ℝ) * (ρ / 8) * (ρ * Y) := by
              have h10 : (8 : ℝ) ≤ ρ * Y := hYρ'
              nlinarith [hNR.le, hρ0.le]
            linarith
          have hρY0 : (0 : ℝ) < ρ * Y := by nlinarith [hρ0]
          have h11 := le_of_mul_le_mul_right h6 hρY0
          linarith [h5, h11]
        -- `(1+3ρ/8)·N·m₀ ≤ (N − m₀)·(w₀+1)`
        have hNm₀ : (m₀ : ℝ) ≤ (N : ℝ) := by
          nlinarith [hm₀N', (by linarith : (1:ℝ) ≤ 2 * Y), hm₀0R.le]
        have hp1 := mul_le_mul_of_nonneg_left hkey
          (by linarith : (0:ℝ) ≤ (N:ℝ) - m₀)
        have hp2 := mul_le_mul_of_nonneg_left habs hm₀0R.le
        nlinarith [hp1, hp2]
      linarith [h1, h2, hBr]
    have hmono : Real.log ((1 + 3 * ρ / 8) * (A : ℝ)) ≤ Real.log B :=
      Real.log_le_log (by positivity) hratio
    rw [Real.log_mul (by positivity) hAposR.ne'] at hmono
    have hlx : ρ / 4 ≤ Real.log (1 + 3 * ρ / 8) := by
      have h3 := Real.log_le_sub_one_of_pos
        (x := (1 + 3 * ρ / 8)⁻¹) (by positivity)
      rw [Real.log_inv] at h3
      have h4 : (1 + 3 * ρ / 8)⁻¹ - 1 = -(3 * ρ / 8) / (1 + 3 * ρ / 8) := by
        field_simp
        ring
      rw [h4] at h3
      have h5 : ρ / 4 ≤ (3 * ρ / 8) / (1 + 3 * ρ / 8) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [hρ0.le, hρ1]
      have h6 : -(3 * ρ / 8) / (1 + 3 * ρ / 8)
          = -((3 * ρ / 8) / (1 + 3 * ρ / 8)) := by ring
      linarith
    linarith [hmono, hlx]
  -- 5. pointwise smallness on the m-window
  refine ⟨A, B, hYA, hAB, hB2QY, hgain, ?_⟩
  intro m hm
  rw [Finset.mem_Ioc] at hm
  have hm0 : 0 < m := by omega
  have hfib_ge : m₀ ≤ N / m := by
    have h1 : m * m₀ ≤ N := by
      have h2 := (Nat.le_div_iff_mul_le (show 0 < m₀ by omega)).1 hm.2
      rw [hB] at hm
      exact (Nat.le_div_iff_mul_le (show 0 < m₀ by omega)).1 hm.2
    have h3 : m₀ * m ≤ N := by
      rw [Nat.mul_comm]
      exact h1
    exact (Nat.le_div_iff_mul_le hm0).2 h3
  have hfib_le : N / m ≤ w₀ := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : w₀ + 1 ≤ N / m := by omega
    have h2 : (w₀ + 1) * m ≤ N := (Nat.le_div_iff_mul_le hm0).1 h1
    have h3 : m * (w₀ + 1) ≤ N := by
      rw [Nat.mul_comm]
      exact h2
    have h4 : m ≤ N / (w₀ + 1) :=
      (Nat.le_div_iff_mul_le (by omega : 0 < w₀ + 1)).2 h3
    rw [← hA] at h4
    omega
  have hfibρ : ((N / m : ℕ) : ℝ) ≤ (1 + ρ) * m₀ := by
    have h1 : ((N / m : ℕ) : ℝ) ≤ (w₀ : ℝ) := by exact_mod_cast hfib_le
    linarith [hw_le]
  have hpt := hpoint (N / m) hfib_ge hfibρ
  have hjun := hjunkf (N / m) (by omega : N / (2 * Q * Y) < N / m)
  calc |psiRemainder (N / m)|
      ≤ (δ + ρ * (Real.log (1 / ρ) + 3)) * ((N / m : ℕ) : ℝ)
        + (Real.log ((Q * W₀ : ℕ) : ℝ) + 1)
        + 2 * Real.sqrt ((N / m : ℕ) : ℝ)
          * Real.log ((N / m : ℕ) : ℝ) := hpt
    _ ≤ (δ + ρ * (Real.log (1 / ρ) + 3)) * ((N / m : ℕ) : ℝ)
        + κ * ((N / m : ℕ) : ℝ) := by
        rw [hW₀] at hjun ⊢
        linarith [hjun]
    _ = (δ + ρ * (Real.log (1 / ρ) + 3) + κ) * ((N / m : ℕ) : ℝ) := by
        ring

end RHTower
