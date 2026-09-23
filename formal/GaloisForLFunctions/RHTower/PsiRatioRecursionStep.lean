import GaloisForLFunctions.RHTower.SelbergFiberTransfer
import GaloisForLFunctions.RHTower.SelbergSecondInequality

/-!
# The ψ-ratio recursion step

Feeding the contracted fiber transfer into Selberg's second inequality:

`|R(N)|·log²N ≤ (a − θ + 12a/x₁)·N·log²N + C·N·log N`,

`θ = (a − ε')·ρ/(8·log(2Q))`, `C = 80a + 32·log c + 8·G(x₁) + 8466`.

Every sub-`log²N` term of the transfer folds into `C·N·log N` once
`log N ≥ 1`; the only additions to the main coefficient are the strict
contraction `−θ` and the head leak `12a/x₁`, which the iteration kills
by choosing `x₁` large.  Dividing by `log²N` this is the recursion
`a ↦ a − θ(a) + 12a/x₁ + C/log N` on the remainder ratio.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

set_option maxHeartbeats 1600000 in
theorem psi_ratio_recursion_step {a δ ρ κ : ℝ} {Q x₀ x₁ c N : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hQ1 : 1 ≤ Q) (hQ : 40 / δ + 2 < Real.log Q)
    (hx₁8 : 8 ≤ x₁) (hx₁ρ : 8 / ρ ≤ (x₁ : ℝ))
    (hx₁Q : Real.log ((2 * Q : ℕ) : ℝ) + 2 ≤ 2 * Real.log x₁)
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a)
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t)
    (hc8 : 8 * Q ≤ c)
    (hρc : 2 / ρ ≤ (c : ℝ) / (2 * Q) - 1)
    (hx₀c : (x₀ : ℝ) ≤ (c : ℝ) / (2 * Q) - 1)
    (hcx₁N : c * x₁ ≤ N)
    (hjunkc : ∀ t : ℕ, (c : ℝ) / (2 * Q) - 1 ≤ (t : ℝ) →
      Real.log N + 1 + 2 * Real.sqrt t * Real.log t ≤ κ * t) :
    |psiRemainder N| * Real.log N ^ (2 : ℕ)
      ≤ (a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * ρ
            / (8 * Real.log ((2 * Q : ℕ) : ℝ)) + 12 * a / x₁)
          * N * Real.log N ^ (2 : ℕ)
        + (80 * a + 32 * Real.log c
            + 8 * (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁) + 8466)
          * N * Real.log N := by
  set ε' : ℝ := δ + ρ * (Real.log (1 / ρ) + 3) + κ with hε'
  set L : ℝ := Real.log ((2 * Q : ℕ) : ℝ) with hL
  set θ : ℝ := (a - ε') * ρ / (8 * L) with hθ
  have hεa : ε' ≤ a := hε'a
  have hε'0 : 0 ≤ ε' := by
    have hρlog0 : 0 ≤ Real.log (1 / ρ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hρ0, one_mul]; linarith)
    rw [hε']
    positivity
  have hLhalf : 1 / 2 ≤ L := by
    have h1 : Real.log 2 ≤ L := by
      rw [hL]
      apply Real.log_le_log (by norm_num)
      exact_mod_cast (by omega : 2 ≤ 2 * Q)
    linarith [Real.log_two_gt_d9]
  have hL0 : 0 < L := by linarith
  have hθ0 : 0 ≤ θ := by
    rw [hθ]
    apply div_nonneg (mul_nonneg (by linarith) hρ0.le) (by linarith)
  have hθa : θ ≤ a := by
    have h1 : (a - ε') * ρ ≤ a * (1 / 2) :=
      mul_le_mul (by linarith) hρ1 hρ0.le ha.le
    have h2 : θ ≤ a * (1 / 2) / (8 * L) := by
      rw [hθ]
      exact div_le_div_of_nonneg_right h1 (by positivity)
    have h3 : a * (1 / 2) / (8 * L) ≤ a * (1 / 2) / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      linarith
    linarith
  have hx₁0 : 0 < x₁ := by omega
  have hx₁R : (0 : ℝ) < x₁ := by exact_mod_cast hx₁0
  have hN64 : 64 ≤ N := by
    have h1 : 64 ≤ c * x₁ := by
      calc 64 = 8 * 8 := by norm_num
        _ ≤ c * x₁ := Nat.mul_le_mul (by omega) hx₁8
    omega
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlogN1 : 1 ≤ Real.log N := by
    have h1 : Real.exp 1 < 3 :=
      lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2 : (3 : ℝ) ≤ N := by exact_mod_cast (by omega : 3 ≤ N)
    have h3 : Real.log (Real.exp 1) ≤ Real.log N :=
      Real.log_le_log (Real.exp_pos 1) (by linarith)
    rwa [Real.log_exp] at h3
  have hlogN0 : 0 ≤ Real.log N := by linarith
  have hlogx₁0 : 0 ≤ Real.log x₁ :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x₁))
  have hGx₁0 : 0 ≤ Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁ := by positivity
  have hlogc0 : 0 ≤ Real.log c :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c))
  -- the two inputs
  have hssi := selberg_second_inequality N (by omega)
  have hsft := selberg_weight_fiber_transfer ha hδ hρ0 hρ1 hκ hQ1 hQ hx₁8
    hx₁ρ hx₁Q hε'a hratio hc8 hρc hx₀c hcx₁N hjunkc
  rw [← hε', ← hL, ← hθ] at hsft
  -- fold every sub-`log²N` term into `C·log N`
  have hfold : (a - θ) * ((Real.log N ^ (2 : ℕ) + 2 * Real.log N)
        - (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁))
      + (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
      + 8 * ((2 * Real.log N + 8) / x₁)
      + 8 * Real.log c * (2 * Real.log N + 2)
      + 8 * (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁) + 66
      + 840 * Real.log N + 3780
      + 800 * Real.log N + 2900
      ≤ (a - θ + 12 * a / x₁) * Real.log N ^ (2 : ℕ)
        + (80 * a + 32 * Real.log c
            + 8 * (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁) + 8466)
          * Real.log N := by
    have h1 : (a - θ) * ((Real.log N ^ (2 : ℕ) + 2 * Real.log N)
          - (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁))
        ≤ (a - θ) * Real.log N ^ (2 : ℕ) + 2 * a * Real.log N := by
      have ha1 : (a - θ) * ((Real.log N ^ (2 : ℕ) + 2 * Real.log N)
            - (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁))
          ≤ (a - θ) * (Real.log N ^ (2 : ℕ) + 2 * Real.log N) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have ha2 : (a - θ) * (2 * Real.log N) ≤ a * (2 * Real.log N) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      nlinarith [ha1, ha2]
    have h2 : (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
        ≤ 12 * a / x₁ * Real.log N ^ (2 : ℕ) + 78 * a * Real.log N := by
      have hexp : (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
          = 12 * a / x₁ * Real.log N ^ (2 : ℕ)
            + (54 * a * Real.log N + 24 * a) / x₁ := by
        field_simp
        ring
      rw [hexp]
      have hd : (54 * a * Real.log N + 24 * a) / x₁
          ≤ 54 * a * Real.log N + 24 * a := by
        rw [div_le_iff₀ hx₁R]
        have hnum : 0 ≤ 54 * a * Real.log N + 24 * a := by positivity
        have hx1 : (1 : ℝ) ≤ x₁ := by exact_mod_cast (by omega : 1 ≤ x₁)
        nlinarith [mul_nonneg hnum (by linarith : (0 : ℝ) ≤ (x₁ : ℝ) - 1)]
      nlinarith [hd, hlogN1, ha]
    have h3 : 8 * ((2 * Real.log N + 8) / x₁) ≤ 80 * Real.log N := by
      have hd : (2 * Real.log N + 8) / x₁ ≤ 2 * Real.log N + 8 := by
        rw [div_le_iff₀ hx₁R]
        have hx1 : (1 : ℝ) ≤ x₁ := by exact_mod_cast (by omega : 1 ≤ x₁)
        have hnum : (0 : ℝ) ≤ 2 * Real.log N + 8 := by linarith
        nlinarith [mul_nonneg hnum (by linarith : (0 : ℝ) ≤ (x₁ : ℝ) - 1)]
      nlinarith [hd, hlogN1]
    have h4 : 8 * Real.log c * (2 * Real.log N + 2)
        ≤ 32 * Real.log c * Real.log N := by
      nlinarith [hlogc0, hlogN1]
    have h5 : 8 * (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁) + 66
        ≤ (8 * (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁) + 66) * Real.log N := by
      nlinarith [hGx₁0, hlogN1]
    have h6 : 840 * Real.log N + 3780 + 800 * Real.log N + 2900
        ≤ 8320 * Real.log N := by
      nlinarith [hlogN1]
    nlinarith [h1, h2, h3, h4, h5, h6]
  -- assemble
  have hmul := mul_le_mul_of_nonneg_left hfold hNR.le
  calc |psiRemainder N| * Real.log N ^ (2 : ℕ)
      ≤ (∑ m ∈ Finset.Icc 1 N,
          (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m)
            * |psiRemainder (N / m)|)
        + 800 * N * Real.log N + 2900 * N := hssi
    _ ≤ (N : ℝ) * ((a - θ)
          * ((Real.log N ^ (2 : ℕ) + 2 * Real.log N)
            - (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁))
        + (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
        + 8 * ((2 * Real.log N + 8) / x₁)
        + 8 * Real.log c * (2 * Real.log N + 2)
        + 8 * (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁) + 66
        + 840 * Real.log N + 3780)
        + 800 * N * Real.log N + 2900 * N := by linarith [hsft]
    _ = (N : ℝ) * ((a - θ)
          * ((Real.log N ^ (2 : ℕ) + 2 * Real.log N)
            - (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁))
        + (2 * Real.log N + 1) * (3 * a * ((2 * Real.log N + 8) / x₁))
        + 8 * ((2 * Real.log N + 8) / x₁)
        + 8 * Real.log c * (2 * Real.log N + 2)
        + 8 * (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁) + 66
        + 840 * Real.log N + 3780
        + 800 * Real.log N + 2900) := by ring
    _ ≤ (N : ℝ) * ((a - θ + 12 * a / x₁) * Real.log N ^ (2 : ℕ)
        + (80 * a + 32 * Real.log c
            + 8 * (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁) + 8466)
          * Real.log N) := hmul
    _ = (a - θ + 12 * a / x₁) * N * Real.log N ^ (2 : ℕ)
        + (80 * a + 32 * Real.log c
            + 8 * (Real.log x₁ ^ (2 : ℕ) + 2 * Real.log x₁) + 8466)
          * N * Real.log N := by ring

end RHTower
