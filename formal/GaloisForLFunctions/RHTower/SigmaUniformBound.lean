import GaloisForLFunctions.RHTower.ScaleSigmaSum

/-!
# The uniform σ bound and its scale summation

Under the ladder hypotheses, the σ-partial sums obey a single closed form
at every scale,

`σ(s) ≤ (a − g/L)·log s + C₁`,  `C₁ = g + 14a/x₁ + 8(log x₁ + 2)`,

(crude `8(log s + 2)` head below `x₁`, ladder contraction above), and
therefore

`∑_{s ≤ M} σ(s)/s ≤ (a − g/L)·(½log²M + 1) + C₁·(log M + 2)` —

the quantity the discrete Fubini pairs with the fiber transfer.  The rate
survives: `g/L ≤ a/3 < a` since `g ≤ aρ/3 ≤ a/6` and `L ≥ log 2 ≥ 1/2`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- The crude σ bound `σ(s) ≤ 8(log s + 2)`. -/
theorem sigmaPartial_le_crude (s : ℕ) (hs : 1 ≤ s) :
    sigmaPartial s ≤ 8 * (Real.log s + 2) := by
  have hterm : ∀ v ∈ Finset.Icc 1 s,
      |psiRemainder v| * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1))
        ≤ 8 * (1 / (v : ℝ)) := by
    intro v hv
    rw [Finset.mem_Icc] at hv
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
    have hR := abs_psiRemainder_le v
    have hnw : (v : ℝ) * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1))
        = 1 / ((v : ℝ) + 1) := by
      field_simp
      ring
    have hwpos : (0 : ℝ) ≤ 1 / (v : ℝ) - 1 / ((v : ℝ) + 1) := by
      rw [sub_nonneg]
      apply div_le_div_of_nonneg_left one_pos.le hv0
      linarith
    have hsucc : 1 / ((v : ℝ) + 1) ≤ 1 / v :=
      div_le_div_of_nonneg_left one_pos.le hv0 (by linarith)
    calc |psiRemainder v| * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1))
        ≤ (8 * v) * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hR hwpos
      _ = 8 * ((v : ℝ) * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1))) := by ring
      _ = 8 * (1 / ((v : ℝ) + 1)) := by rw [hnw]
      _ ≤ 8 * (1 / (v : ℝ)) := by linarith [hsucc]
  calc sigmaPartial s
      ≤ ∑ v ∈ Finset.Icc 1 s, 8 * (1 / (v : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 8 * ∑ v ∈ Finset.Icc 1 s, 1 / (v : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ 8 * (Real.log s + 2) := by
        have := sum_inv_le s hs
        linarith

/-- The contraction rate never exceeds the ratio: `g/L ≤ a`. -/
theorem gain_div_log_le {a δ ρ κ : ℝ} {Q : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hQ1 : 1 ≤ Q)
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a) :
    (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
      / Real.log ((2 * Q : ℕ) : ℝ) ≤ a := by
  have hε'0 : 0 ≤ δ + ρ * (Real.log (1 / ρ) + 3) + κ := by
    have hρlog0 : 0 ≤ Real.log (1 / ρ) :=
      Real.log_nonneg (by
        rw [le_div_iff₀ hρ0, one_mul]
        linarith)
    positivity
  have hL2 : Real.log 2 ≤ Real.log ((2 * Q : ℕ) : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
    push_cast
    nlinarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (x := (1 / 2 : ℝ)) (by norm_num)
    rw [one_div, Real.log_inv] at h
    norm_num at h
    linarith
  have hL0 : (0 : ℝ) < Real.log ((2 * Q : ℕ) : ℝ) := by linarith
  rw [div_le_iff₀ hL0]
  have hg : (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
      ≤ a * (1 / 6) := by
    have h1 : a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ) ≤ a := by linarith
    have h2 : ρ / 3 ≤ 1 / 6 := by linarith
    have h3 : 0 ≤ a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ) := by linarith
    nlinarith [h1, h2, h3, ha.le]
  nlinarith [hg, hL2, hlog2, ha.le]

set_option maxHeartbeats 1000000 in
/-- **Uniform σ bound**: `σ(s) ≤ (a − g/L)·log s + C₁` at every scale. -/
theorem sigmaPartial_le_of_ratio {a δ ρ κ : ℝ} {Q x₀ x₁ : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hQ1 : 1 ≤ Q)
    (hQ : 40 / δ + 2 < Real.log Q)
    (hx₁1 : 1 ≤ x₁) (hx₀x₁ : x₀ ≤ x₁) (hx₁ρ : 2 / ρ ≤ (x₁ : ℝ))
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a)
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t)
    (hjunk1 : ∀ t : ℕ, x₁ < t →
      2 * Real.sqrt t * Real.log t ≤ κ / 2 * t)
    (hbase0 : Real.log ((Q * x₁ : ℕ) : ℝ) + 1 ≤ κ / 2 * x₁)
    (hbase : Real.log ((2 * Q : ℕ) : ℝ) ≤ κ / 2 * x₁) :
    ∀ s : ℕ, 1 ≤ s →
      sigmaPartial s
        ≤ (a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
              / Real.log ((2 * Q : ℕ) : ℝ)) * Real.log s
          + ((a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
            + 14 * a / x₁ + 8 * (Real.log x₁ + 2)) := by
  intro s hs
  have hθa := gain_div_log_le ha hδ hρ0 hρ1 hκ hQ1 hε'a
  have hlogs0 : 0 ≤ Real.log s :=
    Real.log_nonneg (by exact_mod_cast hs)
  have hlogx₁0 : 0 ≤ Real.log x₁ :=
    Real.log_nonneg (by exact_mod_cast hx₁1)
  have hg0 : 0 ≤ (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3) :=
    mul_nonneg (by linarith) (by linarith)
  have h14 : 0 ≤ 14 * a / (x₁ : ℝ) := by positivity
  rcases le_or_gt s x₁ with hsx | hsx
  · -- head: crude bound
    have hcrude := sigmaPartial_le_crude s hs
    have hmono : Real.log s ≤ Real.log x₁ :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < s))
        (by exact_mod_cast hsx)
    nlinarith [hcrude, hmono, mul_nonneg (by linarith : (0:ℝ) ≤ a
      - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
        / Real.log ((2 * Q : ℕ) : ℝ)) hlogs0]
  · -- above the ladder base
    have hsplit : Finset.Icc 1 s
        = Finset.Icc 1 x₁ ∪ Finset.Ioc x₁ s := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 x₁) (Finset.Ioc x₁ s) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_Icc] at hx
      rw [Finset.mem_Ioc] at hx'
      omega
    have hσs : sigmaPartial s = sigmaPartial x₁
        + ∑ n ∈ Finset.Ioc x₁ s,
            |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      rw [sigmaPartial, sigmaPartial, hsplit, Finset.sum_union hdisj]
    have hwin := sigma_window_contraction_of_ratio ha hδ hρ0 hρ1 hκ hQ1 hQ
      hx₁1 hx₀x₁ hx₁ρ hε'a hratio hjunk1 hbase0 hbase (le_of_lt hsx)
    have hhead := sigmaPartial_le_crude x₁ hx₁1
    have hθ0 : 0 ≤ a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
        / Real.log ((2 * Q : ℕ) : ℝ) := by linarith
    have hmono : Real.log x₁ ≤ Real.log s :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < x₁))
        (by exact_mod_cast le_of_lt hsx)
    nlinarith [hσs, hwin, hhead, mul_nonneg hθ0 hlogx₁0]

end RHTower
