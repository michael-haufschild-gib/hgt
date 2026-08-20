import GaloisForLFunctions.RHTower.XiSymmetricMassSharp
import GaloisForLFunctions.RHTower.XiAdmissibleHeights

/-!
# The divisor-mass asymptotic at arbitrary heights

The sharp mass asymptotic is proved at admissible heights, where the argument principle applies.
Since the mass is monotone in the height and admissible heights are dense, squeezing between two
admissible heights within distance one of `T` transfers the asymptotic to every height: the cost is
`(T \pm 1)\log(T \pm 1) = T\log T + O(\log T)`, which is absorbed by the relative error.
-/

open Complex Filter Topology


noncomputable section

namespace RHTower

theorem mul_log_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a * Real.log a ≤ b * Real.log b := by
  have hloga : 0 ≤ Real.log a := Real.log_nonneg ha
  have hlogab : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  nlinarith

theorem neg_two_mul_le_log_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -(2 * x) ≤ Real.log (1 - x) := by
  have h1 : (0 : ℝ) < 1 - x := by linarith
  have hinv : (0 : ℝ) < (1 - x)⁻¹ := by positivity
  have h := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at h
  have hbound : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    rw [sub_le_iff_le_add, inv_le_iff_one_le_mul₀ h1]
    nlinarith
  linarith

theorem succ_mul_log_le {T : ℝ} (hT : 1 ≤ T) :
    (T + 1) * Real.log (T + 1) ≤ T * Real.log T + Real.log T + 2 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hsplit : Real.log (T + 1) = Real.log T + Real.log (1 + 1 / T) := by
    rw [← Real.log_mul hT0.ne' (by positivity)]
    congr 1
    field_simp
  have hlog : Real.log (1 + 1 / T) ≤ 1 / T := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1 / T by positivity)
    linarith
  have hTinv : (T + 1) * (1 / T) ≤ 2 := by
    rw [mul_one_div, div_le_iff₀ hT0]
    linarith
  rw [hsplit, mul_add]
  have hstep : (T + 1) * Real.log (1 + 1 / T) ≤ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hlog (by linarith)) hTinv
  nlinarith [hstep]

theorem pred_mul_log_ge {T : ℝ} (hT : 2 ≤ T) :
    T * Real.log T - Real.log T - 2 ≤ (T - 1) * Real.log (T - 1) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hx : (1 : ℝ) / T ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hT0 (by norm_num)]
    linarith
  have hsplit : Real.log (T - 1) = Real.log T + Real.log (1 - 1 / T) := by
    rw [← Real.log_mul hT0.ne' (by
      have : (0:ℝ) < 1 - 1 / T := by
        rw [sub_pos, div_lt_one hT0]; linarith
      exact this.ne')]
    congr 1
    field_simp
  have hlog := neg_two_mul_le_log_one_sub (x := 1 / T) (by positivity) hx
  have hstep : (T - 1) * (Real.log T - 2 * (1 / T)) ≤ (T - 1) * Real.log (T - 1) := by
    rw [hsplit]
    have : Real.log T - 2 * (1 / T) ≤ Real.log T + Real.log (1 - 1 / T) := by linarith
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have hexp : (T - 1) * (Real.log T - 2 * (1 / T))
      = T * Real.log T - Real.log T - 2 + 2 * (1 / T) := by
    field_simp
    ring
  rw [hexp] at hstep
  have : (0:ℝ) < 2 * (1 / T) := by positivity
  linarith

/-- **The sharp divisor-mass asymptotic at every height.** -/
theorem exists_xiSymmetricMass_close (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |(xiSymmetricMass T : ℝ) - (1 / Real.pi) * (T * Real.log T)|
        ≤ ε * (T * Real.log T) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set P : ℝ := 1 / Real.pi with hPdef
  have hP : (0 : ℝ) < P := by rw [hPdef]; positivity
  have hPpi : P * Real.pi = 1 := by rw [hPdef]; field_simp
  set ε₁ : ℝ := ε / 2 with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  obtain ⟨Ta, hTa4, hadm⟩ := exists_xiSymmetricMass_admissible_close ε₁ hε₁
  refine ⟨max (max (Ta + 1) (3 / (Real.pi * ε₁) + 3)) 8, le_trans (by norm_num)
    (le_max_right _ _), fun T hT => ?_⟩
  have hT8 : (8 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTa1 : Ta + 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTthr : 3 / (Real.pi * ε₁) + 3 ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hTlog : (0 : ℝ) < T * Real.log T := by positivity
  have hεrel : ε₁ * (T * Real.log T) + ε₁ * (T * Real.log T) = ε * (T * Real.log T) := by
    rw [hε₁def]; ring
  -- the threshold inequality
  have hkey : (P + ε₁) * (Real.log T + 2) ≤ ε₁ * (T * Real.log T) := by
    have h3 : Real.log T + 2 ≤ 3 * Real.log T := by linarith
    have hthr : 3 * (P + ε₁) ≤ ε₁ * T := by
      have hb : 3 / (Real.pi * ε₁) ≤ T - 3 := by linarith
      rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi * ε₁)] at hb
      have h3pi : 3 * P ≤ (T - 3) * ε₁ := by
        have hmul : (3 * P) * Real.pi ≤ ((T - 3) * ε₁) * Real.pi := by
          rw [show (3 * P) * Real.pi = 3 * (P * Real.pi) by ring, hPpi, mul_one,
            show ((T - 3) * ε₁) * Real.pi = (T - 3) * (Real.pi * ε₁) by ring]
          exact hb
        exact le_of_mul_le_mul_right hmul hπ
      linarith
    calc (P + ε₁) * (Real.log T + 2)
        ≤ (P + ε₁) * (3 * Real.log T) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (3 * (P + ε₁)) * Real.log T := by ring
      _ ≤ (ε₁ * T) * Real.log T := mul_le_mul_of_nonneg_right hthr (by linarith)
      _ = ε₁ * (T * Real.log T) := by ring
  -- upper bound via an admissible height just above T
  obtain ⟨T₂, hT₂mem, hT₂adm⟩ := exists_admissible_height (a := T) (b := T + 1) (by linarith)
  obtain ⟨T₃, hT₃mem, hT₃adm⟩ := exists_admissible_height (a := T - 1) (b := T) (by linarith)
  have hupper : (xiSymmetricMass T : ℝ) ≤ P * (T * Real.log T)
      + ε * (T * Real.log T) := by
    have hmono : xiSymmetricMass T ≤ xiSymmetricMass T₂ :=
      xiSymmetricMass_mono hT0.le hT₂mem.1.le
    have hmono' : (xiSymmetricMass T : ℝ) ≤ (xiSymmetricMass T₂ : ℝ) := by exact_mod_cast hmono
    have hb := hadm T₂ (by linarith [hT₂mem.1]) hT₂adm
    rw [abs_le, ← hPdef] at hb
    have hT₂log : T₂ * Real.log T₂ ≤ (T + 1) * Real.log (T + 1) :=
      mul_log_mono (by linarith [hT₂mem.1]) hT₂mem.2.le
    have hT₂log' : (T + 1) * Real.log (T + 1) ≤ T * Real.log T + Real.log T + 2 :=
      succ_mul_log_le (by linarith)
    have hcoef : (P + ε₁) * (T₂ * Real.log T₂)
        ≤ (P + ε₁) * (T * Real.log T + Real.log T + 2) :=
      mul_le_mul_of_nonneg_left (le_trans hT₂log hT₂log') (by positivity)
    linarith [hmono', hb.2, hcoef, hkey, hεrel]
  have hlower : P * (T * Real.log T) - ε * (T * Real.log T)
      ≤ (xiSymmetricMass T : ℝ) := by
    have hmono : xiSymmetricMass T₃ ≤ xiSymmetricMass T :=
      xiSymmetricMass_mono (by linarith [hT₃mem.1]) hT₃mem.2.le
    have hmono' : (xiSymmetricMass T₃ : ℝ) ≤ (xiSymmetricMass T : ℝ) := by exact_mod_cast hmono
    have hb := hadm T₃ (by linarith [hT₃mem.1]) hT₃adm
    rw [abs_le, ← hPdef] at hb
    have hT₃low : T * Real.log T - Real.log T - 2 ≤ T₃ * Real.log T₃ := by
      refine le_trans (pred_mul_log_ge (by linarith)) ?_
      exact mul_log_mono (by linarith [hT₃mem.1]) hT₃mem.1.le
    have hT₃high : T₃ * Real.log T₃ ≤ T * Real.log T :=
      mul_log_mono (by linarith [hT₃mem.1]) hT₃mem.2.le
    have hcoef : P * (T * Real.log T - Real.log T - 2)
        ≤ P * (T₃ * Real.log T₃) :=
      mul_le_mul_of_nonneg_left hT₃low (by positivity)
    have hcoef2 : ε₁ * (T₃ * Real.log T₃) ≤ ε₁ * (T * Real.log T) :=
      mul_le_mul_of_nonneg_left hT₃high hε₁.le
    have hslack : (0 : ℝ) ≤ ε₁ * Real.log T := by positivity
    linarith [hmono', hb.1, hcoef, hcoef2, hkey, hslack, hεrel]
  rw [abs_le]
  constructor <;> linarith

end RHTower

end
