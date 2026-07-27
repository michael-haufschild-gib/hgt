import GaloisForLFunctions.RHTower.DirichletLLeftEdge
import GaloisForLFunctions.RHTower.DirichletCompletedLOrderOne

/-!
# Growth of the Dirichlet L-function inside the strip

Inside `-2 ≤ Re s ≤ 3`, away from the real axis, the L-function is the completed L-function divided
by the Archimedean factor.  The numerator obeys the order-one envelope; the denominator is bounded
below by `κ e^{-π|t|/2}` because `Γ` is, and `e^{π|t|/2}` is itself dominated by the order-one
envelope.  So the L-function satisfies an order-one envelope on the strip — far inside the
double-exponential allowance of the Phragmén–Lindelöf principle.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **Order-one growth of `L` inside the strip.** -/
theorem exists_growth_LFunction_strip {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, -2 ≤ s.re → s.re ≤ 3 → 2 ≤ |s.im| →
      ‖DirichletCharacter.LFunction χ s‖
        ≤ Real.exp (B * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨d, hd, hgf⟩ := gammaFactor_eq_Gammaℝ χ
  obtain ⟨C, hC, henv⟩ := completedLFunction_orderOneEnvelope hχ
  obtain ⟨B₀, hB₀, hlow⟩ := exists_lower_bound_norm_Gamma_strip (-1 : ℝ) (2 : ℝ)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  set κ : ℝ := Real.pi ^ (-2 : ℝ) * Real.pi / B₀ with hκ
  have hκpos : 0 < κ := by rw [hκ]; positivity
  set L₀ : ℝ := max (Real.log (1 / κ)) 0 with hL₀
  have hL₀nn : 0 ≤ L₀ := le_max_right _ _
  refine ⟨C + Real.pi / (2 * Real.log 2) + L₀ / Real.log 2,
    add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hC (by positivity)) (by positivity),
    fun s h1 h2 h3 => ?_⟩
  have hsim : s.im ≠ 0 := by
    intro h
    rw [h] at h3
    norm_num at h3
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hsim
    simp at hsim
  -- the Archimedean factor
  have hargim : ((s + ((d : ℝ) : ℂ)) / 2).im = s.im / 2 := by simp
  have hargre : ((s + ((d : ℝ) : ℂ)) / 2).re = (s.re + d) / 2 := by simp
  have hargabs : 1 ≤ |((s + ((d : ℝ) : ℂ)) / 2).im| := by
    rw [hargim, abs_div, show |(2 : ℝ)| = 2 by norm_num]
    linarith
  have hd0 : 0 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  have hd1 : d ≤ 1 := by rcases hd with rfl | rfl <;> norm_num
  have hargbound := hlow ((s + ((d : ℝ) : ℂ)) / 2) (by rw [hargre]; linarith)
    (by rw [hargre]; linarith) hargabs
  have hgfne : DirichletCharacter.gammaFactor χ s ≠ 0 := by
    rw [hgf s]
    intro hcon
    rw [Complex.Gammaℝ_eq_zero_iff] at hcon
    obtain ⟨n, hn⟩ := hcon
    have him : (s + ((d : ℝ) : ℂ)).im = s.im := by simp
    rw [hn] at him
    simp at him
    exact hsim him.symm
  have hLeq := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hsne)
  have hΛ : DirichletCharacter.completedLFunction χ s
      = DirichletCharacter.LFunction χ s * DirichletCharacter.gammaFactor χ s := by
    rw [hLeq, div_mul_cancel₀ _ hgfne]
  have hnormΛ : ‖DirichletCharacter.LFunction χ s‖ *
      ‖DirichletCharacter.gammaFactor χ s‖ = ‖DirichletCharacter.completedLFunction χ s‖ := by
    rw [hΛ, norm_mul]
  -- lower bound on the Archimedean factor
  have hgfval : ‖DirichletCharacter.gammaFactor χ s‖
      = Real.pi ^ (-(s.re + d) / 2) * ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖ := by
    rw [hgf s, norm_Gammaℝ]
    congr 2
  have hpipow : Real.pi ^ (-(2 : ℝ)) ≤ Real.pi ^ (-(s.re + d) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hpi1 (by linarith)
  have hEpos : (0 : ℝ) < Real.exp (Real.pi * |s.im| / 2) := Real.exp_pos _
  have hGnn : 0 ≤ ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖ := norm_nonneg _
  have hargeq : Real.pi * |((s + ((d : ℝ) : ℂ)) / 2).im| = Real.pi * |s.im| / 2 := by
    rw [hargim, abs_div, show |(2 : ℝ)| = 2 by norm_num]
    ring
  rw [hargeq] at hargbound
  -- `κ e^{-π|t|/2} ≤ ‖gammaFactor‖`
  have hgflow : κ * Real.exp (-(Real.pi * |s.im| / 2))
      ≤ ‖DirichletCharacter.gammaFactor χ s‖ := by
    rw [hgfval, hκ]
    have hEinv : Real.exp (-(Real.pi * |s.im| / 2)) * Real.exp (Real.pi * |s.im| / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have hstep : Real.pi ^ (-(2 : ℝ)) * Real.pi / B₀ * Real.exp (-(Real.pi * |s.im| / 2))
        ≤ Real.pi ^ (-(2 : ℝ)) * ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hB₀]
      have hmul := mul_le_mul_of_nonneg_left hargbound
        (by positivity :
          (0 : ℝ) ≤ Real.pi ^ (-(2 : ℝ)) * Real.exp (-(Real.pi * |s.im| / 2)))
      have hcollapse : Real.pi ^ (-(2 : ℝ)) * Real.exp (-(Real.pi * |s.im| / 2)) *
          (B₀ * Real.exp (Real.pi * |s.im| / 2) *
            ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖)
          = Real.pi ^ (-(2 : ℝ)) * ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖ * B₀ := by
        linear_combination (Real.pi ^ (-(2 : ℝ)) * B₀ *
          ‖Complex.Gamma ((s + ((d : ℝ) : ℂ)) / 2)‖) * hEinv
      linarith [hmul, hcollapse]
    refine hstep.trans (mul_le_mul_of_nonneg_right hpipow hGnn)
  -- combine
  have hLnn : 0 ≤ ‖DirichletCharacter.LFunction χ s‖ := norm_nonneg _
  have hkey : ‖DirichletCharacter.LFunction χ s‖ * (κ * Real.exp (-(Real.pi * |s.im| / 2)))
      ≤ Real.exp (orderOneWeight C s) := by
    calc ‖DirichletCharacter.LFunction χ s‖ * (κ * Real.exp (-(Real.pi * |s.im| / 2)))
        ≤ ‖DirichletCharacter.LFunction χ s‖ * ‖DirichletCharacter.gammaFactor χ s‖ :=
          mul_le_mul_of_nonneg_left hgflow hLnn
      _ = ‖DirichletCharacter.completedLFunction χ s‖ := hnormΛ
      _ ≤ Real.exp (orderOneWeight C s) := henv s
  -- absorb the exponential and the constant into an order-one envelope
  have hsnn : 0 ≤ ‖s‖ := norm_nonneg s
  have himle : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hshape := log_two_le_shape s
  have hshapenn := shape_nonneg s
  have hexpand : orderOneWeight C s + Real.pi * |s.im| / 2 + L₀
      ≤ (C + Real.pi / (2 * Real.log 2) + L₀ / Real.log 2) * (1 + ‖s‖) * Real.log (2 + ‖s‖) := by
    rw [orderOneWeight]
    have hA : Real.pi * |s.im| / 2
        ≤ Real.pi / (2 * Real.log 2) * ((1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log 2)]
      have hp1 : |s.im| * Real.log 2 ≤ (1 + ‖s‖) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hlog2.le
      have hlogle : Real.log 2 ≤ Real.log (2 + ‖s‖) :=
        Real.log_le_log (by norm_num) (by linarith)
      have hp2 : (1 + ‖s‖) * Real.log 2 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) :=
        mul_le_mul_of_nonneg_left hlogle (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left (hp1.trans hp2) Real.pi_pos.le]
    have hB : L₀ ≤ L₀ / Real.log 2 * ((1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith [hshape, hL₀nn]
    nlinarith [hA, hB]
  have hfinal : ‖DirichletCharacter.LFunction χ s‖
      ≤ Real.exp (orderOneWeight C s + Real.pi * |s.im| / 2 + L₀) := by
    have hκinv : Real.exp L₀ * κ ≥ 1 := by
      have hlk : Real.log (1 / κ) ≤ L₀ := le_max_left _ _
      have h1 : Real.exp (Real.log (1 / κ)) = 1 / κ := Real.exp_log (by positivity)
      have h2 : (1 : ℝ) / κ ≤ Real.exp L₀ := by
        rw [← h1]
        exact Real.exp_le_exp.mpr hlk
      rw [ge_iff_le, ← div_le_iff₀ hκpos]
      simpa [one_div] using h2
    have hsplit : Real.exp (orderOneWeight C s + Real.pi * |s.im| / 2 + L₀)
        = Real.exp (orderOneWeight C s) * Real.exp (Real.pi * |s.im| / 2) * Real.exp L₀ := by
      rw [← Real.exp_add, ← Real.exp_add]
    rw [hsplit]
    have hEinv : Real.exp (-(Real.pi * |s.im| / 2)) * Real.exp (Real.pi * |s.im| / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have hstep1 : ‖DirichletCharacter.LFunction χ s‖ * κ
        ≤ Real.exp (orderOneWeight C s) * Real.exp (Real.pi * |s.im| / 2) := by
      have hmul := mul_le_mul_of_nonneg_right hkey hEpos.le
      have hrw : ‖DirichletCharacter.LFunction χ s‖ *
          (κ * Real.exp (-(Real.pi * |s.im| / 2))) * Real.exp (Real.pi * |s.im| / 2)
          = ‖DirichletCharacter.LFunction χ s‖ * κ *
            (Real.exp (-(Real.pi * |s.im| / 2)) * Real.exp (Real.pi * |s.im| / 2)) := by ring
      rw [hrw, hEinv, mul_one] at hmul
      exact hmul
    have hstep2 : ‖DirichletCharacter.LFunction χ s‖
        ≤ ‖DirichletCharacter.LFunction χ s‖ * (κ * Real.exp L₀) := by
      nlinarith [hLnn, hκinv]
    calc ‖DirichletCharacter.LFunction χ s‖
        ≤ ‖DirichletCharacter.LFunction χ s‖ * (κ * Real.exp L₀) := hstep2
      _ = ‖DirichletCharacter.LFunction χ s‖ * κ * Real.exp L₀ := by ring
      _ ≤ Real.exp (orderOneWeight C s) * Real.exp (Real.pi * |s.im| / 2) * Real.exp L₀ :=
          mul_le_mul_of_nonneg_right hstep1 (Real.exp_pos _).le
  exact hfinal.trans (Real.exp_le_exp.mpr hexpand)

end RHTower
