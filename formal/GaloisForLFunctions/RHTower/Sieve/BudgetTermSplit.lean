import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetLadderTail

/-!
# Splitting the normalised budget

The Route E gate divides the budget by `W²h²√x`.  The resulting quotient splits into four groups:
the Gallagher head, the two tail groups, and the non-spectral part.
-/

namespace RHTower.Sieve

noncomputable section

/-- **The normalised budget, split.** -/
theorem budget_div_eq {sx h W G T0 δ αL βL Ec B0 ns1 ns2 : ℝ}
    (hsx : 0 < sx) (hW : 0 < W) (hh : 0 < h) (hG : 0 < G) :
    (16 * sx * (2 * δ ^ (2 : ℕ) * (αL * G + βL)
        + (4 * (αL + 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * B0 * Ec / T0)
              / (Real.pi ^ (2 : ℕ) * G)
          + 4 * βL / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ)))) + ns1 + ns2) / (W ^ (2 : ℕ) * h ^ (2 : ℕ) * sx)
      = 32 * δ ^ (2 : ℕ) * (αL * G + βL) / (W ^ (2 : ℕ) * h ^ (2 : ℕ))
        + 64 * (αL + 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * B0 * Ec / T0)
            / (Real.pi ^ (2 : ℕ) * G * (W ^ (2 : ℕ) * h ^ (2 : ℕ)))
        + 64 * βL / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ)))
        + (ns1 + ns2) / (W ^ (2 : ℕ) * h ^ (2 : ℕ) * sx) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp
  ring

/-- **The three spectral groups, reduced to three quotients.** -/
theorem spectral_terms_le {sx h W G T0 δ αL βL Ec B0 : ℝ}
    (hsx : 0 < sx) (hW : 1 ≤ W) (hh : 1 ≤ h) (hB0 : 0 < B0)
    (hδ : 0 ≤ δ) (hδle : δ ≤ h / sx) (hGh : G * h = B0) (hG0 : 0 < G) (hT0 : T0 = B0)
    (hxB : B0 ^ (2 : ℕ) ≤ 4 * sx ^ (2 : ℕ)) (hαL : 0 ≤ αL) (hβL : 0 ≤ βL) (hEc : 0 ≤ Ec) :
    32 * δ ^ (2 : ℕ) * (αL * G + βL) / (W ^ (2 : ℕ) * h ^ (2 : ℕ))
        + 64 * (αL + 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * B0 * Ec / T0)
            / (Real.pi ^ (2 : ℕ) * G * (W ^ (2 : ℕ) * h ^ (2 : ℕ)))
        + 64 * βL / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ)))
      ≤ 136 * αL / (B0 * h * W ^ (2 : ℕ)) + 140 * Ec / (B0 * h * W ^ (2 : ℕ))
        + 131 * βL / (B0 ^ (2 : ℕ) * W ^ (2 : ℕ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hp9 : (9 : ℝ) ≤ Real.pi ^ (2 : ℕ) := by nlinarith [hpi3]
  have he3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hW2 : (0 : ℝ) < W ^ (2 : ℕ) := pow_pos hW0 2
  have hh2 : (0 : ℝ) < h ^ (2 : ℕ) := pow_pos hh0 2
  have hsx2 : (0 : ℝ) < sx ^ (2 : ℕ) := pow_pos hsx 2
  have hB02 : (0 : ℝ) < B0 ^ (2 : ℕ) := pow_pos hB0 2
  have hG2 : (0 : ℝ) < G ^ (2 : ℕ) := pow_pos hG0 2
  have hWh : (0 : ℝ) < W ^ (2 : ℕ) * h ^ (2 : ℕ) := mul_pos hW2 hh2
  have hBhW : (0 : ℝ) < B0 * h * W ^ (2 : ℕ) := mul_pos (mul_pos hB0 hh0) hW2
  have hB2W : (0 : ℝ) < B0 ^ (2 : ℕ) * W ^ (2 : ℕ) := mul_pos hB02 hW2
  have hsxW : (0 : ℝ) < sx ^ (2 : ℕ) * W ^ (2 : ℕ) := mul_pos hsx2 hW2
  have h9G : (0 : ℝ) < 9 * G * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) := by
    have : (0 : ℝ) < 9 * G := by linarith
    exact mul_pos this hWh
  have h27G : (0 : ℝ) < 27 * G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) := by
    have : (0 : ℝ) < 27 * G ^ (2 : ℕ) := by linarith
    exact mul_pos this hWh
  have hδsq : δ ^ (2 : ℕ) ≤ h ^ (2 : ℕ) / sx ^ (2 : ℕ) := by
    have := pow_le_pow_left₀ hδ hδle 2
    rw [div_pow] at this
    exact this
  have hA : 32 * δ ^ (2 : ℕ) * (αL * G + βL) / (W ^ (2 : ℕ) * h ^ (2 : ℕ))
      ≤ 128 * αL / (B0 * h * W ^ (2 : ℕ)) + 128 * βL / (B0 ^ (2 : ℕ) * W ^ (2 : ℕ)) := by
    have hnum0 : (0 : ℝ) ≤ αL * G + βL := by
      have := mul_nonneg hαL hG0.le
      linarith
    have hstep : 32 * δ ^ (2 : ℕ) * (αL * G + βL) ≤ 32 * (h ^ (2 : ℕ) / sx ^ (2 : ℕ)) * (αL * G + βL) := by
      nlinarith [hδsq, hnum0]
    refine (div_le_div_of_nonneg_right hstep hWh.le).trans ?_
    have hid : 32 * (h ^ (2 : ℕ) / sx ^ (2 : ℕ)) * (αL * G + βL) / (W ^ (2 : ℕ) * h ^ (2 : ℕ))
        = 32 * (αL * G) / (sx ^ (2 : ℕ) * W ^ (2 : ℕ)) + 32 * βL / (sx ^ (2 : ℕ) * W ^ (2 : ℕ)) := by
      field_simp
    rw [hid]
    have h1 : 32 * (αL * G) / (sx ^ (2 : ℕ) * W ^ (2 : ℕ)) ≤ 128 * αL / (B0 * h * W ^ (2 : ℕ)) := by
      rw [div_le_div_iff₀ hsxW hBhW]
      have hkey : 32 * (αL * G) * (B0 * h * W ^ (2 : ℕ)) = 32 * αL * B0 ^ (2 : ℕ) * W ^ (2 : ℕ) := by
        rw [← hGh]; ring
      rw [hkey]
      nlinarith [mul_nonneg (mul_nonneg hαL (by linarith : (0:ℝ) ≤ 4 * sx ^ (2 : ℕ) - B0 ^ (2 : ℕ)))
        hW2.le]
    have h2 : 32 * βL / (sx ^ (2 : ℕ) * W ^ (2 : ℕ)) ≤ 128 * βL / (B0 ^ (2 : ℕ) * W ^ (2 : ℕ)) := by
      rw [div_le_div_iff₀ hsxW hB2W]
      nlinarith [mul_nonneg (mul_nonneg hβL (by linarith : (0:ℝ) ≤ 4 * sx ^ (2 : ℕ) - B0 ^ (2 : ℕ)))
        hW2.le]
    linarith
  have hB : 64 * (αL + 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * B0 * Ec / T0)
        / (Real.pi ^ (2 : ℕ) * G * (W ^ (2 : ℕ) * h ^ (2 : ℕ)))
      ≤ 8 * αL / (B0 * h * W ^ (2 : ℕ)) + 140 * Ec / (B0 * h * W ^ (2 : ℕ)) := by
    have hval : 5 * Real.exp 1 / 2 * B0 * Ec / T0 = 5 * Real.exp 1 / 2 * Ec := by
      rw [hT0]
      field_simp
    rw [hval]
    have hcoef : 5 * Real.pi / 2 + 5 * Real.exp 1 / 2 ≤ 18 := by linarith
    have hcoefEc : 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * Ec ≤ 18 * Ec := by
      have h0 := mul_le_mul_of_nonneg_right hcoef hEc
      rw [add_mul] at h0
      linarith
    have hnum : 64 * (αL + 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * Ec)
        ≤ 64 * (αL + 18 * Ec) := by linarith
    have hc0 : (0 : ℝ) ≤ 64 * (αL + 18 * Ec) := by linarith
    have hden : (9 : ℝ) * G * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) ≤ Real.pi ^ (2 : ℕ) * G * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) := by
      have hfac : (0 : ℝ) ≤ G * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) := mul_nonneg hG0.le hWh.le
      have h0 : (9 : ℝ) * (G * (W ^ (2 : ℕ) * h ^ (2 : ℕ))) ≤ Real.pi ^ (2 : ℕ) * (G * (W ^ (2 : ℕ) * h ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_right hp9 hfac
      calc (9 : ℝ) * G * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) = 9 * (G * (W ^ (2 : ℕ) * h ^ (2 : ℕ))) := by ring
        _ ≤ Real.pi ^ (2 : ℕ) * (G * (W ^ (2 : ℕ) * h ^ (2 : ℕ))) := h0
        _ = Real.pi ^ (2 : ℕ) * G * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) := by ring
    refine (div_le_div₀ hc0 hnum h9G hden).trans ?_
    have hd : (9 : ℝ) * G * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) = 9 * (B0 * h * W ^ (2 : ℕ)) := by
      rw [← hGh]; ring
    rw [hd]
    have hid : 64 * (αL + 18 * Ec) / (9 * (B0 * h * W ^ (2 : ℕ)))
        = 64 / 9 * αL / (B0 * h * W ^ (2 : ℕ)) + 128 * Ec / (B0 * h * W ^ (2 : ℕ)) := by
      field_simp
      ring
    rw [hid]
    have h1 : 64 / 9 * αL / (B0 * h * W ^ (2 : ℕ)) ≤ 8 * αL / (B0 * h * W ^ (2 : ℕ)) := by
      refine div_le_div_of_nonneg_right ?_ hBhW.le
      linarith
    have h3 : 128 * Ec / (B0 * h * W ^ (2 : ℕ)) ≤ 140 * Ec / (B0 * h * W ^ (2 : ℕ)) := by
      refine div_le_div_of_nonneg_right ?_ hBhW.le
      linarith
    linarith
  have hC : 64 * βL / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ)))
      ≤ 3 * βL / (B0 ^ (2 : ℕ) * W ^ (2 : ℕ)) := by
    have hden : (27 : ℝ) * G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ))
        ≤ 3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) := by
      have hfac : (0 : ℝ) ≤ G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) := mul_nonneg hG2.le hWh.le
      have h0 : (27 : ℝ) * (G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ)))
          ≤ (3 * Real.pi ^ (2 : ℕ)) * (G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_right (by linarith) hfac
      calc (27 : ℝ) * G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) = 27 * (G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ))) := by ring
        _ ≤ (3 * Real.pi ^ (2 : ℕ)) * (G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ))) := h0
        _ = 3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) := by ring
    have h64 : (0 : ℝ) ≤ 64 * βL := by linarith
    refine (div_le_div_of_nonneg_left h64 h27G hden).trans ?_
    have hd : (27 : ℝ) * G ^ (2 : ℕ) * (W ^ (2 : ℕ) * h ^ (2 : ℕ)) = 27 * (B0 ^ (2 : ℕ) * W ^ (2 : ℕ)) := by
      rw [← hGh]; ring
    rw [hd]
    have hid : 64 * βL / (27 * (B0 ^ (2 : ℕ) * W ^ (2 : ℕ))) = 64 / 27 * βL / (B0 ^ (2 : ℕ) * W ^ (2 : ℕ)) := by
      field_simp
    rw [hid]
    refine div_le_div_of_nonneg_right ?_ hB2W.le
    linarith
  have hfin1 : 128 * αL / (B0 * h * W ^ (2 : ℕ)) + 8 * αL / (B0 * h * W ^ (2 : ℕ))
      = 136 * αL / (B0 * h * W ^ (2 : ℕ)) := by ring
  have hfin2 : 128 * βL / (B0 ^ (2 : ℕ) * W ^ (2 : ℕ)) + 3 * βL / (B0 ^ (2 : ℕ) * W ^ (2 : ℕ))
      = 131 * βL / (B0 ^ (2 : ℕ) * W ^ (2 : ℕ)) := by ring
  linarith [hA, hB, hC]

end

end RHTower.Sieve
