import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LinearFlowFourierPacketWindow

open Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

noncomputable section

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Multiplicative Fourier ℓ¹ cost for an indexed packet.  Indexing retains
mode-sheet multiplicity instead of collapsing equal characters. -/
noncomputable def indexedMultiplicativeFourierL1Cost
    (c : ι → ℂ) (q : ι → (Fin n → ℤ)) (eps : ℝ) : ℝ :=
  ∑ i, ‖c i‖ * (PiPlus (q i) / PiPlus (q i) ^ (-eps))

/-- Indexed finite-packet discrepancy.  Equal characters may occur on many
sheets; their full coefficient cost is retained. -/
theorem exists_global_indexedFourierPacketWindowSuppression
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (c : ι → ℂ) (q : ι → (Fin n → ℤ)),
        (∀ i, q i ≠ 0) → ∀ u T : ℝ, 0 < T →
          ‖(1 / (T : ℂ)) *
              ∫ t in u..(u + T),
                ∑ i, c i * Complex.exp
                  ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I)‖ ≤
            (2 * C / T) * indexedMultiplicativeFourierL1Cost c q eps := by
  classical
  obtain ⟨C, hC, hchar⟩ :=
    exists_global_characterWindowSuppression hy heps
  refine ⟨C, hC, ?_⟩
  intro c q hq u T hT
  have hsplit :
      (1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ i, c i * Complex.exp
              ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I) =
        ∑ i, c i * ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            Complex.exp ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I)) := by
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [intervalIntegral.integral_const_mul]
        ring
    · intro i _
      exact (intervalIntegrable_exp_mode (dotProd (q i) y) u T).const_mul (c i)
  rw [hsplit]
  calc
    ‖∑ i, c i * ((1 / (T : ℂ)) *
        ∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I))‖ ≤
      ∑ i, ‖c i * ((1 / (T : ℂ)) *
        ∫ t in u..(u + T),
          Complex.exp ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, (2 * C / T) *
        (‖c i‖ * (PiPlus (q i) / PiPlus (q i) ^ (-eps))) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hw : 0 < PiPlus (q i) ^ (-eps) :=
        Real.rpow_pos_of_pos (PiPlus_pos (q i)) _
      have hi := hchar (q i) (hq i) u T hT
      have hmean :
          ‖(1 / (T : ℂ)) *
              ∫ t in u..(u + T),
                Complex.exp ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I)‖ ≤
            (2 * C * PiPlus (q i) / T) / PiPlus (q i) ^ (-eps) :=
        (le_div_iff₀ hw).2 hi
      rw [norm_mul]
      calc
        ‖c i‖ *
            ‖(1 / (T : ℂ)) *
              ∫ t in u..(u + T),
                Complex.exp ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I)‖ ≤
          ‖c i‖ * ((2 * C * PiPlus (q i) / T) / PiPlus (q i) ^ (-eps)) :=
          mul_le_mul_of_nonneg_left hmean (norm_nonneg _)
        _ = (2 * C / T) *
            (‖c i‖ * (PiPlus (q i) / PiPlus (q i) ^ (-eps))) := by ring
    _ = (2 * C / T) * indexedMultiplicativeFourierL1Cost c q eps := by
      rw [indexedMultiplicativeFourierL1Cost, Finset.mul_sum]

/-- Centered indexed law with arbitrary Haar constant. -/
theorem exists_global_indexedFourierPacketHaarDiscrepancy
    {y : Fin n → ℝ} (hy : ¬ VWMA y) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a₀ : ℂ) (c : ι → ℂ) (q : ι → (Fin n → ℤ)),
        (∀ i, q i ≠ 0) → ∀ u T : ℝ, 0 < T →
          ‖((1 / (T : ℂ)) *
              ∫ t in u..(u + T),
                (a₀ + ∑ i, c i * Complex.exp
                  ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I))) - a₀‖ ≤
            (2 * C / T) * indexedMultiplicativeFourierL1Cost c q eps := by
  classical
  obtain ⟨C, hC, hpacket⟩ :=
    exists_global_indexedFourierPacketWindowSuppression (ι := ι) hy heps
  refine ⟨C, hC, ?_⟩
  intro a₀ c q hq u T hT
  have hint : IntervalIntegrable
      (fun t : ℝ => ∑ i, c i * Complex.exp
        ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I))
      MeasureTheory.volume u (u + T) := by
    have hcont : Continuous fun t : ℝ => ∑ i, c i * Complex.exp
        ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I) := by
      refine continuous_finsetSum _ fun i _ => ?_
      fun_prop
    exact hcont.intervalIntegrable u (u + T)
  have hcenter :
      ((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            (a₀ + ∑ i, c i * Complex.exp
              ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I))) - a₀ =
        (1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ∑ i, c i * Complex.exp
              ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I) := by
    let J : ℂ := ∫ t in u..(u + T),
      ∑ i, c i * Complex.exp
        ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I)
    have hadd :
        (∫ t in u..(u + T),
          (a₀ + ∑ i, c i * Complex.exp
            ((t : ℂ) * (dotProd (q i) y : ℂ) * Complex.I))) =
          (T : ℂ) * a₀ + J := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hint,
        intervalIntegral.integral_const, add_sub_cancel_left, Complex.real_smul]
    rw [hadd]
    change (1 / (T : ℂ)) * ((T : ℂ) * a₀ + J) - a₀ =
      (1 / (T : ℂ)) * J
    have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hT
    field_simp
    ring
  rw [hcenter]
  exact hpacket c q hq u T hT

end

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
