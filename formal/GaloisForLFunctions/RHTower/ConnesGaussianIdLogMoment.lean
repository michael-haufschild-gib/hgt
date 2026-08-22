import GaloisForLFunctions.RHTower.ConnesGaussianLogMoment

/-!
# The `x log x` Gaussian moment at an arbitrary width

The corpus already owns the case `b = 2π` (`connes_integral_id_log_mul_gaussian_twoPi`, App. II
(41)); the §V constant needs the case `b = π`, so the computation is recorded here for every
positive width.  The proof is the substitution `t = b r²` against
`∫_0^∞ e^{-t} log t dt = -γ`.
-/

open MeasureTheory Set Filter Topology Real

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- `∫_0^∞ r log r e^{-b r²} dr = (-γ - log b)/(4b)` for every `b > 0`. -/
theorem connes_integral_id_log_mul_gaussian {b : ℝ} (hb : 0 < b) :
    (∫ r : ℝ in Ioi 0, r * (Real.log r * Real.exp (-b * r ^ 2)))
      = (-Real.eulerMascheroniConstant - Real.log b) / (4 * b) := by
  set H : ℝ → ℝ := fun t => Real.log t * Real.exp (-t) with hH
  set M : ℝ := ∫ r : ℝ in Ioi 0, r * (Real.log r * Real.exp (-b * r ^ 2)) with hM
  have hscale : (∫ x : ℝ in Ioi 0, H (b * x)) = b⁻¹ • ∫ x : ℝ in Ioi 0, H x := by
    have h := integral_comp_mul_left_Ioi H 0 hb
    simpa using h
  have hquad : (∫ r : ℝ in Ioi 0, ((|(2:ℝ)| * r ^ ((2:ℝ) - 1)) • H (b * r ^ (2:ℝ))))
      = ∫ y : ℝ in Ioi 0, H (b * y) :=
    integral_comp_rpow_Ioi (fun s : ℝ => H (b * s)) (p := 2) two_ne_zero
  have hpt : ∀ r ∈ Ioi (0:ℝ), ((|(2:ℝ)| * r ^ ((2:ℝ) - 1)) • H (b * r ^ (2:ℝ)))
      = 2 * Real.log b * (r * Real.exp (-b * r ^ 2))
        + 4 * (r * (Real.log r * Real.exp (-b * r ^ 2))) := by
    intro r hr
    have hr0 : (0:ℝ) < r := hr
    have hr2 : r ^ (2:ℝ) = r ^ (2:ℕ) := by
      rw [← Real.rpow_natCast r 2]; norm_num
    have hlogprod : Real.log (b * r ^ (2:ℝ)) = Real.log b + 2 * Real.log r := by
      rw [Real.log_mul (ne_of_gt hb) (by positivity), Real.log_rpow hr0]
    have hexp : Real.exp (-(b * r ^ (2:ℝ))) = Real.exp (-b * r ^ 2) := by
      rw [hr2]; ring_nf
    simp only [hH, smul_eq_mul, hlogprod, hexp]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hxr : r ^ ((2:ℝ) - 1) = r := by norm_num
    rw [hxr]
    ring
  have hsplit : (∫ r : ℝ in Ioi 0,
        (2 * Real.log b * (r * Real.exp (-b * r ^ 2))
          + 4 * (r * (Real.log r * Real.exp (-b * r ^ 2)))))
      = 2 * Real.log b * (1 / (2 * b)) + 4 * M := by
    have h1 : IntegrableOn (fun r : ℝ =>
        2 * Real.log b * (r * Real.exp (-b * r ^ 2))) (Ioi (0:ℝ)) := by
      have h0 := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (1:ℝ))
        (by norm_num)).integrableOn (s := Ioi (0:ℝ))
      have h0' : IntegrableOn (fun r : ℝ => r * Real.exp (-b * r ^ 2)) (Ioi (0:ℝ)) := by
        refine h0.congr ?_
        filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x _
        rw [Real.rpow_one]
      exact h0'.const_mul _
    have h2 : IntegrableOn (fun r : ℝ =>
        4 * (r * (Real.log r * Real.exp (-b * r ^ 2)))) (Ioi (0:ℝ)) := by
      have h0 := connes_integrableOn_pow_log_mul_gaussian hb 1
      have h0' : IntegrableOn (fun r : ℝ =>
          r * (Real.log r * Real.exp (-b * r ^ 2))) (Ioi (0:ℝ)) := by
        refine h0.congr ?_
        filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x _
        rw [pow_one]
      exact h0'.const_mul _
    rw [integral_add h1 h2, integral_const_mul, integral_const_mul,
      connes_integral_id_mul_gaussian_Ioi hb, ← hM]
  have hkey : (∫ x : ℝ in Ioi 0, H x)
      = b * (2 * Real.log b * (1 / (2 * b)) + 4 * M) := by
    have h1 : (∫ y : ℝ in Ioi 0, H (b * y))
        = 2 * Real.log b * (1 / (2 * b)) + 4 * M := by
      rw [← hquad, setIntegral_congr_fun measurableSet_Ioi hpt, hsplit]
    have h2 : b⁻¹ * (∫ x : ℝ in Ioi 0, H x)
        = 2 * Real.log b * (1 / (2 * b)) + 4 * M := by
      rw [← h1, hscale, smul_eq_mul]
    calc (∫ x : ℝ in Ioi 0, H x) = b * (b⁻¹ * ∫ x : ℝ in Ioi 0, H x) := by
          field_simp
      _ = b * (2 * Real.log b * (1 / (2 * b)) + 4 * M) := by rw [h2]
  rw [hH] at hkey
  rw [HTGeometry.integral_log_mul_exp_neg_Ioi] at hkey
  have hbne : b ≠ 0 := ne_of_gt hb
  rw [hM] at hkey ⊢
  field_simp at hkey ⊢
  linarith [hkey]

end

end GaloisForLFunctions.RHTower
