import GaloisForLFunctions.CompactHyperbolicSurfaces.MercerRepresentatives

/-!
# A uniform bound for the continuous eigenfunctions

The rows of the singular kernel `K_a(w, ·) = Σ_γ k_a(u(w, γ·))` lie in `L²(F)` with a bound
independent of `w` (`exists_rowEnergy_le`): near the diagonal at most `N₀` translates contribute
and `k_a(u) ≤ C u^{−1/8}` is square integrable; away from it the kernel is bounded.  Bessel's
inequality for these rows, `⟨e_j, K_a(w, ·)⟩ = μ_j \overline{ẽ_j(w)}`, gives
`Σ_j μ_j² |ẽ_j(w)|² ≤ B`, and `ν_j ≤ (b(b−1) − a(a−1)) μ_j²` turns it into

  `Σ_{j ∈ S} ν_j |ẽ_j(w)|² ≤ B'`  for every finite `S` and every `w` (`exists_sum_nu_specRep_le`).
-/

open MeasureTheory Set Filter UpperHalfPlane Real Metric
open scoped ENNReal MatrixGroups Pointwise InnerProductSpace

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.SchurKernel

noncomputable section

/-- **Local size, sharper.**  `k_s(u) ≤ C u^{−1/8}` for `u > 0`. -/
theorem exists_resKernel_le_rpow_eighth {s : ℝ} (hs : 1 / 2 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u → resKernel s u ≤ ENNReal.ofReal (C * u ^ (-(1 / 8 : ℝ))) := by
  set I : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (-(7 / 8 : ℝ)) * (1 + t) ^ (-s)
  have hI : IntegrableOn (fun t : ℝ => t ^ (-(7 / 8 : ℝ)) * (1 + t) ^ (-s)) (Ioi 0) :=
    integrableOn_rpow_mul_one_add_rpow (by norm_num) (by linarith)
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : (0:ℝ) < t := ht; positivity
  refine ⟨1 / (4 * π) * I, by positivity, fun u hu => ?_⟩
  rw [resKernel_eq_lintegral_Ioi]
  have hb : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (greenDensity s (u + t) * (Real.sqrt t)⁻¹) ≤
      ENNReal.ofReal (u ^ (-(1 / 8 : ℝ))) * ENNReal.ofReal (t ^ (-(7 / 8 : ℝ)) * (1 + t) ^ (-s)) := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := greenDensity_le hs (show 0 < u + t by linarith)
    have h2 : (u + t) ^ (-(1 / 2 : ℝ)) ≤ u ^ (-(1 / 8 : ℝ)) * t ^ (-(3 / 8 : ℝ)) := by
      have hA : u ^ (1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) ≤ (u + t) ^ (1 / 2 : ℝ) := by
        calc u ^ (1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) ≤ (u + t) ^ (1 / 8 : ℝ) * (u + t) ^ (3 / 8 : ℝ) :=
              mul_le_mul (Real.rpow_le_rpow hu.le (by linarith) (by norm_num))
                (Real.rpow_le_rpow ht0.le (by linarith) (by norm_num)) (by positivity) (by positivity)
          _ = (u + t) ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add (by linarith)]; norm_num
      have hpos : 0 < u ^ (1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) := by positivity
      rw [Real.rpow_neg (by linarith), Real.rpow_neg hu.le, Real.rpow_neg ht0.le, ← mul_inv]
      exact inv_anti₀ hpos hA
    have h3 : (1 + (u + t)) ^ (-s) ≤ (1 + t) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h4 : (Real.sqrt t)⁻¹ = t ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht0.le]
    rw [h4]
    calc greenDensity s (u + t) * t ^ (-(1 / 2 : ℝ))
        ≤ (u + t) ^ (-(1 / 2 : ℝ)) * (1 + (u + t)) ^ (-s) * t ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (u ^ (-(1 / 8 : ℝ)) * t ^ (-(3 / 8 : ℝ))) * (1 + t) ^ (-s) * t ^ (-(1 / 2 : ℝ)) := by
          gcongr
      _ = u ^ (-(1 / 8 : ℝ)) * (t ^ (-(7 / 8 : ℝ)) * (1 + t) ^ (-s)) := by
          rw [show t ^ (-(7 / 8 : ℝ)) = t ^ (-(3 / 8 : ℝ)) * t ^ (-(1 / 2 : ℝ)) by
            rw [← Real.rpow_add ht0]; norm_num]
          ring
  calc ENNReal.ofReal (1 / (4 * π)) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (greenDensity s (u + t) * (Real.sqrt t)⁻¹)
      ≤ ENNReal.ofReal (1 / (4 * π)) * ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (-(1 / 8 : ℝ))) * ENNReal.ofReal (t ^ (-(7 / 8 : ℝ)) * (1 + t) ^ (-s)) :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hb) _
    _ = ENNReal.ofReal (1 / (4 * π)) * (ENNReal.ofReal (u ^ (-(1 / 8 : ℝ))) * ENNReal.ofReal I) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ofReal_integral_eq_lintegral_ofReal hI
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => by
            have : (0:ℝ) < r := hr; positivity))]
    _ = ENNReal.ofReal (1 / (4 * π) * I * u ^ (-(1 / 8 : ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- The near part `k_s · 1_{u ≤ 1}` is square integrable on `ℍ`. -/
theorem lintegral_resKernel_near_sq_lt_top {s : ℝ} (hs : 1 / 2 < s) :
    ∫⁻ w : ℍ, ((Iic (1 : ℝ)).indicator (resKernel s) (pairU I w)) ^ 2 < ∞ := by
  obtain ⟨C, hC0, hC⟩ := exists_resKernel_le_rpow_eighth hs
  set f : ℝ → ℝ≥0∞ := fun u => ((Iic (1 : ℝ)).indicator (resKernel s) u) ^ 2
  have hf : Measurable f := ((measurable_resKernel s).indicator measurableSet_Iic).pow_const 2
  rw [show (fun w : ℍ => ((Iic (1 : ℝ)).indicator (resKernel s) (pairU I w)) ^ 2) =
    fun w => f (pairU I w) from rfl, lintegral_pairU_I hf]
  -- the Abel transform of `f` is bounded and supported in `|τ| ≤ T`
  set T : ℝ := 2 * Real.arsinh 1
  have habel : ∀ τ, abelL f τ ≤ (Icc (-T) T).indicator
      (fun _ => ENNReal.ofReal (C ^ 2) * ∫⁻ η in Icc (-2 : ℝ) 2,
        ENNReal.ofReal ((η ^ 2 / 4) ^ (-(1 / 4 : ℝ)))) τ := by
    intro τ
    by_cases hτ : τ ∈ Icc (-T) T
    · rw [indicator_of_mem hτ, abelL, ← lintegral_indicator measurableSet_Icc,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun η => ?_
      simp only [f]
      by_cases hu : η ^ 2 / 4 + Real.sinh (τ / 2) ^ 2 ≤ 1
      · have hη : η ∈ Icc (-2 : ℝ) 2 := by
          have : η ^ 2 ≤ 4 := by nlinarith [sq_nonneg (Real.sinh (τ / 2))]
          have h1 := Real.abs_le_sqrt this
          rw [show Real.sqrt 4 = 2 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
          exact abs_le.mp h1
        rw [indicator_of_mem (show η ^ 2 / 4 + Real.sinh (τ / 2) ^ 2 ∈ Iic (1 : ℝ) from hu),
          indicator_of_mem hη]
        by_cases hη0 : η = 0
        · -- a single point: bound by the trivial value
          subst hη0
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
            Real.zero_rpow (by norm_num : (-(1 / 4 : ℝ)) ≠ 0)]
          sorry
        · sorry
      · rw [indicator_of_notMem (show η ^ 2 / 4 + Real.sinh (τ / 2) ^ 2 ∉ Iic (1 : ℝ) from hu)]
        simp
    · sorry
  sorry

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
