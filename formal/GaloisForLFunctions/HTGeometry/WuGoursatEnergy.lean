import GaloisForLFunctions.HTGeometry.WuDoubleNullEnergy
import GaloisForLFunctions.HTGeometry.ClockGoursatPointwise

/-!
# Characteristic source integration with closed energy bounds

Wu's Lemma 2.3 applies to the corpus's Goursat/clock Volterra operator.
The kernel and source are arbitrary bounded continuous data. Their norms
supply all bounds in the existing operator API, including continuity in both
characteristic coordinates. The resulting rectangle estimate also controls
perturbations of the source.
-/
namespace GaloisForLFunctions.HTGeometry.Wu
open MeasureTheory
noncomputable section

/-- The existing characteristic Volterra operator as a jointly bounded continuous field. -/
def goursatResponse (K : BoundedContinuousFunction (ℝ × ℝ) ℝ) (b : ℝ)
    (U : BoundedContinuousFunction ℝ ℝ) : BoundedContinuousFunction (ℝ × ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => volterraFun (fun r => K (p.1, r)) 0 |b| U p.2)
    (by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      · exact (K.continuous.comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).mul
          (U.continuous.comp continuous_snd)
      · exact (continuous_clampTo 0 |b|).comp continuous_snd)
    (‖K‖ * |b| * ‖U‖)
    (fun p => by
      rw [Real.norm_eq_abs]
      have hb := abs_volterraFun_le (abs_nonneg b)
        (K := fun r => K (p.1, r)) (U := U)
        (fun r _ => by simpa only [Real.norm_eq_abs] using K.norm_coe_le_norm (p.1, r))
        (fun r => by simpa only [Real.norm_eq_abs] using U.norm_coe_le_norm r)
        (norm_nonneg K) (norm_nonneg U) p.2
      simpa only [sub_zero, mul_right_comm] using hb)

theorem norm_goursatResponse_le (K : BoundedContinuousFunction (ℝ × ℝ) ℝ) (b : ℝ)
    (U : BoundedContinuousFunction ℝ ℝ) : ‖goursatResponse K b U‖ ≤ ‖K‖ * |b| * ‖U‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

/-- The integrated source vanishes on its incoming characteristic boundary. -/
theorem goursatResponse_boundary (K : BoundedContinuousFunction (ℝ × ℝ) ℝ) (b ξ : ℝ)
    (U : BoundedContinuousFunction ℝ ℝ) : goursatResponse K b U (ξ, 0) = 0 := by
  change volterraFun (fun r => K (ξ, r)) 0 |b| U 0 = 0
  simp [volterraFun, clampTo]

/-- Differentiation recovers the original source in the interior of the characteristic interval. -/
theorem goursatResponse_hasDerivAt (K : BoundedContinuousFunction (ℝ × ℝ) ℝ) (b ξ : ℝ)
    (U : BoundedContinuousFunction ℝ ℝ) :
    HasDerivAt (fun η => goursatResponse K (Real.exp b) U (ξ, η))
      (K (ξ, Real.exp b / 2) * U (Real.exp b / 2)) (Real.exp b / 2) := by
  apply hasDerivAt_volterraFun
    (K.continuous.comp (continuous_const.prodMk continuous_id)) U.continuous
  constructor
  · positivity
  · rw [abs_of_pos (Real.exp_pos b)]
    linarith [Real.exp_pos b]

/-- One characteristic slice gains one inverse rate in squared energy. -/
theorem goursat_slice_energy_le (K : BoundedContinuousFunction (ℝ × ℝ) ℝ)
    (b ξ d t : ℝ) (U : BoundedContinuousFunction ℝ ℝ) :
    energy d t (fun η => volterraFun (fun r => K (ξ, r)) 0 |b| U η) ≤
      (‖K‖ * |b| * ‖U‖) ^ (2 : ℕ) / (2 * Real.exp d) := by
  let p : C(ℝ, ℝ × ℝ) := ⟨fun η => (ξ, η), continuous_const.prodMk continuous_id⟩
  have hb : ‖(goursatResponse K b U).compContinuous p‖ ≤ ‖K‖ * |b| * ‖U‖ :=
    ((goursatResponse K b U).norm_compContinuous_le p).trans (norm_goursatResponse_le K b U)
  exact (energy_le d t ((goursatResponse K b U).compContinuous p)).trans
    (div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb) (by positivity))

/-- Full characteristic rectangle control for the actual Volterra response. -/
theorem goursat_rectangle_energy_le (K : BoundedContinuousFunction (ℝ × ℝ) ℝ)
    (b d u v : ℝ) (U : BoundedContinuousFunction ℝ ℝ) :
    rectangleEnergy d u v (fun p => volterraFun (fun r => K (p.1, r)) 0 |b| U p.2) ≤
      (‖K‖ * |b| * ‖U‖) ^ (2 : ℕ) / (2 * Real.exp d) ^ (2 : ℕ) := by
  exact (rectangleEnergy_le d u v (goursatResponse K b U)).trans
    (div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_goursatResponse_le K b U))
      (sq_nonneg _))

/-- Source subtraction commutes with characteristic integration. -/
theorem goursatResponse_sub (K : BoundedContinuousFunction (ℝ × ℝ) ℝ) (b : ℝ)
    (U V : BoundedContinuousFunction ℝ ℝ) :
    goursatResponse K b U - goursatResponse K b V = goursatResponse K b (U - V) := by
  ext p
  change (∫ r in (0 : ℝ)..clampTo 0 |b| p.2, K (p.1, r) * U r) -
    (∫ r in (0 : ℝ)..clampTo 0 |b| p.2, K (p.1, r) * V r) =
    ∫ r in (0 : ℝ)..clampTo 0 |b| p.2, K (p.1, r) * (U r - V r)
  have hK : Continuous (fun r : ℝ => K (p.1, r)) :=
    K.continuous.comp (continuous_const.prodMk continuous_id)
  have hU : IntervalIntegrable (fun r => K (p.1, r) * U r) volume 0 (clampTo 0 |b| p.2) :=
    (hK.mul U.continuous).intervalIntegrable _ _
  have hV : IntervalIntegrable (fun r => K (p.1, r) * V r) volume 0 (clampTo 0 |b| p.2) :=
    (hK.mul V.continuous).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hU hV]
  simp_rw [mul_sub]

/-- Residual stability: the response error depends on the source error, with no background-size loss. -/
theorem goursat_difference_energy_le (K : BoundedContinuousFunction (ℝ × ℝ) ℝ)
    (b d u v : ℝ) (U V : BoundedContinuousFunction ℝ ℝ) :
    rectangleEnergy d u v (fun p => goursatResponse K b U p - goursatResponse K b V p) ≤
      (‖K‖ * |b| * ‖U - V‖) ^ (2 : ℕ) / (2 * Real.exp d) ^ (2 : ℕ) := by
  change rectangleEnergy d u v (goursatResponse K b U - goursatResponse K b V) ≤ _
  rw [goursatResponse_sub]
  exact goursat_rectangle_energy_le K b d u v (U - V)

end
end GaloisForLFunctions.HTGeometry.Wu
