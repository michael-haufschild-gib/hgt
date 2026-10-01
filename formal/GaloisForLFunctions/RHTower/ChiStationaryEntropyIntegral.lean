import GaloisForLFunctions.RHTower.ChiStationaryExteriorBound
import GaloisForLFunctions.RHTower.ChiStationaryQuadraticError
import GaloisForLFunctions.RHTower.QuadraticPhaseStationary

open Complex MeasureTheory Set
noncomputable section
namespace RHTower

/-- The reversed model phase is integrable on every positive compact interval. -/
theorem intervalIntegrable_chiStationaryEntropy_neg (a : ℝ) {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) :
    IntervalIntegrable (fun t => bourgainOscillation (-chiStationaryEntropy a t)) volume l u := by
  have hlog : ContinuousOn Real.log (Set.uIcc l u) := by
    intro x hx
    rw [Set.uIcc_of_le hlu] at hx
    exact (Real.continuousAt_log (hl.trans_le hx.1).ne').continuousWithinAt
  have hd : ContinuousOn (chiStationaryEntropy a) (Set.uIcc l u) := by
    unfold chiStationaryEntropy
    exact ((continuousOn_id.mul (hlog.sub continuousOn_const)).sub continuousOn_id).add continuousOn_const
  have hb : Continuous bourgainOscillation := by unfold bourgainOscillation; fun_prop
  exact (hb.comp_continuousOn hd.neg).intervalIntegrable

private theorem norm_integral_entropy_center_sub_quad_le {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) (hha : h ≤ a / 2) :
    ‖(∫ t in (a - h)..(a + h), bourgainOscillation (-chiStationaryEntropy a t)) -
      ∫ t in (a - h)..(a + h), bourgainOscillation (-(t - a) ^ 2 / (2 * a))‖ ≤
        4 * h ^ 4 / a ^ 2 := by
  have hab : a - h ≤ a + h := by linarith
  have hf := intervalIntegrable_chiStationaryEntropy_neg a (show 0 < a - h by linarith) hab
  have hg : IntervalIntegrable (fun t : ℝ => bourgainOscillation (-(t - a) ^ 2 / (2 * a))) volume
      (a - h) (a + h) := by
    apply Continuous.intervalIntegrable
    unfold bourgainOscillation
    fun_prop
  rw [← intervalIntegral.integral_sub hf hg]
  have hbound : ∀ t ∈ Set.uIoc (a - h) (a + h),
      ‖bourgainOscillation (-chiStationaryEntropy a t) -
        bourgainOscillation (-(t - a) ^ 2 / (2 * a))‖ ≤ 2 * h ^ 3 / a ^ 2 := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hdist : |t - a| ≤ h := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have herr := abs_stationary_entropy_sub_quadratic_le ha (hdist.trans hha)
    rw [Real.log_div ht0.ne' ha.ne'] at herr
    apply (norm_bourgainOscillation_sub_le _ _).trans
    have he : -chiStationaryEntropy a t - (-(t - a) ^ 2 / (2 * a)) =
        -(t * (Real.log t - Real.log a) - t + a - (t - a) ^ 2 / (2 * a)) := by
      unfold chiStationaryEntropy
      ring
    rw [he, abs_neg]
    apply herr.trans
    gcongr
  apply (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans_eq
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  ring

private theorem norm_integral_entropy_center_sub_value_le {a h : ℝ}
    (ha : 0 < a) (hh : 0 < h) (hha : h ≤ a / 2) :
    ‖(∫ t in (a - h)..(a + h), bourgainOscillation (-chiStationaryEntropy a t)) -
      (Real.sqrt (2 * Real.pi * a) : ℂ) * bourgainOscillation (-(Real.pi / 4))‖ ≤
        4 * h ^ 4 / a ^ 2 + 8 * a / h := by
  let Q : ℝ → ℂ := fun t => bourgainOscillation (-(t - a) ^ 2 / (2 * a))
  let M : ℂ := (Real.sqrt (2 * Real.pi * a) : ℂ) * bourgainOscillation (-(Real.pi / 4))
  have htrans : (∫ t in (a - h)..(a + h), Q t) =
      ∫ x in (-h)..h, Complex.exp (((-((a⁻¹) * x ^ 2 / 2) : ℝ) : ℂ) * I) := by
    have he (t : ℝ) : Q t =
        (fun x : ℝ => Complex.exp (((-((a⁻¹) * x ^ 2 / 2) : ℝ) : ℂ) * I)) (t - a) := by
      dsimp only [Q, bourgainOscillation]
      congr 1
      push_cast
      ring
    rw [intervalIntegral.integral_congr (fun t _ => he t),
      intervalIntegral.integral_comp_sub_right
        (fun x : ℝ => Complex.exp (((-((a⁻¹) * x ^ 2 / 2) : ℝ) : ℂ) * I)) a]
    congr 1 <;> ring
  have hquad : ‖(∫ t in (a - h)..(a + h), Q t) - M‖ ≤ 8 * a / h := by
    have hfres := GaloisForLFunctions.RHTower.norm_integral_quadPhase_conj_sub_le (inv_pos.mpr ha) hh
    have hm : (Real.sqrt (2 * Real.pi / a⁻¹) : ℂ) *
        Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I) = M := by
      dsimp only [M, bourgainOscillation]
      rw [div_inv_eq_mul]
      congr 1
      congr 1
      ring
    rw [htrans, ← hm]
    apply hfres.trans_eq
    field_simp
  have hc := norm_integral_entropy_center_sub_quad_le ha hh hha
  calc
    _ = ‖((∫ t in (a - h)..(a + h), bourgainOscillation (-chiStationaryEntropy a t)) -
        ∫ t in (a - h)..(a + h), Q t) + ((∫ t in (a - h)..(a + h), Q t) - M)‖ := by
      congr 1
      dsimp only [M]
      ring
    _ ≤ ‖(∫ t in (a - h)..(a + h), bourgainOscillation (-chiStationaryEntropy a t)) -
        ∫ t in (a - h)..(a + h), Q t‖ + ‖(∫ t in (a - h)..(a + h), Q t) - M‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hc hquad

/-- Full stationary leading term for the literal conductor entropy. Every
finite pre-saddle and post-saddle segment is retained with an explicit error. -/
theorem norm_integral_entropy_sub_stationary_value_le {a h l u : ℝ}
    (ha : 0 < a) (hh : 0 < h) (hha : h ≤ a / 2)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a) :
    ‖(∫ t in l..u, bourgainOscillation (-chiStationaryEntropy a t)) -
      (Real.sqrt (2 * Real.pi * a) : ℂ) * bourgainOscillation (-(Real.pi / 4))‖ ≤
        4 * h ^ 4 / a ^ 2 + 40 * a / h := by
  let f : ℝ → ℂ := fun t => bourgainOscillation (-chiStationaryEntropy a t)
  let M : ℂ := (Real.sqrt (2 * Real.pi * a) : ℂ) * bourgainOscillation (-(Real.pi / 4))
  have hl0 : 0 < l := by linarith
  have hc0 : 0 < a - h := by linarith
  have hc : a - h ≤ a + h := by linarith
  have hi1 := intervalIntegrable_chiStationaryEntropy_neg a hl0 hlh
  have hi2 := intervalIntegrable_chiStationaryEntropy_neg a hc0 hc
  have hi3 := intervalIntegrable_chiStationaryEntropy_neg a (show 0 < a + h by linarith) hhu
  have hi12 := intervalIntegrable_chiStationaryEntropy_neg a hl0 (show l ≤ a + h by linarith)
  have hsplit : (∫ t in l..u, f t) = (∫ t in l..(a - h), f t) +
      (∫ t in (a - h)..(a + h), f t) + (∫ t in (a + h)..u, f t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hi12 hi3,
      ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hleft := norm_integral_chiStationaryEntropy_neg_exterior_le ha hh hl hlh
    (show a - h ≤ 2 * a by linarith) (Or.inl (le_refl _))
  have hright := norm_integral_chiStationaryEntropy_neg_exterior_le ha hh
    (show a / 2 ≤ a + h by linarith) hhu hu (Or.inr (le_refl _))
  have hcenter := norm_integral_entropy_center_sub_value_le ha hh hha
  change ‖(∫ t in l..u, f t) - M‖ ≤ _
  rw [hsplit]
  have he : (∫ t in l..(a - h), f t) + (∫ t in (a - h)..(a + h), f t) +
      (∫ t in (a + h)..u, f t) - M =
      ((∫ t in l..(a - h), f t) + ((∫ t in (a - h)..(a + h), f t) - M)) +
        (∫ t in (a + h)..u, f t) := by ring
  rw [he]
  have htri := (norm_add_le ((∫ t in l..(a - h), f t) +
    ((∫ t in (a - h)..(a + h), f t) - M)) (∫ t in (a + h)..u, f t)).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
  apply htri.trans
  change ‖∫ t in l..(a - h), f t‖ + ‖(∫ t in (a - h)..(a + h), f t) - M‖ +
      ‖∫ t in (a + h)..u, f t‖ ≤ _
  calc
    _ ≤ 16 * a / h + (4 * h ^ 4 / a ^ 2 + 8 * a / h) + 16 * a / h :=
      add_le_add (add_le_add hleft hcenter) hright
    _ = _ := by ring

end RHTower
