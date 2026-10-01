import GaloisForLFunctions.RHTower.BourgainPhasePerturbation
import GaloisForLFunctions.RHTower.VanDerCorputLocal

open Complex MeasureTheory Set
noncomputable section
namespace RHTower

/-- Conductor saddle entropy, written with separate logarithms for differentiation. -/
def chiStationaryEntropy (a t : ℝ) : ℝ :=
  t * (Real.log t - Real.log a) - t + a

/-- The complete model tail on either side of its saddle has inverse-distance
control, uniformly over every subinterval of the comparable-height window. -/
theorem norm_integral_chiStationaryEntropy_exterior_le
    {a h l u : ℝ} (ha : 0 < a) (hh : 0 < h) (hl : a / 2 ≤ l)
    (hlu : l ≤ u) (hu : u ≤ 2 * a) (hside : u ≤ a - h ∨ a + h ≤ l) :
    ‖∫ t in l..u, bourgainOscillation (chiStationaryEntropy a t)‖ ≤ 16 * a / h := by
  have hxpos (x : ℝ) (hx : x ∈ Icc l u) : 0 < x := by linarith [hx.1]
  have hd (x : ℝ) (hx : x ∈ Icc l u) :
      HasDerivAt (chiStationaryEntropy a) (Real.log x - Real.log a) x := by
    have hx0 := hxpos x hx
    have hderiv := (((hasDerivAt_id x).mul
      ((Real.hasDerivAt_log hx0.ne').sub_const (Real.log a))).sub (hasDerivAt_id x)).add_const a
    apply hderiv.congr_deriv
    dsimp only [id]
    simp only [one_mul, mul_inv_cancel₀ hx0.ne', add_sub_cancel_right]
  have hd' (x : ℝ) (hx : x ∈ Icc l u) :
      HasDerivAt (fun t : ℝ => Real.log t - Real.log a) x⁻¹ x :=
    (Real.hasDerivAt_log (hxpos x hx).ne').sub_const _
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Icc l u) :=
    fun x hx => (continuousAt_inv₀ (hxpos x hx).ne').continuousWithinAt
  have hbound (x : ℝ) (hx : x ∈ Icc l u) :
      h / (2 * a) ≤ |Real.log x - Real.log a| := by
    have hx0 := hxpos x hx
    rw [← Real.log_div hx0.ne' ha.ne']
    rcases hside with hleft | hright
    · have hlog := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hx0 ha)) ha.le
      have he : a * (x / a - 1) = x - a := by field_simp
      rw [he] at hlog
      have hn : Real.log (x / a) < 0 := by nlinarith [hx.2]
      rw [abs_of_neg hn, div_le_iff₀ (by positivity : 0 < 2 * a)]
      nlinarith [hx.2]
    · have hlog := mul_le_mul_of_nonneg_left
        (Real.one_sub_inv_le_log_of_pos (div_pos hx0 ha)) hx0.le
      have he : x * (1 - (x / a)⁻¹) = x - a := by field_simp
      rw [he] at hlog
      have hn : 0 < Real.log (x / a) := by nlinarith [hx.1]
      rw [abs_of_pos hn, div_le_iff₀ (by positivity : 0 < 2 * a)]
      nlinarith [hx.1, hx.2, mul_nonneg (show 0 ≤ 2 * a - x by linarith [hx.2]) hn.le]
  have hb := firstDerivTestOn hlu (by positivity : 0 < h / (2 * a))
    hd hd' hc (fun x _ => hasDerivAt_const x (1 : ℂ)) continuousOn_const
    (fun x hx => inv_nonneg.mpr (hxpos x hx).le) hbound
  have he : (∫ t in l..u, (1 : ℂ) * Complex.exp (I * (chiStationaryEntropy a t : ℂ))) =
      ∫ t in l..u, bourgainOscillation (chiStationaryEntropy a t) := by
    simp only [one_mul, bourgainOscillation]
  rw [he] at hb
  simp only [norm_one, norm_zero, intervalIntegral.integral_zero, add_zero] at hb
  calc
    _ ≤ 4 * (1 + 1) / (h / (2 * a)) := hb
    _ = _ := by field_simp; ring

/-- The exterior bound for the reversed conductor phase used by actual chi. -/
theorem norm_integral_chiStationaryEntropy_neg_exterior_le
    {a h l u : ℝ} (ha : 0 < a) (hh : 0 < h) (hl : a / 2 ≤ l)
    (hlu : l ≤ u) (hu : u ≤ 2 * a) (hside : u ≤ a - h ∨ a + h ≤ l) :
    ‖∫ t in l..u, bourgainOscillation (-chiStationaryEntropy a t)‖ ≤ 16 * a / h := by
  have he (t : ℝ) : bourgainOscillation (-chiStationaryEntropy a t) =
      (starRingEnd ℂ) (bourgainOscillation (chiStationaryEntropy a t)) := by
    unfold bourgainOscillation
    rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  have hi : (∫ t in l..u, bourgainOscillation (-chiStationaryEntropy a t)) =
      (starRingEnd ℂ) (∫ t in l..u, bourgainOscillation (chiStationaryEntropy a t)) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    exact intervalIntegral.integral_congr (fun t _ => he t)
  rw [hi, Complex.norm_conj]
  exact norm_integral_chiStationaryEntropy_exterior_le ha hh hl hlu hu hside

end RHTower
