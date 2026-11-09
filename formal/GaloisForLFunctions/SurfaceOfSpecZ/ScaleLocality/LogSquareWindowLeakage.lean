import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ZetaMixedMomentBounds

/-!
# Exponentially small leakage from logarithmic-square windows

The zeta head and tail moment bounds allow a Chernoff parameter equal
to the observation height. A fixed logarithmic-square radius then pays
for the whole moment and leaves exponentially small leakage.
-/

open Complex Filter Topology
open _root_.RHTower
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

def zetaLogSquareMomentConstant : ℝ :=
  80 * Real.pi * (xiLineTwoLogDerivConstant + 2) + 32 * Real.pi ^ 2

def zetaLogSquareRadius : ℝ := 2 * (zetaLogSquareMomentConstant + 1)

theorem zetaLogSquareRadius_pos : 0 < zetaLogSquareRadius := by
  have hA := xiLineTwoLogDerivConstant_nonneg
  unfold zetaLogSquareRadius zetaLogSquareMomentConstant
  positivity

private theorem zetaHeadShiftBound_le_logSquare {T : ℝ} (hT : 3 ≤ T)
    (hE : 1 ≤ Real.log (T + 2)) :
    zetaHeadShiftBound T ≤
      40 * Real.pi * (xiLineTwoLogDerivConstant + 2) * Real.log (T + 2) ^ 2 := by
  let A := xiLineTwoLogDerivConstant
  let E := Real.log (T + 2)
  have hA : 0 ≤ A := xiLineTwoLogDerivConstant_nonneg
  have hE0 : 0 ≤ E := by dsimp only [E]; linarith only [hE]
  have hlog6 : Real.log (T + 6) ≤ 2 * E := by
    have hh := Real.log_le_log (show 0 < T + 6 by linarith only [hT])
      (show T + 6 ≤ (T + 2) ^ 2 by nlinarith only [hT, sq_nonneg T])
    rw [Real.log_pow] at hh
    norm_num at hh
    exact hh
  have hlog1 : Real.log (T + 1) ≤ E :=
    Real.log_le_log (by linarith only [hT]) (by linarith)
  have ha : A + Real.log (T + 6) ≤ (A + 2) * E := by
    have hh := mul_le_mul_of_nonneg_left hE hA
    change A * 1 ≤ A * E at hh
    nlinarith only [hh, hlog6]
  have hb : 1 + Real.log (T + 1) ≤ 2 * E := by
    change 1 ≤ E at hE
    linarith only [hE, hlog1]
  have hb0 : 0 ≤ 1 + Real.log (T + 1) := by
    have hh := Real.log_nonneg (show 1 ≤ T + 1 by linarith only [hT])
    linarith only [hh]
  have hm := mul_le_mul ha hb hb0 (show 0 ≤ (A + 2) * E by positivity)
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 20 * Real.pi by positivity)
  calc
    zetaHeadShiftBound T = 20 * Real.pi *
        ((A + Real.log (T + 6)) * (1 + Real.log (T + 1))) := by
      unfold zetaHeadShiftBound A
      ring
    _ ≤ 20 * Real.pi * (((A + 2) * E) * (2 * E)) := hm'
    _ = _ := by dsimp only [A, E]; ring

/-- At moment parameter `D+T`, every zeta prefix costs at most `C₀ T log²(T+2)`. -/
theorem zetaMixedMomentBound_le_logSquare {D T : ℝ} (hD : 0 ≤ D) (hDT : D ≤ T)
    (hT : 3 ≤ T) (hE : 1 ≤ Real.log (T + 2)) :
    zetaMixedMomentBound T (D + T) ≤
      zetaLogSquareMomentConstant * T * Real.log (T + 2) ^ 2 := by
  let A := xiLineTwoLogDerivConstant
  let E := Real.log (T + 2)
  have hA : 0 ≤ A := xiLineTwoLogDerivConstant_nonneg
  have hE0 : 0 ≤ E := by dsimp only [E]; linarith only [hE]
  have hT0 : 0 < T := by linarith only [hT]
  have hs0 : 0 ≤ D + T := by linarith only [hD, hT0]
  have hs : D + T ≤ 2 * T := by linarith only [hDT]
  have hh := zetaHeadShiftBound_le_logSquare hT hE
  have hhead : (D + T) * zetaHeadShiftBound T ≤ 80 * Real.pi * (A + 2) * T * E ^ 2 := by
    calc
      _ ≤ (D + T) * (40 * Real.pi * (A + 2) * E ^ 2) :=
        mul_le_mul_of_nonneg_left hh hs0
      _ ≤ (2 * T) * (40 * Real.pi * (A + 2) * E ^ 2) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by ring
  have hlog : Real.log T ≤ E := Real.log_le_log hT0 (by linarith)
  have htail : zetaTailSquareBound T ≤ 16 * Real.pi ^ 2 * E / T := by
    have hh := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hlog hT0.le) (show 0 ≤ 16 * Real.pi ^ 2 by positivity)
    calc
      zetaTailSquareBound T = 16 * Real.pi ^ 2 * (Real.log T / T) := rfl
      _ ≤ 16 * Real.pi ^ 2 * (E / T) := hh
      _ = _ := by ring
  have hsq : (D + T) ^ 2 / 2 ≤ 2 * T ^ 2 := by
    have hh := pow_le_pow_left₀ hs0 hs 2
    nlinarith only [hh]
  have hEsq : E ≤ E ^ 2 := by
    change 1 ≤ E at hE
    nlinarith only [hE, sq_nonneg (E - 1)]
  have hquad : ((D + T) ^ 2 / 2) * zetaTailSquareBound T ≤ 32 * Real.pi ^ 2 * T * E ^ 2 := by
    calc
      _ ≤ ((D + T) ^ 2 / 2) * (16 * Real.pi ^ 2 * E / T) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ (2 * T ^ 2) * (16 * Real.pi ^ 2 * E / T) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 32 * Real.pi ^ 2 * T * E := by field_simp [hT0.ne']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hEsq (by positivity)
  unfold zetaMixedMomentBound
  rw [abs_of_nonneg hs0]
  change (D + T) * zetaHeadShiftBound T + ((D + T) ^ 2 / 2) * zetaTailSquareBound T ≤
    zetaLogSquareMomentConstant * T * E ^ 2
  unfold zetaLogSquareMomentConstant
  change _ ≤ (80 * Real.pi * (A + 2) + 32 * Real.pi ^ 2) * T * E ^ 2
  nlinarith only [hhead, hquad]

/-- A fixed log-square radius leaves exponentially small leakage for every zeta deletion tail. -/
theorem infinite_zeta_logSquare_floor {ι : Type*} (α : ℝ) (M : ℕ) (c w : ι → ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hc : Summable fun i => ‖c i‖)
    (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D) {K B T t : ℝ}
    (hK : 0 ≤ K) (hDT : D ≤ T) (hT : 3 ≤ T) (hheight : Real.exp 12 ≤ T)
    (hE : 1 ≤ Real.log (T + 2)) (hED : D + 1 ≤ Real.log (T + 2) ^ 2)
    (ht : |t| ≤ T + B)
    (hlocal : ∀ u, |u - t| ≤ zetaLogSquareRadius * Real.log (T + 2) ^ 2 / 2 →
      -K ≤ ∑' i, (c i * Complex.exp (w i * u)).re) :
    -K - 2 * (∑' i, ‖c i‖) * Real.exp (D * B - T) ≤
      ∑' i, (c i * (∏' n, quartetFactor (zetaDeletionDepth α (n + M))
        (zetaDeletionShift (n + M)) (w i)) * Complex.exp (w i * t)).re := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hsq : Summable fun n => zetaDeletionShift (n + M) ^ 2 :=
    (summable_nat_add_iff M).mpr summable_zetaDeletionShift_sq
  have hmoment := zetaMixedMomentBound_le_logSquare hD hDT hT hE
  have hf := infinite_tail_translated_mixed_floor
    (fun n => zetaDeletionDepth α (n + M)) (fun n => zetaDeletionShift (n + M))
    hsq c w hD hc hw hK hT0
    (fun N => (zeta_mixedMomentCost_le α M N (D + T) hheight).trans hmoment) hlocal
  have harg : D * |t| - T * (zetaLogSquareRadius * Real.log (T + 2) ^ 2 / 2) +
      zetaLogSquareMomentConstant * T * Real.log (T + 2) ^ 2 ≤ D * B - T := by
    have hh := mul_le_mul_of_nonneg_left ht hD
    have he := mul_le_mul_of_nonneg_right hED hT0
    unfold zetaLogSquareRadius
    nlinarith only [hh, he]
  have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg)
    (show 0 ≤ 2 * (∑' i, ‖c i‖) by positivity)
  linarith only [hf, hm]

#print axioms zetaMixedMomentBound_le_logSquare
#print axioms infinite_zeta_logSquare_floor

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
