import GaloisForLFunctions.RHTower.PaperThetaRelativeTail
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmIntervalAnomaly

/-! # A lower tail bound for the actual theta CDF

A window of length `exp (-2*x)` retains a fixed proportion of the theta
envelope. Its mass bounds the reciprocal CDF tail needed at the Fourier seam.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

private theorem exp_sub_one_le (s : ℝ) :
    Real.exp s - 1 ≤ s * Real.exp s := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-s)) (Real.exp_pos s).le
  rw [← Real.exp_add] at h
  simp only [neg_add_cancel, Real.exp_zero] at h
  nlinarith

private theorem envelope_short_window {x s : ℝ} (hx : 1 ≤ x)
    (hs : s ∈ Icc 0 (Real.exp (-2*x))) :
    Real.exp (-2*Real.pi*Real.exp 2) * thetaEnvelope x ≤ thetaEnvelope (x+s) := by
  have hh : Real.exp (-2*x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsmall : Real.exp (2*s) - 1 ≤ 2*Real.exp 2*s := by
    calc
      _ ≤ (2*s)*Real.exp (2*s) := exp_sub_one_le _
      _ ≤ (2*s)*Real.exp 2 := by gcongr <;> linarith [hs.1, hs.2]
      _ = _ := by ring
  have hexpcancel : Real.exp (2*x)*Real.exp (-2*x) = 1 := by
    rw [← Real.exp_add, show 2*x + -2*x = 0 by ring, Real.exp_zero]
  have hdiff : Real.exp (2*(x+s)) - Real.exp (2*x) ≤ 2*Real.exp 2 := by
    calc
      _ = Real.exp (2*x)*(Real.exp (2*s)-1) := by
        rw [show 2*(x+s)=2*x+2*s by ring, Real.exp_add]; ring
      _ ≤ Real.exp (2*x)*(2*Real.exp 2*s) := by gcongr
      _ ≤ Real.exp (2*x)*(2*Real.exp 2*Real.exp (-2*x)) := by gcongr; exact hs.2
      _ = 2*Real.exp 2 := by
        calc
          _ = (2*Real.exp 2)*(Real.exp (2*x)*Real.exp (-2*x)) := by ring
          _ = _ := by rw [hexpcancel, mul_one]
  unfold thetaEnvelope
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos, hs.1]

/-- A concrete positive lower bound on the right CDF tail. -/
theorem cdfTail_ge_short_window (x : Ici (1 : ℝ)) :
    Real.exp (-2*x.1) *
        (thetaEnvelopeLower * Real.exp (-2*Real.pi*Real.exp 2) * thetaEnvelope x.1) /
          thetaSource.mass ≤ 1 - thetaSource.cdfFun x.1 := by
  let h := Real.exp (-2*x.1)
  let C := thetaEnvelopeLower * Real.exp (-2*Real.pi*Real.exp 2) * thetaEnvelope x.1
  have hx : 1 ≤ x.1 := x.2
  have hh : 0 < h := Real.exp_pos _
  have hab : x.1 ≤ x.1+h := by linarith
  have hlocal : ∀ y ∈ Ioc x.1 (x.1+h), C ≤ thetaSource.k y := by
    intro y hy
    have he := envelope_short_window x.2 (s := y-x.1) ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hl := thetaCuspFullSource_ge_envelope (show 0 < y by linarith [hy.1])
    calc
      C ≤ thetaEnvelopeLower * thetaEnvelope y := by
        dsimp [C]
        have := mul_le_mul_of_nonneg_left he thetaEnvelopeLower_pos.le
        simpa only [add_sub_cancel, mul_assoc] using this
      _ ≤ _ := hl
  have hmass : h*C ≤ thetaSource.mass *
      (thetaSource.cdfFun (x.1+h) - thetaSource.cdfFun x.1) := by
    rw [HedenmalmIntervalAnomaly.mass_mul_cdfFun_sub thetaSource hab,
      HedenmalmIntervalAnomaly.intervalMass]
    calc
      h*C = ∫ _ in Ioc x.1 (x.1+h), C := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hab]
        simp
      _ ≤ _ := setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
        thetaSource.integrable_k.integrableOn measurableSet_Ioc hlocal
  have hF := (thetaSource.cdfFun_mem_Ioo (x.1+h)).2
  change h*C/thetaSource.mass ≤ _
  apply (div_le_iff₀ thetaSource.mass_pos).mpr
  nlinarith [thetaSource.mass_pos]

/-- The actual density divided by its remaining CDF mass grows at most as `exp (2*x)`. -/
theorem cdfHazard_le_exp (x : Ici (1 : ℝ)) :
    thetaSource.normalized x.1 / (1 - thetaSource.cdfFun x.1) ≤
      (thetaEnvelopeUpper / (thetaEnvelopeLower * Real.exp (-2*Real.pi*Real.exp 2))) *
        Real.exp (2*x.1) := by
  have hx : 1 ≤ x.1 := x.2
  have hLpos := thetaEnvelopeLower_pos
  have hUpos := thetaEnvelopeUpper_pos
  have hMpos := thetaSource.mass_pos
  have hL := cdfTail_ge_short_window x
  have hU := thetaCuspFullSource_le_envelope (show 0 ≤ x.1 by linarith)
  have hE := thetaEnvelope_pos x.1
  have hc := Real.exp_pos (-2*Real.pi*Real.exp 2)
  have hh := Real.exp_pos (-2*x.1)
  have hn : thetaSource.normalized x.1 ≤ thetaEnvelopeUpper * thetaEnvelope x.1 / thetaSource.mass :=
    (div_le_div_iff_of_pos_right thetaSource.mass_pos).mpr hU
  calc
    _ ≤ (thetaEnvelopeUpper * thetaEnvelope x.1 / thetaSource.mass) /
        (Real.exp (-2*x.1) *
          (thetaEnvelopeLower * Real.exp (-2*Real.pi*Real.exp 2) * thetaEnvelope x.1) /
            thetaSource.mass) :=
      div_le_div₀ (by positivity) hn (by positivity) hL
    _ = _ := by
      rw [show -2*x.1 = -(2*x.1) by ring, Real.exp_neg]
      field_simp [thetaSource.mass_ne_zero, thetaEnvelopeLower_pos.ne', hE.ne', hc.ne', hh.ne']

end RHTower.PaperThetaEndpoint
