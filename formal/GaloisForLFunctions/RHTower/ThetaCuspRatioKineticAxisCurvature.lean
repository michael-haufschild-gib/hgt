import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticTerminalCurvature
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false


def terminalCurvatureAxisQuotient (h : ℝ) : ℝ :=
  (13688314407775983685466978280013824)*h^(4-4) +
  (-191636401708863771596537695920193536)*h^(5-4) +
  (-100761203279462102129131923450101760)*h^(6-4) +
  (-1612939714382936744270858940661628928)*h^(7-4) +
  (-7123447402873192719735652185268027392)*h^(8-4) +
  (3035644248542167855192818008796954624)*h^(9-4) +
  (-38234124637772972790418255521861599232)*h^(10-4) +
  (-19298194400360036221506398118098239488)*h^(11-4) +
  (-9716388544238880759289440129968504832)*h^(12-4) +
  (-10603349547006080647656138931011846144)*h^(13-4) +
  (1858849676962792449360473241264586752)*h^(14-4) +
  (4443656985667914837913001314593275904)*h^(15-4) +
  (1103017452915388871039878564065312768)*h^(16-4) +
  (176895839336789562216835160481988608)*h^(17-4) +
  (61119267607551402029296231831830528)*h^(18-4) +
  (-72277176426392770002720264617459712)*h^(19-4) +
  (-54715902179364055714189911263281152)*h^(20-4) +
  (-11556803617103781459957977702203392)*h^(21-4) +
  (-203715360720612599239311391457280)*h^(22-4) +
  (202699787025425444105676228919296)*h^(23-4) +
  (18130295628432993941145073483776)*h^(24-4)

theorem terminalCurvature_axis_factor (h : ℝ) :
    negKineticCurvatureControl h 9 (1/3) 17 = h^4*terminalCurvatureAxisQuotient h := by
  have he := (negKineticCurvatureDefectControl17Norm h 0).property
  norm_num only [zero_mul,sub_zero] at he
  rw [he]
  dsimp only [negKineticCurvatureDefectControl17Norm,terminalCurvatureAxisQuotient]
  norm_num [Nat.rawCast,Int.rawCast]
  ring

theorem terminalCurvatureAxisQuotient_upper (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    terminalCurvatureAxisQuotient h ≤
      13688314407775983685466978280013824*(1-14*h) -
      100761203279462102129131923450101760*h^2 := by
  have ha : (-7123447402873192719735652185268027392)*h^(8-4)+(3035644248542167855192818008796954624)*h^(9-4) ≤ 0 := by
    have hp := pow_nonneg hh0 4
    have hp5 : h^5 ≤ h^4 := pow_le_pow_of_le_one hh0 hh1 (by omega)
    norm_num only at ⊢
    linarith only [hp,hp5]
  have hb : (-10603349547006080647656138931011846144)*h^(13-4)+(1858849676962792449360473241264586752)*h^(14-4)+(4443656985667914837913001314593275904)*h^(15-4)+(1103017452915388871039878564065312768)*h^(16-4)+(176895839336789562216835160481988608)*h^(17-4)+(61119267607551402029296231831830528)*h^(18-4) ≤ 0 := by
    have hp := pow_nonneg hh0 9
    have hp10 : h^10 ≤ h^9 := pow_le_pow_of_le_one hh0 hh1 (by omega)
    have hp11 : h^11 ≤ h^9 := pow_le_pow_of_le_one hh0 hh1 (by omega)
    have hp12 : h^12 ≤ h^9 := pow_le_pow_of_le_one hh0 hh1 (by omega)
    have hp13 : h^13 ≤ h^9 := pow_le_pow_of_le_one hh0 hh1 (by omega)
    have hp14 : h^14 ≤ h^9 := pow_le_pow_of_le_one hh0 hh1 (by omega)
    norm_num only at ⊢
    linarith only [hp,hp10,hp11,hp12,hp13,hp14]
  have hc : (-72277176426392770002720264617459712)*h^(19-4)+(202699787025425444105676228919296)*h^(23-4)+(18130295628432993941145073483776)*h^(24-4) ≤ 0 := by
    have hp := pow_nonneg hh0 15
    have hp19 : h^19 ≤ h^15 := pow_le_pow_of_le_one hh0 hh1 (by omega)
    have hp20 : h^20 ≤ h^15 := pow_le_pow_of_le_one hh0 hh1 (by omega)
    norm_num only at ⊢
    linarith only [hp,hp19,hp20]
  have hr7 : (-1612939714382936744270858940661628928)*h^(7-4) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hh0 _)
  have hr10 : (-38234124637772972790418255521861599232)*h^(10-4) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hh0 _)
  have hr11 : (-19298194400360036221506398118098239488)*h^(11-4) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hh0 _)
  have hr12 : (-9716388544238880759289440129968504832)*h^(12-4) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hh0 _)
  have hr20 : (-54715902179364055714189911263281152)*h^(20-4) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hh0 _)
  have hr21 : (-11556803617103781459957977702203392)*h^(21-4) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hh0 _)
  have hr22 : (-203715360720612599239311391457280)*h^(22-4) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hh0 _)
  unfold terminalCurvatureAxisQuotient
  norm_num only [pow_zero,pow_one,mul_one] at *
  linarith only [ha,hb,hc,hr7,hr10,hr11,hr12,hr20,hr21,hr22]

theorem terminalCurvatureAxisQuotient_neg (h : ℝ) (hh0 : 0 < h)
    (hh1 : h ≤ 1) (hh : 1 ≤ 14*h) : terminalCurvatureAxisQuotient h < 0 := by
  have hu := terminalCurvatureAxisQuotient_upper h hh0.le hh1
  have hs : 0 < h^2 := sq_pos_of_pos hh0
  nlinarith

theorem reducedKineticCurvatureCore_terminal_axis_pos (h : ℝ) (hh0 : 0 < h)
    (hh1 : h ≤ 1) (hh : 1 ≤ 14*h) :
    0 < reducedKineticCurvatureCore h 9 (1/3) := by
  have hq := terminalCurvatureAxisQuotient_neg h hh0 hh1 hh
  have hm : h^4*terminalCurvatureAxisQuotient h < 0 :=
    mul_neg_of_pos_of_neg (pow_pos hh0 4) hq
  rw [← terminalCurvature_axis_factor,negKineticCurvatureControl_terminal] at hm
  linarith

theorem reducedKineticValue_terminal_axis_second_derivative_pos (h : ℝ)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hh : 1 ≤ 14*h) :
    0 < deriv (deriv (reducedKineticValue h 9)) (1/3) := by
  rw [reducedKineticValue_second_derivative]
  exact mul_pos (by norm_num) (reducedKineticCurvatureCore_terminal_axis_pos h hh0 hh1 hh)

end
end HTGeometry.ThetaRatioKineticContraction
