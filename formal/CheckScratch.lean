import GaloisForLFunctions.RHTower.SoninSemilocalTwoPlaceAssociation

#check Real.cosh_eq
#check Real.sqrt_eq_rpow
#check Real.rpow_neg
#check Real.div_rpow
#check Real.rpow_le_rpow_of_nonpos
#check Real.rpow_le_rpow

open RHTower
noncomputable section

def testKernel (t u : ℝ) : ℝ :=
  Real.sqrt (semilocalArchimedeanCharacteristic (2 * t)) *
    Real.sqrt (semilocalArchimedeanCharacteristic (2 * u)) *
      semilocalArchimedeanCharacteristic (t - u)

example (t u : ℝ) : 0 < testKernel t u := by
  unfold testKernel
  have hchar (x : ℝ) : 0 < semilocalArchimedeanCharacteristic x := by
    exact Real.rpow_pos_of_pos (Real.cosh_pos x) (-(1 : ℝ) / 2)
  exact mul_pos (mul_pos (Real.sqrt_pos.2 (hchar (2 * t)))
    (Real.sqrt_pos.2 (hchar (2 * u)))) (hchar (t - u))

example (t : ℝ) :
    testKernel t t = semilocalArchimedeanCharacteristic (2 * t) := by
  unfold testKernel
  have hchar : 0 ≤ semilocalArchimedeanCharacteristic (2 * t) :=
    (Real.rpow_pos_of_pos (Real.cosh_pos (2 * t)) (-(1 : ℝ) / 2)).le
  rw [sub_self]
  have hzero : semilocalArchimedeanCharacteristic 0 = 1 := by
    simp [semilocalArchimedeanCharacteristic]
  rw [hzero, mul_one]
  simpa [pow_two] using Real.sq_sqrt hchar

example {t : ℝ} :
    semilocalArchimedeanCharacteristic (2 * t) ≤
      Real.sqrt 2 * Real.exp (-t) := by
  have hexp : Real.exp (2 * t) / 2 ≤ Real.cosh (2 * t) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-(2 * t))
    linarith
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < Real.exp (2 * t) / 2)
    hexp (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
  dsimp [semilocalArchimedeanCharacteristic]
  refine hpow.trans_eq ?_
  rw [Real.div_rpow (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.exp_mul]
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.sqrt_eq_rpow]
  rw [div_inv_eq_mul]
  rw [show 2 * t * -(1 / 2 : ℝ) = -t by ring]
  ring
