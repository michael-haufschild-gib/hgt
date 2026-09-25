import GaloisForLFunctions.RHTower.XiShiftEulerFinitePrimeCertificate
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneSchurPoleNoGo

open Complex
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The uncancelled archimedean pole of every finite shifted-prime quotient. -/
def finiteThetaPole (omega : ℝ) : ℂ :=
  ((1 / 2 - omega : ℝ) : ℂ) * I

private theorem shiftedPlus_at_finiteThetaPole (omega : ℝ) :
    1 / 2 + (omega : ℂ) - finiteThetaPole omega * I = 1 := by
  unfold finiteThetaPole
  rw [mul_assoc, I_mul_I]
  push_cast
  ring

private theorem shiftedMinus_at_finiteThetaPole (omega : ℝ) :
    1 / 2 - (omega : ℂ) - finiteThetaPole omega * I = ((1 - 2 * omega : ℝ) : ℂ) := by
  unfold finiteThetaPole
  rw [mul_assoc, I_mul_I]
  push_cast
  ring

private theorem eulerXiArchimedeanFactor_one_eq_zero :
    eulerXiArchimedeanFactor 1 = 0 := by
  simp [eulerXiArchimedeanFactor]

private theorem eulerXiArchimedeanFactor_one_sub_twoOmega_ne_zero
    {omega : ℝ} (h0 : 0 < omega) (hhalf : omega < 1 / 2) :
    eulerXiArchimedeanFactor ((1 - 2 * omega : ℝ) : ℂ) ≠ 0 := by
  have hr0 : 0 < 1 - 2 * omega := by linarith
  have hr1 : 1 - 2 * omega ≠ 1 := by linarith
  have h0c : (((1 - 2 * omega : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hr0.ne'
  have h1c : (((1 - 2 * omega : ℝ) : ℂ)) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hr1)
  exact mul_ne_zero
    (div_ne_zero (mul_ne_zero h0c h1c) (by norm_num))
    (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hr0))

private theorem finiteThetaPole_arch_numerator_ne_zero
    {omega : ℝ} (h0 : 0 < omega) (hhalf : omega < 1 / 2) :
    eulerXiArchimedeanFactor
      (1 / 2 - (omega : ℂ) - finiteThetaPole omega * I) ≠ 0 := by
  rw [shiftedMinus_at_finiteThetaPole]
  exact eulerXiArchimedeanFactor_one_sub_twoOmega_ne_zero h0 hhalf

private theorem finiteThetaPole_arch_denominator_zero (omega : ℝ) :
    eulerXiArchimedeanFactor
      (1 / 2 + (omega : ℂ) - finiteThetaPole omega * I) = 0 := by
  rw [shiftedPlus_at_finiteThetaPole]
  exact eulerXiArchimedeanFactor_one_eq_zero

private theorem finiteThetaPole_primeFactor_pos
    (p : Nat.Primes) {omega : ℝ} (hhalf : omega < 1 / 2) :
    0 < eulerXiPrimeAnchorFactor p omega (1 / 2 - omega) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hnum : Real.exp (-(1 : ℝ) * Real.log p) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    simpa using (neg_lt_zero.mpr hlog)
  have hden : Real.exp (-(1 - 2 * omega) * Real.log p) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hpos : 0 < 1 - 2 * omega := by linarith
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hpos) hlog
  unfold eulerXiPrimeAnchorFactor
  have heqnum : 1 / 2 + omega + (1 / 2 - omega) = (1 : ℝ) := by ring
  have heqden : 1 / 2 - omega + (1 / 2 - omega) = 1 - 2 * omega := by ring
  rw [heqnum, heqden]
  exact div_pos (sub_pos.mpr hnum) (sub_pos.mpr hden)

private theorem finiteThetaPole_primeFactor_ne_zero
    (p : Nat.Primes) {omega : ℝ} (hhalf : omega < 1 / 2) :
    eulerXiPrimeShiftFactor p omega (finiteThetaPole omega) ≠ 0 := by
  rw [finiteThetaPole, eulerXiPrimeShiftFactor_mul_I]
  exact_mod_cast (finiteThetaPole_primeFactor_pos p hhalf).ne'

private theorem finiteThetaPole_primeProduct_ne_zero
    (S : Finset Nat.Primes) {omega : ℝ} (hhalf : omega < 1 / 2) :
    (∏ p ∈ S, eulerXiPrimeShiftFactor p omega (finiteThetaPole omega)) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => finiteThetaPole_primeFactor_ne_zero p hhalf)

private def finiteThetaShiftMinus (omega : ℝ) (z : ℂ) : ℂ :=
  1 / 2 - (omega : ℂ) - z * I

private def finiteThetaShiftPlus (omega : ℝ) (z : ℂ) : ℂ :=
  1 / 2 + (omega : ℂ) - z * I

private def finiteThetaClearedNumerator
    (omega : ℝ) (S : Finset Nat.Primes) (z : ℂ) : ℂ :=
  eulerXiArchimedeanFactor (finiteThetaShiftMinus omega z) *
    ∏ p ∈ S, finiteEulerLocalFactor p (finiteThetaShiftPlus omega z)

private def finiteThetaClearedDenominator
    (omega : ℝ) (S : Finset Nat.Primes) (z : ℂ) : ℂ :=
  eulerXiArchimedeanFactor (finiteThetaShiftPlus omega z) *
    ∏ p ∈ S, finiteEulerLocalFactor p (finiteThetaShiftMinus omega z)

private theorem finiteTheta_eq_clearedQuotient
    (omega : ℝ) (S : Finset Nat.Primes) (z : ℂ) :
    eulerXiShiftFinitePrimeTheta omega S z =
      finiteThetaClearedNumerator omega S z /
        finiteThetaClearedDenominator omega S z := by
  unfold eulerXiShiftFinitePrimeTheta eulerXiArchimedeanQuotient
    finiteThetaClearedNumerator finiteThetaClearedDenominator
    finiteThetaShiftMinus finiteThetaShiftPlus
  simp_rw [eulerXiPrimeShiftFactor]
  rw [Finset.prod_div_distrib (G := ℂ) (ι := Nat.Primes) (s := S)
    (fun p : Nat.Primes => finiteEulerLocalFactor p (1 / 2 + (omega : ℂ) - z * I))
    (fun p : Nat.Primes => finiteEulerLocalFactor p (1 / 2 - (omega : ℂ) - z * I))]
  ring

private theorem finiteEulerLocalFactor_ne_zero_of_re_pos
    (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    finiteEulerLocalFactor p s ≠ 0 := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hre : (-s * (Real.log p : ℂ)).re = -s.re * Real.log p := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have hnorm : ‖Complex.exp (-s * Real.log p)‖ < 1 := by
    rw [Complex.norm_exp, hre, Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hlog
  intro hzero
  have hexp : Complex.exp (-s * Real.log p) = 1 := by
    simpa [finiteEulerLocalFactor] using (sub_eq_zero.mp hzero).symm
  have hnorm1 := congrArg norm hexp
  rw [norm_one] at hnorm1
  linarith

private theorem analyticAt_eulerXiArchimedeanFactor_of_posRe
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ eulerXiArchimedeanFactor s := by
  have hgamma : AnalyticAt ℂ Complex.Gammaℝ s :=
    Gammaℝ_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos hs)
  have hpoly : AnalyticAt ℂ (fun w : ℂ => w * (w - 1) / 2) s := by fun_prop
  change AnalyticAt ℂ (fun w : ℂ => w * (w - 1) / 2 * Complex.Gammaℝ w) s
  exact hpoly.mul hgamma

private theorem analyticAt_finiteEulerLocalFactor (p : Nat.Primes) (s : ℂ) :
    AnalyticAt ℂ (finiteEulerLocalFactor p) s := by
  unfold finiteEulerLocalFactor
  fun_prop

private theorem analyticAt_finiteThetaClearedNumerator
    (omega : ℝ) (S : Finset Nat.Primes) {z : ℂ}
    (hm : 0 < (finiteThetaShiftMinus omega z).re) :
    AnalyticAt ℂ (finiteThetaClearedNumerator omega S) z := by
  have hminus : AnalyticAt ℂ (finiteThetaShiftMinus omega) z := by
    unfold finiteThetaShiftMinus
    fun_prop
  have hplus : AnalyticAt ℂ (finiteThetaShiftPlus omega) z := by
    unfold finiteThetaShiftPlus
    fun_prop
  have harch : AnalyticAt ℂ
      (fun w => eulerXiArchimedeanFactor (finiteThetaShiftMinus omega w)) z :=
    (analyticAt_eulerXiArchimedeanFactor_of_posRe hm).comp hminus
  have hprod : AnalyticAt ℂ
      (fun w => ∏ p ∈ S, finiteEulerLocalFactor p (finiteThetaShiftPlus omega w)) z := by
    apply Finset.analyticAt_fun_prod
    intro p hp
    exact (analyticAt_finiteEulerLocalFactor p (finiteThetaShiftPlus omega z)).comp hplus
  exact harch.mul hprod

private theorem analyticAt_finiteThetaClearedDenominator
    (omega : ℝ) (S : Finset Nat.Primes) {z : ℂ}
    (hp : 0 < (finiteThetaShiftPlus omega z).re) :
    AnalyticAt ℂ (finiteThetaClearedDenominator omega S) z := by
  have hminus : AnalyticAt ℂ (finiteThetaShiftMinus omega) z := by
    unfold finiteThetaShiftMinus
    fun_prop
  have hplus : AnalyticAt ℂ (finiteThetaShiftPlus omega) z := by
    unfold finiteThetaShiftPlus
    fun_prop
  have harch : AnalyticAt ℂ
      (fun w => eulerXiArchimedeanFactor (finiteThetaShiftPlus omega w)) z :=
    (analyticAt_eulerXiArchimedeanFactor_of_posRe hp).comp hplus
  have hprod : AnalyticAt ℂ
      (fun w => ∏ p ∈ S, finiteEulerLocalFactor p (finiteThetaShiftMinus omega w)) z := by
    apply Finset.analyticAt_fun_prod
    intro p hmem
    exact (analyticAt_finiteEulerLocalFactor p (finiteThetaShiftMinus omega z)).comp hminus
  exact harch.mul hprod

/-- Every finite shifted Euler product leaves the archimedean `s₊ = 1` zero
uncancelled.  This is a numerator/denominator assertion, since Lean's total
division assigns a value even at the pole. -/
theorem finiteThetaPole_uncancelled
    (S : Finset Nat.Primes) {omega : ℝ} (h0 : 0 < omega) (hhalf : omega < 1 / 2) :
    eulerXiArchimedeanFactor
        (1 / 2 + (omega : ℂ) - finiteThetaPole omega * I) = 0 ∧
      eulerXiArchimedeanFactor
        (1 / 2 - (omega : ℂ) - finiteThetaPole omega * I) *
          (∏ p ∈ S, eulerXiPrimeShiftFactor p omega (finiteThetaPole omega)) ≠ 0 := by
  exact ⟨finiteThetaPole_arch_denominator_zero omega,
    mul_ne_zero (finiteThetaPole_arch_numerator_ne_zero h0 hhalf)
      (finiteThetaPole_primeProduct_ne_zero S hhalf)⟩

private theorem finiteThetaShiftPlus_re (omega : ℝ) (z : ℂ) :
    (finiteThetaShiftPlus omega z).re = 1 / 2 + omega + z.im := by
  simp [finiteThetaShiftPlus, Complex.mul_re]

private theorem finiteThetaShiftMinus_re (omega : ℝ) (z : ℂ) :
    (finiteThetaShiftMinus omega z).re = 1 / 2 - omega + z.im := by
  simp [finiteThetaShiftMinus, Complex.mul_re]

private theorem finiteThetaPole_clearedNumerator_ne_zero
    (S : Finset Nat.Primes) {omega : ℝ} (h0 : 0 < omega) (hhalf : omega < 1 / 2) :
    finiteThetaClearedNumerator omega S (finiteThetaPole omega) ≠ 0 := by
  have hm : finiteThetaShiftMinus omega (finiteThetaPole omega) =
      ((1 - 2 * omega : ℝ) : ℂ) := shiftedMinus_at_finiteThetaPole omega
  have hp : finiteThetaShiftPlus omega (finiteThetaPole omega) = 1 :=
    shiftedPlus_at_finiteThetaPole omega
  unfold finiteThetaClearedNumerator
  rw [hm, hp]
  exact mul_ne_zero
    (eulerXiArchimedeanFactor_one_sub_twoOmega_ne_zero h0 hhalf)
    (Finset.prod_ne_zero_iff.mpr (fun p _ =>
      finiteEulerLocalFactor_ne_zero_of_re_pos p (by norm_num)))

private theorem finiteThetaPole_clearedDenominator_zero
    (S : Finset Nat.Primes) (omega : ℝ) :
    finiteThetaClearedDenominator omega S (finiteThetaPole omega) = 0 := by
  have hp : finiteThetaShiftPlus omega (finiteThetaPole omega) = 1 :=
    shiftedPlus_at_finiteThetaPole omega
  unfold finiteThetaClearedDenominator
  rw [hp, eulerXiArchimedeanFactor_one_eq_zero, zero_mul]

private theorem finiteThetaClearedDenominator_ne_zero_abovePole
    (S : Finset Nat.Primes) {omega : ℝ} (hhalf : omega < 1 / 2)
    {z : ℂ} (hz : 1 / 2 - omega < z.im) :
    finiteThetaClearedDenominator omega S z ≠ 0 := by
  have hp : 1 < (finiteThetaShiftPlus omega z).re := by
    rw [finiteThetaShiftPlus_re]
    linarith
  have hm : 0 < (finiteThetaShiftMinus omega z).re := by
    rw [finiteThetaShiftMinus_re]
    linarith
  exact mul_ne_zero (eulerXiArchimedeanFactor_ne_zero hp)
    (Finset.prod_ne_zero_iff.mpr (fun p _ =>
      finiteEulerLocalFactor_ne_zero_of_re_pos p hm))

private theorem finiteThetaClearedNumerator_analytic_abovePole
    (S : Finset Nat.Primes) {omega : ℝ} (hhalf : omega < 1 / 2) :
    AnalyticOnNhd ℂ (finiteThetaClearedNumerator omega S)
      {z : ℂ | 1 / 2 - omega < z.im} := by
  intro z hz
  change 1 / 2 - omega < z.im at hz
  apply analyticAt_finiteThetaClearedNumerator
  rw [finiteThetaShiftMinus_re]
  linarith

private theorem finiteThetaClearedDenominator_analytic_abovePole
    (S : Finset Nat.Primes) (omega : ℝ) :
    AnalyticOnNhd ℂ (finiteThetaClearedDenominator omega S)
      {z : ℂ | 1 / 2 - omega < z.im} := by
  intro z hz
  change 1 / 2 - omega < z.im at hz
  apply analyticAt_finiteThetaClearedDenominator
  rw [finiteThetaShiftPlus_re]
  linarith

private theorem finiteThetaClearedNumerator_continuousAt_pole
    (S : Finset Nat.Primes) {omega : ℝ} (hhalf : omega < 1 / 2) :
    ContinuousAt (finiteThetaClearedNumerator omega S) (finiteThetaPole omega) := by
  have han : AnalyticAt ℂ (finiteThetaClearedNumerator omega S)
      (finiteThetaPole omega) := by
    apply analyticAt_finiteThetaClearedNumerator
    rw [show finiteThetaShiftMinus omega (finiteThetaPole omega) =
        ((1 - 2 * omega : ℝ) : ℂ) from shiftedMinus_at_finiteThetaPole omega]
    simpa using (show 0 < 1 - 2 * omega by linarith)
  exact han.continuousAt

private theorem finiteThetaClearedDenominator_continuousAt_pole
    (S : Finset Nat.Primes) (omega : ℝ) :
    ContinuousAt (finiteThetaClearedDenominator omega S) (finiteThetaPole omega) := by
  have han : AnalyticAt ℂ (finiteThetaClearedDenominator omega S)
      (finiteThetaPole omega) := by
    apply analyticAt_finiteThetaClearedDenominator
    rw [show finiteThetaShiftPlus omega (finiteThetaPole omega) = 1 from
        shiftedPlus_at_finiteThetaPole omega]
    norm_num
  exact han.continuousAt

/-- No finite prime truncation has a positive Schur kernel on every Euler
sample: the all-prime completion must cancel a genuine interior pole. -/
theorem not_isPSDKernel_eulerXiShiftFinitePrimePick
    (S : Finset Nat.Primes) {omega : ℝ} (h0 : 0 < omega) (hhalf : omega < 1 / 2) :
    ¬ IsPSDKernel (fun z w : xiShiftEulerUpperSet omega =>
        eulerXiShiftFinitePrimePick omega S z.1 w.1) := by
  have h0p : 0 < 1 / 2 - omega := by linarith
  have h01 : 1 / 2 - omega < 1 / 2 + omega := by linarith
  have hno := not_isPSDKernel_upperHalfPlane_of_uncancelled_pole
    h0p h01
    (finiteThetaClearedNumerator omega S)
    (finiteThetaClearedDenominator omega S)
    (finiteThetaClearedNumerator_analytic_abovePole S hhalf)
    (finiteThetaClearedDenominator_analytic_abovePole S omega)
    (fun z hz => finiteThetaClearedDenominator_ne_zero_abovePole S hhalf hz)
    (by simpa only [finiteThetaPole] using
      finiteThetaClearedNumerator_continuousAt_pole S hhalf)
    (by simpa only [finiteThetaPole] using
      finiteThetaClearedDenominator_continuousAt_pole S omega)
    (by simpa only [finiteThetaPole] using
      finiteThetaPole_clearedNumerator_ne_zero S h0 hhalf)
    (by simpa only [finiteThetaPole] using
      finiteThetaPole_clearedDenominator_zero S omega)
  intro hK
  apply hno
  change IsPSDKernel (fun z w : {z : ℂ | 1 / 2 + omega < z.im} =>
    upperHalfPlaneSchurKernel (eulerXiShiftFinitePrimeTheta omega S) z.1 w.1) at hK
  refine hK.congr (fun z w => ?_)
  simp only [upperHalfPlaneSchurKernel, finiteTheta_eq_clearedQuotient]

/-- Even Gaussian-rational Euler samples contain a finite negative Pick packet
for every finite prime truncation.  Thus a negative finite-prime margin by
itself cannot distinguish an off-line Xi zero; its all-prime tail is essential. -/
theorem not_isPSDKernel_eulerXiShiftFinitePrimePick_gaussianRational
    (S : Finset Nat.Primes) {omega : ℝ} (h0 : 0 < omega) (hhalf : omega < 1 / 2) :
    ¬ IsPSDKernel (fun z w : xiShiftEulerGaussianRationalSet omega =>
        eulerXiShiftFinitePrimePick omega S z.1 w.1) := by
  have h0p : 0 < 1 / 2 - omega := by linarith
  have h01 : 1 / 2 - omega < 1 / 2 + omega := by linarith
  obtain ⟨p, hp, hfreq⟩ := xiShiftEulerGaussianRationalSet_accumulates omega
  have hno := not_isPSDKernel_accumulationSet_of_uncancelled_pole
    h0p h01 (xiShiftEulerGaussianRationalSet omega)
    (fun z hz => hz.1) p hp hfreq
    (finiteThetaClearedNumerator omega S)
    (finiteThetaClearedDenominator omega S)
    (finiteThetaClearedNumerator_analytic_abovePole S hhalf)
    (finiteThetaClearedDenominator_analytic_abovePole S omega)
    (fun z hz => finiteThetaClearedDenominator_ne_zero_abovePole S hhalf hz)
    (by simpa only [finiteThetaPole] using
      finiteThetaClearedNumerator_continuousAt_pole S hhalf)
    (by simpa only [finiteThetaPole] using
      finiteThetaClearedDenominator_continuousAt_pole S omega)
    (by simpa only [finiteThetaPole] using
      finiteThetaPole_clearedNumerator_ne_zero S h0 hhalf)
    (by simpa only [finiteThetaPole] using
      finiteThetaPole_clearedDenominator_zero S omega)
  intro hK
  apply hno
  change IsPSDKernel (fun z w : xiShiftEulerGaussianRationalSet omega =>
    upperHalfPlaneSchurKernel (eulerXiShiftFinitePrimeTheta omega S) z.1 w.1) at hK
  refine hK.congr (fun z w => ?_)
  simp only [upperHalfPlaneSchurKernel, finiteTheta_eq_clearedQuotient]

private theorem finitePrimeSchur_conj_symm (theta : ℂ → ℂ) (z w : ℂ) :
    starRingEnd ℂ (upperHalfPlaneSchurKernel theta z w) =
      upperHalfPlaneSchurKernel theta w z := by
  unfold upperHalfPlaneSchurKernel
  simp only [map_mul, map_div₀, map_sub, map_one, conj_I, conj_conj]
  rw [show (starRingEnd ℂ) z - w = -(w - (starRingEnd ℂ) z) by ring]
  rw [neg_div_neg_eq]
  ring

/-- Every finite prime set admits an actual negative-energy Gaussian-rational
Euler packet, without assuming an off-line zero. -/
theorem exists_eulerXiShiftFinitePrimePick_gaussianRational_negativeEnergy
    (S : Finset Nat.Primes) {omega : ℝ} (h0 : 0 < omega) (hhalf : omega < 1 / 2) :
    ∃ u : xiShiftEulerGaussianRationalSet omega →₀ ℂ,
      (kernelForm (fun z w : xiShiftEulerGaussianRationalSet omega =>
        eulerXiShiftFinitePrimePick omega S z.1 w.1) u u).re < 0 := by
  let K : xiShiftEulerGaussianRationalSet omega →
      xiShiftEulerGaussianRationalSet omega → ℂ :=
    fun z w => eulerXiShiftFinitePrimePick omega S z.1 w.1
  by_contra hn
  have hnonneg (u : xiShiftEulerGaussianRationalSet omega →₀ ℂ) :
      0 ≤ (kernelForm K u u).re := by
    by_contra hu
    exact hn ⟨u, lt_of_not_ge hu⟩
  have hK : IsPSDKernel K := by
    refine ⟨?_, ?_⟩
    · intro z w
      exact finitePrimeSchur_conj_symm (eulerXiShiftFinitePrimeTheta omega S) z.1 w.1
    · exact hnonneg
  exact (not_isPSDKernel_eulerXiShiftFinitePrimePick_gaussianRational S h0 hhalf) hK

end

end RHTower
