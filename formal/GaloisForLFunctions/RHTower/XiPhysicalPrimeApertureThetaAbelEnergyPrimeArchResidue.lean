import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergySymmetricRadiusSourceCriterion
import GaloisForLFunctions.RHTower.XiMassArchimedeanUniformBound

/-!
# Physical theta--Abel prime/archimedean residue separation

The exact continued source integrand splits pointwise into continued prime
flux and completed-archimedean channels.  On every source-domain rectangle
crossing the unique centered archimedean zero `-I/2`, the weighted argument
principle collapses the whole archimedean contour to one detector value.

For the physical-energy detector this value is the explicit real square

`(exp(a/2) * 2 * (1-exp(-L/2)) * c * A)^2`.

It is nonnegative without parameter assumptions and strictly positive for
`L,A,c>0`.  Hence no Gamma-tail estimate remains in this source family; all
unresolved sign burden lies in the continued prime-flux channel.
-/

open Complex Filter Topology Set intervalIntegral

namespace RHTower

noncomputable section

theorem xiPhysicalThetaAbelEntireModeAmplitude_neg_half
    (L A c : ℝ) :
    xiPhysicalThetaAbelEntireModeAmplitude L A c (-1 / 2) = 0 := by
  rw [xiPhysicalThetaAbelEntireModeAmplitude]
  have hzero : (-1 / 2 : ℂ) + 1 / 2 = 0 := by ring
  rw [hzero]
  ring

theorem xiPhysicalThetaAbelEntireModeAmplitude_half
    (L A c : ℝ) :
    xiPhysicalThetaAbelEntireModeAmplitude L A c (1 / 2) =
      rectangularWindowAmplitude L (1 / 2) * c * A := by
  rw [xiPhysicalThetaAbelEntireModeAmplitude]
  have hzero : (1 / 2 : ℂ) - 1 / 2 = 0 := by ring
  rw [hzero]
  simp only [rectangularWindowAmplitude_zero]
  ring

theorem rectangularWindowAmplitude_half_eq_real (L : ℝ) :
    rectangularWindowAmplitude L (1 / 2) =
      ((2 * (1 - Real.exp (-(L / 2))) : ℝ) : ℂ) := by
  rw [rectangularWindowAmplitude_eq_div (by norm_num : (1 / 2 : ℂ) ≠ 0)]
  rw [show (-(L : ℂ) * (1 / 2)) = ((-(L / 2) : ℝ) : ℂ) by
    push_cast
    ring]
  rw [← Complex.ofReal_exp]
  push_cast
  ring

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_archPole
    (L A c a : ℝ) :
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a xiMassArchPole =
      Complex.exp (a / 2) * rectangularWindowAmplitude L (1 / 2) * c * A := by
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform]
  have hw : I * xiMassArchPole = (1 / 2 : ℂ) := by
    apply Complex.ext <;> norm_num [xiMassArchPole, Complex.mul_re,
      Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq]
  rw [hw, xiPhysicalThetaAbelEntireModeAmplitude_half,
    show -(1 / 2 : ℂ) = -1 / 2 by ring,
    xiPhysicalThetaAbelEntireModeAmplitude_neg_half]
  simp
  ring

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_archPole_eq_real
    (L A c a : ℝ) :
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a xiMassArchPole =
      ((Real.exp (a / 2) * 2 * (1 - Real.exp (-(L / 2))) * c * A : ℝ) : ℂ) := by
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform_archPole,
    rectangularWindowAmplitude_half_eq_real]
  rw [show (a : ℂ) / 2 = ((a / 2 : ℝ) : ℂ) by
    norm_num [div_eq_mul_inv]]
  rw [← Complex.ofReal_exp]
  push_cast
  ring

theorem physicalThetaAbelEnergy_sourceIntegrand_eq_prime_add_arch
    (L A c a : ℝ) (z : ℂ) :
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ 2 *
        continuedPrimeArchSourceRelativeTrace z =
      xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ 2 *
          (-I * infinitePrimeFlux (1 / 2 + z * I)) +
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ 2 *
          (I * logDeriv archFactor (1 / 2 + z * I)) := by
  rw [continuedPrimeArchSourceRelativeTrace]
  ring

private def xiPhysicalThetaAbelArchDomain : Set ℂ :=
  {z : ℂ | z.im < 1 / 2}

private theorem isOpen_xiPhysicalThetaAbelArchDomain :
    IsOpen xiPhysicalThetaAbelArchDomain := by
  exact isOpen_lt Complex.continuous_im continuous_const

private theorem analyticOnNhd_xiPhysicalThetaAbelArchCofactor :
    AnalyticOnNhd ℂ xiMassCenteredArchCofactor
      xiPhysicalThetaAbelArchDomain := by
  intro z hz
  let a : ℝ := |z.im| + 1
  apply analyticOnNhd_xiMassCenteredArchCofactor (a := a)
  change z ∈ xiMassStrip a ∧ z.im < 1 / 2
  refine ⟨?_, hz⟩
  change |z.im| < a
  simp [a]

private theorem xiPhysicalThetaAbelArchCofactor_ne_zero
    {z : ℂ} (hz : z ∈ xiPhysicalThetaAbelArchDomain) :
    xiMassCenteredArchCofactor z ≠ 0 := by
  let a : ℝ := |z.im| + 1
  apply xiMassCenteredArchCofactor_ne_zero (a := a)
  change z ∈ xiMassStrip a ∧ z.im < 1 / 2
  refine ⟨?_, hz⟩
  change |z.im| < a
  simp [a]

theorem rectIntegral_physicalThetaAbelEnergy_mul_archSource_eq
    {L A c a : ℝ} {z₁ z₂ : ℂ}
    (him : z₁.im < z₂.im)
    (hleft : z₁.re < 0) (hright : 0 < z₂.re)
    (hbelow : z₁.im < -(1 / 2)) (habove : -(1 / 2) < z₂.im)
    (htop : z₂.im < 1 / 2) :
    rectIntegral (fun z =>
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ 2 *
          (I * logDeriv archFactor (1 / 2 + z * I))) z₁ z₂ =
      2 * Real.pi * I *
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a xiMassArchPole ^ 2 := by
  let g : ℂ → ℂ := fun z =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ 2
  let U : Set ℂ := xiPhysicalThetaAbelArchDomain
  let rho : Unit → ℂ := fun _ => xiMassArchPole
  let mult : Unit → ℕ := fun _ => 1
  let h : ℂ → ℂ := xiMassCenteredArchCofactor
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    intro z hz
    change z.im < 1 / 2
    have hzIm := (Complex.mem_reProdIm.mp hz).2
    rw [uIcc_of_le him.le] at hzIm
    exact hzIm.2.trans_lt htop
  have hin : ∀ i ∈ ({()} : Finset Unit),
      z₁.re < (rho i).re ∧ (rho i).re < z₂.re ∧
        z₁.im < (rho i).im ∧ (rho i).im < z₂.im := by
    intro i _
    have hi : i = () := Subsingleton.elim _ _
    subst i
    simp only [rho]
    have hpRe : xiMassArchPole.re = 0 := by
      norm_num [xiMassArchPole, Complex.div_re, Complex.normSq]
    have hpIm : xiMassArchPole.im = -(1 / 2) := by
      norm_num [xiMassArchPole, Complex.div_im, Complex.normSq]
    rw [hpRe, hpIm]
    exact ⟨hleft, hright, hbelow, habove⟩
  have hcentered : rectIntegral (fun z =>
      g z * logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z)
      z₁ z₂ = 2 * Real.pi * I * g xiMassArchPole := by
    have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
      ({()} : Finset Unit) rho mult
      (f := fun z => archFactor (xiMassCenteredArchPoint z))
      (g := g) (h := h) (z₁ := z₁) (z₂ := z₂) (U := U)
      isOpen_xiPhysicalThetaAbelArchDomain
      ((xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd
        L A c a).mono (fun _ _ => Set.mem_univ _))
      hin hsub analyticOnNhd_xiPhysicalThetaAbelArchCofactor
      (fun z hz => xiPhysicalThetaAbelArchCofactor_ne_zero hz)
      (fun z _ => by
        rw [archFactor_centered_factorization]
        simp only [Finset.prod_singleton, mult, rho, h, pow_one])
    simpa only [rho, mult, Finset.sum_singleton, Nat.cast_one, one_mul]
      using hres
  have heq : ∀ z ∈ U,
      g z * (I * logDeriv archFactor (1 / 2 + z * I)) =
        g z * logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z := by
    intro z hz
    rw [logDeriv_centeredArchFactor_eq_I_mul]
    · rfl
    · rw [xiMassCenteredArchPoint_re]
      exact sub_pos.mpr hz
  have hcontour : rectIntegral (fun z =>
      g z * (I * logDeriv archFactor (1 / 2 + z * I))) z₁ z₂ =
      rectIntegral (fun z =>
        g z * logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z)
        z₁ z₂ := by
    exact rectIntegral_congr heq
      (fun _x _hx => by
        change (((_ : ℂ) + z₁.im * I).im) < 1 / 2
        simp
        linarith)
      (fun _x _hx => by
        change (((_ : ℂ) + z₂.im * I).im) < 1 / 2
        simpa using htop)
      (fun y hy => by
        rw [uIcc_of_le him.le] at hy
        have himEq : (((z₂.re : ℂ) + y * I).im) = y := by simp
        change (((z₂.re : ℂ) + y * I).im) < 1 / 2
        rw [himEq]
        exact hy.2.trans_lt htop)
      (fun y hy => by
        rw [uIcc_of_le him.le] at hy
        have himEq : (((z₁.re : ℂ) + y * I).im) = y := by simp
        change (((z₁.re : ℂ) + y * I).im) < 1 / 2
        rw [himEq]
        exact hy.2.trans_lt htop)
  simpa only [g] using hcontour.trans hcentered

/-- Normalized completed-archimedean channel of the physical-energy source
contour. -/
def xiPhysicalThetaAbelEnergyNormalizedArchSourceContour
    (L A c a : ℝ) (z₁ z₂ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * rectIntegral (fun z =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ 2 *
      (I * logDeriv archFactor (1 / 2 + z * I))) z₁ z₂

theorem xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_eq_archPole_sq
    {L A c a : ℝ} {z₁ z₂ : ℂ}
    (him : z₁.im < z₂.im)
    (hleft : z₁.re < 0) (hright : 0 < z₂.re)
    (hbelow : z₁.im < -(1 / 2)) (habove : -(1 / 2) < z₂.im)
    (htop : z₂.im < 1 / 2) :
    xiPhysicalThetaAbelEnergyNormalizedArchSourceContour L A c a z₁ z₂ =
      xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a xiMassArchPole ^ 2 := by
  rw [xiPhysicalThetaAbelEnergyNormalizedArchSourceContour,
    rectIntegral_physicalThetaAbelEnergy_mul_archSource_eq
      him hleft hright hbelow habove htop]
  have hfactor : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hfactor, one_mul]

theorem xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_eq_explicit
    {L A c a : ℝ} {z₁ z₂ : ℂ}
    (him : z₁.im < z₂.im)
    (hleft : z₁.re < 0) (hright : 0 < z₂.re)
    (hbelow : z₁.im < -(1 / 2)) (habove : -(1 / 2) < z₂.im)
    (htop : z₂.im < 1 / 2) :
    xiPhysicalThetaAbelEnergyNormalizedArchSourceContour L A c a z₁ z₂ =
      ((Real.exp (a / 2) * 2 * (1 - Real.exp (-(L / 2))) * c * A : ℝ) : ℂ) ^ 2 := by
  rw [xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_eq_archPole_sq
    him hleft hright hbelow habove htop,
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_archPole_eq_real]

theorem xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_re_nonneg
    {L A c a : ℝ} {z₁ z₂ : ℂ}
    (him : z₁.im < z₂.im)
    (hleft : z₁.re < 0) (hright : 0 < z₂.re)
    (hbelow : z₁.im < -(1 / 2)) (habove : -(1 / 2) < z₂.im)
    (htop : z₂.im < 1 / 2) :
    0 ≤ (xiPhysicalThetaAbelEnergyNormalizedArchSourceContour
      L A c a z₁ z₂).re := by
  rw [xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_eq_explicit
    him hleft hright hbelow habove htop]
  rw [pow_two]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  exact mul_self_nonneg _

theorem xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_re_pos
    {L A c a : ℝ} {z₁ z₂ : ℂ}
    (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (him : z₁.im < z₂.im)
    (hleft : z₁.re < 0) (hright : 0 < z₂.re)
    (hbelow : z₁.im < -(1 / 2)) (habove : -(1 / 2) < z₂.im)
    (htop : z₂.im < 1 / 2) :
    0 < (xiPhysicalThetaAbelEnergyNormalizedArchSourceContour
      L A c a z₁ z₂).re := by
  rw [xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_eq_explicit
    him hleft hright hbelow habove htop, pow_two]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  have hwindow : 0 < 1 - Real.exp (-(L / 2)) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  positivity

end

end RHTower
