import GaloisForLFunctions.EulerFETransportTheory.ContinuousEulerPerturbationsHaveIntegrableDefects
import GaloisForLFunctions.StripBochnerWeilForcing.TheSimplePoleClassIsZeta
import GaloisForLFunctions.RHTower.CrystallineProducerRigidity

/-!
# The Hamburger strip for continuous prime perturbations

The multiplier `exp(ε/(s+1)²)` changes zeta's residue to `exp(ε/4)`.
Subtracting half this residue times `Γℝ(s-1)` removes the pole throughout
the Hamburger strip. A divided difference supplies its value at the
removed pole. The resulting remainder is holomorphic and decays as the
inverse square of height; its central reflection defect is the integrable
uncompleted defect of the continuous Euler perturbation.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.StripBochnerWeilForcing
open GaloisForLFunctions.ArithmeticPositiveDuality

namespace GaloisForLFunctions.EulerFETransportTheory

/-- Half the pole residue, in the Hamburger normalization. -/
def continuousEulerResidue (ε : ℝ≥0) : ℂ := Complex.exp ((ε : ℂ) / 4) / 2

/-- The holomorphic pole subtraction, including its removable value at `s=1`. -/
def continuousEulerRemainder (ε : ℝ≥0) (s : ℂ) : ℂ :=
  Complex.exp ((ε : ℂ) / (s + 1) ^ 2) * (completedRiemannZeta₀ s - 1 / s) +
    dslope (fun z : ℂ => Complex.exp ((ε : ℂ) / (z + 1) ^ 2)) 1 s -
    continuousEulerResidue ε * gammaℝReg (s - 1)

private theorem differentiableOn_continuousEulerMultiplier (ε : ℝ≥0) :
    DifferentiableOn ℂ (fun s : ℂ => Complex.exp ((ε : ℂ) / (s + 1) ^ 2))
      {s : ℂ | 0 < s.re} := by
  intro s hs
  have hn : s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h'
    linarith only [hs, h']
  exact (Complex.differentiable_exp.differentiableAt.comp s
    (differentiableAt_const.div ((differentiableAt_id.add_const 1).pow 2)
      (pow_ne_zero 2 hn))).differentiableWithinAt

/-- No pole remains anywhere in the right half-plane. -/
theorem differentiableOn_continuousEulerRemainder (ε : ℝ≥0) :
    DifferentiableOn ℂ (continuousEulerRemainder ε) {s : ℂ | 0 < s.re} := by
  have hM := differentiableOn_continuousEulerMultiplier ε
  have hU : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hds := (differentiableOn_dslope hU).mpr hM
  have hG : DifferentiableOn ℂ (fun s : ℂ => gammaℝReg (s - 1)) {s : ℂ | 0 < s.re} := by
    intro s hs
    have hm : -2 < (s - 1).re := by simp only [Complex.sub_re, Complex.one_re]; linarith only [hs]
    have hgd := differentiableOn_gammaℝReg.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hm)
    exact (hgd.comp s (differentiableAt_id.sub_const 1)).differentiableWithinAt
  have hinv : DifferentiableOn ℂ (fun s : ℂ => (1 : ℂ) / s) {s : ℂ | 0 < s.re} := by
    intro s hs
    exact (differentiableAt_const.div differentiableAt_id (by
      intro h
      simpa only [h, Complex.zero_re, lt_self_iff_false] using hs)).differentiableWithinAt
  exact ((hM.mul (differentiable_completedZeta₀.differentiableOn.sub hinv)).add hds).sub
    (hG.const_mul (continuousEulerResidue ε))

/-- Away from the removed pole, the remainder is exactly the completed zeta subtraction. -/
theorem continuousEulerRemainder_eq (ε : ℝ≥0) {s : ℂ} (hs : s ≠ 1) :
    continuousEulerRemainder ε s =
      Complex.exp ((ε : ℂ) / (s + 1) ^ 2) * completedRiemannZeta s -
        continuousEulerResidue ε * Complex.Gammaℝ (s - 1) := by
  rw [continuousEulerRemainder, dslope_of_ne _ hs, slope_def_field,
    gammaℝReg_eq (sub_ne_zero.mpr hs), completedRiemannZeta_eq]
  norm_num only [one_add_one_eq_two, one_pow, show (2 : ℂ) ^ 2 = 4 by norm_num]
  rw [show (1 : ℂ) - s = -(s - 1) by ring, div_neg]
  unfold continuousEulerResidue
  ring

private theorem completedZeta_eq_gamma_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
  have h0 : s ≠ 0 := by intro h; simpa only [h, Complex.zero_re, lt_self_iff_false] using hs
  rw [riemannZeta_def_of_ne_zero h0]
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs]

/-- The actual positive Euler measure supplies the right boundary of the strip. -/
theorem continuousEulerRemainder_right_boundary (ε : ℝ≥0) {s : ℂ} (hs : s.re = 3 / 2) :
    Complex.Gammaℝ s *
        measureDirichlet (beurlingIntegerMeasure (perturbedRiemannPrimeMeasure ε)) s =
      continuousEulerRemainder ε s + continuousEulerResidue ε * Complex.Gammaℝ (s - 1) := by
  have h0 : 0 < s.re := by rw [hs]; norm_num
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  rw [continuousEulerRemainder_eq ε h1, completedZeta_eq_gamma_mul h0,
    measureDirichlet_perturbedRiemannIntegerMeasure ε (by rw [hs]; norm_num), continuousEulerZeta]
  ring

/-- Central reflection has precisely the uncompleted defect already proved in `L¹∩L²`. -/
theorem continuousEulerRemainder_center (ε : ℝ≥0) {s : ℂ} (hs : s.re = 1 / 2) :
    continuousEulerRemainder ε s - continuousEulerRemainder ε (1 - s) =
      -(continuousEulerResidue ε * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) +
        Complex.Gammaℝ s * continuousEulerDefect ε (s.im / 2) := by
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have h1' : (1 : ℂ) - s ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num [hs] at h'
  have hpt : (1 / 2 : ℂ) + (2 * (s.im / 2) : ℝ) * I = s := by
    apply Complex.ext <;> simp [hs]
  rw [continuousEulerRemainder_eq ε h1, continuousEulerRemainder_eq ε h1',
    completedRiemannZeta_one_sub, completedZeta_eq_gamma_mul (by rw [hs]; norm_num),
    continuousEulerDefect, hpt]
  rw [show (1 : ℂ) - s - 1 = -s by ring,
    show (1 : ℂ) - s + 1 = 2 - s by ring]
  ring

private theorem exists_decay_completedZeta_hamburger :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 4 ≤ |s.im| →
      ‖completedRiemannZeta s‖ ≤ D / (1 + s.im ^ 2) := by
  obtain ⟨C, N, hC, hΛ⟩ := RHTower.exists_bound_completedRiemannZeta_strip
  obtain ⟨K, hK, hbound⟩ := RHTower.exists_bound_pow_mul_exp_neg (N + 2)
  refine ⟨C * K, mul_nonneg hC hK, fun s hs₀ hs₁ ht => ?_⟩
  have hdec := RHTower.pow_mul_exp_neg_le_div hbound (abs_nonneg s.im)
  rw [sq_abs] at hdec
  calc
    ‖completedRiemannZeta s‖ ≤
        C * |s.im| ^ N * Real.exp (-(Real.pi * |s.im| / 4)) :=
      hΛ s (by linarith only [hs₀]) (by linarith only [hs₁]) (by linarith only [ht])
    _ ≤ C * (|s.im| + 4) ^ N * Real.exp (-(Real.pi * |s.im| / 4)) := by gcongr; linarith
    _ = C * ((|s.im| + 4) ^ N * Real.exp (-(Real.pi * |s.im| / 4))) := by ring
    _ ≤ C * (K / (1 + s.im ^ 2)) := mul_le_mul_of_nonneg_left hdec hC
    _ = _ := by ring

/-- The pole-subtracted continuation has the full uniform Hamburger decay. -/
theorem exists_decay_continuousEulerRemainder (ε : ℝ≥0) :
    ∃ C : ℝ, ∀ s ∈ verticalStrip (1 / 2) (3 / 2),
      ‖continuousEulerRemainder ε s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨D, hD, hΛ⟩ := exists_decay_completedZeta_hamburger
  obtain ⟨G, hG, hΓ⟩ := RHTower.exists_decay_Gammaℝ_sub_one
  let K : Set ℂ := Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-4 : ℝ) 4
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : K ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    have h := (Complex.mem_reProdIm.mp hs).1.1
    linarith only [h]
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((differentiableOn_continuousEulerRemainder ε).continuousOn.mono hsub)
  refine ⟨max (17 * max M 0) (Real.exp ε * D + ‖continuousEulerResidue ε‖ * G),
    fun s hs => ?_⟩
  rw [mem_verticalStrip] at hs
  have hden : 0 < 1 + s.im ^ 2 := by positivity
  by_cases ht : 4 ≤ |s.im|
  · have h1 : s ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
    have hmult : ‖Complex.exp ((ε : ℂ) / (s + 1) ^ 2)‖ ≤ Real.exp ε := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans
        (norm_continuousEulerExponent_le ε (by linarith only [hs.1])))
    rw [continuousEulerRemainder_eq ε h1]
    calc
      _ ≤ ‖Complex.exp ((ε : ℂ) / (s + 1) ^ 2)‖ * ‖completedRiemannZeta s‖ +
          ‖continuousEulerResidue ε‖ * ‖Complex.Gammaℝ (s - 1)‖ := by
        simpa only [norm_mul] using norm_sub_le
          (Complex.exp ((ε : ℂ) / (s + 1) ^ 2) * completedRiemannZeta s)
          (continuousEulerResidue ε * Complex.Gammaℝ (s - 1))
      _ ≤ Real.exp ε * (D / (1 + s.im ^ 2)) +
          ‖continuousEulerResidue ε‖ * (G / (1 + s.im ^ 2)) := by
        exact add_le_add
          (mul_le_mul hmult (hΛ s hs.1 hs.2 ht) (norm_nonneg _) (Real.exp_pos _).le)
          (mul_le_mul_of_nonneg_left (hΓ s hs.1 hs.2 ht) (norm_nonneg _))
      _ = (Real.exp ε * D + ‖continuousEulerResidue ε‖ * G) / (1 + s.im ^ 2) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hden.le
  · have hsmall : |s.im| < 4 := lt_of_not_ge ht
    have hsK : s ∈ K := by
      rw [Complex.mem_reProdIm]
      exact ⟨hs, abs_le.mp hsmall.le⟩
    have hsq : s.im ^ 2 ≤ 16 := by
      nlinarith only [sq_abs s.im, abs_nonneg s.im, hsmall.le]
    calc
      _ ≤ max M 0 := (hM s hsK).trans (le_max_left _ _)
      _ ≤ 17 * max M 0 / (1 + s.im ^ 2) := by
        apply (le_div_iff₀ hden).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hsq (le_max_right M 0)]
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) hden.le

/-- Continuity includes both vertical edges of the Hamburger strip. -/
theorem continuousOn_continuousEulerRemainder_strip (ε : ℝ≥0) :
    ContinuousOn (continuousEulerRemainder ε) (verticalStrip (1 / 2) (3 / 2)) := by
  apply (differentiableOn_continuousEulerRemainder ε).continuousOn.mono
  intro s hs
  rw [mem_verticalStrip] at hs
  linarith only [hs.1]

#print axioms differentiableOn_continuousEulerRemainder
#print axioms continuousEulerRemainder_right_boundary
#print axioms continuousEulerRemainder_center
#print axioms exists_decay_continuousEulerRemainder

end GaloisForLFunctions.EulerFETransportTheory
