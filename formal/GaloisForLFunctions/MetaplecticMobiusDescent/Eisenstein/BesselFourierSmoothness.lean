import GaloisForLFunctions.HTGeometry.ComplexAnalysis.BesselArgumentSmoothness
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.SourceCuspData
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedContinuationHasNoMellinPoles

/-!
# Joint smoothness of cubic Fourier–Bessel sources

The Fourier–Bessel family with arbitrary complex Bessel order and subexponential coefficients
is closed under differentiation: height differentiation shifts the order by `±1`, while
horizontal differentiation multiplies coefficients by linear frequency weights. Exponential
majorants justify differentiation of the actual sum. Induction on the differentiability order
then gives joint smoothness throughout the positive-height half-space.

The positive-ray and hyperbolic-cosh Bessel kernels agree, so this family contains the actual
cubic residual source after adding its constant mode and multiplying by height.
-/

open MeasureTheory Set Filter Complex
open scoped ContDiff Topology ComplexConjugate Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- Subexponential growth measured in the actual cusp-frequency lattice. -/
def CuspSubexponential (c : O → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
    ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖)

/-- Multiplying a Fourier coefficient by a linear frequency weight preserves subexponential growth. -/
lemma CuspSubexponential.linearWeight {c : O → ℂ} (hc : CuspSubexponential c)
    (m : O → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hm : ∀ h : O, h ≠ 0 → ‖m h‖ ≤ L * ‖cuspFrequency h‖) :
    CuspSubexponential (fun h => m h * c h) :=
  cubicBesselCoefficient_linearWeight_subexponential c m hc L hL hm

/-- The weight contributed by one height derivative. -/
def cuspHeightWeight (h : O) : ℂ := (4 * Real.pi * ‖cuspFrequency h‖ : ℝ)

/-- The weights contributed by the two horizontal Wirtinger derivatives. -/
def cuspHolWeight (h : O) : ℂ := (2 * Real.pi * Complex.I) * cuspFrequency h

def cuspAntiholWeight (h : O) : ℂ := (2 * Real.pi * Complex.I) * conj (cuspFrequency h)

lemma CuspSubexponential.heightWeight {c : O → ℂ} (hc : CuspSubexponential c) :
    CuspSubexponential (fun h => cuspHeightWeight h * c h) := by
  apply hc.linearWeight _ (4 * Real.pi) (by positivity)
  intro h _
  exact le_of_eq (Complex.norm_of_nonneg (by positivity))

lemma CuspSubexponential.holWeight {c : O → ℂ} (hc : CuspSubexponential c) :
    CuspSubexponential (fun h => cuspHolWeight h * c h) := by
  apply hc.linearWeight _ (2 * Real.pi) (by positivity)
  intro h _
  exact le_of_eq (by simp [cuspHolWeight, abs_of_pos Real.pi_pos])

lemma CuspSubexponential.antiholWeight {c : O → ℂ} (hc : CuspSubexponential c) :
    CuspSubexponential (fun h => cuspAntiholWeight h * c h) := by
  apply hc.linearWeight _ (2 * Real.pi) (by positivity)
  intro h _
  exact le_of_eq (by simp [cuspAntiholWeight, abs_of_pos Real.pi_pos])

/-- One nonzero Fourier–Bessel mode with arbitrary complex Bessel order. -/
def besselPlaneTerm (ν : ℂ) (c : O → ℂ) (h : O) (p : ℝ × ℂ) : ℂ :=
  if h = 0 then 0 else c h *
    modifiedBesselKOrder (4 * Real.pi * ‖cuspFrequency h‖ * p.1) ν *
      tracePhase (cuspFrequency h * p.2)

def besselPlaneSeries (ν : ℂ) (c : O → ℂ) (p : ℝ × ℂ) : ℂ :=
  ∑' h : O, besselPlaneTerm ν c h p

/-- Every positive height strip admits an exponentially decaying Fourier majorant. -/
theorem besselPlaneTerm_strip_bound (ν : ℂ) {c : O → ℂ} (hc : CuspSubexponential c)
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, ∀ p : ℝ × ℂ, a ≤ p.1 →
      ‖besselPlaneTerm ν c h p‖ ≤ C * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) := by
  have hgap : 0 < ‖(3 : ℂ) * ringComplex traceLambda‖⁻¹ := by
    apply inv_pos.2
    exact norm_pos_iff.mpr
      (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero))
  obtain ⟨U, hU, hu⟩ := exists_modifiedBesselKOrder_exp_bound ν
    (4 * Real.pi * a * ‖(3 : ℂ) * ringComplex traceLambda‖⁻¹) (by positivity)
  obtain ⟨C, hC, hcoeff⟩ := hc (Real.pi * a) (mul_pos Real.pi_pos ha)
  refine ⟨C * U, mul_nonneg hC hU, ?_⟩
  intro h p hp
  by_cases hh : h = 0
  · simp only [besselPlaneTerm, if_pos hh, norm_zero]
    positivity
  have hx : 4 * Real.pi * a * ‖(3 : ℂ) * ringComplex traceLambda‖⁻¹ ≤
      4 * Real.pi * ‖cuspFrequency h‖ * p.1 := by
    have hm := mul_le_mul (cuspFrequency_norm_lower h hh) hp ha.le (norm_nonneg _)
    have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4 * Real.pi)
    nlinarith only [hm']
  simp only [besselPlaneTerm, if_neg hh, norm_mul, tracePhase_norm, mul_one]
  calc
    _ ≤ (C * Real.exp ((Real.pi * a) * ‖cuspFrequency h‖)) *
        (U * Real.exp (-(4 * Real.pi * ‖cuspFrequency h‖ * p.1))) :=
      mul_le_mul (hcoeff h hh) (hu _ hx) (norm_nonneg _) (by positivity)
    _ = (C * U) * Real.exp ((Real.pi * a) * ‖cuspFrequency h‖ -
        4 * Real.pi * ‖cuspFrequency h‖ * p.1) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hC hU)
      have hm := mul_le_mul_of_nonneg_left hp
        (by positivity : 0 ≤ 4 * Real.pi * ‖cuspFrequency h‖)
      have hn : 0 ≤ Real.pi * a * ‖cuspFrequency h‖ := by positivity
      nlinarith only [hm, hn]

theorem besselPlaneTerm_summable_norm (ν : ℂ) {c : O → ℂ} (hc : CuspSubexponential c)
    (p : ℝ × ℂ) (hp : 0 < p.1) : Summable (fun h => ‖besselPlaneTerm ν c h p‖) := by
  obtain ⟨C, hC, hbound⟩ := besselPlaneTerm_strip_bound ν hc p.1 hp
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun h => hbound h p le_rfl)
    ((summable_exp_neg_cuspFrequency_norm (Real.pi * p.1) (mul_pos Real.pi_pos hp)).mul_left C)

/-- The derivative family closes under adjacent Bessel orders and linear frequency weights. -/
def besselPlaneTermFDeriv (ν : ℂ) (c : O → ℂ) (h : O) (p : ℝ × ℂ) :
    (ℝ × ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      (-(1 / 2 : ℂ) *
        (besselPlaneTerm (ν + 1) (fun j => cuspHeightWeight j * c j) h p +
          besselPlaneTerm (ν - 1) (fun j => cuspHeightWeight j * c j) h p)) +
    besselPlaneTerm ν (fun j => cuspHolWeight j * c j) h p •
      ContinuousLinearMap.snd ℝ ℝ ℂ +
    besselPlaneTerm ν (fun j => cuspAntiholWeight j * c j) h p •
      Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ ℂ)

lemma besselPlaneTermFDeriv_apply (ν : ℂ) (c : O → ℂ) (h : O) (p u : ℝ × ℂ) :
    besselPlaneTermFDeriv ν c h p u =
      (u.1 : ℂ) * (-(1 / 2 : ℂ) *
        (besselPlaneTerm (ν + 1) (fun j => cuspHeightWeight j * c j) h p +
          besselPlaneTerm (ν - 1) (fun j => cuspHeightWeight j * c j) h p)) +
      besselPlaneTerm ν (fun j => cuspHolWeight j * c j) h p * u.2 +
      besselPlaneTerm ν (fun j => cuspAntiholWeight j * c j) h p * conj u.2 := rfl

/-- Termwise differentiation in height and both horizontal directions. -/
theorem besselPlaneTerm_hasFDerivAt (ν : ℂ) (c : O → ℂ) (h : O) (p : ℝ × ℂ)
    (hp : 0 < p.1) :
    HasFDerivAt (besselPlaneTerm ν c h) (besselPlaneTermFDeriv ν c h p) p := by
  by_cases hh : h = 0
  · subst h
    have hf : besselPlaneTerm ν c 0 = fun _ => 0 := by
      funext q
      simp [besselPlaneTerm]
    have hd : besselPlaneTermFDeriv ν c 0 p = 0 := by
      apply ContinuousLinearMap.ext
      intro u
      simp [besselPlaneTermFDeriv_apply, besselPlaneTerm]
    rw [hf, hd]
    exact hasFDerivAt_const 0 p
  have hscale : 0 < 4 * Real.pi * ‖cuspFrequency h‖ := by
    have := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    positivity
  have hi : HasFDerivAt (fun q : ℝ × ℂ => 4 * Real.pi * ‖cuspFrequency h‖ * q.1)
      ((4 * Real.pi * ‖cuspFrequency h‖) • ContinuousLinearMap.fst ℝ ℝ ℂ) p :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_mul _
  have hk := (RHTower.d4BM_hasDerivAt_modifiedBesselKOrder_argument
    (mul_pos hscale hp) ν).hasFDerivAt.comp p hi
  have hz := (tracePhase_hasFDerivAt (cuspFrequency h) p.2).comp p
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  convert! (hk.const_mul (c h)).mul hz using 1
  · funext q
    simp only [besselPlaneTerm, if_neg hh, Function.comp_def, Pi.mul_apply]
  · apply ContinuousLinearMap.ext
    intro u
    rw [besselPlaneTermFDeriv_apply]
    change _ =
      (c h * modifiedBesselKOrder (4 * Real.pi * ‖cuspFrequency h‖ * p.1) ν) *
        (tracePhase (cuspFrequency h * p.2) * horizontalPhaseCLM (cuspFrequency h) u.2) +
      tracePhase (cuspFrequency h * p.2) *
        (c h * (((4 * Real.pi * ‖cuspFrequency h‖ * u.1 : ℝ) : ℂ) *
          (-(1 / 2 : ℂ) *
            (modifiedBesselKOrder (4 * Real.pi * ‖cuspFrequency h‖ * p.1) (ν + 1) +
              modifiedBesselKOrder (4 * Real.pi * ‖cuspFrequency h‖ * p.1) (ν - 1)))))
    rw [horizontalPhaseCLM_apply]
    simp only [besselPlaneTerm, if_neg hh, cuspHeightWeight, cuspHolWeight, cuspAntiholWeight,
      Complex.ofReal_mul, Complex.star_def, map_mul]
    ring

lemma besselPlaneTermFDeriv_norm_le (ν : ℂ) (c : O → ℂ) (h : O) (p : ℝ × ℂ) :
    ‖besselPlaneTermFDeriv ν c h p‖ ≤
      (1 / 2 : ℝ) *
        (‖besselPlaneTerm (ν + 1) (fun j => cuspHeightWeight j * c j) h p‖ +
          ‖besselPlaneTerm (ν - 1) (fun j => cuspHeightWeight j * c j) h p‖) +
      ‖besselPlaneTerm ν (fun j => cuspHolWeight j * c j) h p‖ +
      ‖besselPlaneTerm ν (fun j => cuspAntiholWeight j * c j) h p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [besselPlaneTermFDeriv_apply]
  calc
    _ ≤ (‖(u.1 : ℂ) * (-(1 / 2 : ℂ) *
        (besselPlaneTerm (ν + 1) (fun j => cuspHeightWeight j * c j) h p +
          besselPlaneTerm (ν - 1) (fun j => cuspHeightWeight j * c j) h p))‖ +
      ‖besselPlaneTerm ν (fun j => cuspHolWeight j * c j) h p * u.2‖) +
      ‖besselPlaneTerm ν (fun j => cuspAntiholWeight j * c j) h p * conj u.2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖u‖ * ((1 / 2 : ℝ) *
        (‖besselPlaneTerm (ν + 1) (fun j => cuspHeightWeight j * c j) h p‖ +
          ‖besselPlaneTerm (ν - 1) (fun j => cuspHeightWeight j * c j) h p‖)) +
      ‖besselPlaneTerm ν (fun j => cuspHolWeight j * c j) h p‖ * ‖u‖) +
      ‖besselPlaneTerm ν (fun j => cuspAntiholWeight j * c j) h p‖ * ‖u‖ := by
        simp only [norm_mul, Complex.norm_real, Complex.norm_conj]
        norm_num only [norm_neg, norm_div, norm_one, Complex.norm_two]
        gcongr
        · exact norm_fst_le u
        · exact norm_add_le _ _
        · exact norm_snd_le u
        · exact norm_snd_le u
    _ = _ := by ring

/-- The entire derivative family has a common exponentially summable majorant on height strips. -/
theorem besselPlaneTermFDeriv_strip_bound (ν : ℂ) {c : O → ℂ}
    (hc : CuspSubexponential c) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, ∀ p : ℝ × ℂ, a ≤ p.1 →
      ‖besselPlaneTermFDeriv ν c h p‖ ≤ C * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) := by
  obtain ⟨Cp, hCp, hbp⟩ := besselPlaneTerm_strip_bound (ν + 1) hc.heightWeight a ha
  obtain ⟨Cm, hCm, hbm⟩ := besselPlaneTerm_strip_bound (ν - 1) hc.heightWeight a ha
  obtain ⟨Ch, hCh, hbh⟩ := besselPlaneTerm_strip_bound ν hc.holWeight a ha
  obtain ⟨Ca, hCa, hba⟩ := besselPlaneTerm_strip_bound ν hc.antiholWeight a ha
  refine ⟨(1 / 2) * (Cp + Cm) + Ch + Ca, by positivity, ?_⟩
  intro h p hp
  apply (besselPlaneTermFDeriv_norm_le ν c h p).trans
  calc
    _ ≤ (1 / 2 : ℝ) * (Cp * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) +
        Cm * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖)) +
        Ch * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) +
        Ca * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) := by
      gcongr
      · exact hbp h p hp
      · exact hbm h p hp
      · exact hbh h p hp
      · exact hba h p hp
    _ = _ := by ring

/-- Uniform domination gives the derivative of the actual Fourier–Bessel sum. -/
theorem besselPlaneSeries_hasFDerivAt (ν : ℂ) {c : O → ℂ} (hc : CuspSubexponential c)
    (p : ℝ × ℂ) (hp : 0 < p.1) :
    HasFDerivAt (besselPlaneSeries ν c) (∑' h : O, besselPlaneTermFDeriv ν c h p) p := by
  obtain ⟨C, hC, hb⟩ := besselPlaneTermFDeriv_strip_bound ν hc (p.1 / 2) (half_pos hp)
  have hs := (summable_exp_neg_cuspFrequency_norm (Real.pi * (p.1 / 2))
    (mul_pos Real.pi_pos (half_pos hp))).mul_left C
  have hmem : p ∈ Ioo (p.1 / 2) (2 * p.1) ×ˢ (univ : Set ℂ) :=
    ⟨⟨by linarith only [hp], by linarith only [hp]⟩, mem_univ _⟩
  exact hasFDerivAt_tsum_of_isPreconnected
    (f := besselPlaneTerm ν c) (f' := besselPlaneTermFDeriv ν c)
    hs (isOpen_Ioo.prod isOpen_univ) (isPreconnected_Ioo.prod isPreconnected_univ)
    (fun h q hq => besselPlaneTerm_hasFDerivAt ν c h q ((half_pos hp).trans hq.1.1))
    (fun h q hq => hb h q hq.1.1.le) hmem
    (besselPlaneTerm_summable_norm ν hc p hp).of_norm hmem

/-- The differential of the sum lies in four adjacent Fourier–Bessel families. -/
theorem besselPlaneSeries_fderiv_apply (ν : ℂ) {c : O → ℂ} (hc : CuspSubexponential c)
    (p u : ℝ × ℂ) (hp : 0 < p.1) :
    fderiv ℝ (besselPlaneSeries ν c) p u =
      (u.1 : ℂ) * (-(1 / 2 : ℂ) *
        (besselPlaneSeries (ν + 1) (fun j => cuspHeightWeight j * c j) p +
          besselPlaneSeries (ν - 1) (fun j => cuspHeightWeight j * c j) p)) +
      besselPlaneSeries ν (fun j => cuspHolWeight j * c j) p * u.2 +
      besselPlaneSeries ν (fun j => cuspAntiholWeight j * c j) p * conj u.2 := by
  obtain ⟨C, hC, hb⟩ := besselPlaneTermFDeriv_strip_bound ν hc p.1 hp
  have hds : Summable (fun h => besselPlaneTermFDeriv ν c h p) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun h => hb h p le_rfl)
      ((summable_exp_neg_cuspFrequency_norm (Real.pi * p.1) (mul_pos Real.pi_pos hp)).mul_left C)).of_norm
  have hsp := (besselPlaneTerm_summable_norm (ν + 1) hc.heightWeight p hp).of_norm
  have hsm := (besselPlaneTerm_summable_norm (ν - 1) hc.heightWeight p hp).of_norm
  have hsh := (besselPlaneTerm_summable_norm ν hc.holWeight p hp).of_norm
  have hsb := (besselPlaneTerm_summable_norm ν hc.antiholWeight p hp).of_norm
  rw [(besselPlaneSeries_hasFDerivAt ν hc p hp).fderiv]
  change (ContinuousLinearMap.apply ℝ ℂ u) (∑' h : O, besselPlaneTermFDeriv ν c h p) = _
  rw [(ContinuousLinearMap.apply ℝ ℂ u).map_tsum hds]
  change (∑' h : O, besselPlaneTermFDeriv ν c h p u) = _
  simp_rw [besselPlaneTermFDeriv_apply]
  have hva := ((hsp.add hsm).mul_left (-(1 / 2 : ℂ))).mul_left (u.1 : ℂ)
  have hvh := hsh.mul_right u.2
  have hvb := hsb.mul_right (conj u.2)
  rw [(hva.add hvh).tsum_add hvb, hva.tsum_add hvh, tsum_mul_left, tsum_mul_left,
    hsp.tsum_add hsm, tsum_mul_right, tsum_mul_right]
  rfl

/-- All real derivatives of the Fourier–Bessel family are smooth on positive heights.
The induction uses closure under adjacent orders and linear frequency weights. -/
theorem contDiffOn_besselPlaneSeries (ν : ℂ) {c : O → ℂ} (hc : CuspSubexponential c) :
    ContDiffOn ℝ ∞ (besselPlaneSeries ν c) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := isOpen_Ioi.prod isOpen_univ
  have hall : ∀ n : ℕ, ∀ μ : ℂ, ∀ d : O → ℂ, CuspSubexponential d →
      ContDiffOn ℝ n (besselPlaneSeries μ d) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := by
    intro n
    induction n with
    | zero =>
        intro μ d hd
        exact contDiffOn_zero.2 (fun p hp =>
          (besselPlaneSeries_hasFDerivAt μ hd p hp.1).continuousAt.continuousWithinAt)
    | succ n ih =>
        intro μ d hd
        rw [show (↑(n + 1) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
          contDiffOn_succ_iff_fderiv_apply hU.uniqueDiffOn]
        refine ⟨fun p hp => (besselPlaneSeries_hasFDerivAt μ hd p hp.1).differentiableAt.differentiableWithinAt,
          by simp, ?_⟩
        intro u
        have hform : ContDiffOn ℝ n (fun p : ℝ × ℂ =>
            (u.1 : ℂ) * (-(1 / 2 : ℂ) *
              (besselPlaneSeries (μ + 1) (fun j => cuspHeightWeight j * d j) p +
                besselPlaneSeries (μ - 1) (fun j => cuspHeightWeight j * d j) p)) +
            besselPlaneSeries μ (fun j => cuspHolWeight j * d j) p * u.2 +
            besselPlaneSeries μ (fun j => cuspAntiholWeight j * d j) p * conj u.2)
            (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) :=
          ((contDiffOn_const.mul (contDiffOn_const.mul
            ((ih (μ + 1) _ hd.heightWeight).add (ih (μ - 1) _ hd.heightWeight)))).add
            ((ih μ _ hd.holWeight).mul contDiffOn_const)).add
            ((ih μ _ hd.antiholWeight).mul contDiffOn_const)
        apply hform.congr
        intro p hp
        have hD := besselPlaneSeries_hasFDerivAt μ hd p hp.1
        have he : fderivWithin ℝ (besselPlaneSeries μ d)
            (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) p = fderiv ℝ (besselPlaneSeries μ d) p :=
          (hD.hasFDerivWithinAt.fderivWithin (hU.uniqueDiffWithinAt hp)).trans hD.fderiv.symm
        rw [he, besselPlaneSeries_fderiv_apply μ hd p u hp.1]
  exact contDiffOn_infty.2 (fun n => hall n ν c hc)

/-- The actual residual cubic source belongs to the smooth Fourier–Bessel family. -/
theorem cubicSourceResidualFunction_eq_besselPlaneSeries (p : ℝ × ℂ) (hp : 0 < p.1) :
    cubicSourceResidualFunction (cuspCoordinateLift p) =
      (3 * (Real.pi : ℂ) * constantArithmeticResidue) * (p.1 : ℂ) ^ (2 / 3 : ℂ) +
        (p.1 : ℂ) * besselPlaneSeries (1 / 3) rationalSourceResidualFourierCoefficient p := by
  rw [cubicSourceResidualFunction_bessel_coordinates p hp]
  congr 1
  calc
    _ = ∑' h : O, (p.1 : ℂ) *
        besselPlaneTerm (1 / 3) rationalSourceResidualFourierCoefficient h p := by
      apply tsum_congr
      intro h
      by_cases hh : h = 0
      · simp [cubicBesselTerm, cubicBesselAmplitude, besselPlaneTerm, hh]
      · have hx : 0 < 4 * Real.pi * ‖cuspFrequency h‖ * p.1 := by
          have := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
          positivity
        simp only [cubicBesselTerm, cubicBesselAmplitude, besselPlaneTerm, if_neg hh]
        rw [GaloisForLFunctions.SpectralTheoryOfTheCubicCover.schlafliBesselK_eq_modifiedBesselKOrder _ hx]
        ring
    _ = _ := tsum_mul_left

/-- The constant cusp mode is smooth at every positive height. -/
private theorem contDiffOn_cusp_height_cpow (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (p.1 : ℂ) ^ s)
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := by
  intro p hp
  have hlog : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => Real.log q.1) p :=
    (Real.contDiffAt_log.2 (ne_of_gt hp.1)).comp p contDiffAt_fst
  have he : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ =>
      Complex.exp (s * (Real.log q.1 : ℂ))) p :=
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p hlog)).cexp
  apply (he.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp.1)] with q hq
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hq)),
    ← Complex.ofReal_log (le_of_lt hq)]
  congr 1
  ring

/-- Joint infinite smoothness of the actual cubic residual source in positive cusp coordinates. -/
theorem cubicSourceResidualFunction_coordinate_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => cubicSourceResidualFunction (cuspCoordinateLift p))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := by
  have hs := contDiffOn_besselPlaneSeries (1 / 3)
    (c := rationalSourceResidualFourierCoefficient)
    rationalSourceResidualFourierCoefficient_subexponential
  have hv : ContDiff ℝ ∞ (fun p : ℝ × ℂ => (p.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  apply ((contDiffOn_const.mul (contDiffOn_cusp_height_cpow (2 / 3))).add
    (hv.contDiffOn.mul hs)).congr
  intro p hp
  exact cubicSourceResidualFunction_eq_besselPlaneSeries p hp.1

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
