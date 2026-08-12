import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemma401Continuation
import GaloisForLFunctions.RHTower.SuzukiCompactL2Fourier
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# Suzuki (2012), Lemma 4.3: compact-output obstruction

For `omega > 1/2`, a source supported in a logarithmic left half-line cannot have compactly
supported canonical Hankel output unless it vanishes.  Equation (4.01) shows that the compact
output transform, shifted by `i omega`, vanishes at every centered Xi zero.  The already formalized
Titchmarsh--Jensen exponential-type uniqueness theorem then forces that transform, and hence the
output, to vanish.

The proof explicitly verifies that Suzuki's denominator is nonzero at every inherited numerator
zero; it does not exploit Lean's totalized `0 / 0` convention.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform ENNReal

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

/-! ## Full and cutoff Fourier integrals -/

theorem suzukiLowerFourierLaplace_eq_full_integral_of_fixed
    {B : ℝ} {p : SoninL2} (hp : logLowerHalflineCutoff B p = p)
    (z : ℂ) :
    suzukiLowerFourierLaplace B p z =
      ∫ t : ℝ, Complex.exp (I * z * (t : ℂ)) * p t := by
  rw [suzukiLowerFourierLaplace_eq_integral]
  have hpae : (p : ℝ → ℂ) =ᵐ[volume]
      (Ici B).indicator (fun t => (p : ℝ → ℂ) t) := by
    have hcut := indicatorCutoff_ae (Ici B) measurableSet_Ici p
    have heq : (logLowerHalflineCutoff B p : ℝ → ℂ) = (p : ℝ → ℂ) :=
      congrArg (fun v : SoninL2 => (v : ℝ → ℂ)) hp
    filter_upwards [hcut] with t ht
    have heqPoint : logLowerHalflineCutoff B p t = p t :=
      congrFun heq t
    rw [← heqPoint]
    simpa [logLowerHalflineCutoff] using ht
  apply integral_congr_ae
  filter_upwards [hpae] with t ht
  rw [ht]
  by_cases htB : t ∈ Ici B <;> simp [htB]

theorem suzukiCompactL2Fourier_eq_full_integral_of_fixed
    {R : ℝ} {p : SoninL2} (hp : suzukiCutoff R p = p)
    (z : ℂ) :
    suzukiCompactL2Fourier R p z =
      ∫ t : ℝ, Complex.exp (I * z * (t : ℂ)) * p t := by
  rw [suzukiCompactL2Fourier]
  have heq : (suzukiCutoff R p : ℝ → ℂ) = (p : ℝ → ℂ) :=
    congrArg (fun v : SoninL2 => (v : ℝ → ℂ)) hp
  apply integral_congr_ae
  filter_upwards with t
  rw [heq]
  ring

/-! ## Shifted Paley--Wiener transform -/

def suzukiShiftedCompactOutputFourier
    (omega R : ℝ) (p : SoninL2) (z : ℂ) : ℂ :=
  suzukiCompactL2Fourier R p (z + (omega : ℂ) * I)

theorem differentiable_suzukiShiftedCompactOutputFourier
    {R : ℝ} (hR : 0 ≤ R) (omega : ℝ) (p : SoninL2) :
    Differentiable ℂ (suzukiShiftedCompactOutputFourier omega R p) := by
  exact (differentiable_suzukiCompactL2Fourier hR p).comp
    (by fun_prop)

theorem suzukiShiftedCompactOutputFourier_exponentialType
    {R : ℝ} (hR : 0 ≤ R) (omega : ℝ) (p : SoninL2) :
    ∃ A C : ℝ, 0 ≤ A ∧ 1 ≤ C ∧ ∀ z : ℂ,
      ‖suzukiShiftedCompactOutputFourier omega R p z‖ ≤
        C * Real.exp (A * ‖z‖) := by
  obtain ⟨C₀, hC₀, hgrow⟩ := suzukiCompactL2Fourier_exponentialType hR p
  let D : ℝ := C₀ * Real.exp (R * |omega|)
  let C : ℝ := max 1 D
  refine ⟨R, C, hR, le_max_left _ _, ?_⟩
  intro z
  have hshift : ‖z + (omega : ℂ) * I‖ ≤ ‖z‖ + |omega| := by
    calc
      ‖z + (omega : ℂ) * I‖ ≤ ‖z‖ + ‖(omega : ℂ) * I‖ := norm_add_le _ _
      _ = ‖z‖ + |omega| := by simp
  have hexp : Real.exp (R * ‖z + (omega : ℂ) * I‖) ≤
      Real.exp (R * ‖z‖) * Real.exp (R * |omega|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc
    ‖suzukiShiftedCompactOutputFourier omega R p z‖ =
        ‖suzukiCompactL2Fourier R p (z + (omega : ℂ) * I)‖ := rfl
    _ ≤ C₀ * Real.exp (R * ‖z + (omega : ℂ) * I‖) := hgrow _
    _ ≤ C₀ * (Real.exp (R * ‖z‖) * Real.exp (R * |omega|)) := by
      gcongr
    _ = D * Real.exp (R * ‖z‖) := by dsimp only [D]; ring
    _ ≤ C * Real.exp (R * ‖z‖) := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)

/-! ## Lemma 4.3 -/

/-- **Suzuki (2012), Lemma 4.3, logarithmic exact form.**  If the canonical Hankel output of a
left-half-line-supported `L²` source has compact support, then both output and source are zero. -/
theorem suzuki2012_lemma_four_three
    {omega A R : ℝ} (homega : 1 / 2 < omega) (hR : 0 ≤ R)
    (q : SoninL2) (hq : logHalflineCutoff A q = q)
    (hcompact : suzukiCutoff R
        (suzukiCanonicalLogHankelUnitary omega
          (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) q) =
      suzukiCanonicalLogHankelUnitary omega
        (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) q) :
    suzukiCanonicalLogHankelUnitary omega
        (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) q = 0 ∧
      q = 0 := by
  let hinner := suzukiCanonicalTheta_meromorphicInner_of_half_lt homega
  let H := suzukiCanonicalLogHankelUnitary omega hinner
  let p := H q
  let F := suzukiShiftedCompactOutputFourier omega R p
  have hpLower : logLowerHalflineCutoff (-A) p = p :=
    suzukiCanonicalLogHankelUnitary_maps_upper_to_reflected_lower homega q hq
  have hFdiff : Differentiable ℂ F :=
    differentiable_suzukiShiftedCompactOutputFourier hR omega p
  have hFtype : ∃ B C : ℝ, 0 ≤ B ∧ 1 ≤ C ∧ ∀ z : ℂ,
      ‖F z‖ ≤ C * Real.exp (B * ‖z‖) :=
    suzukiShiftedCompactOutputFourier_exponentialType hR omega p
  have hFzeros : ∀ w : ℂ, xi (1 / 2 - I * w) = 0 → F w = 0 := by
    intro w hw
    let rho : ℂ := 1 / 2 - I * w
    let z : ℂ := w + (omega : ℂ) * I
    have hrho : xi rho = 0 := by simpa [rho] using hw
    obtain ⟨hrho0, _hrho1⟩ := xi_zero_re_mem_open_unit hrho
    have hz : 0 < z.im := by
      have hrhoRe : rho.re = 1 / 2 + w.im := by
        simp [rho, Complex.mul_re]
      dsimp only [z]
      simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, mul_one]
      linarith
    have hnumArg :
        1 / 2 - (omega : ℂ) - z * I = rho := by
      dsimp only [z, rho]
      rw [add_mul, mul_assoc, I_mul_I]
      ring
    have hdenArg :
        1 / 2 + (omega : ℂ) - z * I = rho + (2 * omega : ℝ) := by
      dsimp only [z, rho]
      rw [add_mul, mul_assoc, I_mul_I]
      push_cast
      ring
    have hdenRe : 1 < (rho + (2 * omega : ℝ)).re := by
      simp only [add_re, ofReal_re]
      linarith
    have hden : xi (rho + (2 * omega : ℝ)) ≠ 0 :=
      xi_ne_zero_of_one_lt_re hdenRe
    have htheta : suzukiCanonicalTheta omega z = 0 := by
      rw [suzukiCanonicalTheta, hnumArg, hdenArg]
      exact (div_eq_iff hden).2 (by rw [hrho, zero_mul])
    have heq401 := suzuki2012_equation_four_zero_one homega q hq hz
    have hpTransform :
        suzukiLowerFourierLaplace (-A) p z =
          suzukiCompactL2Fourier R p z := by
      rw [suzukiLowerFourierLaplace_eq_full_integral_of_fixed hpLower,
        suzukiCompactL2Fourier_eq_full_integral_of_fixed hcompact]
    dsimp only [F, suzukiShiftedCompactOutputFourier]
    change suzukiCompactL2Fourier R p z = 0
    rw [← hpTransform, heq401, htheta, zero_mul]
  have hFzero : F = fun _ => 0 :=
    suzuki_lemma_two_one hFdiff 0 hFtype hFzeros
  have hpzero : p = 0 := by
    apply eq_zero_of_supported_fourier_constant_on_xiZeros hR hcompact
    intro w hw
    have h := congrFun hFzero (w - (omega : ℂ) * I)
    dsimp only [F, suzukiShiftedCompactOutputFourier] at h
    rw [sub_add_cancel] at h
    exact h
  constructor
  · exact hpzero
  · exact H.injective (by simpa only [p, map_zero] using hpzero)

end RHTower
