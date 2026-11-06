import GaloisForLFunctions.CompletedArithmeticForms.ApertureRadialProfile
import GaloisForLFunctions.CompletedArithmeticForms.ThetaAtomPairComplex

/-!
# Literal aperture-weighted theta-pair jets

Exponential radial substitution retains the product scale and label-ratio
translation. Every signed Schwartz jet equals the corresponding literal
aperture-weighted source derivative.
-/

set_option autoImplicit false

open Complex Filter Set MeasureTheory
open scoped Topology SchwartzMap FourierTransform
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry _root_.RHTower
noncomputable section

/-- The positive radial scale of an ordered pair. -/
theorem thetaPair_radialScale_ge_two {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    2 ≤ Real.pi * n * m := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 := le_mul_of_one_le_right Real.pi_pos.le hnR
  have h2 := le_mul_of_one_le_right (show 0 ≤ Real.pi * n by positivity) hmR
  linarith only [Real.pi_gt_three, h1, h2]

private theorem apertureRadialWeight_expScale (a : ℝ) {q : ℝ} (hq : 0 < q) (s : ℝ) :
    apertureRadialWeight a q (q * Real.exp s) = s * Real.sinh (a * s) := by
  simp only [apertureRadialWeight, mul_div_cancel_left₀ _ hq.ne', Real.log_exp]

/-- The literal weighted complex pair jet is an integrable radial jet after substitution. -/
theorem integrableOn_weighted_thetaAtomPair_jet {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    IntegrableOn (fun s : ℝ => (s * Real.sinh (a * s) : ℂ) *
      iteratedDeriv k (thetaAtomPairComplex n m s) 0) (Ioi 0) := by
  let q : ℝ := Real.pi * n * m
  let δ : ℝ := (Real.log n - Real.log m) / 2
  have hq : 2 ≤ q := thetaPair_radialScale_ge_two hn hm
  have hq0 : 0 < q := by linarith only [hq]
  have hδ : |(δ : ℂ).im| < Real.pi / 6 := by simp; positivity
  have hi := integrableOn_apertureRadialWeight_mul_jet ha0 ha1 hq k hδ
  have hc := ((integrableOn_Ioi_expScale hq0 _).mp hi).const_mul
    ((4 * q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  apply hc.congr
  filter_upwards with s
  rw [thetaAtomPairComplex_jet_eq_radial hn hm, apertureRadialWeight_expScale a hq0]
  simp only [Complex.real_smul, q, δ]
  push_cast
  ring

/-- Exponential radial substitution identifies every aperture-weighted pair jet. -/
theorem integral_weighted_thetaAtomPair_jet {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    (∫ s in Ioi (0 : ℝ), (s * Real.sinh (a * s) : ℂ) *
      iteratedDeriv k (thetaAtomPairComplex n m s) 0) =
      ((4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        iteratedDeriv k (apertureRadialProfile a (Real.pi * n * m))
          (((Real.log n - Real.log m) / 2 : ℝ) : ℂ) := by
  let q : ℝ := Real.pi * n * m
  let δ : ℝ := (Real.log n - Real.log m) / 2
  have hq : 2 ≤ q := thetaPair_radialScale_ge_two hn hm
  have hq0 : 0 < q := by linarith only [hq]
  have hδ : |(δ : ℂ).im| < Real.pi / 6 := by simp; positivity
  rw [iteratedDeriv_apertureRadialProfile ha0 ha1 hq k hδ,
    integral_Ioi_expScale hq0, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp only
  rw [thetaAtomPairComplex_jet_eq_radial hn hm, apertureRadialWeight_expScale a hq0]
  simp only [Complex.real_smul, q, δ]
  push_cast
  ring

/-- The Schwartz profile for an ordered pair retains its radial scale and real translation. -/
def thetaPairApertureSchwartz (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : SchwartzMap ℝ ℂ :=
  ((4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
    (apertureRadialSchwartz a (Real.pi * n * m) ha0 ha1
      (thetaPair_radialScale_ge_two hn hm)).compSubConstCLM ℂ
        (-((Real.log n - Real.log m) / 2))

theorem thetaPairApertureSchwartz_apply {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    thetaPairApertureSchwartz n m hn hm a ha0 ha1 t =
      ((4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        apertureRadialProfile a (Real.pi * n * m)
          ((t : ℂ) + (((Real.log n - Real.log m) / 2 : ℝ) : ℂ)) := by
  change _ * apertureRadialProfile a (Real.pi * n * m)
    ((t - -((Real.log n - Real.log m) / 2) : ℝ) : ℂ) = _
  rw [sub_neg_eq_add, Complex.ofReal_add]

/-- The real Schwartz jets equal the translated holomorphic radial jets. -/
theorem thetaPairApertureSchwartz_jet {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    iteratedDeriv k (thetaPairApertureSchwartz n m hn hm a ha0 ha1) 0 =
      ((4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        iteratedDeriv k (apertureRadialProfile a (Real.pi * n * m))
          (((Real.log n - Real.log m) / 2 : ℝ) : ℂ) := by
  let q : ℝ := Real.pi * n * m
  let δ : ℝ := (Real.log n - Real.log m) / 2
  let C : ℂ := ((4 * q ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  let G : ℂ → ℂ := fun z => C * apertureRadialProfile a q (z + (δ : ℂ))
  have hq : 2 ≤ q := thetaPair_radialScale_ge_two hn hm
  have hG : ∀ z : ℂ, |z.im| < Real.pi / 6 → DifferentiableAt ℂ G z := by
    intro z hz
    apply DifferentiableAt.const_mul
    exact (differentiableAt_apertureRadialProfile ha0 ha1 hq
      (by simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hz)).comp z
        (differentiableAt_id.add_const _)
  have he : (thetaPairApertureSchwartz n m hn hm a ha0 ha1 : ℝ → ℂ) =
      fun t : ℝ => G (t : ℂ) := funext (thetaPairApertureSchwartz_apply hn hm ha0 ha1)
  rw [he, HTGeometry.iteratedDeriv_ofReal_on_strip (by positivity : 0 < Real.pi / 6) hG k 0]
  dsimp only [G]
  rw [iteratedDeriv_const_mul_field]
  dsimp only
  rw [HTGeometry.iteratedDeriv_comp_add_right, Complex.ofReal_zero, zero_add]

/-- Signed literal pair jets are absolutely integrable with the aperture primitive. -/
theorem integrableOn_signed_thetaPairJet {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    IntegrableOn (fun s : ℝ => s * Real.sinh (a * s) * ((-I) ^ k).re *
      iteratedDeriv k (fun t : ℝ =>
        thetaCuspSourceTerm (s / 2 + t) n * thetaCuspSourceTerm (s / 2 - t) m) 0) (Ioi 0) := by
  have hi := (integrableOn_weighted_thetaAtomPair_jet hn hm ha0 ha1 k).const_mul ((-I) ^ k)
  have hr := Complex.reCLM.integrable_comp hi
  apply hr.congr
  filter_upwards with s
  rw [thetaAtomPairComplex_jet hn hm]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero]
  ring

/-- Every signed Schwartz jet is the literal aperture-weighted source derivative. -/
theorem thetaPairApertureSchwartz_signedJet {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    ((-I) ^ k * iteratedDeriv k (thetaPairApertureSchwartz n m hn hm a ha0 ha1) 0).re =
      ∫ s in Ioi (0 : ℝ), s * Real.sinh (a * s) * ((-I) ^ k).re *
        iteratedDeriv k (fun t : ℝ =>
          thetaCuspSourceTerm (s / 2 + t) n * thetaCuspSourceTerm (s / 2 - t) m) 0 := by
  have hi := integrableOn_weighted_thetaAtomPair_jet hn hm ha0 ha1 k
  have he := Complex.reCLM.integral_comp_comm (hi.const_mul ((-I) ^ k))
  simp only [Complex.reCLM_apply] at he
  rw [integral_const_mul, integral_weighted_thetaAtomPair_jet hn hm ha0 ha1,
    ← thetaPairApertureSchwartz_jet hn hm ha0 ha1] at he
  rw [← he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp only
  rw [thetaAtomPairComplex_jet hn hm]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  ring

#print axioms integrableOn_weighted_thetaAtomPair_jet
#print axioms integral_weighted_thetaAtomPair_jet
#print axioms thetaPairApertureSchwartz_signedJet

end
end GaloisForLFunctions.CompletedArithmeticForms
