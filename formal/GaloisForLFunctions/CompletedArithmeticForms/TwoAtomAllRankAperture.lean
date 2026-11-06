import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairApertureFourier
import GaloisForLFunctions.CompletedArithmeticForms.TwoAtomApertureSpectrum
import GaloisForLFunctions.CompletedArithmeticForms.FourierPositiveHankel
import GaloisForLFunctions.HTGeometry.HankelSuccessorSchurStrict

/-!
# Strict two-atom aperture sections at every rank

The exact two-atom Fourier spectrum is strictly positive. Its literal
aperture-weighted source jets therefore have positive definite Hankel
sections, positive determinants, and strictly positive successor Schur
coordinates at every finite rank.
-/

set_option autoImplicit false

open Complex Filter Set MeasureTheory Matrix
open scoped Topology SchwartzMap FourierTransform
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry _root_.RHTower
noncomputable section

private theorem iteratedDeriv_four_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f₁ f₂ f₃ f₄ : ℝ → E} {k : ℕ}
    (h₁ : ContDiff ℝ k f₁) (h₂ : ContDiff ℝ k f₂)
    (h₃ : ContDiff ℝ k f₃) (h₄ : ContDiff ℝ k f₄) (x : ℝ) :
    iteratedDeriv k (fun t => f₁ t + f₂ t + f₃ t + f₄ t) x =
      iteratedDeriv k f₁ x + iteratedDeriv k f₂ x +
        iteratedDeriv k f₃ x + iteratedDeriv k f₄ x := by
  have h12 := iteratedDeriv_add h₁.contDiffAt h₂.contDiffAt (x := x)
  have h123 := iteratedDeriv_add (h₁.add h₂).contDiffAt h₃.contDiffAt (x := x)
  have h1234 := iteratedDeriv_add ((h₁.add h₂).add h₃).contDiffAt h₄.contDiffAt (x := x)
  calc
    _ = iteratedDeriv k (fun t => f₁ t + f₂ t + f₃ t) x + iteratedDeriv k f₄ x := h1234
    _ = (iteratedDeriv k (fun t => f₁ t + f₂ t) x + iteratedDeriv k f₃ x) +
        iteratedDeriv k f₄ x := congrArg (fun y => y + iteratedDeriv k f₄ x) h123
    _ = _ := congrArg (fun y => y + iteratedDeriv k f₃ x + iteratedDeriv k f₄ x) h12

/-- The first two ordinary theta atoms. -/
def twoAtomThetaSource (x : ℝ) : ℝ := thetaCuspSourceTerm x 1 + thetaCuspSourceTerm x 2

/-- The Schwartz profile of all four ordered pairs, with the aperture primitive retained. -/
def twoAtomApertureSchwartz (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : SchwartzMap ℝ ℂ :=
  thetaPairApertureSchwartz 1 1 (by decide) (by decide) a ha0 ha1 +
  thetaPairApertureSchwartz 1 2 (by decide) (by decide) a ha0 ha1 +
  thetaPairApertureSchwartz 2 1 (by decide) (by decide) a ha0 ha1 +
  thetaPairApertureSchwartz 2 2 (by decide) (by decide) a ha0 ha1

/-- The exact two-atom aperture spectrum is strictly positive at every frequency. -/
theorem fourier_twoAtomApertureSchwartz_re_pos {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (ξ : ℝ) :
    0 < (𝓕 (twoAtomApertureSchwartz a ha0.le (by linarith only [ha]) : ℝ → ℂ) ξ).re := by
  have hadd (f g : SchwartzMap ℝ ℂ) :
      𝓕 ((f + g : SchwartzMap ℝ ℂ) : ℝ → ℂ) ξ =
        𝓕 (f : ℝ → ℂ) ξ + 𝓕 (g : ℝ → ℂ) ξ := by
    change 𝓕 (fun t : ℝ => f t + g t) ξ = _
    exact HTGeometry.fourierIntegral_add f.integrable g.integrable ξ
  simp only [twoAtomApertureSchwartz, hadd, Complex.add_re]
  rw [fourier_thetaPairApertureSchwartz_re, fourier_thetaPairApertureSchwartz_re,
    fourier_thetaPairApertureSchwartz_re, fourier_thetaPairApertureSchwartz_re]
  exact twoAtom_apertureSpectrum_pos ha0 ha (-Real.pi * ξ)

private theorem literal_two_atom_jet (s : ℝ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => twoAtomThetaSource (s / 2 + t) *
      twoAtomThetaSource (s / 2 - t)) 0 =
    iteratedDeriv k (fun t : ℝ => thetaCuspSourceTerm (s / 2 + t) 1 * thetaCuspSourceTerm (s / 2 - t) 1) 0 +
    iteratedDeriv k (fun t : ℝ => thetaCuspSourceTerm (s / 2 + t) 1 * thetaCuspSourceTerm (s / 2 - t) 2) 0 +
    iteratedDeriv k (fun t : ℝ => thetaCuspSourceTerm (s / 2 + t) 2 * thetaCuspSourceTerm (s / 2 - t) 1) 0 +
    iteratedDeriv k (fun t : ℝ => thetaCuspSourceTerm (s / 2 + t) 2 * thetaCuspSourceTerm (s / 2 - t) 2) 0 := by
  let f (n m : ℕ) : ℝ → ℝ := fun t =>
    thetaCuspSourceTerm (s / 2 + t) n * thetaCuspSourceTerm (s / 2 - t) m
  have hc (n m : ℕ) : ContDiff ℝ k (f n m) := by
    unfold f thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have he : (fun t : ℝ => twoAtomThetaSource (s / 2 + t) *
      twoAtomThetaSource (s / 2 - t)) = f 1 1 + f 1 2 + f 2 1 + f 2 2 := by
    funext t
    dsimp only [twoAtomThetaSource, f, Pi.add_apply]
    ring
  rw [he]
  exact iteratedDeriv_four_add (hc 1 1) (hc 1 2) (hc 2 1) (hc 2 2) 0

/-- Every two-atom signed jet equals its literal aperture-weighted source integral. -/
theorem twoAtomApertureSchwartz_signedJet {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    ((-I) ^ k * iteratedDeriv k (twoAtomApertureSchwartz a ha0 ha1) 0).re =
      ∫ s in Ioi (0 : ℝ), s * Real.sinh (a * s) * ((-I) ^ k).re *
        iteratedDeriv k (fun t : ℝ =>
          twoAtomThetaSource (s / 2 + t) * twoAtomThetaSource (s / 2 - t)) 0 := by
  let f11 := thetaPairApertureSchwartz 1 1 (by decide) (by decide) a ha0 ha1
  let f12 := thetaPairApertureSchwartz 1 2 (by decide) (by decide) a ha0 ha1
  let f21 := thetaPairApertureSchwartz 2 1 (by decide) (by decide) a ha0 ha1
  let f22 := thetaPairApertureSchwartz 2 2 (by decide) (by decide) a ha0 ha1
  have hj : iteratedDeriv k (twoAtomApertureSchwartz a ha0 ha1) 0 =
      iteratedDeriv k f11 0 + iteratedDeriv k f12 0 +
      iteratedDeriv k f21 0 + iteratedDeriv k f22 0 := by
    change iteratedDeriv k (fun t : ℝ => f11 t + f12 t + f21 t + f22 t) 0 = _
    exact iteratedDeriv_four_add (f11.smooth k) (f12.smooth k)
      (f21.smooth k) (f22.smooth k) 0
  rw [hj]
  simp only [mul_add, Complex.add_re]
  rw [thetaPairApertureSchwartz_signedJet, thetaPairApertureSchwartz_signedJet,
    thetaPairApertureSchwartz_signedJet, thetaPairApertureSchwartz_signedJet]
  have h11 := integrableOn_signed_thetaPairJet (by decide : 0 < 1) (by decide : 0 < 1) ha0 ha1 k
  have h12 := integrableOn_signed_thetaPairJet (by decide : 0 < 1) (by decide : 0 < 2) ha0 ha1 k
  have h21 := integrableOn_signed_thetaPairJet (by decide : 0 < 2) (by decide : 0 < 1) ha0 ha1 k
  have h22 := integrableOn_signed_thetaPairJet (by decide : 0 < 2) (by decide : 0 < 2) ha0 ha1 k
  have h12sum := integral_add h11 h12
  have h123sum := integral_add (h11.add h12) h21
  have h1234sum := integral_add ((h11.add h12).add h21) h22
  simp only [Pi.add_apply] at h12sum h123sum h1234sum
  rw [← h12sum, ← h123sum, ← h1234sum]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp only
  rw [literal_two_atom_jet]
  ring

/-- The literal aperture-weighted signed source jet at one order. -/
def twoAtomApertureSignedJet (a : ℝ) (k : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s * Real.sinh (a * s) * ((-I) ^ k).re *
    iteratedDeriv k (fun t : ℝ =>
      twoAtomThetaSource (s / 2 + t) * twoAtomThetaSource (s / 2 - t)) 0

/-- The literal signed section of the two-atom source with its exact aperture weight. -/
def twoAtomApertureMatrix (a : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => twoAtomApertureSignedJet a ((i : ℕ) + (j : ℕ))

/-- All ranks of the literal two-atom aperture section are positive definite. -/
theorem twoAtomApertureMatrix_posDef {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (N : ℕ) :
    (twoAtomApertureMatrix a N).PosDef := by
  have ha1 : a ≤ 1 := by linarith only [ha]
  have hp := signedSchwartzJet_hankel_posDef (twoAtomApertureSchwartz a ha0.le ha1)
    (fourier_twoAtomApertureSchwartz_re_pos ha0 ha) N
  have he : twoAtomApertureMatrix a N = _root_.HTGeometry.momentHankelMatrix
      (fun k => ((-I) ^ k * iteratedDeriv k (twoAtomApertureSchwartz a ha0.le ha1) 0).re) N := by
    ext i j
    exact (twoAtomApertureSchwartz_signedJet ha0.le ha1 ((i : ℕ) + (j : ℕ))).symm
  rw [he]
  exact hp

/-- Every principal determinant of the literal two-atom hierarchy is positive. -/
theorem twoAtomApertureMatrix_det_pos {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (N : ℕ) :
    0 < (twoAtomApertureMatrix a N).det := (twoAtomApertureMatrix_posDef ha0 ha N).det_pos

/-- Every successor Schur coordinate of the exact two-atom hierarchy is strictly positive. -/
theorem twoAtomApertureSuccessorSchur_pos {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (N : ℕ) :
    0 < HTGeometry.finiteHankelSuccessorSchur (twoAtomApertureSignedJet a) N := by
  exact (HTGeometry.finiteHankelMatrix_succ_posDef_iff_schur_pos
    (twoAtomApertureMatrix_posDef ha0 ha N)).mp
      (twoAtomApertureMatrix_posDef ha0 ha (N + 1))

#print axioms twoAtomApertureMatrix_posDef
#print axioms twoAtomApertureMatrix_det_pos
#print axioms twoAtomApertureSuccessorSchur_pos

end
end GaloisForLFunctions.CompletedArithmeticForms
