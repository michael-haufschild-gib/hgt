import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.QuadraticTorusProbePhases
import GaloisForLFunctions.RepresentationLifting.Actions.QuadraticTorusAdjoint

/-!
# Transverse Weyl determinants on the zero-coordinate probe

At the real nonsplit torus, conjugation on the two real transverse
coordinates is complex multiplication by the phase of the negative
reflection sector. The Weyl determinant of a relative element gives the
projective overlap loss on every probe, including each actual zero coordinate.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open RepresentationLifting ArithmeticCastelnuovoSeveri Zeta23
open scoped ComplexConjugate
private theorem torusNorm_eq (z : ℂˣ) :
    quadraticTorusNorm (-1) (z:ℂ).re (z:ℂ).im = Complex.normSq (z:ℂ) := by
  rw [quadraticTorusNorm,Complex.normSq_apply]; ring

/-- Complex multiplication by the probe phase has the coefficients of the nonsplit transverse action. -/
theorem transversePhase_coefficients (z : ℂˣ) :
    quadraticAdjointCoefficients (-1) (z:ℂ).re (z:ℂ).im =
      (((conjugationPhase z):ℂ).re, ((conjugationPhase z):ℂ).im) := by
  change _ = ((conj (z:ℂ)/(z:ℂ)).re,(conj (z:ℂ)/(z:ℂ)).im)
  rw [quadraticAdjointCoefficients,torusNorm_eq,Complex.div_re,Complex.div_im]
  simp only [Complex.conj_re,Complex.conj_im]
  apply Prod.ext <;> dsimp <;> ring

/-- The entire real matrix on the transverse plane is determined by the phase on ZeroSpace. -/
theorem transversePhase_matrix (z : ℂˣ) :
    quadraticAdjointMatrix (-1) (z:ℂ).re (z:ℂ).im =
      !![((conjugationPhase z):ℂ).re,-((conjugationPhase z):ℂ).im;
         ((conjugationPhase z):ℂ).im,((conjugationPhase z):ℂ).re] := by
  rw [quadraticAdjointMatrix,transversePhase_coefficients]
  simp

/-- The determinant of one minus the real transverse action. -/
def probeWeyl (z : ℂˣ) : ℝ :=
  (1 - quadraticAdjointMatrix (-1) (z:ℂ).re (z:ℂ).im).det

/-- This determinant equals the squared phase chord. -/
theorem probeWeyl_eq_chord (z : ℂˣ) : probeWeyl z = ‖(conjugationPhase z:ℂ)-1‖^2 := by
  rw [probeWeyl,transversePhase_matrix,Matrix.det_fin_two,Complex.sq_norm,Complex.normSq_apply]
  simp [Matrix.sub_apply,Complex.sub_re,Complex.sub_im]
  ring

/-- In normalized coordinates the Weyl determinant is four times the imaginary-coordinate mass. -/
theorem probeWeyl_eq_imaginary_mass (z : ℂˣ) :
    probeWeyl z = 4*(z:ℂ).im^2 / Complex.normSq (z:ℂ) := by
  have hn : quadraticTorusNorm (-1) (z:ℂ).re (z:ℂ).im ≠ 0 := by
    rw [torusNorm_eq]; exact (Complex.normSq_pos.mpr z.ne_zero).ne'
  rw [probeWeyl,quadraticAdjoint_weyl _ _ _ hn,torusNorm_eq]
  ring

/-- The sharp maximum is attained exactly by imaginary representatives. -/
theorem probeWeyl_eq_four_iff (z : ℂˣ) : probeWeyl z = 4 ↔ (z:ℂ).re = 0 := by
  rw [probeWeyl_eq_imaginary_mass,div_eq_iff ((Complex.normSq_pos.mpr z.ne_zero).ne'),Complex.normSq_apply]
  constructor
  · intro h
    have hsq : (z:ℂ).re^2 = 0 := by linear_combination -h / 4
    exact sq_eq_zero_iff.mp hsq
  · intro h; rw [h]; ring

private theorem relative_phase_chord (z w : ℂˣ) :
    ‖(conjugationPhase (z/w):ℂ) - 1‖ = ‖(conjugationPhase z:ℂ)-(conjugationPhase w:ℂ)‖ := by
  have hw : (conjugationPhase w:ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [map_div,Circle.coe_div,div_sub_one hw,norm_div,Circle.norm_coe,div_one]

/-- The same relative Weyl determinant controls projective loss for every zero-space vector. -/
theorem torusProbe_loss_eq_weyl (z w : ℂˣ) (x : ZeroSpace) :
    ‖x‖^4 - ‖inner ℂ (torusProbeAction z x) (torusProbeAction w x)‖^2 =
      positiveMass x * negativeMass x * probeWeyl (z/w) := by
  rw [probeWeyl_eq_chord,relative_phase_chord]
  exact phaseRotate_projective_loss _ _ _

/-- A single off-line zero reads exactly one quarter of the transverse Weyl determinant. -/
theorem zeroBasis_weyl_loss (ρ : zetaZeroConfig.carrier) (z w : ℂˣ) :
    1 - ‖inner ℂ (torusProbeAction z (zeroBasis ρ)) (torusProbeAction w (zeroBasis ρ))‖^2 =
      if (ρ:ℂ).re = 1/2 then 0 else probeWeyl (z/w)/4 := by
  have quarter (u : ℝ) : u/4 = (1/4)*u := by ring
  rw [probeWeyl_eq_chord,relative_phase_chord,quarter]
  exact zeroBasis_projective_loss ρ (conjugationPhase z) (conjugationPhase w)

/-- Two translates of one zero coordinate are orthogonal exactly for an off-line zero and a
purely imaginary relative representative. -/
theorem zeroBasis_torus_inner_zero_iff (ρ : zetaZeroConfig.carrier) (z w : ℂˣ) :
    inner ℂ (torusProbeAction z (zeroBasis ρ)) (torusProbeAction w (zeroBasis ρ)) = 0 ↔
      (ρ:ℂ).re ≠ 1/2 ∧ ((z/w:ℂˣ):ℂ).re = 0 := by
  have h := zeroBasis_weyl_loss ρ z w
  by_cases hρ : (ρ:ℂ).re = 1/2
  · rw [if_pos hρ] at h
    constructor
    · intro he; rw [he,norm_zero,zero_pow two_ne_zero,sub_zero] at h; exact (one_ne_zero h).elim
    · exact fun H => (H.1 hρ).elim
  · rw [if_neg hρ] at h
    constructor
    · intro he; rw [he,norm_zero,zero_pow two_ne_zero,sub_zero] at h
      exact ⟨hρ,(probeWeyl_eq_four_iff _).1 (by linarith only [h])⟩
    · intro H
      rw [(probeWeyl_eq_four_iff _).2 H.2] at h
      apply norm_eq_zero.mp
      apply sq_eq_zero_iff.mp
      linarith only [h]

#print axioms transversePhase_coefficients
#print axioms transversePhase_matrix
#print axioms probeWeyl_eq_chord
#print axioms probeWeyl_eq_imaginary_mass
#print axioms probeWeyl_eq_four_iff
#print axioms torusProbe_loss_eq_weyl
#print axioms zeroBasis_weyl_loss
#print axioms zeroBasis_torus_inner_zero_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
