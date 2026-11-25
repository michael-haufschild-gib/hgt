import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Linarith

/-! # Recovering a unitary eigenphase from one approximating column -/

open ComplexConjugate
open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
noncomputable section

/-- The unit phase of a complex number, with phase one selected at zero. -/
def unitPhase (a : ℂ) := Complex.exp ((a.arg:ℂ)*Complex.I)

theorem norm_unitPhase (a : ℂ) : ‖unitPhase a‖=1 := Complex.norm_exp_ofReal_mul_I _

/-- For unit vectors within the open right-angle chord, replacing the
comparison vector by its normalized component along the eigenline can
only reduce the error. Thus one common operator error gives the sharp
one-coordinate chord on every eigenspace. -/
theorem sharp_line_chord {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (u v : V) (hu : ‖u‖=1) (hv : ‖v‖=1) (z : ℂ) (hz : ‖z‖=1)
    (hnear : ‖z • u-v‖ < Real.sqrt 2) :
    ‖z-unitPhase (inner ℂ u v)‖ ≤ ‖z • u-v‖ := by
  let a := inner ℂ u v
  let q := unitPhase a
  have hq : ‖q‖=1 := norm_unitPhase a
  have hnorm : ‖a‖ ≤ 1 := by simpa only [a,hu,hv,mul_one] using norm_inner_le_norm u v (𝕜:=ℂ)
  have hp : (‖a‖:ℂ)*q=a := Complex.norm_mul_exp_arg_mul_I a
  have hcmp : (conj z*a).re=‖a‖*(conj z*q).re := calc
    (conj z*a).re = (conj z*((‖a‖:ℂ)*q)).re := congrArg (fun b : ℂ => (conj z*b).re) hp.symm
    _ = ((‖a‖:ℂ)*(conj z*q)).re := congrArg Complex.re (by ring)
    _ = _ := by simp only [Complex.re_ofReal_mul]
  have hd : ‖z • u-v‖^2=2-2*(conj z*a).re := by
    rw [norm_sub_sq (𝕜:=ℂ),norm_smul,hz,hu,hv,inner_smul_left]
    change _=2-2*(conj z*inner ℂ u v).re
    ring
  have hs : 0 < (conj z*a).re := by
    have h := (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg 2)).mpr hnear
    rw [hd,Real.sq_sqrt zero_le_two] at h
    linarith only [h]
  have hc : 0 ≤ (conj z*q).re := (pos_of_mul_pos_right (hcmp ▸ hs) (norm_nonneg _)).le
  have hle := mul_le_of_le_one_left hc hnorm
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖z-q‖^2 ≤ ‖z • u-v‖^2
  rw [norm_sub_sq (𝕜:=ℂ),hz,hq,RCLike.inner_apply',hd]
  change (1:ℝ)^2-2*(conj z*q).re+1^2 ≤ 2-2*(conj z*a).re
  linarith only [hle,hcmp]

#print axioms sharp_line_chord
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
