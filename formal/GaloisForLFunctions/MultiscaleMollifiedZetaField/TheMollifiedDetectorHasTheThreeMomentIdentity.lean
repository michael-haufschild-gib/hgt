import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDetectorEnergyComesFromThreeMoments
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The actual mollified detector and its three coefficient moments

The product jets of zeta and the finite mollifier identify the first two
moment derivatives. The coefficient correction is the finite polynomial
with coefficients `-λ log(n) w(n)`.
-/

open Complex Filter MeasureTheory Metric Set Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Zeta times the literal finite mollifier, as a function of the complex argument. -/
def mollifiedZetaField (N : ℕ) (w : ℕ → ℝ) (s : ℂ) : ℂ :=
  riemannZeta s * edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N) s

/-- Complex derivatives of the mollified zeta field. -/
def mollifiedZetaFieldJet (N : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℂ → ℂ :=
  iteratedDeriv n (mollifiedZetaField N w)

theorem analyticAt_mollifiedZetaFieldJet (N : ℕ) (w : ℕ → ℝ) (n : ℕ)
    {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (mollifiedZetaFieldJet N w n) s := by
  have hf : DifferentiableOn ℂ (mollifiedZetaField N w) ({1}ᶜ : Set ℂ) := by
    intro v hv
    exact ((differentiableAt_riemannZeta hv).mul
      (differentiable_edPoly (fun n => (w n : ℂ))
        (fun n hn => (Finset.mem_Icc.mp hn).1) v)).differentiableWithinAt
  induction n with
  | zero => exact hf.analyticOnNhd isOpen_compl_singleton s hs
  | succ n ih => simpa only [mollifiedZetaFieldJet, iteratedDeriv_succ] using ih.deriv

theorem hasDerivAt_mollifiedZetaFieldJet (N : ℕ) (w : ℕ → ℝ) (n : ℕ)
    {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (mollifiedZetaFieldJet N w n) (mollifiedZetaFieldJet N w (n + 1) s) s := by
  simpa only [mollifiedZetaFieldJet, iteratedDeriv_succ] using
    (analyticAt_mollifiedZetaFieldJet N w n hs).differentiableAt.hasDerivAt

private theorem iteratedDeriv_commutes_conj {f : ℂ → ℂ}
    (hf : ∀ s, f (conj s) = conj (f s)) (n : ℕ) (s : ℂ) :
    iteratedDeriv n f (conj s) = conj (iteratedDeriv n f s) := by
  induction n generalizing s with
  | zero => exact hf s
  | succ n ih =>
    have he : (conj ∘ iteratedDeriv n f ∘ conj) = iteratedDeriv n f := by
      funext z
      simp only [Function.comp_apply, ih, map_star, star_star]
    have hh := congrArg (fun F : ℂ → ℂ => deriv F (conj s)) he
    rw [deriv_conj_conj] at hh
    simpa only [iteratedDeriv_succ, Function.comp_apply, map_star, star_star] using hh.symm

/-- Real coefficients preserve reflection for every field derivative. -/
theorem mollifiedZetaFieldJet_conj (N : ℕ) (w : ℕ → ℝ) (n : ℕ) (s : ℂ) :
    mollifiedZetaFieldJet N w n (conj s) = conj (mollifiedZetaFieldJet N w n s) := by
  apply iteratedDeriv_commutes_conj
  intro v
  unfold mollifiedZetaField
  rw [riemannZeta_conj, edPoly_conj (fun k => (w k : ℂ))
    (fun k hk => (Finset.mem_Icc.mp hk).1) (fun k _ => Complex.conj_ofReal (w k)), map_mul]

private theorem field_argument_ne_one {z : ℂ} (hz : ‖z‖ < 1 / 4) (t : ℝ) :
    (1 / 2 : ℂ) - z + (t : ℂ) * I ≠ 1 := by
  have hr := (Complex.abs_re_le_norm z).trans_lt hz
  intro he
  have hre := congrArg Complex.re he
  norm_num at hre
  linarith only [hre, (abs_lt.mp hr).1]

private theorem hasDerivAt_displacement_field_jet (N : ℕ) (w : ℕ → ℝ) (n : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1 / 4) (t : ℝ) :
    HasDerivAt (fun v : ℂ => mollifiedZetaFieldJet N w n ((1 / 2 : ℂ) - v + (t : ℂ) * I))
      (-mollifiedZetaFieldJet N w (n + 1) ((1 / 2 : ℂ) - z + (t : ℂ) * I)) z := by
  have hp : HasDerivAt (fun v : ℂ => (1 / 2 : ℂ) - v + (t : ℂ) * I) (-1) z := by
    simpa using ((hasDerivAt_id z).const_sub (1 / 2 : ℂ)).add_const ((t : ℂ) * I)
  exact ((hasDerivAt_mollifiedZetaFieldJet N w n (field_argument_ne_one hz t)).comp z hp).congr_deriv (by ring)

end GaloisForLFunctions.MultiscaleMollifiedZetaField
