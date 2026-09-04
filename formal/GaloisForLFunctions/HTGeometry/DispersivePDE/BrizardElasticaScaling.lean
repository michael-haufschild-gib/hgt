import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobi
import Mathlib.Tactic

/-!
# NLS scaling and the breather-lattice endpoint in arXiv:2607.21750

The paper identifies the endpoint of its doubly-periodic lattice with a scaled bright soliton.
This module builds the scaling operation at the certified-jet level and applies it to the corpus's
existing focusing NLS solution.  The specialization `a = sqrt 2` is the paper's explicit endpoint.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- NLS scaling `u(t,x) ↦ a u(a²t, ax)`, including certified derivatives. -/
noncomputable def nlsScaleJet (a : ℝ) (J : ComplexEvolutionJet2) : ComplexEvolutionJet2 where
  u := fun t x => (a : ℂ) * J.u (a ^ 2 * t) (a * x)
  ut := fun t x => (a ^ 3 : ℝ) * J.ut (a ^ 2 * t) (a * x)
  ux := fun t x => (a ^ 2 : ℝ) * J.ux (a ^ 2 * t) (a * x)
  uxx := fun t x => (a ^ 3 : ℝ) * J.uxx (a ^ 2 * t) (a * x)
  hasDerivAt_time := by
    intro t x
    have hinner : HasDerivAt (fun s : ℝ => a ^ 2 * s) (a ^ 2) t := by
      simpa using (hasDerivAt_id t).const_mul (a ^ 2)
    have houter : HasDerivAt (fun s : ℝ => J.u s (a * x))
        (J.ut (a ^ 2 * t) (a * x)) (a ^ 2 * t) :=
      J.hasDerivAt_time (a ^ 2 * t) (a * x)
    have h := houter.scomp t hinner
    have hscaled := h.const_mul (a : ℂ)
    apply hscaled.congr_deriv
    simp only [Complex.real_smul]
    push_cast
    ring
  hasDerivAt_space := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => a * y) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have houter : HasDerivAt (J.u (a ^ 2 * t))
        (J.ux (a ^ 2 * t) (a * x)) (a * x) :=
      J.hasDerivAt_space (a ^ 2 * t) (a * x)
    have h := houter.scomp x hinner
    have hscaled := h.const_mul (a : ℂ)
    apply hscaled.congr_deriv
    simp only [Complex.real_smul]
    push_cast
    ring
  hasDerivAt_space_one := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => a * y) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have houter : HasDerivAt (J.ux (a ^ 2 * t))
        (J.uxx (a ^ 2 * t) (a * x)) (a * x) :=
      J.hasDerivAt_space_one (a ^ 2 * t) (a * x)
    have h := houter.scomp x hinner
    have hscaled := h.const_mul (a ^ 2 : ℂ)
    apply (hscaled.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards with y
      simp only [Function.comp_apply]
      push_cast
      rfl
    · simp only [Complex.real_smul]
      push_cast
      ring

/-- Every real scaling of the corpus bright soliton remains an exact focusing-NLS solution. -/
theorem nlsScaleJet_bright_solves (a : ℝ) :
    SolvesFocusingNLS (nlsScaleJet a nlsBrightSolitonJet) := by
  intro t x
  have h := nlsBrightSoliton_solves (a ^ 2 * t) (a * x)
  simp only [nlsScaleJet]
  have hnorm :
      ‖(a : ℂ) * nlsBrightSolitonJet.u (a ^ 2 * t) (a * x)‖ ^ 2 =
        a ^ 2 * ‖nlsBrightSolitonJet.u (a ^ 2 * t) (a * x)‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
  rw [hnorm]
  push_cast at h ⊢
  calc
    _ = (a : ℂ) ^ 3 *
        (Complex.I * nlsBrightSolitonJet.ut (a ^ 2 * t) (a * x) +
          nlsBrightSolitonJet.uxx (a ^ 2 * t) (a * x) +
          (2 : ℂ) * (‖nlsBrightSolitonJet.u (a ^ 2 * t) (a * x)‖ ^ 2 : ℂ) *
            nlsBrightSolitonJet.u (a ^ 2 * t) (a * x)) := by ring
    _ = 0 := by rw [h, mul_zero]

/-- Paper's `sqrt 2 sech(sqrt 2 x) exp(2it)` breather-lattice endpoint. -/
noncomputable def breatherLatticeEndpoint : ComplexEvolutionJet2 :=
  nlsScaleJet (Real.sqrt 2) nlsBrightSolitonJet

theorem breatherLatticeEndpoint_solves : SolvesFocusingNLS breatherLatticeEndpoint := by
  exact nlsScaleJet_bright_solves (Real.sqrt 2)

/-- Exact identification with the paper's displayed scaling of the corpus bright soliton. -/
theorem breatherLatticeEndpoint_eq (t x : ℝ) :
    breatherLatticeEndpoint.u t x =
      (Real.sqrt 2 : ℂ) * nlsBrightSoliton (2 * t) (Real.sqrt 2 * x) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  simp only [breatherLatticeEndpoint, nlsScaleJet, nlsBrightSolitonJet]
  rw [hs]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
