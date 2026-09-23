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
  u := fun t x => (a : ℂ) * J.u (a ^ (2 : ℕ) * t) (a * x)
  ut := fun t x => (a ^ (3 : ℕ) : ℝ) * J.ut (a ^ (2 : ℕ) * t) (a * x)
  ux := fun t x => (a ^ (2 : ℕ) : ℝ) * J.ux (a ^ (2 : ℕ) * t) (a * x)
  uxx := fun t x => (a ^ (3 : ℕ) : ℝ) * J.uxx (a ^ (2 : ℕ) * t) (a * x)
  hasDerivAt_time := by
    intro t x
    have hinner : HasDerivAt (fun s : ℝ => a ^ (2 : ℕ) * s) (a ^ (2 : ℕ)) t := by
      simpa using (hasDerivAt_id t).const_mul (a ^ (2 : ℕ))
    have houter : HasDerivAt (fun s : ℝ => J.u s (a * x))
        (J.ut (a ^ (2 : ℕ) * t) (a * x)) (a ^ (2 : ℕ) * t) :=
      J.hasDerivAt_time (a ^ (2 : ℕ) * t) (a * x)
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
    have houter : HasDerivAt (J.u (a ^ (2 : ℕ) * t))
        (J.ux (a ^ (2 : ℕ) * t) (a * x)) (a * x) :=
      J.hasDerivAt_space (a ^ (2 : ℕ) * t) (a * x)
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
    have houter : HasDerivAt (J.ux (a ^ (2 : ℕ) * t))
        (J.uxx (a ^ (2 : ℕ) * t) (a * x)) (a * x) :=
      J.hasDerivAt_space_one (a ^ (2 : ℕ) * t) (a * x)
    have h := houter.scomp x hinner
    have hscaled := h.const_mul (a ^ (2 : ℕ) : ℂ)
    apply (hscaled.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards with y
      simp only [Function.comp_apply]
      push_cast
      rfl
    · simp only [Complex.real_smul]
      push_cast
      ring

/-- The scaling transform multiplies density by `a²`, including at the degenerate scale `a = 0`. -/
theorem norm_nlsScaleJet_sq (a : ℝ) (J : ComplexEvolutionJet2) (t x : ℝ) :
    ‖(nlsScaleJet a J).u t x‖ ^ (2 : ℕ) =
      a ^ (2 : ℕ) * ‖J.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) := by
  simp only [nlsScaleJet]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- Every real scaling of the corpus bright soliton remains an exact focusing-NLS solution. -/
theorem nlsScaleJet_bright_solves (a : ℝ) :
    SolvesFocusingNLS (nlsScaleJet a nlsBrightSolitonJet) := by
  intro t x
  have h := nlsBrightSoliton_solves (a ^ (2 : ℕ) * t) (a * x)
  simp only [nlsScaleJet]
  have hnorm :
      ‖(a : ℂ) * nlsBrightSolitonJet.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ‖nlsBrightSolitonJet.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
  rw [hnorm]
  push_cast at h ⊢
  calc
    _ = (a : ℂ) ^ (3 : ℕ) *
        (Complex.I * nlsBrightSolitonJet.ut (a ^ (2 : ℕ) * t) (a * x) +
          nlsBrightSolitonJet.uxx (a ^ (2 : ℕ) * t) (a * x) +
          (2 : ℂ) * (‖nlsBrightSolitonJet.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) : ℂ) *
            nlsBrightSolitonJet.u (a ^ (2 : ℕ) * t) (a * x)) := by ring
    _ = 0 := by rw [h, mul_zero]

/-- The paper's scaling symmetry applied to the corpus focusing plane wave. -/
theorem nlsScaleJet_plane_solves (a : ℝ) :
    SolvesFocusingNLS (nlsScaleJet a nlsPlaneWaveJet) := by
  intro t x
  have h := nlsPlaneWave_solves (a ^ (2 : ℕ) * t) (a * x)
  have hnorm :
      ‖(a : ℂ) * nlsPlaneWaveJet.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ‖nlsPlaneWaveJet.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) := by
    simpa only [nlsScaleJet] using norm_nlsScaleJet_sq a nlsPlaneWaveJet t x
  simp only [nlsScaleJet]
  rw [hnorm]
  push_cast at h ⊢
  calc
    _ = (a : ℂ) ^ (3 : ℕ) *
        (Complex.I * nlsPlaneWaveJet.ut (a ^ (2 : ℕ) * t) (a * x) +
          nlsPlaneWaveJet.uxx (a ^ (2 : ℕ) * t) (a * x) +
          (2 : ℂ) * (‖nlsPlaneWaveJet.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) : ℂ) *
            nlsPlaneWaveJet.u (a ^ (2 : ℕ) * t) (a * x)) := by ring
    _ = 0 := by rw [h, mul_zero]

/-- Cubic NLS dilation also preserves the corpus defocusing dark-soliton equation. -/
theorem nlsScaleJet_dark_solves (a : ℝ) :
    SolvesDefocusingNLS (nlsScaleJet a nlsDarkSolitonJet) := by
  intro t x
  have h := nlsDarkSoliton_solves (a ^ (2 : ℕ) * t) (a * x)
  have hnorm :
      ‖(a : ℂ) * nlsDarkSolitonJet.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ‖nlsDarkSolitonJet.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) := by
    simpa only [nlsScaleJet] using norm_nlsScaleJet_sq a nlsDarkSolitonJet t x
  simp only [nlsScaleJet]
  rw [hnorm]
  push_cast at h ⊢
  calc
    _ = (a : ℂ) ^ (3 : ℕ) *
        (Complex.I * nlsDarkSolitonJet.ut (a ^ (2 : ℕ) * t) (a * x) +
          nlsDarkSolitonJet.uxx (a ^ (2 : ℕ) * t) (a * x) -
          (2 : ℂ) * (‖nlsDarkSolitonJet.u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) : ℂ) *
            nlsDarkSolitonJet.u (a ^ (2 : ℕ) * t) (a * x)) := by ring
    _ = 0 := by rw [h, mul_zero]

/-- Scaling applied to every paper plane wave, for arbitrary dispersion `D`. -/
theorem nlsScaleJet_brizardPlane_solves (a D b k : ℝ) :
    SolvesNLS D (nlsScaleJet a (planeWaveJet D b k)) := by
  intro t x
  have h := planeWave_solves D b k (a ^ (2 : ℕ) * t) (a * x)
  have hnorm :
      ‖(a : ℂ) * (planeWaveJet D b k).u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ‖(planeWaveJet D b k).u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) := by
    simpa only [nlsScaleJet] using norm_nlsScaleJet_sq a (planeWaveJet D b k) t x
  simp only [nlsScaleJet]
  rw [hnorm]
  push_cast at h ⊢
  calc
    _ = (a : ℂ) ^ (3 : ℕ) *
        (Complex.I * (planeWaveJet D b k).ut (a ^ (2 : ℕ) * t) (a * x) +
          (D : ℂ) * (planeWaveJet D b k).uxx (a ^ (2 : ℕ) * t) (a * x) +
          (D : ℂ) / 2 *
            (‖(planeWaveJet D b k).u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) : ℂ) *
            (planeWaveJet D b k).u (a ^ (2 : ℕ) * t) (a * x)) := by ring
    _ = 0 := by rw [h, mul_zero]

/-- Scaling applied to the paper's complete Galilean bright-soliton family. -/
theorem nlsScaleJet_envelope_solves (a D k v : ℝ) :
    SolvesNLS D (nlsScaleJet a (envelopeSolitonJet D k v)) := by
  intro t x
  have h := envelopeSoliton_solves D k v (a ^ (2 : ℕ) * t) (a * x)
  have hnorm :
      ‖(a : ℂ) * (envelopeSolitonJet D k v).u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ‖(envelopeSolitonJet D k v).u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) := by
    simpa only [nlsScaleJet] using norm_nlsScaleJet_sq a (envelopeSolitonJet D k v) t x
  simp only [nlsScaleJet]
  rw [hnorm]
  push_cast at h ⊢
  calc
    _ = (a : ℂ) ^ (3 : ℕ) *
        (Complex.I * (envelopeSolitonJet D k v).ut (a ^ (2 : ℕ) * t) (a * x) +
          (D : ℂ) * (envelopeSolitonJet D k v).uxx (a ^ (2 : ℕ) * t) (a * x) +
          (D : ℂ) / 2 *
            (‖(envelopeSolitonJet D k v).u (a ^ (2 : ℕ) * t) (a * x)‖ ^ (2 : ℕ) : ℂ) *
            (envelopeSolitonJet D k v).u (a ^ (2 : ℕ) * t) (a * x)) := by ring
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
  have hs : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by positivity)
  simp only [breatherLatticeEndpoint, nlsScaleJet, nlsBrightSolitonJet]
  rw [hs]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
