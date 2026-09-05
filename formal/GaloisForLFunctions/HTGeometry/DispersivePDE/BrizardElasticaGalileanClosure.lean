import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaGalileanOrbit
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaScalingClosure
import Mathlib.Tactic

/-!
# Closed Galilean action on transport-compatible NLS jets

Equation (26) of arXiv:2607.21750 is a symmetry of the NLS equation, not merely an identity between
the paper's displayed fields.  The corpus's basic complex jet records separate time and space
derivatives; separate differentiability alone does not justify differentiation along a moving line.
`TransportCompatibleJet2` supplies exactly that missing analytic certificate.  The resulting
Galilean transform is a genuine certified jet, and it sends every bundled Brizard-NLS solution to
another solution without theorem-side hypotheses.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- A complex jet whose recorded partials obey the chain rule along every affine transport line. -/
structure TransportCompatibleJet2 extends ComplexEvolutionJet2 where
  hasDerivAt_transport : ∀ (c t x : ℝ),
    HasDerivAt (fun s : ℝ => u s (x - c * s))
      (ut t (x - c * t) - (c : ℂ) * ux t (x - c * t)) t

/-- Galilean transformation of a transport-compatible jet, including certified derivatives. -/
noncomputable def galileanJet (D v : ℝ) (J : TransportCompatibleJet2) :
    ComplexEvolutionJet2 where
  u := fun t x =>
    J.u t (x - 2 * D * v * t) * linearPhase (-D * v ^ 2) v t x
  ut := fun t x =>
    (J.ut t (x - 2 * D * v * t) -
        ((2 * D * v : ℝ) : ℂ) * J.ux t (x - 2 * D * v * t)) *
        linearPhase (-D * v ^ 2) v t x +
      J.u t (x - 2 * D * v * t) *
        (linearPhase (-D * v ^ 2) v t x *
          (Complex.I * ((-D * v ^ 2 : ℝ) : ℂ)))
  ux := fun t x =>
    J.ux t (x - 2 * D * v * t) * linearPhase (-D * v ^ 2) v t x +
      J.u t (x - 2 * D * v * t) *
        (linearPhase (-D * v ^ 2) v t x * (Complex.I * (v : ℂ)))
  uxx := fun t x =>
    J.uxx t (x - 2 * D * v * t) * linearPhase (-D * v ^ 2) v t x +
      J.ux t (x - 2 * D * v * t) *
        (linearPhase (-D * v ^ 2) v t x * (Complex.I * (v : ℂ))) +
      (J.ux t (x - 2 * D * v * t) *
          (linearPhase (-D * v ^ 2) v t x * (Complex.I * (v : ℂ))) +
        J.u t (x - 2 * D * v * t) *
          (linearPhase (-D * v ^ 2) v t x * (Complex.I * (v : ℂ)) *
            (Complex.I * (v : ℂ))))
  hasDerivAt_time := by
    intro t x
    have hu := J.hasDerivAt_transport (2 * D * v) t x
    have hp := hasDerivAt_linearPhase_time (-D * v ^ 2) v t x
    exact hu.mul hp
  hasDerivAt_space := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => y - 2 * D * v * t) 1 x := by
      simpa using (hasDerivAt_id x).sub_const (2 * D * v * t)
    have hu := (J.hasDerivAt_space t (x - 2 * D * v * t)).scomp x hinner
    have hp := hasDerivAt_linearPhase_space (-D * v ^ 2) v t x
    simpa only [Function.comp_apply, one_smul] using! hu.mul hp
  hasDerivAt_space_one := by
    intro t x
    have hinner : HasDerivAt (fun y : ℝ => y - 2 * D * v * t) 1 x := by
      simpa using (hasDerivAt_id x).sub_const (2 * D * v * t)
    have hux := (J.hasDerivAt_space_one t (x - 2 * D * v * t)).scomp x hinner
    have hu := (J.hasDerivAt_space t (x - 2 * D * v * t)).scomp x hinner
    have hp := hasDerivAt_linearPhase_space (-D * v ^ 2) v t x
    have hip := hp.mul_const (Complex.I * (v : ℂ))
    simpa only [Function.comp_apply, one_smul] using! (hux.mul hp).add (hu.mul hip)

theorem galileanJet_norm_sq (D v : ℝ) (J : TransportCompatibleJet2) (t x : ℝ) :
    ‖(galileanJet D v J).u t x‖ ^ 2 = ‖J.u t (x - 2 * D * v * t)‖ ^ 2 := by
  simp only [galileanJet, norm_mul, norm_linearPhase, mul_one]

abbrev TransportCompatibleBrizardSolution (D : ℝ) :=
  {J : TransportCompatibleJet2 // SolvesNLS D J.toComplexEvolutionJet2}

/-- Galilean symmetry as an unconditional map from compatible solutions to certified solutions. -/
noncomputable def galileanBrizardSolution (D v : ℝ)
    (S : TransportCompatibleBrizardSolution D) : BrizardSolutionJet D :=
  ⟨galileanJet D v S, by
    intro t x
    have h := S.property t (x - 2 * D * v * t)
    have hnorm := galileanJet_norm_sq D v S.val t x
    simp only [galileanJet]
    rw [show
      ‖S.val.u t (x - 2 * D * v * t) * linearPhase (-D * v ^ 2) v t x‖ ^ 2 =
        ‖S.val.u t (x - 2 * D * v * t)‖ ^ 2 by
          simpa only [galileanJet] using hnorm]
    push_cast at h ⊢
    calc
      _ = linearPhase (-D * v ^ 2) v t x *
          (Complex.I * S.val.ut t (x - 2 * D * v * t) +
            (D : ℂ) * S.val.uxx t (x - 2 * D * v * t) +
            (D : ℂ) / 2 *
              (‖S.val.u t (x - 2 * D * v * t)‖ ^ 2 : ℂ) *
                S.val.u t (x - 2 * D * v * t)) := by
            ring_nf
      _ = 0 := by rw [h, mul_zero]⟩

theorem galileanBrizardSolution_solves (D v : ℝ)
    (S : TransportCompatibleBrizardSolution D) :
    SolvesNLS D (galileanBrizardSolution D v S).val :=
  (galileanBrizardSolution D v S).property

theorem galileanBrizardSolution_field (D v : ℝ)
    (S : TransportCompatibleBrizardSolution D) (t x : ℝ) :
    (galileanBrizardSolution D v S).val.u t x = galileanField D v S.val.u t x := by
  rfl

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
