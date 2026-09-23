import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaGalileanClosure
import Mathlib.Tactic

/-!
# Galilean action on transport-compatible solution space

The certified Galilean transform in `BrizardElasticaGalileanClosure` produced an ordinary jet.
This module proves that affine transport-chain compatibility is itself preserved.  Consequently
paper equation (26) acts repeatedly on the same bundled solution space, rather than leaving its
analytic domain after one boost.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- A Galilean boost preserves the transport-chain certificate. -/
noncomputable def galileanCompatibleJet (D v : ℝ) (J : TransportCompatibleJet2) :
    TransportCompatibleJet2 where
  toComplexEvolutionJet2 := galileanJet D v J
  hasDerivAt_transport := by
    intro c t x
    have hu := J.hasDerivAt_transport (c + 2 * D * v) t x
    have hp := hasDerivAt_linearPhase_time (-D * v ^ (2 : ℕ) - v * c) v t x
    have hprod := hu.mul hp
    apply (hprod.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards with s
      simp only [galileanJet]
      rw [linearPhase_shift]
      congr 2
      ring
    · simp only [galileanJet]
      rw [linearPhase_shift]
      push_cast
      ring_nf

theorem galileanCompatibleJet_field (D v : ℝ) (J : TransportCompatibleJet2) (t x : ℝ) :
    (galileanCompatibleJet D v J).u t x = galileanField D v J.u t x := rfl

/-- Galilean symmetry as an endomorphism of compatible Brizard-NLS solutions. -/
noncomputable def galileanCompatibleBrizardSolution (D v : ℝ)
    (S : TransportCompatibleBrizardSolution D) : TransportCompatibleBrizardSolution D :=
  ⟨galileanCompatibleJet D v S, by
    exact (galileanBrizardSolution D v S).property⟩

theorem galileanCompatibleBrizardSolution_solves (D v : ℝ)
    (S : TransportCompatibleBrizardSolution D) :
    SolvesNLS D (galileanCompatibleBrizardSolution D v S).val.toComplexEvolutionJet2 :=
  (galileanCompatibleBrizardSolution D v S).property

theorem galileanCompatibleBrizardSolution_field (D v : ℝ)
    (S : TransportCompatibleBrizardSolution D) (t x : ℝ) :
    (galileanCompatibleBrizardSolution D v S).val.u t x =
      galileanField D v S.val.u t x := rfl

/-- Repeated certified boosts have the paper's additive field action. -/
theorem galileanCompatibleBrizardSolution_add_field (D v w : ℝ)
    (S : TransportCompatibleBrizardSolution D) (t x : ℝ) :
    (galileanCompatibleBrizardSolution D v
        (galileanCompatibleBrizardSolution D w S)).val.u t x =
      (galileanCompatibleBrizardSolution D (v + w) S).val.u t x := by
  simp only [galileanCompatibleBrizardSolution_field]
  exact galileanField_add D v w S.val.u t x

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
