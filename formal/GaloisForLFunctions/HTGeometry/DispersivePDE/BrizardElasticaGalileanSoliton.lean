import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaGalileanAction
import Mathlib.Tactic

/-!
# Localized solitons inhabit the compatible Galilean solution space

The paper's complete `sech` family obeys the affine transport chain rule required by the certified
Galilean action.  Thus equation (26) acts internally on localized Brizard-NLS solutions, and the
stationary optical soliton is a genuine orbit representative rather than only a field-level one.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Every explicit moving `sech` soliton has the transport compatibility needed by repeated boosts. -/
noncomputable def envelopeSolitonCompatibleJet (D k v : ℝ) : TransportCompatibleJet2 where
  toComplexEvolutionJet2 := envelopeSolitonJet D k v
  hasDerivAt_transport := by
    intro c t x
    let ω : ℝ := D * (k ^ (2 : ℕ) - v ^ (2 : ℕ))
    have hcoord : HasDerivAt
        (fun s : ℝ => envelopeCoordinate D k v s (x - c * s))
        (-k * (2 * D * v + c)) t := by
      have h := (((hasDerivAt_const t x).sub
        ((hasDerivAt_id t).const_mul c)).sub
          ((hasDerivAt_id t).const_mul (2 * D * v))).const_mul k
      apply h.congr_deriv
      ring
    have henvReal : HasDerivAt
        (fun s : ℝ => envelope D k v s (x - c * s))
        (envelopeT D k v t (x - c * t) -
          c * envelopeX D k v t (x - c * t)) t := by
      have h := ((hasDerivAt_solitonA _).comp t hcoord).const_mul (2 * k)
      apply (h.congr_deriv ?_).congr_of_eventuallyEq
      · filter_upwards with s
        rfl
      · simp only [envelopeT, envelopeX]
        ring
    have hphase : HasDerivAt
        (fun s : ℝ => linearPhase ω v s (x - c * s))
        (linearPhase ω v t (x - c * t) *
          (Complex.I * ((ω - v * c : ℝ) : ℂ))) t := by
      have h := hasDerivAt_linearPhase_time (ω - v * c) v t x
      apply (h.congr_deriv ?_).congr_of_eventuallyEq
      · filter_upwards with s
        exact linearPhase_shift ω v c s x
      · rw [linearPhase_shift]
    have hprod := henvReal.ofReal_comp.mul hphase
    apply (hprod.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards with s
      rfl
    · simp only [envelopeSolitonJet]
      dsimp only [ω]
      push_cast
      ring

/-- Bundled localized solution in the domain of the certified Galilean action. -/
noncomputable def envelopeSolitonCompatibleSolution (D k v : ℝ) :
    TransportCompatibleBrizardSolution D :=
  ⟨envelopeSolitonCompatibleJet D k v, envelopeSoliton_solves D k v⟩

theorem envelopeSolitonCompatibleSolution_solves (D k v : ℝ) :
    SolvesNLS D (envelopeSolitonCompatibleSolution D k v).val.toComplexEvolutionJet2 :=
  (envelopeSolitonCompatibleSolution D k v).property

/-- A certified boost translates velocity throughout the localized soliton family. -/
theorem galileanCompatible_envelopeSoliton_field (D k v w t x : ℝ) :
    (galileanCompatibleBrizardSolution D w
        (envelopeSolitonCompatibleSolution D k v)).val.u t x =
      envelopeSoliton D k (w + v) t x := by
  rw [galileanCompatibleBrizardSolution_field]
  exact galileanField_envelopeSoliton D k w v t x

theorem galileanCompatible_envelopeSoliton_solves (D k v w : ℝ) :
    SolvesNLS D
      (galileanCompatibleBrizardSolution D w
        (envelopeSolitonCompatibleSolution D k v)).val.toComplexEvolutionJet2 :=
  (galileanCompatibleBrizardSolution D w
    (envelopeSolitonCompatibleSolution D k v)).property

/-- The stationary optical soliton generates every certified moving `sech` field. -/
theorem galileanCompatible_opticalSoliton_field (D k v t x : ℝ) :
    (galileanCompatibleBrizardSolution D v
        (envelopeSolitonCompatibleSolution D k 0)).val.u t x =
      envelopeSoliton D k v t x := by
  simpa using galileanCompatible_envelopeSoliton_field D k 0 v t x

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
