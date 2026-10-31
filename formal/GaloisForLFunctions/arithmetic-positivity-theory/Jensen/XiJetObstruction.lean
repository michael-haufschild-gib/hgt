import GaloisForLFunctions.RHTower.OrderOneEvenLaguerrePolya
import GaloisForLFunctions.RHTower.XiRealRootedPolynomialPreimage
import GaloisForLFunctions.RHTower.XiShiftedIntervalLaguerrePolyaRH
import GaloisForLFunctions.RHTower.XiJensenPolynomialRiemannHypothesis

/-!
# Finite differential-jet obstructions to RH

RH forces every Jensen section of every real translate of
`(1-c₁D)⋯(1-cₙD)Dᵏ Ξ` to split over the reals. The witness is a finite polynomial
formed from actual Xi jets. Closure and reality are proved, not witness premises.
-/

open Polynomial Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- Real first-order differential factors preserve conjugation symmetry. -/
theorem firstOrderChain_schwarzReal {F : ℂ → ℂ}
    (hs : ∀ z, F (conj z) = conj (F z)) (cs : List ℝ) :
    ∀ z, KernelStrip.firstOrderChain cs F (conj z) =
      conj (KernelStrip.firstOrderChain cs F z) := by
  induction cs with
  | nil => exact hs
  | cons c cs ih =>
    intro z
    have hd := iteratedDeriv_conj_of_schwarzReal ih 1 z
    simp only [iteratedDeriv_eq_iterate, Function.iterate_one] at hd
    simp only [KernelStrip.firstOrderChain, ih z, hd,
      map_sub, map_mul, Complex.conj_ofReal]

/-- A real translate of a real-rooted constant-coefficient differential transform of Xi. -/
def xiDifferentialJetSource (cs : List ℝ) (k : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  KernelStrip.firstOrderChain cs (deriv^[k] XiC) ((a : ℂ) + z)

/-- A finite Jensen polynomial formed from the transformed Xi jets. -/
def xiDifferentialJensenPolynomial (cs : List ℝ) (k : ℕ) (a : ℝ) (d : ℕ) : ℝ[X] :=
  jensenPoly (realTaylorCoeff (xiDifferentialJetSource cs k a)) d

theorem xiDifferentialJetSource_schwarzReal (cs : List ℝ) (k : ℕ) (a : ℝ) :
    ∀ z, xiDifferentialJetSource cs k a (conj z) =
      conj (xiDifferentialJetSource cs k a z) := by
  have hder : ∀ z, (deriv^[k] XiC) (conj z) = conj ((deriv^[k] XiC) z) := by
    intro z
    simpa only [iteratedDeriv_eq_iterate] using
      iteratedDeriv_conj_of_schwarzReal (fun w => XiC_conj w) k z
  intro z
  simpa only [xiDifferentialJetSource, map_add, Complex.conj_ofReal] using
    firstOrderChain_schwarzReal hder cs ((a : ℂ) + z)

theorem laguerrePolya_xiDifferentialJetSource_of_rh
    (hRH : RiemannHypothesis) (cs : List ℝ) (k : ℕ) (a : ℝ) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (xiDifferentialJetSource cs k a) :=
  IntervalLaguerrePolya.laguerrePolya_comp_add
    (KernelStrip.laguerrePolya_firstOrderChain cs
      (laguerrePolya_iterate_deriv
        (riemannHypothesis_iff_laguerrePolya_XiC.mp hRH) k)) a

/-- RH controls every finite section, every derivative order, every real center,
and every finite list of real first-order factors. -/
theorem xiDifferentialJensenPolynomial_splits_of_rh
    (hRH : RiemannHypothesis) (cs : List ℝ) (k : ℕ) (a : ℝ) (d : ℕ) :
    (xiDifferentialJensenPolynomial cs k a d).Splits :=
  splits_jensenPoly_realTaylorCoeff
    (laguerrePolya_xiDifferentialJetSource_of_rh hRH cs k a)
    (xiDifferentialJetSource_schwarzReal cs k a) d

/-- One nonsplitting finite differential-jet section falsifies RH. -/
theorem not_riemannHypothesis_of_xiDifferentialJensenPolynomial_not_splits :
    (∃ (cs : List ℝ) (k : ℕ) (a : ℝ) (d : ℕ),
      ¬ (xiDifferentialJensenPolynomial cs k a d).Splits) → ¬ RiemannHypothesis := by
  rintro ⟨cs, k, a, d, hbad⟩ hRH
  exact hbad (xiDifferentialJensenPolynomial_splits_of_rh hRH cs k a d)

/-- The necessary direction completes the existing Xi Jensen criterion. -/
theorem riemannHypothesis_iff_splits_jensenPoly_XiC :
    RiemannHypothesis ↔ ∀ d, (jensenPoly (realTaylorCoeff XiC) d).Splits :=
  ⟨fun hRH d => splits_jensenPoly_realTaylorCoeff
    (riemannHypothesis_iff_laguerrePolya_XiC.mp hRH) (fun z => XiC_conj z) d,
    riemannHypothesis_of_splits_jensenPoly_XiC⟩

#print axioms xiDifferentialJensenPolynomial_splits_of_rh
#print axioms not_riemannHypothesis_of_xiDifferentialJensenPolynomial_not_splits
#print axioms riemannHypothesis_iff_splits_jensenPoly_XiC

end RHTower
