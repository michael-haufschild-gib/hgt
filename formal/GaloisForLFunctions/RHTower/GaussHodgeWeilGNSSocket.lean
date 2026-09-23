import GaloisForLFunctions.RHTower.GaussHodgeWeilPolarizationFusion
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion

/-!
# The GNS socket: RH ⟺ a square realization of the Weil form

The corpus's positivity criterion states RH ⟺ nonnegativity of the diagonal Weil polarization
on square-summable tests.  A Gate-II entry — a compressed-trace or spectral (GNS) construction
in the style of the function-field proof or the Connes–Consani semi-local theorem — produces
something stronger than nonnegativity: it exhibits each diagonal value as a sum of squares.
This module formalizes that target as a single `Prop` and proves it is *exactly* RH:

`XiWeilSquareRealization` — a coordinate family `g` realizing every square-summable diagonal
value `Re(xiWeilPolarization F F)` as `Σ (g F q)²` — implies RH through the criterion, and RH
conversely supplies the tautological realization `g F q = ‖F(α_q)‖` through the diagonal law.
Hence **RH ⟺ the diagonal Weil form is a sum of squares**, and, through the loop, a square
realization is equivalent to the vanishing of the Hodge mass current.  Any future compressed
positivity construction needs only to hit this socket; everything downstream is already
unconditional Lean.
-/

open Complex

namespace RHTower

noncomputable section

/-- A global square realization (coordinate GNS) of the diagonal Weil form: every
square-summable diagonal value is a convergent sum of real squares. -/
def XiWeilSquareRealization : Prop :=
  ∃ g : (ℂ → ℂ) → XiZeroCopy → ℝ,
    ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
      HasSum (fun q => g F q ^ (2 : ℕ)) ((xiWeilPolarization F F).re)

/-- **A square realization forces RH**: sums of squares are nonnegative, and nonnegativity of
the diagonal Weil form is the corpus's positivity criterion. -/
theorem riemannHypothesis_of_xiWeilSquareRealization
    (h : XiWeilSquareRealization) : RiemannHypothesis := by
  obtain ⟨g, hg⟩ := h
  rw [riemannHypothesis_iff_xiWeilPolarization_nonneg]
  intro F hF
  have hsum := hg F hF
  have : (xiWeilPolarization F F).re = ∑' q : XiZeroCopy, g F q ^ (2 : ℕ) :=
    hsum.tsum_eq.symm
  rw [this]
  exact tsum_nonneg fun q => sq_nonneg _

/-- **RH supplies the tautological realization**: under RH the diagonal law makes
`g F q = ‖F(α_q)‖` a square realization. -/
theorem xiWeilSquareRealization_of_riemannHypothesis
    (hRH : RiemannHypothesis) : XiWeilSquareRealization := by
  refine ⟨fun F q => ‖F (xiSpectralPoint q)‖, ?_⟩
  intro F hF
  have hdiag := xiWeilPolarization_diagonal_of_riemannHypothesis hRH F
  have hsumC : Summable (fun q : XiZeroCopy =>
      ((‖F (xiSpectralPoint q)‖ ^ (2 : ℕ) : ℝ) : ℂ)) := by
    simpa only [Function.comp_apply] using!
      hF.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  have hre : (xiWeilPolarization F F).re =
      ∑' q : XiZeroCopy, ‖F (xiSpectralPoint q)‖ ^ (2 : ℕ) := by
    rw [hdiag, Complex.re_tsum hsumC]
    exact tsum_congr fun q => Complex.ofReal_re _
  rw [hre]
  exact hF.hasSum

/-- **The GNS criterion**: RH holds exactly when the diagonal Weil form is a sum of
squares. -/
theorem riemannHypothesis_iff_xiWeilSquareRealization :
    RiemannHypothesis ↔ XiWeilSquareRealization :=
  ⟨xiWeilSquareRealization_of_riemannHypothesis,
    riemannHypothesis_of_xiWeilSquareRealization⟩

/-- **Gate II lands on the loop**: a square realization of the Weil form is equivalent to the
vanishing of the Hodge mass current. -/
theorem xiWeilSquareRealization_iff_gaussHodgeMass_vanishing :
    XiWeilSquareRealization ↔
      ∀ (q : XiZeroCopy) (p : Nat.Primes), gaussHodgeMassCurrent 1 q p = 0 :=
  riemannHypothesis_iff_xiWeilSquareRealization.symm.trans
    (gaussHodgeMass_vanishing_iff_riemannHypothesis (le_refl 1)).symm

end

end RHTower
