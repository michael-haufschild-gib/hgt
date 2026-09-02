import GaloisForLFunctions.RHTower.FZZCigarParityFixedQuinticEigenphaseCompletion
import GaloisForLFunctions.RHTower.FZZCigarParityKreinEigenpairCofinalEscape

/-!
# Neutral conjugate-eigenphase collapse for the FZZ parity source

The physical cigar vacuum and replica-area expansions have equal total numbers of opposite
winding screenings.  In the corpus source block, the corresponding balanced eigenline coordinates
are a unit phase and its complex conjugate.  This module proves that every coefficient-only neutral
monomial therefore collapses to `1`, at every positive source scale and every screening depth.

Consequently neutralization erases the fixed-quintic phase completion: neither the quintic nor any
other equal-charge global eigenline power can provide the dynamical phase-incidence premise in

`neutral coefficient phase -> divisor eigenphase landing -> Mellin completeness -> RH`.

The sharp survivor is a phase in the position/prime-form kernel, or an unbalanced winding phase
whose charge is compensated by external insertions.  Those interacting branches are not excluded.

`[NEW] [ALL-DEPTH EXACT COLLAPSE] [FIXED-QUINTIC ROUTE KILL]
[KERNEL-PHASE SURVIVOR] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Global coefficient phase at neutral screening depth `n`: equal powers of the two balanced
conjugate FZZ source eigenlines. -/
def fzzCigarParityNeutralConjugateEigenphaseCoefficient
    (n : ℕ) (beta : ℝ) : ℂ :=
  fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ^ n *
    fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate beta ^ n

/-- **All-depth neutral phase collapse.**  Equal-charge conjugate pairing erases the complete
global eigenline phase at every positive physical scale. -/
theorem fzzCigarParityNeutralConjugateEigenphaseCoefficient_eq_one
    (n : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityNeutralConjugateEigenphaseCoefficient n beta = 1 := by
  rw [fzzCigarParityNeutralConjugateEigenphaseCoefficient,
    fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate_eq_star,
    ← mul_pow, Complex.star_def, Complex.mul_conj',
    norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate hbeta]
  norm_num

/-- Phase completeness after imposing equal-charge conjugate neutralization at every depth. -/
def FZZCigarParityNeutralConjugateEigenphaseComplete : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    ∃ n : ℕ, ∃ beta : ℝ, 0 < beta ∧
      fzzCigarParityNeutralConjugateEigenphaseCoefficient n beta = z

/-- Neutral coefficient phases are not unit-circle complete: the unit target `-1` is absent even
when screening depth and positive source scale may both vary. -/
theorem not_fzzCigarParityNeutralConjugateEigenphaseComplete :
    ¬FZZCigarParityNeutralConjugateEigenphaseComplete := by
  intro hcomplete
  obtain ⟨n, beta, hbeta, hmatch⟩ := hcomplete (-1) (by simp)
  rw [fzzCigarParityNeutralConjugateEigenphaseCoefficient_eq_one n hbeta] at hmatch
  norm_num at hmatch

/-- Physical neutralization of the corpus's fixed-quintic phase channel. -/
def fzzCigarParityNeutralizedFixedQuinticEigenphase (beta : ℝ) : ℂ :=
  fzzCigarParityFixedQuinticEigenphase beta *
    star (fzzCigarParityFixedQuinticEigenphase beta)

/-- The fixed-quintic endpoint becomes the constant phase `1` after conjugate neutralization. -/
theorem fzzCigarParityNeutralizedFixedQuinticEigenphase_eq_one
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityNeutralizedFixedQuinticEigenphase beta = 1 := by
  rw [fzzCigarParityNeutralizedFixedQuinticEigenphase,
    Complex.star_def, Complex.mul_conj',
    norm_fzzCigarParityFixedQuinticEigenphase hbeta]
  norm_num

/-- A neutral global source coefficient cannot alter any complex position/prime-form kernel. -/
theorem fzzCigarParityNeutralConjugateEigenphaseCoefficient_mul_kernel
    (n : ℕ) {beta : ℝ} (hbeta : 0 < beta) (kernel : ℂ) :
    fzzCigarParityNeutralConjugateEigenphaseCoefficient n beta * kernel = kernel := by
  rw [fzzCigarParityNeutralConjugateEigenphaseCoefficient_eq_one n hbeta, one_mul]

/-- Arbitrary postprocessing sees only the surviving kernel, never the neutral global phase. -/
theorem fzzCigarParityNeutralConjugateEigenphaseCoefficient_postprocess
    {Target : Type*} (n : ℕ) {beta : ℝ} (hbeta : 0 < beta)
    (kernel : ℂ) (postprocess : ℂ → Target) :
    postprocess
        (fzzCigarParityNeutralConjugateEigenphaseCoefficient n beta * kernel) =
      postprocess kernel := by
  rw [fzzCigarParityNeutralConjugateEigenphaseCoefficient_mul_kernel n hbeta kernel]

/-- Closed certificate killing coefficient-only neutral eigenphase landing while retaining the
exact position-kernel survivor. -/
def FZZCigarParityNeutralConjugateEigenphaseCollapseNoGo : Prop :=
  (∀ (n : ℕ) (beta : ℝ), 0 < beta →
    fzzCigarParityNeutralConjugateEigenphaseCoefficient n beta = 1) ∧
  ¬FZZCigarParityNeutralConjugateEigenphaseComplete ∧
  (∀ (n : ℕ) (beta : ℝ) (kernel : ℂ), 0 < beta →
    fzzCigarParityNeutralConjugateEigenphaseCoefficient n beta * kernel = kernel) ∧
  (∀ beta : ℝ, 0 < beta →
    fzzCigarParityNeutralizedFixedQuinticEigenphase beta = 1)

/-- **FZZ-P route-class kill.**  Physical conjugate neutralization destroys every global
coefficient-only eigenphase, including the fixed-quintic completion, at all depths and scales. -/
theorem fzzCigarParity_neutralConjugateEigenphaseCollapse_noGo :
    FZZCigarParityNeutralConjugateEigenphaseCollapseNoGo := by
  refine ⟨?_, not_fzzCigarParityNeutralConjugateEigenphaseComplete, ?_, ?_⟩
  · intro n beta hbeta
    exact fzzCigarParityNeutralConjugateEigenphaseCoefficient_eq_one n hbeta
  · intro n beta kernel hbeta
    exact fzzCigarParityNeutralConjugateEigenphaseCoefficient_mul_kernel n hbeta kernel
  · intro beta hbeta
    exact fzzCigarParityNeutralizedFixedQuinticEigenphase_eq_one hbeta

end

end RHTower
