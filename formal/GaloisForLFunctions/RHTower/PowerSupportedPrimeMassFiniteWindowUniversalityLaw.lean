import GaloisForLFunctions.RHTower.DirichletPolynomialSincEnergy
import GaloisForLFunctions.RHTower.SquareSupportPrimeMass

/-!
# Power-supported prime mass finite-window universality

Every power-supported coefficient family that is forced to carry reciprocal prime mass has two
universal observation laws.  Its independent Steinhaus second moment carries that mass exactly
through the diagonal, while every deterministic symmetric window can lose at most the explicit
sinc collision energy.  The statement applies simultaneously to every dilation rung.
-/

open Complex MeasureTheory intervalIntegral Finset
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-- **Power-supported finite-window transference law.**  Forced prime mass transfers exactly to
the independent random second moment and, on every symmetric deterministic window, survives after
subtracting only the explicit off-diagonal sinc collision energy. -/
theorem powerSupportedPrimeMass_randomExact_deterministicWindowLowerBound
    {S P : Finset ℕ} {b : ℕ → ℝ} {δ : ℝ} {m : ℕ}
    (hm : m ≠ 0) (hδ0 : 0 ≤ δ)
    (hmem : ∀ p ∈ P, p ^ m ∈ S)
    (hval : ∀ p ∈ P,
      δ * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ |b (p ^ m)|)
    (hS : ∀ n ∈ S, 1 ≤ n) (T : ℝ) (hT : 0 < T) :
    (∫ ω, ‖∑ n ∈ S, (b n : ℂ) * X n ω‖ ^ 2 ∂steinhausMeasure =
        ∑ n ∈ S, (b n) ^ 2) ∧
      δ ^ 2 * ∑ p ∈ P, (p : ℝ)⁻¹ ≤
        ∫ ω, ‖∑ n ∈ S, (b n : ℂ) * X n ω‖ ^ 2 ∂steinhausMeasure ∧
      δ ^ 2 * ∑ p ∈ P, (p : ℝ)⁻¹ -
          dpolySincOffDiagonalEnergy b S T ≤
        (∫ t in (-T)..T, ‖dpoly b S t‖ ^ 2) / (2 * T) := by
  have hforced := primeMass_le_pow_sum_of_forced hm hδ0 hmem hval
  have hrandom := integral_normSq_dpoly b S
    (fun n hn => Nat.one_le_iff_ne_zero.mp (hS n hn))
  have herror := secondMoment_symmetric_sinc_error_le b S T hT hS
  refine ⟨hrandom, ?_, ?_⟩
  · rw [hrandom]
    exact hforced
  · have hlower := neg_le_of_abs_le herror
    linarith

end

end RHTower
