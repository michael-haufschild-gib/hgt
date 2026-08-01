import GaloisForLFunctions.HTGeometry.CommonCharacterFusionConservation
import GaloisForLFunctions.RHTower.HighExponentShellOrthogonalDivisorReplication
import GaloisForLFunctions.RHTower.HighExponentShellLeastAtomAsymptotic
import GaloisForLFunctions.RHTower.DirichletHilbertRiggingBarrier

/-!
# Fusion conservation for the high-exponent Riemann shell frame

Finite packets of high-exponent shell multipliers are relatively differentially independent and
replicate the completed-zeta divisor.  Their label double carries the universal common-character
fusion decomposition, while the infinite unit-response codiagonal is not closable.  The adjacent
shell transport supplies the centered modular character whose unitary locus is the critical line.
-/

open scoped Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances

namespace RHTower

open Complex
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HTGeometry

noncomputable section

/-- Consecutive high-shell labels beginning at the zero-free threshold. -/
def finiteHighShellLevel {n : ℕ} (i : Fin n) : {m : ℕ // 12 ≤ m} :=
  ⟨12 + i, by omega⟩

theorem finiteHighShellLevel_injective {n : ℕ} :
    Function.Injective (finiteHighShellLevel (n := n)) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Subtype.val h
  simpa [finiteHighShellLevel] using hval

/-- Every finite high-shell packet remains relatively differentially independent over the full
zeta differential field. -/
theorem finiteHighShell_relativeDifferentialIndependent {n : ℕ} :
    DifferentialIndependent zetaUpperEndDifferentialField
      (fun i : Fin n =>
        relativeShellMultiplierUpperEndCarrier
          (finiteHighShellLevel i).1) := by
  exact relativeShellMultiplierUpperEndCarrier_differentialIndependent.comp
    finiteHighShellLevel finiteHighShellLevel_injective

/-- Every member of a finite high-shell packet has the completed-zeta analytic order throughout
the strict right half-plane away from the endpoint. -/
theorem finiteHighShell_analyticOrderReplication {n : ℕ}
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) (i : Fin n) :
    analyticOrderAt
        (fun z => completedRiemannZeta z *
          shellMultiplier (finiteHighShellLevel i).1 z) s =
      analyticOrderAt completedRiemannZeta s := by
  exact analyticOrderAt_completedRiemannZeta_mul_shellMultiplier
    (finiteHighShellLevel i).2 hs hs1

/-- The finite high-shell label double splits exactly into its common-divisor response and its
centered transverse-label response. -/
theorem finiteHighShell_reciprocalFusionConservation {n : ℕ}
    (hn : 0 < n) (x y : Fin n → ℝ) :
    reciprocalLabelQuadratic (x, y) =
      2 * (finiteLabelFusion x * finiteLabelFusion y / (n : ℝ)) +
        2 * ∑ i, finiteLabelCentered x i * finiteLabelCentered y i :=
  reciprocalLabelQuadratic_fusion_conservation hn x y

/-- **High-shell common-character fusion law.** The actual shell frame has simultaneously a
genuine relative differential label packet, replicated completed-zeta order, and the exact
longitudinal/transverse reciprocal fusion decomposition. -/
theorem highShell_commonCharacterFusion_law {n : ℕ} (hn : 0 < n)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentialIndependent zetaUpperEndDifferentialField
        (fun i : Fin n =>
          relativeShellMultiplierUpperEndCarrier
            (finiteHighShellLevel i).1) ∧
      (∀ i : Fin n,
        analyticOrderAt
            (fun z => completedRiemannZeta z *
              shellMultiplier (finiteHighShellLevel i).1 z) s =
          analyticOrderAt completedRiemannZeta s) ∧
      (∀ x y : Fin n → ℝ,
        reciprocalLabelQuadratic (x, y) =
          2 * (finiteLabelFusion x * finiteLabelFusion y / (n : ℝ)) +
            2 * ∑ i, finiteLabelCentered x i * finiteLabelCentered y i) := by
  exact ⟨finiteHighShell_relativeDifferentialIndependent,
    fun i => finiteHighShell_analyticOrderReplication hs hs1 i,
    finiteHighShell_reciprocalFusionConservation hn⟩

/-- The infinite high-shell fusion row is singular in the standard Hilbert label topology, while
the shell transport character is unitary exactly on the critical line. -/
theorem highShell_infiniteFusionSingularity_and_unitaryLocus :
    (¬ IsSequentiallyClosableBetween shellCodiagonal shellLabelEmbedding) ∧
      (∀ s : ℂ, ‖shellTransferCharacter s‖ = 1 ↔ s.re = 1 / 2) := by
  exact ⟨shellCodiagonal_not_closable,
    norm_shellTransferCharacter_eq_one_iff⟩

/-- **Stable-realization no-go.**  A Bessel realization of the countably many source labels
cannot have one bounded vector with the same nonzero unit response on every label; independently,
the literal unit codiagonal on orthogonal shell labels is not closable.  Thus neither a stable
nonorthogonal frame nor the canonical orthogonal Hilbert sum regularizes uniform divisor fusion. -/
theorem highShell_no_stableHilbert_unitFusion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : ℕ → E) (B : ℝ) (hB : HasBesselBound u B) :
    (¬ ∃ y : E, ∀ i, inner ℂ (u i) y = 1) ∧
      ¬ IsSequentiallyClosableBetween shellCodiagonal shellLabelEmbedding := by
  exact ⟨no_bessel_family_with_unit_response u B hB,
    shellCodiagonal_not_closable⟩

end

end RHTower
