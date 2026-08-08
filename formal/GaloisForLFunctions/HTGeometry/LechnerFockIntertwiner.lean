import GaloisForLFunctions.HTGeometry.LpFamilyIsometry
import GaloisForLFunctions.HTGeometry.UnimodularMulLp

/-!
# The Lechner intertwiner on the rapidity Fock space

Assembling the per-particle-number intertwiners over all `n` gives one operator on the direct sum

`lp (fun n => L^2 (Fin n -> R)) 2`,

which is the rapidity Fock space.  It is a linear isometry because each summand map is, and the
`lp` norm depends only on the summand norms.

Its action is the pair multiplier at each particle number, so the exchange law is converted into
the constant Bose/Fermi law by `intertwine_swapAt` and the creation string of `(10b)` is
`pairMultiplierFin_succ`.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The rapidity Fock space: the `l^2` direct sum of the `n`-particle rapidity spaces. -/
abbrev rapidityFock : Type :=
  lp (fun n : ℕ => Lp ℂ 2 (volume : Measure (Fin n → ℝ))) 2

/-- **Lechner's intertwiner on the Fock space.**  The direct sum over particle number of the
pair-multiplier isometries. -/
noncomputable def lechnerFockIntertwiner {y : ℝ → ℂ} (hy1 : ∀ t : ℝ, ‖y t‖ = 1)
    (hym : Measurable y) : rapidityFock →ₗᵢ[ℂ] rapidityFock :=
  lpFamilyIsometry (by simp) (fun n => lechnerIntertwiner hy1 hym n 2)

theorem lechnerFockIntertwiner_apply {y : ℝ → ℂ} (hy1 : ∀ t : ℝ, ‖y t‖ = 1)
    (hym : Measurable y) (x : rapidityFock) (n : ℕ) :
    (lechnerFockIntertwiner hy1 hym x : ∀ n, Lp ℂ 2 (volume : Measure (Fin n → ℝ))) n
      = lechnerIntertwiner hy1 hym n 2 (x n) := rfl

theorem norm_lechnerFockIntertwiner {y : ℝ → ℂ} (hy1 : ∀ t : ℝ, ‖y t‖ = 1)
    (hym : Measurable y) (x : rapidityFock) :
    ‖lechnerFockIntertwiner hy1 hym x‖ = ‖x‖ :=
  (lechnerFockIntertwiner hy1 hym).norm_map x

/-- **The conjugated creation formula `(10b)`.**  Conjugating the one-to-many-particle creation
step by the intertwiner turns the free creator into the same creator dressed by the pair-phase
string of the new rapidity against all the old ones.  The intertwiner of the old particles is
untouched. -/
theorem conjugated_creation_multiplier (y : ℝ → ℂ) {n : ℕ} (ψ : ℝ → ℂ)
    (Φ : (Fin n → ℝ) → ℂ) (θ : Fin (n + 1) → ℝ) :
    pairMultiplierFin y θ * (ψ (θ 0) * Φ (fun j : Fin n => θ j.succ))
      = (ψ (θ 0) * ∏ j : Fin n, y (θ 0 - θ j.succ))
        * (pairMultiplierFin y (fun j : Fin n => θ j.succ) * Φ (fun j : Fin n => θ j.succ)) := by
  rw [pairMultiplierFin_succ]
  ring

end GaloisForLFunctions.HTGeometry
