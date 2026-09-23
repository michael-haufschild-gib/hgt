import GaloisForLFunctions.RHTower.RankOneIncidenceCommutatorEnergy
import GaloisForLFunctions.RHTower.SoninFiniteRankWardBoundaryEnergy

/-!
# Rank-one Ward Bernoulli-clock universality

The singleton specialization of the finite-packet Ward form is the rank-one cutoff commutator
energy.  For a unit vector this is the Bernoulli variance of its cutoff occupancy.  Replacing the
cutoff by its clock involution multiplies the same scalar by exactly four, and vanishing occurs
exactly at pure occupancy.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap
open InnerProductSpace
open GaloisForLFunctions.HTGeometry

/-- The one-entry finite source packet is literally its rank-one projector. -/
theorem finiteRankProbe_finOne_eq_rankOne
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (psi : H) :
    finiteRankProbe (fun _ : Fin 1 => (1 : ℂ)) (fun _ => psi) (fun _ => psi) =
      rankOne ℂ psi psi := by
  rw [finiteRankProbe, Fin.sum_univ_one]
  simp

/-- The singleton diagonal Ward value is the Bernoulli variance of cutoff occupancy. -/
theorem rankOneFiniteWard_eq_bernoulli
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (psi : H) (hpsi : ‖psi‖ = 1) :
    finiteRankCutoffWardForm e
        (fun _ : Fin 1 => (1 : ℂ)) (fun _ => psi) (fun _ => psi)
        (fun _ : Fin 1 => (1 : ℂ)) (fun _ => psi) (fun _ => psi) =
      ((2 * ‖e psi‖ ^ (2 : ℕ) * (1 - ‖e psi‖ ^ (2 : ℕ)) : ℝ) : ℂ) := by
  rw [finiteRankCutoffWardForm_self_eq_hsNormSq,
    finiteRankProbe_finOne_eq_rankOne]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (hsNormSq_rankOneProjection_commutator e he heAdj psi hpsi)

/-- A singleton Ward packet, its cutoff commutator, and its clock-involution commutator are one
Bernoulli variance with exact scale factors one, one, and four. -/
theorem rankOneWard_bernoulliClockUniversality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H →L[ℂ] H) (he : IsIdempotentElem e) (heAdj : adjoint e = e)
    (psi : H) (hpsi : ‖psi‖ = 1) :
    let W := finiteRankCutoffWardForm e
      (fun _ : Fin 1 => (1 : ℂ)) (fun _ => psi) (fun _ => psi)
      (fun _ : Fin 1 => (1 : ℂ)) (fun _ => psi) (fun _ => psi)
    W = ((2 * ‖e psi‖ ^ (2 : ℕ) * (1 - ‖e psi‖ ^ (2 : ℕ)) : ℝ) : ℂ) ∧
      hsNormSq (ccmCommutator (rankOne ℂ psi psi) e) = W.re ∧
      hsNormSq (ccmCommutator (rankOne ℂ psi psi) ((2 : ℂ) • e - 1)) = 4 * W.re ∧
      (W = 0 ↔ ‖e psi‖ ^ (2 : ℕ) = 0 ∨ ‖e psi‖ ^ (2 : ℕ) = 1) := by
  dsimp only
  have hW := rankOneFiniteWard_eq_bernoulli e he heAdj psi hpsi
  have hWre :
      (finiteRankCutoffWardForm e
        (fun _ : Fin 1 => (1 : ℂ)) (fun _ => psi) (fun _ => psi)
        (fun _ : Fin 1 => (1 : ℂ)) (fun _ => psi) (fun _ => psi)).re =
        2 * ‖e psi‖ ^ (2 : ℕ) * (1 - ‖e psi‖ ^ (2 : ℕ)) := by
    rw [hW]
    rw [Complex.ofReal_re]
  refine ⟨hW, ?_, ?_, ?_⟩
  · rw [hsNormSq_rankOneProjection_commutator e he heAdj psi hpsi, hWre]
  · rw [hsNormSq_rankOneProjection_clockInvolution_commutator e he heAdj psi hpsi, hWre]
    ring
  · rw [hW, Complex.ofReal_eq_zero]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · left
        simpa using h
      · right
        linarith
    · rintro (h | h)
      · simp [h]
      · simp [h]

end RHTower
