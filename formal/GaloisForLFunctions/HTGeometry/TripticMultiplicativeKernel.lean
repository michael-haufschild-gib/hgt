import GaloisForLFunctions.HTGeometry.TripticKernelDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.TripticSourceDivisor
import GaloisForLFunctions.HTGeometry.MeromorphicLogDerivLocalForm

/-!
# The kernel of the multiplicative orbital charge

A logarithmic derivative has no Laurent coefficient below its residue, so a multiplicative triptic
source contributes to the orbital divisor of its logarithmic derivative only at order `-1`, where
the coefficient is exactly the shift order.  A source of vanishing orbital charge therefore has a
logarithmic derivative whose orbital divisor vanishes at every order, and the additive kernel
theorem applies.

* `differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- **The kernel of the multiplicative orbital charge.**  A member of the multiplicative triptic
class whose orbital charge vanishes on every orbit has a differentially algebraic logarithmic
derivative, and its mixed constant is zero. -/
theorem differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge
    {Y : ℂ → ℂ} {τ σ : ℂ}
    (hY : MeromorphicOn Y (Set.univ : Set ℂ)) (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤)
    (hYper : ∀ z : ℂ, Y (z + 1) = Y z)
    {Cst : ℂ} (hmixed : ∀ z : ℂ, logDeriv Y (z + τ + σ) - logDeriv Y (z + τ)
      - logDeriv Y (z + σ) + logDeriv Y z = Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hcharge : ∀ p : ℂ, tripticOrbitCharge Y σ p = 0) :
    Cst = 0 ∧ DifferentiallyAlgebraic (toMeromorphicNFOn (logDeriv Y) (Set.univ : Set ℂ)) := by
  have hFmero : MeromorphicOn (logDeriv Y) (Set.univ : Set ℂ) := fun z _ ↦
    ((hY z (Set.mem_univ z)).deriv).div (hY z (Set.mem_univ z))
  have hFper : ∀ z : ℂ, logDeriv Y (z + 1) = logDeriv Y z := by
    intro z
    have hfun : (fun w : ℂ ↦ Y (w + 1)) = Y := funext hYper
    have hd : deriv Y (z + 1) = deriv Y z := by
      have hcomp := deriv_comp_add_const (f := Y) (a := (1 : ℂ)) z
      rw [hfun] at hcomp
      exact hcomp.symm
    rw [logDeriv_apply, logDeriv_apply, hd, hYper z]
  refine differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor hFmero
    (periodicOneGerm_of_forall hFper) (mixedConstGerm_of_forall hmixed) hτ hσ hindep hindepτ
    hindepσ ?_
  intro p ℓ hℓ
  rcases lt_or_eq_of_le (by omega : ℓ ≤ -1) with hlt | heq
  · have hzero : ∀ m : ℤ,
        laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (p + (m : ℂ) * σ) ℓ = 0 := by
      intro m
      rw [laurentCoeff_shiftDiff hFmero σ _ ℓ]
      obtain ⟨n₁, hn₁⟩ := WithTop.ne_top_iff_exists.mp (hfin (p + (m : ℂ) * σ + σ))
      obtain ⟨n₂, hn₂⟩ := WithTop.ne_top_iff_exists.mp (hfin (p + (m : ℂ) * σ))
      rw [laurentCoeff_logDeriv_eq_zero_of_le (hY _ (Set.mem_univ _)) hn₁.symm (by omega),
        laurentCoeff_logDeriv_eq_zero_of_le (hY _ (Set.mem_univ _)) hn₂.symm (by omega), sub_zero]
    rw [finsum_congr hzero, finsum_zero]
  · subst heq
    have hterm : ∀ m : ℤ,
        laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (p + (m : ℂ) * σ) (-1)
          = ((shiftOrder Y σ (p + (m : ℂ) * σ) : ℤ) : ℂ) := fun m ↦
      laurentCoeff_shiftDiff_logDeriv hY hfin σ _
    rw [finsum_congr hterm, ← intCast_finsum]
    have hval : (∑ᶠ m : ℤ, shiftOrder Y σ (p + (m : ℂ) * σ)) = tripticOrbitCharge Y σ p := rfl
    rw [hval, hcharge p]
    norm_num

end

end GaloisForLFunctions.HTGeometry
