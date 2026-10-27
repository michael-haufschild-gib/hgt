import GaloisForLFunctions.ArithmeticIndexDescent.BoundedSourceWork
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.UnboundedOverlapIsTheRiemannHypothesis

/-!
# Work and index have the same finite stratum

The fixed cubic-spline orbit at integer logarithms detects every distinct right
zero. A uniform finite bound on its negative indices is therefore equivalent to
finite off-line support, and hence to eventual boundedness of damped arithmetic
source work. This identifies the finiteness endpoint of the two programmes without
identifying finiteness with the absence of defects.
-/

open Filter RHTower Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- Negative index of the complete Weil form on a finite integer-log spline presentation. -/
def splineIndex (S : Finset ℝ) : ℕ :=
  hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx cubicSpline)))

theorem rightCarrier_finite_iff_offLineSupport_finite :
    {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.Finite ↔ offLineSupport.Finite := by
  constructor
  · intro hR
    have hr : {j : XiDivisorSupport | 1 / 2 < (j : ℂ).re}.Finite := by
      have hi : Function.Injective (fun j : XiDivisorSupport => (j : ℂ)) :=
        Subtype.val_injective
      exact (hR.preimage hi.injOn).subset fun j hj =>
        ⟨(xiDivisorZetaCarrierEquiv j).property, hj⟩
    refine (hr.union (hr.image supportPartner)).subset fun j hj => ?_
    rcases lt_or_gt_of_ne (show (j : ℂ).re ≠ 1 / 2 from hj) with hleft | hright
    · right
      refine ⟨supportPartner j, ?_, supportPartner_involutive j⟩
      change 1 / 2 < (supportPartner j : ℂ).re
      rw [supportPartner_re]
      linarith only [hleft]
    · exact Or.inl hright
  · intro h
    refine (h.image (fun j : XiDivisorSupport => (j : ℂ))).subset fun ρ hρ => ?_
    refine ⟨xiDivisorZetaCarrierEquiv.symm ⟨ρ, hρ.1⟩, ?_, rfl⟩
    exact hρ.2.ne'

/-- One fixed spline and the integer-log orbit detect finiteness of the entire off-line support. -/
theorem bounded_splineIndex_iff_offLineSupport_finite :
    (∃ K : ℕ, ∀ S : Finset ℝ, (↑S : Set ℝ) ⊆ logShifts → splineIndex S ≤ K) ↔
      offLineSupport.Finite := by
  classical
  rw [← rightCarrier_finite_iff_offLineSupport_finite]
  constructor
  · rintro ⟨K, hK⟩
    by_contra hR
    have hlarge : ((K + 1 : ℕ) : ℕ∞) ≤
        {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
      rw [Set.Infinite.encard_eq hR]
      exact le_top
    obtain ⟨S, hS, hindex⟩ := (zeta_splineAtomic_negIndex_law (K + 1)).mpr hlarge
    have hbound := hK S hS
    change splineIndex S ≥ K + 1 at hindex
    omega
  · intro hR
    refine ⟨hR.toFinset.card, fun S hS => ?_⟩
    have hcount := (zeta_splineAtomic_negIndex_law (splineIndex S)).mp ⟨S, hS, le_rfl⟩
    rw [hR.encard_eq_coe_toFinset_card] at hcount
    exact ENat.coe_le_coe.mp hcount

/-- A finite index budget and a finite arithmetic work budget describe the same stratum. -/
theorem bounded_splineIndex_iff_eventually_bounded_dampedSourceWork :
    (∃ K : ℕ, ∀ S : Finset ℝ, (↑S : Set ℝ) ⊆ logShifts → splineIndex S ≤ K) ↔
      ∃ B : ℝ, ∀ᶠ n : ℕ in atTop, xiDampedSourceWork ((n : ℝ) + 4) ≤ B :=
  bounded_splineIndex_iff_offLineSupport_finite.trans
    eventually_bounded_dampedSourceWork_iff.symm

end GaloisForLFunctions.ArithmeticIndexDescent
