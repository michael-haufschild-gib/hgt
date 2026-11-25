import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.MonomialWeights

/-! # Signed Fourier characters away from two closing levels -/

open Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

private def positivePart {L : Type*} [Fintype L] (m : L→ℤ) : L →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun l => (m l).toNat)

private theorem parts_sub (a : ℤ) : (a.toNat:ℝ)-((-a).toNat:ℝ)=(a:ℝ) := by
  exact_mod_cast (show (a.toNat:ℤ)-((-a).toNat:ℤ)=a by omega)

/-- A character is the difference of its two monomial weights, anchored at j. -/
def signedWeight (i j : I) (m : Outside i j→ℤ) (l : I) : ℝ :=
  monomialWeight i j (positivePart m) l-monomialWeight i j (positivePart (-m)) l

theorem signed_balance (i j : I) (m : Outside i j→ℤ) : ∑ l, signedWeight i j m l=0 := by
  simp only [signedWeight,sum_sub_distrib,monomialWeight_balanced,sub_self]

theorem signed_outside (i j : I) (m : Outside i j→ℤ) (l : Outside i j) :
    signedWeight i j m l.val=(m l:ℝ) := by
  rw [signedWeight,monomialWeight_outside,monomialWeight_outside]
  exact parts_sub (m l)

theorem signed_action (i j : I) (m : Outside i j→ℤ) (E : I→ℝ) :
    normalizedAction (signedWeight i j m) E i j=∑ l : Outside i j, (m l:ℝ)*((E l.val-E j)/(E i-E j)) := by
  unfold normalizedAction signedWeight
  simp only [sub_mul,sum_sub_distrib,sub_div]
  change normalizedAction (monomialWeight i j (positivePart m)) E i j-
    normalizedAction (monomialWeight i j (positivePart (-m))) E i j=_
  rw [monomialWeight_action,monomialWeight_action,←sum_sub_distrib]
  apply sum_congr rfl
  intro l _
  rw [←sub_mul]
  change ((m l).toNat-((-(m l)).toNat:ℝ))*_ = _
  rw [parts_sub]

#print axioms signed_action
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
