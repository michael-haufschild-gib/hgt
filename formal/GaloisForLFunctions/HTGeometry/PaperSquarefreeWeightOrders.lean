import GaloisForLFunctions.HTGeometry.PaperWeightOrderIdeals
import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Squarefree weight bounds over arbitrary commutative rings

The source nonnegative-weight theorem gives the Veronese ideal's generator
degree bound without field or domain assumptions. These general bounds are
shared by the existing normal-line and the full normal-family applications.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions.VeroneseIdeal

variable (K : Type*) [CommRing K]

/-- A squarefree coordinate product is homogeneous over any commutative coefficient ring. -/
theorem paperSquarefreeProduct_homogeneous_overRing {σ : Type*} (s : Finset σ) :
    (∏ j ∈ s, (X j : MvPolynomial σ K)).IsHomogeneous s.card := by
  simpa using MvPolynomial.IsHomogeneous.prod s (fun j => (X j : MvPolynomial σ K))
    (fun _ => 1) (fun j _ => MvPolynomial.isHomogeneous_X K j)

/-- The actual native Veronese ideal has the source weight bound over arbitrary rings. -/
theorem paperVeroneseIdeal_weightOrder_overRing (σ : Type*) [DecidableEq σ] (q : ℕ) :
    veroneseIdeal K σ q ≤
      paperWeightOrderIdeal (fun _ : σ => (1 : ℤ)) (by intro _; exact zero_le_one) (q : ℤ) := by
  rw [veroneseIdeal, Ideal.span_le]
  rintro p ⟨s, hcard, rfl⟩
  have hh := paperSquarefreeProduct_homogeneous_overRing K s
  rw [hcard] at hh
  exact paperWeightOrderIdeal_mem_of_homogeneous _ _ (paperIsWeightedHomogeneous_int hh)

end GaloisForLFunctions.HTGeometry
