import GaloisForLFunctions.HTGeometry.IdentityTangentSubmodule
import GaloisForLFunctions.HTGeometry.JetHorizonAdditiveTorsorLaw

/-!
# Constant tangent directions see only the order-zero partials

A differential constant has no jets above order zero, so the linearisation of a differential
polynomial at a point, evaluated on a perturbation with constant entries, collapses to the
*algebraic* differential: only the partial derivatives with respect to the order-zero variables
contribute.

So the constant part of the Lie algebra of a differential algebraic group is the tangent space of
the underlying algebraic variety — the classical Lie algebra — cut out by finitely many linear
equations rather than by differential ones.

* `differentialJet_eq_zero_of_deriv_eq_zero`;
* `linearisationForm_const` — the collapse to the order-zero partials.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [CommRing C] [Differential C] {ι : Type*}

/-- A differential constant has no jets above order zero. -/
theorem differentialJet_eq_zero_of_deriv_eq_zero {c : C} (hc : c′ = 0) :
    ∀ n : ℕ, differentialJet (n + 1) c = 0
  | 0 => by rw [differentialJet_succ, differentialJet_zero, hc]
  | (n + 1) => by
      rw [differentialJet_succ, differentialJet_eq_zero_of_deriv_eq_zero hc n, map_zero]

/-- **The linearisation at a constant perturbation is the algebraic differential.** -/
theorem linearisationForm_const [DecidableEq ι] (p : ι → C) (P : DifferentialPolynomial ι C)
    (s : Finset (ι × ℕ)) {X : ι → C} (hX : ∀ i, (X i)′ = 0) :
    linearisationForm p P s X
      = ∑ v ∈ s.filter (fun v : ι × ℕ => v.2 = 0),
          differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v P) * X v.1 := by
  classical
  rw [linearisationForm, ← Finset.sum_filter_add_sum_filter_not s (fun v : ι × ℕ => v.2 = 0)]
  have htail : ∑ v ∈ s.filter (fun v : ι × ℕ => ¬ v.2 = 0),
      differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v P)
        * differentialJet v.2 (X v.1) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    simp only [Finset.mem_filter] at hv
    obtain ⟨m, hm⟩ : ∃ m, v.2 = m + 1 := ⟨v.2 - 1, by omega⟩
    rw [hm, differentialJet_eq_zero_of_deriv_eq_zero (hX v.1) m, mul_zero]
  rw [htail, add_zero]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp only [Finset.mem_filter] at hv
  rw [hv.2, differentialJet_zero]

end

end GaloisForLFunctions.HTGeometry
