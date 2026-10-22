import GaloisForLFunctions.HTGeometry.Critical.Source.ChartIntegrality
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Chart integrality over an arbitrary subring

The valuative form of the finiteness statement holds for every valuation subring containing the
marked observation chart, so the low coordinates are integral over *any* subring containing that
chart — the integral closure of a subring of a field being the intersection of the valuation
subrings above it.

`isIntegral_of_isIntegral_range` transfers integrality over the image subring of a ring
homomorphism back to the ring itself, by lifting a monic relation along the surjection onto the
image.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option synthInstance.maxHeartbeats 2000000

/-- Integrality over the image subring is integrality over the ring. -/
theorem isIntegral_of_isIntegral_range {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {x : S} (h : IsIntegral (algebraMap R S).range x) : IsIntegral R x := by
  obtain ⟨p, hmonic, heval⟩ := h
  have hsurj : Function.Surjective (algebraMap R S).rangeRestrict :=
    RingHom.rangeRestrict_surjective _
  have hlifts : p ∈ Polynomial.lifts (algebraMap R S).rangeRestrict :=
    Polynomial.lifts_iff_coeff_lifts p |>.mpr fun k => hsurj (p.coeff k)
  obtain ⟨q, hq, -, hqmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmonic
  refine ⟨q, hqmonic, ?_⟩
  have hcomp : (algebraMap R S) =
      ((algebraMap R S).range.subtype).comp (algebraMap R S).rangeRestrict := rfl
  rw [Polynomial.eval₂_eq_eval_map] at heval ⊢
  rw [hcomp, ← Polynomial.map_map, hq]
  exact heval

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

/-- **The critical low coordinates are integral over any subring containing the marked observation
chart.** -/
theorem criticalSourceLow_isIntegral_subring (hm : 0 < m) (hn : 0 < n)
    (R : Subring (criticalSourceField K m n))
    (hR : criticalObservationChart K hm hn ⊆ (R : Set (criticalSourceField K m n))) :
    (∀ i : Fin m, IsIntegral R (criticalSourceRaw K m n ⟨(i : ℕ), by omega⟩)) ∧
      (∀ j : Fin n, IsIntegral R (criticalSourceRecip K m n ⟨(j : ℕ), by omega⟩)) := by
  have hmem : ∀ x : criticalSourceField K m n,
      (∀ V : ValuationSubring (criticalSourceField K m n),
        (R : Set (criticalSourceField K m n)) ⊆ V.toSubring → x ∈ V) → IsIntegral R x := by
    intro x hx
    rw [← mem_integralClosure_iff]
    show x ∈ (integralClosure R (criticalSourceField K m n)).toSubring
    have hclosure : Subring.closure (R : Set (criticalSourceField K m n)) = R :=
      Subring.closure_eq R
    rw [← hclosure, ← iInf_valuationSubring_superset, Subring.mem_iInf]
    rintro ⟨V, hV⟩
    exact hx V hV
  constructor
  · intro i
    refine hmem _ fun V hV => ?_
    exact (criticalSourceLow_mem_valuationSubring K hm hn V
      (fun i' => hV (hR (Or.inl (Or.inl ⟨i', rfl⟩))))
      (fun j' => hV (hR (Or.inl (Or.inr ⟨j', rfl⟩))))
      (hV (hR (Or.inr (by simp)))) (hV (hR (Or.inr (by simp))))
      (criticalSourceRaw_atMarkedIndex_ne_zero K hm hn)
      (criticalSourceRecip_atMarkedIndex_ne_zero K hm hn)).1 i
  · intro j
    refine hmem _ fun V hV => ?_
    exact (criticalSourceLow_mem_valuationSubring K hm hn V
      (fun i' => hV (hR (Or.inl (Or.inl ⟨i', rfl⟩))))
      (fun j' => hV (hR (Or.inl (Or.inr ⟨j', rfl⟩))))
      (hV (hR (Or.inr (by simp)))) (hV (hR (Or.inr (by simp))))
      (criticalSourceRaw_atMarkedIndex_ne_zero K hm hn)
      (criticalSourceRecip_atMarkedIndex_ne_zero K hm hn)).2 j

end GaloisForLFunctions.HTGeometry
