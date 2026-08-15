import GaloisForLFunctions.RHTower.BarnesRemainderComplex
import GaloisForLFunctions.RHTower.EulerJetRealRestriction

/-!
# The ordinary jets of the Barnes remainder, read through the formal tail

Three identifications compose.  The complex Euler jets of the remainder restrict on the positive
axis to the real Euler jets; those are the weighted remainders of the Barnes expansion; and each of
those is, up to a sign, the corresponding Euler jet in the reciprocal variable.  Together with the
unitriangular passage from ordinary to Euler jets this expresses `z^m R^{(m)}` at a positive real
point through the functions whose Poincaré expansions are the Euler jets of the formal Barnes tail.
-/

open Complex Filter Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

variable {s : ℝ}

theorem ofReal_comp_barnesRemainderC (hs : 0 < s) :
    (fun y : ℝ => barnesRemainderC s ((y : ℝ) : ℂ)) = barnesEulerRemainder s 0 := by
  funext y
  exact barnesRemainderC_ofReal hs y

/-- **The complex Euler jets of the remainder are the weighted Barnes remainders.** -/
theorem cEulerDeriv_iterate_barnesRemainderC (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    cEulerDeriv^[k] (barnesRemainderC s) ((x : ℝ) : ℂ) = barnesEulerRemainder s k x := by
  have hmem : ((x : ℝ) : ℂ) ∈ HTGeometry.rightHalfPlane :=
    HTGeometry.ofReal_mem_rightHalfPlane hx
  have h := eulerDeriv_iterate_ofReal HTGeometry.isOpen_rightHalfPlane
    (analyticOnNhd_barnesRemainderC hs) k hmem
  rw [ofReal_comp_barnesRemainderC hs] at h
  rw [← h, ← barnesEulerRemainder_eq_iterate hs hne k hx]

/-- The weighted remainder is the Euler jet in the reciprocal variable. -/
theorem barnesEulerRemainder_eq_jet (s : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    barnesEulerRemainder s k x = ((-1 : ℂ)) ^ k * barnesEulerJet s k (1 / x) := by
  have hinv : 1 / (1 / x) = x := by
    field_simp
  rw [barnesEulerJet, hinv, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- **The ordinary jets of the Barnes remainder at a positive real point.** -/
theorem weightedJet_barnesRemainderC (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    weightedJet (barnesRemainderC s) m ((x : ℝ) : ℂ)
      = ∑ k ∈ Finset.range (m + 1),
          ((eulerJetCoeff m k : ℤ) : ℂ) * (((-1 : ℂ)) ^ k * barnesEulerJet s k (1 / x)) := by
  have hmem : ((x : ℝ) : ℂ) ∈ HTGeometry.rightHalfPlane :=
    HTGeometry.ofReal_mem_rightHalfPlane hx
  rw [weightedJet_eq_sum HTGeometry.isOpen_rightHalfPlane (analyticOnNhd_barnesRemainderC hs)
    m hmem]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cEulerDeriv_iterate_barnesRemainderC hs hne k hx, barnesEulerRemainder_eq_jet s k hx]

end

end RHTower
