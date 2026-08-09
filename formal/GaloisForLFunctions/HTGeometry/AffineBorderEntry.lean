import GaloisForLFunctions.HTGeometry.AffineHeadColumn

/-!
# The border entry of an affine factor family

The border entry at level `m` is the logarithmic gradient of the last factor times the head.  Its
image under the scalar operator has degree `−2` — the two Wronskians — and its own scaled value at
infinity is

`1 + (deg g₁ − deg g₂)`,

one from the factor, which is exactly linear in the newest coordinate, and the degree *difference*
from a rational head.  For a polynomial head that residue is a positive integer and never vanishes;
for a rational one it is an integer of either sign, and the peel needs it nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace AffineFam

variable (E : AffineFam)

theorem logBorder_top (n : ℕ) :
    E.toPairFam.logBorder (n + 1) (n + 1) = E.toPairFam.logTerm n (n + 1) := by
  rw [PairFam.logBorder, Finset.sum_eq_single n]
  · intro j hj hjm
    have hjlt : j < n := by
      have := Finset.mem_range.mp hj
      omega
    exact E.toPairFam.logTerm_eq_zero_of_ne (by omega) (by omega)
  · intro hnot
    exact absurd (Finset.mem_range.mpr (by omega : n < n + 1)) hnot

/-! ## The head's logarithmic gradient -/

theorem fpderiv_ratFact_self_div {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (m : ℕ) :
    fpderiv m (ratFact g₁ g₂ m) / ratFact g₁ g₂ m = logRatFactor g₁ g₂ m := by
  have hne : ratFact g₁ g₂ m ≠ 0 := ratFact_ne_zero hg₁ hg₂ m
  rw [derivation_ratFact (fpderiv m) hg₁ hg₂ m, fpderiv_fx_self, mul_one]
  field_simp

theorem headBorder_ratFact_self {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (m : ℕ) :
    E.toPairFam.headBorder (ratFact g₁ g₂ m) m m
      = E.toPairFam.logBorder m m + logRatFactor g₁ g₂ m := by
  rw [PairFam.headBorder, fpderiv_ratFact_self_div hg₁ hg₂ m]

theorem headBorder_ratFact_of_ne (g₁ g₂ : Polynomial ℂ) {m l : ℕ} (h : l ≠ m) :
    E.toPairFam.headBorder (ratFact g₁ g₂ m) m l = E.toPairFam.logBorder m l := by
  rw [PairFam.headBorder, fpderiv_ratFact_of_ne (fun hc => h hc.symm), zero_div, add_zero]

/-! ## The image of the border entry -/

/-- **The image of the border entry has degree `−2`.** -/
theorem topDegLE_topShift_headBorder {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (n : ℕ) :
    TopDegLE (n + 1) (-2)
      (E.toPairFam.topShift (n + 1)
        (E.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) (n + 1))) := by
  rw [E.headBorder_ratFact_self hg₁ hg₂, E.logBorder_top n, PairFam.topShift]
  have hsplit : E.toPairFam.law
        (E.toPairFam.logTerm n (n + 1) + logRatFactor g₁ g₂ (n + 1))
      + E.toPairFam.response (n + 1) (n + 1)
        * (E.toPairFam.logTerm n (n + 1) + logRatFactor g₁ g₂ (n + 1))
      = E.toPairFam.topShift (n + 1) (E.toPairFam.logTerm n (n + 1))
        + E.toPairFam.topShift (n + 1) (logRatFactor g₁ g₂ (n + 1)) := by
    simp only [PairFam.topShift, map_add]
    ring
  rw [hsplit]
  exact TopDegLE.add (E.topDegLE_topShift_logTerm n)
    (E.topDegLE_topShift_logRatFactor g₁ g₂ n)

/-! ## The residue at the border -/

/-- **The scaled border entry tends to `1 + deg g₁ − deg g₂`.** -/
theorem topLim_fx_mul_headBorder {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (n : ℕ) :
    TopLim (n + 1)
      (fx (n + 1) * E.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) (n + 1))
      (algebraMap ℂ CascadeField (1 + (g₁.natDegree : ℂ) - (g₂.natDegree : ℂ))) := by
  rw [E.headBorder_ratFact_self hg₁ hg₂, E.logBorder_top n, mul_add]
  have hsum := TopLim.add (E.topLim_fx_mul_logTerm_top n)
    (topLim_fx_mul_logRatFactor (n + 1) g₁ g₂)
  have hval : (1 : CascadeField)
      + algebraMap ℂ CascadeField ((g₁.natDegree : ℂ) - (g₂.natDegree : ℂ))
      = algebraMap ℂ CascadeField (1 + (g₁.natDegree : ℂ) - (g₂.natDegree : ℂ)) := by
    rw [map_sub, map_sub, map_add, map_one]
    ring
  rw [hval] at hsum
  exact hsum

/-- **The border entry has degree `−1`.** -/
theorem topDegLE_headBorder_top {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (n : ℕ) :
    TopDegLE (n + 1) (-1)
      (E.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) (n + 1)) := by
  rw [E.headBorder_ratFact_self hg₁ hg₂, E.logBorder_top n]
  refine TopDegLE.add ?_ (topDegLE_logRatFactor (n + 1) g₁ g₂)
  rw [PairFam.logTerm, toPairFam_fac, E.fpderiv_fac_top n, div_eq_mul_inv]
  have h := TopDegLE.mul (E.topFree_lead (by omega : n < n + 1)).topDegLE (E.topDegLE_inv_fac n)
  simpa using h

end AffineFam

end GaloisForLFunctions.HTGeometry
