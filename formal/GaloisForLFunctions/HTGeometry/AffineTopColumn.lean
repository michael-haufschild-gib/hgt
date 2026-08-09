import GaloisForLFunctions.HTGeometry.AffineFactorFamily
import GaloisForLFunctions.HTGeometry.PairHeadDegree

/-!
# The newest column of an affine factor family

At the newest coordinate the law's jet is `(∏_(j<m) fac j)·(lead m·X_(m+1) + cnst m)`, so it has
degree exactly one there and the law does not raise the degree.  The scalar operator sends a
logarithmic derivative to a Wronskian over a square, and the two Wronskians that occur are two
degrees below:

* the factor contributes `(δ lead)·cnst − lead·(δ cnst)` over `fac²`;
* a univariate head `g` contributes `lead·P(g) + cnst·W(g)` over `g²`.

Both are the same computation as for polynomial coefficients; only the coefficients have moved from
univariate factors to arbitrary functions of the older coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace AffineFam

variable (E : AffineFam)

/-! ## The jet at the newest coordinate -/

theorem jet_succ_eq (n : ℕ) :
    E.toPairFam.jet (n + 1) = E.toPairFam.jet n * E.fac n := E.toPairFam.jet_succ n

theorem topFree_jet_top {n m : ℕ} (h : n < m) : TopFree m (E.toPairFam.jet n) :=
  topFree_of_mem_coordField h (E.toPairFam.jet_mem_coordField (le_refl n))

theorem topDegLE_jet_top (n : ℕ) : TopDegLE (n + 1) 1 (E.toPairFam.jet (n + 1)) := by
  rw [E.jet_succ_eq n]
  have h := TopDegLE.mul (E.topFree_jet_top (by omega : n < n + 1)).topDegLE
    (E.topDegLE_fac_top n)
  simpa using h

/-- **The response at the newest coordinate.** -/
theorem response_top (n : ℕ) :
    E.toPairFam.response (n + 1) (n + 1) = E.toPairFam.jet n * E.lead n := by
  rw [PairFam.response, E.jet_succ_eq n, Derivation.leibniz,
    E.toPairFam.fpderiv_jet_of_gt (by omega : n < n + 1), E.fpderiv_fac_top n]
  simp only [smul_eq_mul]
  ring

/-! ## The law does not raise the newest degree -/

theorem topDegLE_law {n : ℕ} {d : ℤ} {f : CascadeField}
    (hmem : f ∈ coordField (n + 1)) (hf : TopDegLE (n + 1) d f) :
    TopDegLE (n + 1) d (E.toPairFam.law f) := by
  rw [E.toPairFam.law_eq_sum_coordField hmem]
  refine topDegLE_sum _ _ fun l hl => ?_
  have hlm : l ≤ n + 1 := by
    have := Finset.mem_range.mp hl
    omega
  rcases eq_or_lt_of_le hlm with rfl | hlt
  · have hder : TopDegLE (n + 1) (d - 1) (fpderiv (n + 1) f) := TopDegLE.fpderiv_top hf
    have hmul := TopDegLE.mul (E.topDegLE_jet_top n) hder
    refine TopDegLE.mono ?_ hmul
    omega
  · have hjet : TopFree (n + 1) (E.toPairFam.jet l) := E.topFree_jet_top hlt
    have hder : TopDegLE (n + 1) d (fpderiv l f) := TopDegLE.fpderiv_of_ne (by omega) hf
    have hmul := TopDegLE.mul hjet.topDegLE hder
    refine TopDegLE.mono ?_ hmul
    omega

theorem topShift_mem_coordField {m : ℕ} {G : CascadeField} (h : G ∈ coordField m) :
    E.toPairFam.topShift m G ∈ coordField m := by
  refine add_mem (E.toPairFam.law_mem_coordField h) (mul_mem ?_ h)
  exact E.toPairFam.response_mem_coordField (le_refl m)

theorem iterate_topShift_mem_coordField {m : ℕ} {G : CascadeField} (h : G ∈ coordField m)
    (r : ℕ) : ((E.toPairFam.topShift m)^[r]) G ∈ coordField m := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact E.topShift_mem_coordField ih

theorem topShift_topDegLE {n : ℕ} {d : ℤ} {G : CascadeField}
    (hmem : G ∈ coordField (n + 1)) (hG : TopDegLE (n + 1) d G) :
    TopDegLE (n + 1) d (E.toPairFam.topShift (n + 1) G) := by
  refine TopDegLE.add (E.topDegLE_law hmem hG) ?_
  rw [E.response_top n]
  have hfree : TopFree (n + 1) (E.toPairFam.jet n * E.lead n) :=
    TopFree.mul (E.topFree_jet_top (by omega)) (E.topFree_lead (by omega))
  have := TopDegLE.mul hfree.topDegLE hG
  simpa using this

/-! ## The factor's contribution -/

theorem lawLead_mem (n : ℕ) : E.toPairFam.law (E.lead n) ∈ coordField n :=
  E.toPairFam.law_mem_coordField (E.lead_mem_coordField (le_refl n))

theorem lawCnst_mem (n : ℕ) : E.toPairFam.law (E.cnst n) ∈ coordField n :=
  E.toPairFam.law_mem_coordField (E.cnst_mem_coordField (le_refl n))

theorem lawFac_eq (n : ℕ) :
    E.toPairFam.law (E.fac n)
      = E.lead n * E.toPairFam.jet (n + 1) + fx (n + 1) * E.toPairFam.law (E.lead n)
        + E.toPairFam.law (E.cnst n) := by
  rw [fac, map_add, Derivation.leibniz, PairFam.law_fx]
  simp only [smul_eq_mul]

theorem fpderiv_top_law_fac (n : ℕ) :
    fpderiv (n + 1) (E.toPairFam.law (E.fac n))
      = E.lead n * (E.toPairFam.jet n * E.lead n) + E.toPairFam.law (E.lead n) := by
  have hL : fpderiv (n + 1) (E.toPairFam.law (E.lead n)) = 0 := by
    have h := E.lawLead_mem n
    rw [mem_coordField_iff] at h
    exact h (n + 1) (by omega)
  have hC : fpderiv (n + 1) (E.toPairFam.law (E.cnst n)) = 0 := by
    have h := E.lawCnst_mem n
    rw [mem_coordField_iff] at h
    exact h (n + 1) (by omega)
  rw [E.lawFac_eq n, map_add, map_add, Derivation.leibniz, Derivation.leibniz, hL, hC,
    E.fpderiv_lead (by omega : n + 1 ≠ n), fpderiv_fx_self,
    show fpderiv (n + 1) (E.toPairFam.jet (n + 1)) = E.toPairFam.response (n + 1) (n + 1) from rfl,
    E.response_top n]
  simp only [smul_eq_mul]
  ring

/-- **The factor's contribution to the newest column is a Wronskian over the square.** -/
theorem topShift_logTerm (n : ℕ) :
    E.toPairFam.topShift (n + 1) (E.toPairFam.logTerm n (n + 1))
      = (E.toPairFam.law (E.lead n) * E.cnst n - E.lead n * E.toPairFam.law (E.cnst n))
          / (E.fac n) ^ 2 := by
  have hne : E.fac n ≠ 0 := E.fac_ne_zero n
  have hmem : E.fac n ∈ coordField (n + 1) := E.fac_mem_coordField n
  have hlt : E.toPairFam.logTerm n (n + 1)
      = fpderiv (n + 1) (E.fac n) / E.fac n := rfl
  rw [hlt, E.toPairFam.topShift_logDeriv hmem hne]
  congr 1
  rw [E.fpderiv_top_law_fac n, E.fpderiv_fac_top n, E.lawFac_eq n, E.jet_succ_eq n, fac]
  ring

theorem topDegLE_topShift_logTerm (n : ℕ) :
    TopDegLE (n + 1) (-2) (E.toPairFam.topShift (n + 1) (E.toPairFam.logTerm n (n + 1))) := by
  rw [E.topShift_logTerm n]
  have hinv : TopDegLE (n + 1) (-1) ((E.fac n)⁻¹) := E.topDegLE_inv_fac n
  have hsq : TopDegLE (n + 1) (-2) (((E.fac n) ^ 2)⁻¹) := by
    have h := TopDegLE.mul hinv hinv
    rw [← mul_inv, ← pow_two] at h
    refine TopDegLE.mono ?_ h
    omega
  have hnum : TopFree (n + 1)
      (E.toPairFam.law (E.lead n) * E.cnst n - E.lead n * E.toPairFam.law (E.cnst n)) := by
    refine TopFree.sub ?_ ?_
    · exact TopFree.mul (topFree_of_mem_coordField (by omega) (E.lawLead_mem n))
        (E.topFree_cnst (by omega))
    · exact TopFree.mul (E.topFree_lead (by omega))
        (topFree_of_mem_coordField (by omega) (E.lawCnst_mem n))
  rw [div_eq_mul_inv]
  have := TopDegLE.mul hnum.topDegLE hsq
  simpa using this

end AffineFam

end GaloisForLFunctions.HTGeometry
