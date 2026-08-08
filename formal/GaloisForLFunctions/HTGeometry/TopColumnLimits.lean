import GaloisForLFunctions.HTGeometry.CascadeChainRule

/-!
# The newest column of the logarithmic Jacobian, scaled and evaluated at infinity

The newest column is the orbit of `∂_m (logSum)` under the shifted operator `G ↦ δG + A_m·G`,
bordered above by the logarithmic derivative `Q_m'/Q_m`.  Its degrees separate:

* the border entry has degree `-1`, and `X_m·(Q_m'/Q_m)` tends to `deg Q_m`;
* every other entry has degree `-2`, because the first one is `(∏_{i<m}Q_i)·W(Q_m,v_m)/Q_m²` — the
  Wronskian is two degrees below the square — and the shifted operator does not raise the degree.

So after scaling the column by `X_m` its value at infinity is `(deg Q_m, 0, …, 0)`: exactly one
nonzero entry, in the border row.  That is the input the peel of the determinant consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Q v : ℕ → Polynomial ℂ}

/-! ## The coordinate itself -/

theorem topDegLE_fx (m : ℕ) : TopDegLE m 1 (fx m) := by
  have h := topDegLE_fact m Polynomial.X
  rw [fact_X, Polynomial.natDegree_X] at h
  simpa using h

/-! ## The shifted operator preserves the low subalgebra and the degree -/

theorem topResponse_mem_lowSub (Q v : ℕ → Polynomial ℂ) (m : ℕ) :
    topResponse Q v m ∈ lowSub Q v m := by
  rw [topResponse_eq]
  exact Subalgebra.mul_mem _ (prodHead_mem_lowSub Q v (le_refl m))
    (fact_mem_lowSub Q v (le_refl m) _)

theorem topDegLE_topResponse {m : ℕ} (hv : (v m).natDegree ≤ 1) :
    TopDegLE m 0 (topResponse (Q := Q) v m) := by
  rw [topResponse_eq]
  have h1 : TopDegLE m 0 (prodHead Q m) := TopFree.topDegLE (topFree_prodHead (le_refl m))
  have h2 : TopDegLE m ((v m).derivative.natDegree : ℤ) (fact (v m).derivative m) :=
    topDegLE_fact m _
  have hd : (v m).derivative.natDegree = 0 := by
    have h := Polynomial.natDegree_derivative_le (v m)
    omega
  rw [hd] at h2
  have := TopDegLE.mul h1 h2
  simpa using this

theorem topShift_mem_lowSub {m : ℕ} {G : CascadeField} (hmem : G ∈ lowSub Q v m) :
    topShift Q v m G ∈ lowSub Q v m := by
  rw [topShift]
  exact Subalgebra.add_mem _ (prodDerivation_mem_lowSub Q v hmem)
    (Subalgebra.mul_mem _ (topResponse_mem_lowSub Q v m) hmem)

theorem iterate_topShift_mem_lowSub {m : ℕ} {G : CascadeField} (hmem : G ∈ lowSub Q v m)
    (r : ℕ) : ((topShift Q v m)^[r]) G ∈ lowSub Q v m := by
  induction r with
  | zero => simpa using hmem
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact topShift_mem_lowSub ih

theorem topShift_topDegLE {m : ℕ} {d : ℤ} {G : CascadeField} (hv : (v m).natDegree ≤ 1)
    (hmem : G ∈ lowSub Q v m) (hG : TopDegLE m d G) :
    TopDegLE m d (topShift Q v m G) := by
  rw [topShift]
  refine TopDegLE.add (TopDegLE.prodDerivation hv hmem hG) ?_
  have h := TopDegLE.mul (topDegLE_topResponse (Q := Q) hv) hG
  simpa using h

/-! ## The first entry below the border -/

theorem fpderiv_logSum_top_mem_lowSub (Q v : ℕ → Polynomial ℂ) (n : ℕ) (hQ : Q (n + 1) ≠ 0) :
    fpderiv (n + 1) (logSum Q v (n + 2)) ∈ lowSub Q v (n + 1) := by
  rw [fpderiv_logSum_top Q v hQ, div_eq_mul_inv]
  refine Subalgebra.mul_mem _ (prodHead_mem_lowSub Q v (le_refl (n + 1))) ?_
  refine Subalgebra.mul_mem _ (fact_mem_lowSub Q v (le_refl (n + 1)) _) ?_
  rw [← inv_pow]
  exact Subalgebra.pow_mem _ (invQ_mem_lowSub Q v (le_refl (n + 1))) 2

/-- **The first entry below the border has degree `-2`.**  The Wronskian is two degrees below the
square of the denominator. -/
theorem topDegLE_fpderiv_logSum_top (n : ℕ) (hQ : Q (n + 1) ≠ 0)
    (hq : 1 ≤ (Q (n + 1)).natDegree) (hv : (v (n + 1)).natDegree = 1) :
    TopDegLE (n + 1) (-2) (fpderiv (n + 1) (logSum Q v (n + 2))) := by
  rw [fpderiv_logSum_top Q v hQ, div_eq_mul_inv, ← inv_pow]
  have h1 : TopDegLE (n + 1) 0 (prodHead Q (n + 1)) :=
    TopFree.topDegLE (topFree_prodHead (le_refl (n + 1)))
  have h2 : TopDegLE (n + 1)
      (((scaledLogWronskian (Q (n + 1)) (v (n + 1))).natDegree : ℤ))
      (fact (scaledLogWronskian (Q (n + 1)) (v (n + 1))) (n + 1)) :=
    topDegLE_fact _ _
  have h3 : TopDegLE (n + 1) (-((Q (n + 1)).natDegree : ℤ)) ((fact (Q (n + 1)) (n + 1))⁻¹) :=
    topDegLE_inv_fact _ hQ
  have h4 : TopDegLE (n + 1)
      (-((Q (n + 1)).natDegree : ℤ) + -((Q (n + 1)).natDegree : ℤ))
      ((fact (Q (n + 1)) (n + 1))⁻¹ ^ 2) := by
    have h := TopDegLE.mul h3 h3
    rw [pow_two]
    exact h
  have hW : (scaledLogWronskian (Q (n + 1)) (v (n + 1))).natDegree
      ≤ 2 * (Q (n + 1)).natDegree - 2 := natDegree_scaledLogWronskian_le_sub_two hq hv
  have hmul := TopDegLE.mul h1 (TopDegLE.mul h2 h4)
  refine TopDegLE.mono ?_ hmul
  omega

/-! ## The whole column -/

/-- **Every entry below the border has degree `-2`.** -/
theorem topDegLE_iterate_topShift (n : ℕ) (hQ : Q (n + 1) ≠ 0)
    (hq : 1 ≤ (Q (n + 1)).natDegree) (hv : (v (n + 1)).natDegree = 1) (r : ℕ) :
    TopDegLE (n + 1) (-2)
      (((topShift Q v (n + 1))^[r]) (fpderiv (n + 1) (logSum Q v (n + 2)))) := by
  have hmem0 : fpderiv (n + 1) (logSum Q v (n + 2)) ∈ lowSub Q v (n + 1) :=
    fpderiv_logSum_top_mem_lowSub Q v n hQ
  have hbase : TopDegLE (n + 1) (-2) (fpderiv (n + 1) (logSum Q v (n + 2))) :=
    topDegLE_fpderiv_logSum_top n hQ hq hv
  induction r with
  | zero => simpa using hbase
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      refine topShift_topDegLE (by omega) ?_ ih
      exact iterate_topShift_mem_lowSub hmem0 r

/-- **The scaled column has a single nonzero value at infinity.**  Below the border every entry
vanishes. -/
theorem topLim_fx_mul_iterate_topShift (n : ℕ) (hQ : Q (n + 1) ≠ 0)
    (hq : 1 ≤ (Q (n + 1)).natDegree) (hv : (v (n + 1)).natDegree = 1) (r : ℕ) :
    TopLim (n + 1)
      (fx (n + 1) * ((topShift Q v (n + 1))^[r]) (fpderiv (n + 1) (logSum Q v (n + 2)))) 0 := by
  rw [TopLim, sub_zero]
  have h := TopDegLE.mul (topDegLE_fx (n + 1)) (topDegLE_iterate_topShift n hQ hq hv r)
  simpa using h

/-- **The border entry of the scaled column tends to the degree.** -/
theorem topLim_fx_mul_border (n : ℕ) (hq : 1 ≤ (Q (n + 1)).natDegree) :
    TopLim (n + 1) (fx (n + 1) * logFactor (Q (n + 1)) (n + 1))
      (algebraMap ℂ CascadeField ((Q (n + 1)).natDegree : ℂ)) :=
  topLim_fx_mul_logFactor (n + 1) hq

end GaloisForLFunctions.HTGeometry
