import GaloisForLFunctions.HTGeometry.AffineBorderShape

/-!
# The lower columns of an affine factor family at infinity

Away from the newest coordinate the shifted operator degenerates, as that coordinate grows, to the
same operator one level down plus a correction carried by the newest column's residue.

Two things differ from a univariate law.  The response above a coordinate is the border row of its
own level, and that row is not free of the newest coordinate: the last factor is seen by three
consecutive coordinates.  Its limit is the border row one level down together with the logarithmic
derivative of the *leading coefficient* — which is exactly the head the class carries.  And the
newest jet contributes `(∏_(i<m−1) fac i)·lead_(m−1)·res`, because the factor is exactly linear in
the newest coordinate with that leading coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace AffineFam

variable (E : AffineFam)

/-! ## The law carries values at infinity -/

theorem law_topLim {n : ℕ} {u a : CascadeField} (hmem : u - a ∈ coordField (n + 1))
    (h : TopLim (n + 1) u a) :
    TopLim (n + 1) (E.toPairFam.law u) (E.toPairFam.law a) := by
  rw [TopLim, ← map_sub]
  exact E.topDegLE_law hmem h

/-! ## The factor's own logarithmic entry -/

theorem fpderiv_lower_fac (n : ℕ) :
    fpderiv n (E.fac n) = fpderiv n (E.lead n) * fx (n + 1) + fpderiv n (E.cnst n) := by
  rw [fac, map_add, Derivation.leibniz, fpderiv_fx_of_ne (by omega : n + 1 ≠ n)]
  simp only [smul_eq_mul]
  ring

/-- **The last factor's own logarithmic entry tends to the head.** -/
theorem topLim_logTerm_self (n : ℕ) :
    TopLim (n + 1) (E.toPairFam.logTerm n n) (fpderiv n (E.lead n) / E.lead n) := by
  have hne : E.fac n ≠ 0 := E.fac_ne_zero n
  have hA : E.lead n ≠ 0 := E.lead_ne_zero n
  have hval : E.toPairFam.logTerm n n - fpderiv n (E.lead n) / E.lead n
      = (fpderiv n (E.cnst n) * E.lead n - fpderiv n (E.lead n) * E.cnst n)
        * ((E.lead n)⁻¹ * (E.fac n)⁻¹) := by
    rw [PairFam.logTerm, toPairFam_fac, E.fpderiv_lower_fac n]
    field_simp
    rw [fac]
    ring
  rw [TopLim, hval]
  have h1 : TopFree (n + 1)
      (fpderiv n (E.cnst n) * E.lead n - fpderiv n (E.lead n) * E.cnst n) := by
    refine TopFree.sub ?_ ?_
    · exact TopFree.mul
        (topFree_of_mem_coordField (by omega)
          (fpderiv_mem_coordField n (E.cnst_mem_coordField (le_refl n))))
        (E.topFree_lead (by omega))
    · exact TopFree.mul
        (topFree_of_mem_coordField (by omega)
          (fpderiv_mem_coordField n (E.lead_mem_coordField (le_refl n))))
        (E.topFree_cnst (by omega))
  have h2 : TopFree (n + 1) ((E.lead n)⁻¹) := TopFree.inv (E.topFree_lead (by omega))
  have h3 : TopDegLE (n + 1) (-1) ((E.fac n)⁻¹) := E.topDegLE_inv_fac n
  have h := TopDegLE.mul h1.topDegLE (TopDegLE.mul h2.topDegLE h3)
  simpa using h

/-- **The border row tends to the border row one level down, with the head.** -/
theorem topLim_logBorder {n k : ℕ} (hk : k ≤ n) :
    TopLim (n + 1) (E.toPairFam.logBorder (n + 1) k)
      (E.toPairFam.headBorder (E.lead n) n k) := by
  rw [E.toPairFam.logBorder_succ]
  rcases eq_or_lt_of_le hk with rfl | hlt
  · rw [PairFam.headBorder]
    exact TopLim.add
      (topLim_of_topFree_sub (by
        rw [sub_self]
        exact topDegLE_zero _ _))
      (E.topLim_logTerm_self k)
  · have hz : fpderiv k (E.lead n) = 0 := E.fpderiv_lead (by omega)
    rw [PairFam.headBorder, hz, zero_div, add_zero,
      E.toPairFam.logTerm_eq_zero_of_ne (by omega) (by omega), add_zero]
    exact topLim_const

/-! ## The newest jet against the newest entry -/

/-- **The newest jet times an entry of the newest column.** -/
theorem topLim_jet_mul {n : ℕ} {u res : CascadeField}
    (hresfree : TopFree (n + 1) res) (hu : TopDegLE (n + 1) (-1) u)
    (hres : TopLim (n + 1) (fx (n + 1) * u) res) :
    TopLim (n + 1) (E.toPairFam.jet (n + 1) * u)
      (E.toPairFam.jet n * E.lead n * res) := by
  have hsplit : E.toPairFam.jet (n + 1) * u
      = E.toPairFam.jet n * E.lead n * (fx (n + 1) * u)
        + E.toPairFam.jet n * E.cnst n * u := by
    rw [E.jet_succ_eq n, fac]
    ring
  rw [hsplit]
  have hJ : TopFree (n + 1) (E.toPairFam.jet n) := E.topFree_jet_top (by omega)
  have hA : TopFree (n + 1) (E.lead n) := E.topFree_lead (by omega)
  have hB : TopFree (n + 1) (E.cnst n) := E.topFree_cnst (by omega)
  have h1 : TopLim (n + 1) (E.toPairFam.jet n * E.lead n * (fx (n + 1) * u))
      (E.toPairFam.jet n * E.lead n * res) :=
    TopLim.mul (TopFree.mul hJ hA) hresfree topLim_const hres
  have h2 : TopLim (n + 1) (E.toPairFam.jet n * E.cnst n * u) 0 := by
    rw [TopLim, sub_zero]
    have := TopDegLE.mul (TopFree.mul hJ hB).topDegLE hu
    simpa using this
  have hsum := TopLim.add h1 h2
  rw [add_zero] at hsum
  exact hsum

/-! ## The recursion of a lower column -/

/-- **The lower columns at infinity.** -/
theorem topLim_gradShift_lower {n k : ℕ} (hk : k ≤ n)
    {u L : ℕ → CascadeField} {res : CascadeField}
    (hsub : ∀ l, u l - L l ∈ coordField (n + 1))
    (hLfree : ∀ l, TopFree (n + 1) (L l))
    (hlim : ∀ l, TopLim (n + 1) (u l) (L l))
    (hresfree : TopFree (n + 1) res)
    (hutop : TopDegLE (n + 1) (-1) (u (n + 1)))
    (hres : TopLim (n + 1) (fx (n + 1) * u (n + 1)) res) :
    TopLim (n + 1) (E.toPairFam.gradShift (n + 1) u k)
      (E.toPairFam.gradShift n L k
        + E.toPairFam.headBorder (E.lead n) n k
          * (E.toPairFam.jet n * E.lead n * res)) := by
  have hsplit : E.toPairFam.gradShift (n + 1) u k
      = (E.toPairFam.law (u k)
          + ∑ l ∈ Finset.range (n + 1), E.toPairFam.response k l * u l)
        + E.toPairFam.response k (n + 1) * u (n + 1) := by
    rw [PairFam.gradShift, Finset.sum_range_succ]
    ring
  rw [hsplit, PairFam.gradShift]
  refine TopLim.add (TopLim.add ?_ ?_) ?_
  · exact E.law_topLim (hsub k) (hlim k)
  · refine topLim_sum _ _ _ fun l hl => ?_
    have hlm : l < n + 1 := Finset.mem_range.mp hl
    have hfree : TopFree (n + 1) (E.toPairFam.response k l) :=
      topFree_of_mem_coordField hlm (E.toPairFam.response_mem_coordField (le_refl l))
    exact TopLim.mul hfree (hLfree l) topLim_const (hlim l)
  · rw [E.toPairFam.response_eq_logBorder k (n + 1), mul_assoc]
    refine TopLim.mul ?_ (TopFree.mul (TopFree.mul (E.topFree_jet_top (by omega))
      (E.topFree_lead (by omega))) hresfree) ?_ ?_
    · exact topFree_of_mem_coordField (by omega)
        (E.toPairFam.headBorder_mem_coordField (E.lead_mem_coordField (le_refl n)) k)
    · exact E.topLim_logBorder hk
    · exact E.topLim_jet_mul hresfree hutop hres

end AffineFam

end GaloisForLFunctions.HTGeometry
