import GaloisForLFunctions.HTGeometry.PairBorderShapeColumn

/-!
# The lower columns at infinity

Away from the newest coordinate the shifted operator degenerates, as that coordinate goes to
infinity, to the same operator one level down plus a single correction carried by the newest
column's residue.

Two things differ from the univariate law.  The response above the coordinate is the border row of
its own level, and that row is *not* free of the newest coordinate: the last placed factor is seen
by three consecutive coordinates.  Its limit is the border row one level down together with the
logarithmic derivative of the leading coefficient — which is exactly the head the class carries.
And the newest jet contributes `(∏_(i<m−1) p_i)·α(X_(m−1))·res`, because the factor is exactly linear
in the newest coordinate with leading coefficient `α(X_(m−1))`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ} {α β : Polynomial ℂ} {m' : ℕ}

/-! ## The law carries values at infinity -/

theorem TopLim.pairDerivation {u a : CascadeField} (hp : p m' = affinePair α β)
    (hmem : u - a ∈ coordField (m' + 1)) (h : TopLim (m' + 1) u a) :
    TopLim (m' + 1) (pairDerivation p u) (pairDerivation p a) := by
  rw [TopLim, ← map_sub]
  exact topDegLE_pairDerivation_coordField
    (by rw [hp]; exact degreeOf_one_affinePair α β) hmem h

/-! ## The border row's own limit -/

theorem fpderiv_lower_pairFactor_top (hp : p m' = affinePair α β) :
    fpderiv m' (pairFactor (p m') m')
      = fact α.derivative m' * fx (m' + 1) + fact β.derivative m' := by
  rw [pairFactor_top_eq hp, map_add, Derivation.leibniz, fpderiv_fact_self, fpderiv_fact_self,
    fpderiv_fx_of_ne (by omega : m' + 1 ≠ m')]
  simp only [smul_eq_mul]
  ring

/-- **The last factor's own logarithmic entry tends to the head.** -/
theorem topLim_pairLogTerm_self (hα : α ≠ 0) (hp : p m' = affinePair α β) :
    TopLim (m' + 1) (pairLogTerm p m' m') (logFactor α m') := by
  have hne : pairFactor (p m') m' ≠ 0 := pairFactor_top_ne_zero hα hp
  have hA : fact α m' ≠ 0 := fact_ne_zero hα m'
  have hval : pairLogTerm p m' m' - logFactor α m'
      = (fact α m' * fact β.derivative m' - fact α.derivative m' * fact β m')
        * ((fact α m')⁻¹ * (pairFactor (p m') m')⁻¹) := by
    rw [pairLogTerm, fpderiv_lower_pairFactor_top hp, logFactor]
    field_simp
    rw [pairFactor_top_eq hp]
    ring
  rw [TopLim, hval]
  have h1 : TopFree (m' + 1)
      (fact α m' * fact β.derivative m' - fact α.derivative m' * fact β m') :=
    TopFree.sub (TopFree.mul (topFree_fact (by omega) α) (topFree_fact (by omega) β.derivative))
      (TopFree.mul (topFree_fact (by omega) α.derivative) (topFree_fact (by omega) β))
  have h2 : TopFree (m' + 1) ((fact α m')⁻¹) := topFree_inv_fact (by omega) α
  have h3 : TopDegLE (m' + 1) (-1) ((pairFactor (p m') m')⁻¹) := by
    rw [hp]
    exact topDegLE_inv_pairFactor_affine hα β m'
  have h := TopDegLE.mul h1.topDegLE (TopDegLE.mul h2.topDegLE h3)
  simpa using h

/-- **The border row tends to the border row one level down, with the head.** -/
theorem topLim_pairLogBorder (hα : α ≠ 0) (hp : p m' = affinePair α β) {k : ℕ} (hk : k ≤ m') :
    TopLim (m' + 1) (pairLogBorder p (m' + 1) k) (headBorder p α m' k) := by
  rw [pairLogBorder_succ]
  rcases eq_or_lt_of_le hk with rfl | hlt
  · rw [headBorder_self]
    exact TopLim.add
      (topLim_of_topFree_sub (by
        rw [sub_self]
        exact topDegLE_zero _ _))
      (topLim_pairLogTerm_self hα hp)
  · rw [headBorder_of_ne (by omega), pairLogTerm_eq_zero_of_ne (by omega) (by omega), add_zero]
    exact topLim_const

/-! ## The newest jet against the newest entry -/

/-- **The newest jet times an entry of the newest column.** -/
theorem topLim_pairJet_mul (hp : p m' = affinePair α β) {u res : CascadeField}
    (hresfree : TopFree (m' + 1) res) (hu : TopDegLE (m' + 1) (-1) u)
    (hres : TopLim (m' + 1) (fx (m' + 1) * u) res) :
    TopLim (m' + 1) (pairJet p (m' + 1) * u) (pairJet p m' * fact α m' * res) := by
  have hsplit : pairJet p (m' + 1) * u
      = pairJet p m' * fact α m' * (fx (m' + 1) * u) + pairJet p m' * fact β m' * u := by
    rw [pairJet_succ, pairFactor_top_eq hp]
    ring
  rw [hsplit]
  have hJ : TopFree (m' + 1) (pairJet p m') := topFree_pairJet_top
  have hA : TopFree (m' + 1) (fact α m') := topFree_fact (by omega) α
  have hB : TopFree (m' + 1) (fact β m') := topFree_fact (by omega) β
  have h1 : TopLim (m' + 1) (pairJet p m' * fact α m' * (fx (m' + 1) * u))
      (pairJet p m' * fact α m' * res) :=
    TopLim.mul (TopFree.mul hJ hA) hresfree topLim_const hres
  have h2 : TopLim (m' + 1) (pairJet p m' * fact β m' * u) 0 := by
    rw [TopLim, sub_zero]
    have := TopDegLE.mul (TopFree.mul hJ hB).topDegLE hu
    simpa using this
  have hsum := TopLim.add h1 h2
  rw [add_zero] at hsum
  exact hsum

/-! ## The recursion of a lower column -/

/-- **The lower columns at infinity.**  The level drops, the head appears, and the starting vector
picks up the residue correction. -/
theorem topLim_pairGradShift_lower (hα : α ≠ 0) (hp : p m' = affinePair α β)
    (hne : ∀ j, pairFactor (p j) j ≠ 0) {k : ℕ} (hk : k ≤ m')
    {u L : ℕ → CascadeField} {res : CascadeField}
    (hsub : ∀ l, u l - L l ∈ coordField (m' + 1))
    (hLfree : ∀ l, TopFree (m' + 1) (L l))
    (hlim : ∀ l, TopLim (m' + 1) (u l) (L l))
    (hresfree : TopFree (m' + 1) res)
    (hutop : TopDegLE (m' + 1) (-1) (u (m' + 1)))
    (hres : TopLim (m' + 1) (fx (m' + 1) * u (m' + 1)) res) :
    TopLim (m' + 1) (pairGradShift p (m' + 1) u k)
      (pairGradShift p m' L k
        + headBorder p α m' k * (pairJet p m' * fact α m' * res)) := by
  have hsplit : pairGradShift p (m' + 1) u k
      = (pairDerivation p (u k)
          + ∑ l ∈ Finset.range (m' + 1), pairResponse p k l * u l)
        + pairResponse p k (m' + 1) * u (m' + 1) := by
    rw [pairGradShift, Finset.sum_range_succ]
    ring
  rw [hsplit, pairGradShift]
  refine TopLim.add (TopLim.add ?_ ?_) ?_
  · exact TopLim.pairDerivation hp (hsub k) (hlim k)
  · refine topLim_sum _ _ _ fun l hl => ?_
    have hlm : l < m' + 1 := Finset.mem_range.mp hl
    exact TopLim.mul (topFree_pairResponse hlm) (hLfree l) topLim_const (hlim l)
  · rw [pairResponse_eq_pairLogBorder hne k (m' + 1), mul_assoc]
    refine TopLim.mul ?_ (TopFree.mul (TopFree.mul topFree_pairJet_top
      (topFree_fact (by omega) α)) hresfree) ?_ ?_
    · exact topFree_of_mem_coordField (by omega) (headBorder_mem_coordField α m' k)
    · exact topLim_pairLogBorder hα hp hk
    · exact topLim_pairJet_mul hp hresfree hutop hres

end GaloisForLFunctions.HTGeometry
