import GaloisForLFunctions.HTGeometry.PairTopColumn

/-!
# The degrees of the newest column

The border entry of the newest column has degree `−1` and its scaled value at infinity is
`1 + deg g`: one from the last placed factor, which is exactly linear in the newest coordinate, and
`deg g` from the head.  Every entry below the border has degree `−2`, because the scalar operator
sends the border entry to a Wronskian over a square and then does not raise the degree.

That is the whole input the peel of the determinant consumes at each level.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ} {α β : Polynomial ℂ} {m' : ℕ}

/-! ## The law does not raise the degree, on the subfield -/

theorem topDegLE_pairDerivation_coordField {n : ℕ} {d : ℤ} {f : CascadeField}
    (hd : MvPolynomial.degreeOf 1 (p n) ≤ 1)
    (hmem : f ∈ coordField (n + 1)) (hf : TopDegLE (n + 1) d f) :
    TopDegLE (n + 1) d (pairDerivation p f) := by
  rw [pairDerivation_eq_sum_coordField hmem]
  refine topDegLE_sum _ _ fun l hl => ?_
  have hlm : l ≤ n + 1 := by
    have := Finset.mem_range.mp hl
    omega
  rcases eq_or_lt_of_le hlm with rfl | hlt
  · have hjet : TopDegLE (n + 1) ((MvPolynomial.degreeOf 1 (p n) : ℤ)) (pairJet p (n + 1)) :=
      topDegLE_pairJet_top n
    have hder : TopDegLE (n + 1) (d - 1) (fpderiv (n + 1) f) := TopDegLE.fpderiv_top hf
    have hmul := TopDegLE.mul hjet hder
    refine TopDegLE.mono ?_ hmul
    have : ((MvPolynomial.degreeOf 1 (p n) : ℕ) : ℤ) ≤ 1 := by exact_mod_cast hd
    omega
  · have hjet : TopFree (n + 1) (pairJet p l) := topFree_pairJet hlt
    have hder : TopDegLE (n + 1) d (fpderiv l f) := TopDegLE.fpderiv_of_ne (by omega) hf
    have hmul := TopDegLE.mul (TopFree.topDegLE hjet) hder
    refine TopDegLE.mono ?_ hmul
    omega

/-! ## The scalar operator preserves the subfield and the degree -/

theorem pairTopShift_mem_coordField {m : ℕ} {G : CascadeField} (h : G ∈ coordField m) :
    pairTopShift p m G ∈ coordField m := by
  refine add_mem (pairDerivation_mem_coordField h) (mul_mem ?_ h)
  rw [pairResponse]
  exact fpderiv_mem_coordField m (pairJet_mem_coordField (le_refl m))

theorem iterate_pairTopShift_mem_coordField {m : ℕ} {G : CascadeField} (h : G ∈ coordField m)
    (r : ℕ) : ((pairTopShift p m)^[r]) G ∈ coordField m := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact pairTopShift_mem_coordField ih

theorem topFree_pairJet_top : TopFree (m' + 1) (pairJet p m') :=
  topFree_of_mem_coordField (by omega) (pairJet_mem_coordField (le_refl m'))

theorem pairTopShift_topDegLE {d : ℤ} {G : CascadeField} (hp : p m' = affinePair α β)
    (hmem : G ∈ coordField (m' + 1)) (hG : TopDegLE (m' + 1) d G) :
    TopDegLE (m' + 1) d (pairTopShift p (m' + 1) G) := by
  refine TopDegLE.add (topDegLE_pairDerivation_coordField ?_ hmem hG) ?_
  · rw [hp]
    exact degreeOf_one_affinePair α β
  · rw [pairResponse_top hp]
    have hfree : TopFree (m' + 1) (pairJet p m' * fact α m') :=
      TopFree.mul topFree_pairJet_top (topFree_fact (by omega) α)
    have := TopDegLE.mul hfree.topDegLE hG
    simpa using this

/-! ## The border entry -/

theorem pairLogBorder_top (p : ℕ → MvPolynomial (Fin 2) ℂ) (m' : ℕ) :
    pairLogBorder p (m' + 1) (m' + 1) = pairLogTerm p m' (m' + 1) := by
  rw [pairLogBorder, Finset.sum_eq_single m']
  · intro j hj hjm
    have hjlt : j < m' := by
      have := Finset.mem_range.mp hj
      omega
    exact pairLogTerm_eq_zero_of_ne (by omega) (by omega)
  · intro hnot
    exact absurd (Finset.mem_range.mpr (by omega : m' < m' + 1)) hnot

theorem fact_zero_eq (m : ℕ) : fact (0 : Polynomial ℂ) m = 0 := by
  rw [fact, univFactor, map_zero, map_zero]

theorem logFactor_eq_zero_of_natDegree_zero {g : Polynomial ℂ} (h : g.natDegree = 0) (m : ℕ) :
    logFactor g m = 0 := by
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp h
  rw [logFactor, ← hc, Polynomial.derivative_C, fact_zero_eq, zero_div]

/-! ## The two contributions have degree `−2` -/

theorem topDegLE_pairTopShift_pairLogTerm (hα : α ≠ 0) (hp : p m' = affinePair α β) :
    TopDegLE (m' + 1) (-2) (pairTopShift p (m' + 1) (pairLogTerm p m' (m' + 1))) := by
  rw [pairTopShift_pairLogTerm hα hp]
  have hne : pairFactor (p m') m' ≠ 0 := pairFactor_top_ne_zero hα hp
  have hinv : TopDegLE (m' + 1) (-1) ((pairFactor (p m') m')⁻¹) := by
    rw [hp]
    exact topDegLE_inv_pairFactor_affine hα β m'
  have hsq : TopDegLE (m' + 1) (-2) (((pairFactor (p m') m') ^ (2 : ℕ))⁻¹) := by
    have := TopDegLE.mul hinv hinv
    rw [← mul_inv, ← pow_two] at this
    refine TopDegLE.mono ?_ this
    omega
  have hnum : TopFree (m' + 1)
      (pairJet p m' * fact (α.derivative * β - α * β.derivative) m') :=
    TopFree.mul (topFree_pairJet_top (p := p) (m' := m'))
      (topFree_fact (m := m' + 1) (j := m') (by omega)
        (α.derivative * β - α * β.derivative))
  rw [div_eq_mul_inv]
  have := TopDegLE.mul hnum.topDegLE hsq
  simpa using this

theorem topDegLE_pairTopShift_logFactor_head {g : Polynomial ℂ} (hg : g ≠ 0)
    (hp : p m' = affinePair α β) :
    TopDegLE (m' + 1) (-2) (pairTopShift p (m' + 1) (logFactor g (m' + 1))) := by
  rcases eq_or_ne g.derivative 0 with hgd | hgd
  · have hzero : logFactor g (m' + 1) = 0 := by
      rw [logFactor, hgd, fact_zero_eq, zero_div]
    rw [hzero, pairTopShift]
    simp only [map_zero, mul_zero, add_zero]
    exact topDegLE_zero _ _
  · have hdeg : 1 ≤ g.natDegree := by
      by_contra hc
      have hg0 : g.natDegree = 0 := by omega
      obtain ⟨c, hc'⟩ := Polynomial.natDegree_eq_zero.mp hg0
      exact hgd (by rw [← hc', Polynomial.derivative_C])
    rw [pairTopShift_logFactor_head hg hp]
    have hA : TopFree (m' + 1) (fact α m') := topFree_fact (by omega) α
    have hB : TopFree (m' + 1) (fact β m') := topFree_fact (by omega) β
    have hP : TopDegLE (m' + 1) (2 * (g.natDegree : ℤ) - 2)
        (fact (headDefect g) (m' + 1)) := by
      refine TopDegLE.mono ?_ (topDegLE_fact (m' + 1) (headDefect g))
      have := natDegree_headDefect_le hdeg
      omega
    have hW : TopDegLE (m' + 1) (2 * (g.natDegree : ℤ) - 2) (fact (headWr g) (m' + 1)) := by
      refine TopDegLE.mono ?_ (topDegLE_fact (m' + 1) (headWr g))
      have := natDegree_headWr_le hdeg
      omega
    have hGinv : TopDegLE (m' + 1) (-(2 * (g.natDegree : ℤ)))
        ((fact g (m' + 1) ^ (2 : ℕ))⁻¹) := by
      have h1 := topDegLE_inv_fact (m' + 1) hg
      have h2 := TopDegLE.mul h1 h1
      rw [← mul_inv, ← pow_two] at h2
      refine TopDegLE.mono ?_ h2
      omega
    have h1 : TopDegLE (m' + 1) (2 * (g.natDegree : ℤ) - 2)
        (fact α m' * fact (headDefect g) (m' + 1)) := by
      have := TopDegLE.mul hA.topDegLE hP
      simpa using this
    have h2 : TopDegLE (m' + 1) (2 * (g.natDegree : ℤ) - 2)
        (fact β m' * fact (headWr g) (m' + 1)) := by
      have := TopDegLE.mul hB.topDegLE hW
      simpa using this
    have hnum : TopDegLE (m' + 1) (2 * (g.natDegree : ℤ) - 2)
        (pairJet p m' * (fact α m' * fact (headDefect g) (m' + 1)
          + fact β m' * fact (headWr g) (m' + 1))) := by
      have hjfree : TopFree (m' + 1) (pairJet p m') := topFree_pairJet_top
      have := TopDegLE.mul hjfree.topDegLE (TopDegLE.add h1 h2)
      simpa using this
    rw [div_eq_mul_inv]
    have := TopDegLE.mul hnum hGinv
    refine TopDegLE.mono ?_ this
    omega

/-- **The image of the border entry has degree `−2`.** -/
theorem topDegLE_pairTopShift_headBorder (hα : α ≠ 0) {g : Polynomial ℂ} (hg : g ≠ 0)
    (hp : p m' = affinePair α β) :
    TopDegLE (m' + 1) (-2) (pairTopShift p (m' + 1) (headBorder p g (m' + 1) (m' + 1))) := by
  rw [headBorder_self, pairLogBorder_top, pairTopShift_add]
  exact TopDegLE.add (topDegLE_pairTopShift_pairLogTerm hα hp)
    (topDegLE_pairTopShift_logFactor_head hg hp)

/-! ## The residue at the border -/

/-- **The scaled border entry tends to `1 + deg g`.** -/
theorem topLim_fx_mul_headBorder (hα : α ≠ 0) (g : Polynomial ℂ) (hp : p m' = affinePair α β) :
    TopLim (m' + 1) (fx (m' + 1) * headBorder p g (m' + 1) (m' + 1))
      (algebraMap ℂ CascadeField (1 + (g.natDegree : ℂ))) := by
  rw [headBorder_self, pairLogBorder_top, mul_add]
  have h1 : TopLim (m' + 1) (fx (m' + 1) * pairLogTerm p m' (m' + 1)) 1 :=
    topLim_fx_mul_pairLogTerm_affine hα β m' hp
  have h2 : TopLim (m' + 1) (fx (m' + 1) * logFactor g (m' + 1))
      (algebraMap ℂ CascadeField (g.natDegree : ℂ)) := by
    rcases Nat.eq_zero_or_pos g.natDegree with h0 | h0
    · rw [logFactor_eq_zero_of_natDegree_zero h0, mul_zero, h0]
      simp only [Nat.cast_zero, map_zero]
      exact topLim_const
    · exact topLim_fx_mul_logFactor (m' + 1) h0
  have hsum := TopLim.add h1 h2
  rw [map_add, map_one]
  exact hsum

end GaloisForLFunctions.HTGeometry
