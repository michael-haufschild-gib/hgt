import GaloisForLFunctions.HTGeometry.MagnitudeBalancedWeight
import GaloisForLFunctions.HTGeometry.DistinctIndexComplexSurvival

/-!
# Nonvanishing top-degree fixed-shift symbols

For a monomial anchor, collect every differential monomial with the same jet
degree and the same coefficient-index shift. Canonical flattening turns that group
into a permanent-symbol polynomial. Distinct derivative multiplicity profiles and
a maximal-order coefficient prove that this polynomial is nonzero.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

/-- The canonical flattened order tuple has exactly the multiplicity profile of the jet powers. -/
theorem flatOrder_multiset {n : ℕ} (e : Fin (n + 1) → ℕ) :
    Multiset.map (flatOrder e)
        (Finset.univ : Finset (Fin (∑ j, e j))).val =
      ∑ j : Fin (n + 1), Multiset.replicate (e j) (j : ℕ) := by
  classical
  set eqv : Fin (∑ j, e j) ≃ (Σ j : Fin (n + 1), Fin (e j)) :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_sigma]; simp)).symm with heqv
  rw [show (Finset.univ : Finset (Fin (∑ j, e j))).val =
      Multiset.map eqv.symm
        (Finset.univ : Finset (Σ j : Fin (n + 1), Fin (e j))).val from by
      rw [← Finset.map_univ_equiv eqv.symm]
      rfl]
  rw [Multiset.map_map]
  rw [show flatOrder e ∘ eqv.symm =
      fun p : Σ j : Fin (n + 1), Fin (e j) => (p.1 : ℕ) from by
      funext p
      simp [flatOrder, eqv]]
  ext k
  rw [Multiset.count_map, Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [← Finset.filter_val, Finset.card_val, Finset.card_filter, ← Finset.univ_sigma_univ,
    Finset.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : k = (j : ℕ) <;> simp [h, eq_comm]

def topShiftJetGroup (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (anchor : Fin (n + 2) →₀ ℕ) : Finset (Fin (n + 2) →₀ ℕ) :=
  Q.support.filter fun m =>
    jetMonomialDegree n m = jetMonomialDegree n anchor ∧
      m 0 + jetMonomialOrder n anchor = anchor 0 + jetMonomialOrder n m

theorem anchor_mem_topShiftJetGroup {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} (ha : anchor ∈ Q.support) :
    anchor ∈ topShiftJetGroup n Q anchor := by
  rw [topShiftJetGroup, Finset.mem_filter]
  exact ⟨ha, rfl, rfl⟩

theorem topShiftJetGroup_degree {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} (m : ↥(topShiftJetGroup n Q anchor)) :
    jetMonomialDegree n m.1 = jetMonomialDegree n anchor :=
  (Finset.mem_filter.mp m.2).2.1

noncomputable def topShiftJetCast {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} (m : ↥(topShiftJetGroup n Q anchor)) :
    Fin (jetMonomialDegree n m.1) ≃ Fin (jetMonomialDegree n anchor) :=
  Equiv.cast (congrArg Fin (topShiftJetGroup_degree m))

noncomputable def topShiftJetOrder {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} (m : ↥(topShiftJetGroup n Q anchor)) :
    Fin (jetMonomialDegree n anchor) → ℕ :=
  fun i => flatOrder (fun j => m.1 j.succ) ((topShiftJetCast m).symm i)

noncomputable def topShiftJetSymbol (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (anchor : Fin (n + 2) →₀ ℕ) :
    MvPolynomial (Fin (jetMonomialDegree n anchor)) ℂ :=
  ∑ m ∈ (topShiftJetGroup n Q anchor).attach,
    MvPolynomial.C (MvPolynomial.coeff m.1 Q) *
      (permSymbolPoly (topShiftJetOrder m)).map (Int.castRingHom ℂ)

theorem topShiftJetOrder_multiset {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} (m : ↥(topShiftJetGroup n Q anchor)) :
    Multiset.map (topShiftJetOrder m)
        (Finset.univ : Finset (Fin (jetMonomialDegree n anchor))).val =
      ∑ j : Fin (n + 1), Multiset.replicate (m.1 j.succ) (j : ℕ) := by
  set e := topShiftJetCast m with he
  rw [show (Finset.univ : Finset (Fin (jetMonomialDegree n anchor))).val =
      Multiset.map e
        (Finset.univ : Finset (Fin (jetMonomialDegree n m.1))).val from by
      rw [← Finset.map_univ_equiv e]
      rfl]
  rw [Multiset.map_map]
  rw [show topShiftJetOrder m ∘ e = flatOrder (fun j => m.1 j.succ) from by
    funext i
    simp [topShiftJetOrder, e]]
  exact flatOrder_multiset (fun j => m.1 j.succ)

/-- The permanent symbol of every nonempty fixed-degree/fixed-shift group is nonzero. -/
theorem topShiftJetSymbol_ne_zero {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ} (ha : anchor ∈ Q.support) :
    topShiftJetSymbol n Q anchor ≠ 0 := by
  classical
  let G := topShiftJetGroup n Q anchor
  have haG : anchor ∈ G := anchor_mem_topShiftJetGroup ha
  obtain ⟨m₀, hm₀G, hm₀max⟩ :=
    Finset.exists_max_image G (jetMonomialOrder n) ⟨anchor, haG⟩
  let m0 : ↥G := ⟨m₀, hm₀G⟩
  have hOle : ∀ m ∈ G.attach,
      ∑ t, topShiftJetOrder m t ≤ ∑ t, topShiftJetOrder m0 t := by
    intro m hm
    rw [show ∑ t, topShiftJetOrder m t = jetMonomialOrder n m.1 by
      calc
        ∑ t, topShiftJetOrder m t =
            ∑ t : Fin (jetMonomialDegree n m.1), flatOrder (fun j => m.1 j.succ) t :=
          Equiv.sum_comp (topShiftJetCast m).symm
            (flatOrder (fun j => m.1 j.succ))
        _ = jetMonomialOrder n m.1 := by
          simpa [jetMonomialOrder] using (flatOrder_sum (fun j => m.1 j.succ))]
    rw [show ∑ t, topShiftJetOrder m0 t = jetMonomialOrder n m0.1 by
      calc
        ∑ t, topShiftJetOrder m0 t =
            ∑ t : Fin (jetMonomialDegree n m0.1), flatOrder (fun j => m0.1 j.succ) t :=
          Equiv.sum_comp (topShiftJetCast m0).symm
            (flatOrder (fun j => m0.1 j.succ))
        _ = jetMonomialOrder n m0.1 := by
          simpa [jetMonomialOrder] using (flatOrder_sum (fun j => m0.1 j.succ))]
    exact hm₀max m.1 m.2
  have hdist : ∀ m ∈ G.attach,
      (∃ σ : Equiv.Perm (Fin (jetMonomialDegree n anchor)),
        ∀ j, topShiftJetOrder m j = topShiftJetOrder m0 (σ j)) → m = m0 := by
    rintro m hm ⟨σ, hσ⟩
    apply Subtype.ext
    have hmulti : Multiset.map (topShiftJetOrder m) Finset.univ.val =
        Multiset.map (topShiftJetOrder m0) Finset.univ.val := by
      have hσmap : Multiset.map (⇑σ) Finset.univ.val = Finset.univ.val := by
        have h := congrArg Finset.val (Finset.map_univ_equiv σ)
        simpa only [Finset.map_val, Equiv.coe_toEmbedding] using h
      have hfun : topShiftJetOrder m = topShiftJetOrder m0 ∘ σ := funext hσ
      rw [hfun, ← Multiset.map_map, hσmap]
    rw [topShiftJetOrder_multiset m, topShiftJetOrder_multiset m0] at hmulti
    have hexp : ∀ j : Fin (n + 1), m.1 j.succ = m0.1 j.succ := by
      intro j
      have hcnt := congrArg (Multiset.count (j : ℕ)) hmulti
      simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Fin.val_injective.eq_iff] at hcnt
      exact hcnt
    have hord : jetMonomialOrder n m.1 = jetMonomialOrder n m0.1 := by
      rw [jetMonomialOrder]
      exact Finset.sum_congr rfl fun j _ => by rw [hexp j]
    have hmshift := (Finset.mem_filter.mp m.2).2.2
    have hm0shift := (Finset.mem_filter.mp m0.2).2.2
    have hz : m.1 0 = m0.1 0 := by omega
    ext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
    · exact hz
    · exact hexp k
  have hc : MvPolynomial.coeff m0.1 Q ≠ 0 :=
    MvPolynomial.mem_support_iff.mp (Finset.mem_filter.mp m0.2).1
  simpa [topShiftJetSymbol, G, m0] using
    combination_permSymbolPolyC_maxorder_ne_zero G.attach topShiftJetOrder
      (fun m : ↥G => MvPolynomial.coeff m.1 Q) (Finset.mem_attach G m0)
      hOle hdist hc

end

end GaloisForLFunctions

