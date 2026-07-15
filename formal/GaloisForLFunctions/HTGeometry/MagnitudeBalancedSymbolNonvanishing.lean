import GaloisForLFunctions.HTGeometry.MagnitudeTopShiftSymbol

/-!
# Nonvanishing of balanced grouped symbols

Every nonempty balanced jet group has a nonzero permanent symbol. The proof
transports each canonical flattened order tuple to the common arity, detects a
maximal-order coefficient, and separates all other monomials by their derivative
multiplicity multisets and the conserved shift equation.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

theorem rename_permSymbolPoly_cast {a b : ℕ} (h : a = b) (μ : Fin a → ℕ) :
    MvPolynomial.rename (Equiv.cast (congrArg Fin h)) (permSymbolPoly μ) =
      permSymbolPoly (fun i => μ ((Equiv.cast (congrArg Fin h)).symm i)) := by
  subst b
  simp

theorem balancedJetSymbol_ne_zero {n N D : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {s : Fin D → ℕ}
    (hne : (balancedJetGroup n N D Q s).Nonempty) :
    balancedJetSymbol n N D Q s ≠ 0 := by
  classical
  let G := balancedJetGroup n N D Q s
  obtain ⟨m₀, hm₀G, hm₀max⟩ :=
    Finset.exists_max_image G (jetMonomialOrder n) hne
  let m0 : ↥G := ⟨m₀, hm₀G⟩
  let ν : ↥G → Fin D → ℕ := fun m i =>
    flatOrder (fun j => m.1 j.succ) ((balancedJetCast m).symm i)
  have hsum : ∀ m : ↥G, ∑ t, ν m t = jetMonomialOrder n m.1 := by
    intro m
    calc
      ∑ t, ν m t =
          ∑ t : Fin (jetMonomialDegree n m.1), flatOrder (fun j => m.1 j.succ) t :=
        Equiv.sum_comp (balancedJetCast m).symm (flatOrder (fun j => m.1 j.succ))
      _ = jetMonomialOrder n m.1 := by
        simpa [jetMonomialOrder] using (flatOrder_sum (fun j => m.1 j.succ))
  have hOle : ∀ m ∈ G.attach, ∑ t, ν m t ≤ ∑ t, ν m0 t := by
    intro m hm
    rw [hsum m, hsum m0]
    exact hm₀max m.1 m.2
  have hmulti : ∀ m : ↥G,
      Multiset.map (ν m) Finset.univ.val =
        ∑ j : Fin (n + 1), Multiset.replicate (m.1 j.succ) (j : ℕ) := by
    intro m
    let e := balancedJetCast m
    rw [show (Finset.univ : Finset (Fin D)).val = Multiset.map e
        (Finset.univ : Finset (Fin (jetMonomialDegree n m.1))).val from by
      rw [← Finset.map_univ_equiv e]
      rfl]
    rw [Multiset.map_map]
    rw [show ν m ∘ e = flatOrder (fun j => m.1 j.succ) from by
      funext i
      simp [ν, e]]
    exact flatOrder_multiset (fun j => m.1 j.succ)
  have hdist : ∀ m ∈ G.attach,
      (∃ σ : Equiv.Perm (Fin D), ∀ j, ν m j = ν m0 (σ j)) → m = m0 := by
    rintro m hm ⟨σ, hσ⟩
    apply Subtype.ext
    have hmap : Multiset.map (ν m) Finset.univ.val =
        Multiset.map (ν m0) Finset.univ.val := by
      have hσmap : Multiset.map (⇑σ) Finset.univ.val = Finset.univ.val := by
        have h := congrArg Finset.val (Finset.map_univ_equiv σ)
        simpa only [Finset.map_val, Equiv.coe_toEmbedding] using h
      have hfun : ν m = ν m0 ∘ σ := funext hσ
      rw [hfun, ← Multiset.map_map, hσmap]
    rw [hmulti m, hmulti m0] at hmap
    have hexp : ∀ j : Fin (n + 1), m.1 j.succ = m0.1 j.succ := by
      intro j
      have hcnt := congrArg (Multiset.count (j : ℕ)) hmap
      simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Fin.val_injective.eq_iff] at hcnt
      exact hcnt
    have hord : jetMonomialOrder n m.1 = jetMonomialOrder n m0.1 := by
      rw [jetMonomialOrder]
      exact Finset.sum_congr rfl fun j _ => by rw [hexp j]
    have hmEq := ((Finset.mem_filter.mp m.2).2).2.2
    have hm0Eq := ((Finset.mem_filter.mp m0.2).2).2.2
    have hmN := ((Finset.mem_filter.mp m.2).2).1
    have hm0N := ((Finset.mem_filter.mp m0.2).2).1
    have hz : m.1 0 = m0.1 0 := by omega
    ext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
    · exact hz
    · exact hexp k
  have hc : MvPolynomial.coeff m0.1 Q ≠ 0 :=
    MvPolynomial.mem_support_iff.mp (Finset.mem_filter.mp m0.2).1
  have hne' := combination_permSymbolPolyC_maxorder_ne_zero G.attach ν
    (fun m : ↥G => MvPolynomial.coeff m.1 Q) (Finset.mem_attach G m0) hOle hdist hc
  intro hzero
  apply hne'
  calc
    ∑ m ∈ G.attach, MvPolynomial.C (MvPolynomial.coeff m.1 Q) *
        (permSymbolPoly (ν m)).map (Int.castRingHom ℂ) =
        balancedJetSymbol n N D Q s := by
      rw [balancedJetSymbol]
      apply Finset.sum_congr rfl
      intro m hm
      congr 1
      simp only [ν, balancedJetCast]
      rw [← rename_permSymbolPoly_cast (balancedJetGroup_degree m)
        (flatOrder (fun j => m.1 j.succ))]
      exact MvPolynomial.map_rename (Int.castRingHom ℂ) (balancedJetCast m)
        (permSymbolPoly (flatOrder (fun j => m.1 j.succ)))
    _ = 0 := hzero

/-- When the level/source data select the fixed-shift group of an anchor, the balanced grouped
symbol is the corresponding top-shift symbol. -/
theorem balancedJetSymbol_eq_topShiftJetSymbol {n N : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {anchor : Fin (n + 2) →₀ ℕ}
    (s : Fin (jetMonomialDegree n anchor) → ℕ)
    (hG : balancedJetGroup n N (jetMonomialDegree n anchor) Q s =
      topShiftJetGroup n Q anchor) :
    balancedJetSymbol n N (jetMonomialDegree n anchor) Q s =
      topShiftJetSymbol n Q anchor := by
  classical
  rw [balancedJetSymbol, topShiftJetSymbol]
  let fwd : ↥(balancedJetGroup n N (jetMonomialDegree n anchor) Q s) →
      ↥(topShiftJetGroup n Q anchor) := fun m =>
    ⟨m.1, by rw [← hG]; exact m.2⟩
  let back : ↥(topShiftJetGroup n Q anchor) →
      ↥(balancedJetGroup n N (jetMonomialDegree n anchor) Q s) := fun m =>
    ⟨m.1, by rw [hG]; exact m.2⟩
  refine Finset.sum_bij' (fun m _ => fwd m) (fun m _ => back m) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    exact Finset.mem_attach _ _
  · intro m hm
    exact Finset.mem_attach _ _
  · intro m hm
    apply Subtype.ext
    rfl
  · intro m hm
    apply Subtype.ext
    rfl
  · intro m hm
    congr 1
    simp only [fwd]
    calc
      MvPolynomial.rename (balancedJetCast m)
          ((permSymbolPoly (flatOrder (fun j => m.1 j.succ))).map (Int.castRingHom ℂ)) =
          (MvPolynomial.rename (balancedJetCast m)
            (permSymbolPoly (flatOrder (fun j => m.1 j.succ)))).map
              (Int.castRingHom ℂ) :=
        (MvPolynomial.map_rename (Int.castRingHom ℂ) (balancedJetCast m)
          (permSymbolPoly (flatOrder (fun j => m.1 j.succ)))).symm
      _ = (permSymbolPoly (fun i => flatOrder (fun j => m.1 j.succ)
            ((balancedJetCast m).symm i))).map (Int.castRingHom ℂ) := by
        exact congrArg (MvPolynomial.map (Int.castRingHom ℂ))
          (by simpa only [balancedJetCast] using
            (rename_permSymbolPoly_cast (balancedJetGroup_degree m)
              (flatOrder (fun j => m.1 j.succ))))
      _ = (permSymbolPoly (topShiftJetOrder (fwd m))).map (Int.castRingHom ℂ) := by
        congr 2

end

end GaloisForLFunctions
