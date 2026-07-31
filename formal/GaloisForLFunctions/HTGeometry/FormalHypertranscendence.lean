import GaloisForLFunctions.HTGeometry.DistinctIndexComplexSurvival
import GaloisForLFunctions.HTGeometry.MagnitudeADEBridge

/-!
# Formal hypertranscendence of a superlacunary gap series

A power series `F` with support on a superlacunary gap set satisfies no nonzero formal algebraic
differential relation `aeval (formalJets n F) Q = 0` with `Q ≠ 0` over `ℂ`.  The proof isolates the
top-degree fixed-`κ` group of monomials at a distinct-scale probe: the `Xᵐ⁰` shift aligns every order
in the group at one coefficient index, so the group contributes the complex permanent combination
`combination_permSymbolPolyC_ne_zero` (nonzero), while every other monomial vanishes by the window or
wrong-degree vanishing lemmas.

`flatten_jet_power_product_multiset` records the order-multiset of the flattened tuple, which supplies
the distinctness the permanent combination requires.
-/

open PowerSeries Finset MvPolynomial
open scoped Nat

namespace GaloisForLFunctions

/-- **Flattened order-multiset.**  A power product `∏ⱼ (F⁽ʲ⁾)^{eⱼ}` flattens to a `Fin (∑ e)` tuple of
single jets whose order-multiset is `∑ⱼ eⱼ • {j}` — each derivation order `j` occurs with multiplicity
`eⱼ`.  This determines `e` from the multiset, hence separates distinct power products. -/
theorem flatten_jet_power_product_multiset (n : ℕ) (F : ℂ⟦X⟧) (e : Fin (n + 1) → ℕ) :
    ∃ (μ : Fin (∑ j, e j) → ℕ),
      (∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j)
        = ∏ i : Fin (∑ j, e j), (⇑(d⁄dX ℂ))^[μ i] F)
      ∧ Multiset.map μ (Finset.univ : Finset (Fin (∑ j, e j))).val
          = ∑ j : Fin (n + 1), Multiset.replicate (e j) (j : ℕ) := by
  classical
  have hcard : Fintype.card (Σ j : Fin (n + 1), Fin (e j)) = ∑ j, e j := by
    rw [Fintype.card_sigma]; simp
  set eqv : Fin (∑ j, e j) ≃ (Σ j : Fin (n + 1), Fin (e j)) :=
    (Fintype.equivFinOfCardEq hcard).symm with heqv
  refine ⟨fun i => ((eqv i).1 : ℕ), ?_, ?_⟩
  · have hsig : ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j)
        = ∏ p : (Σ j : Fin (n + 1), Fin (e j)), (⇑(d⁄dX ℂ))^[((p.1 : ℕ))] F := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hsig, ← Equiv.prod_comp eqv]
  · rw [show (Finset.univ : Finset (Fin (∑ j, e j))).val
          = Multiset.map eqv.symm (Finset.univ : Finset (Σ j : Fin (n + 1), Fin (e j))).val from by
        rw [← Finset.map_univ_equiv eqv.symm]; rfl]
    rw [Multiset.map_map,
      show (fun i => ((eqv i).1 : ℕ)) ∘ eqv.symm = fun p => ((p.1 : ℕ)) from by funext p; simp]
    ext k
    rw [Multiset.count_map, Multiset.count_sum']
    simp only [Multiset.count_replicate]
    rw [← Finset.filter_val, Finset.card_val, Finset.card_filter, ← Finset.univ_sigma_univ,
      Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : k = (j : ℕ) <;> simp [h, eq_comm]

/-- Arity-parameterized flattened order-multiset: for a target degree `D = ∑ e`. -/
theorem flatten_jet_power_product_multiset' (n : ℕ) (F : ℂ⟦X⟧) (e : Fin (n + 1) → ℕ) (D : ℕ)
    (hD : ∑ j, e j = D) :
    ∃ (μ : Fin D → ℕ),
      (∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j) = ∏ i : Fin D, (⇑(d⁄dX ℂ))^[μ i] F)
      ∧ Multiset.map μ (Finset.univ : Finset (Fin D)).val
          = ∑ j : Fin (n + 1), Multiset.replicate (e j) (j : ℕ) := by
  subst hD
  exact flatten_jet_power_product_multiset n F e

/-- **Formal hypertranscendence of a superlacunary gap series.**  A power series `F` supported on a
superlacunary gap set `bnat` (with window `2W`) satisfies no nonzero formal algebraic differential
relation over `ℂ`: for `Q ≠ 0` whose jet degrees are bounded by `r` and whose `z`-powers and orders
are bounded by `W`, the substitution `aeval (formalJets n F) Q` is a nonzero power series.  The proof
probes the coefficient at a distinct-scale index tuned to the maximal-degree, maximal-`(z-order)`
group of monomials: the `Xᵐ⁰` shift aligns that whole group at one coefficient index, where it
contributes the complex permanent combination (nonzero by `combination_permSymbolPolyC_maxorder_ne_zero`),
while every other monomial vanishes by the window or wrong-degree distinct-index lemmas. -/
theorem aeval_survives {n : ℕ} {F : ℂ⟦X⟧} {bnat : ℕ → ℕ} {r W : ℕ}
    (hmono : Monotone bnat) (hb0 : 0 < bnat 0) (hWb : 2 * W < bnat 0)
    (hW : ∀ k, r * bnat k + 2 * W < bnat (k + 1))
    (hbnatinj : Function.Injective bnat) (hbtop : Filter.Tendsto bnat Filter.atTop Filter.atTop)
    (hsupp : ∀ k, coeff k F ≠ 0 → ∃ i, k = bnat i)
    (hinf : {i : ℕ | coeff (bnat i) F ≠ 0}.Infinite)
    {Q : MvPolynomial (Fin (n + 2)) ℂ} (hQ : Q ≠ 0)
    (hdeg : ∀ m ∈ Q.support, ∑ j : Fin (n + 1), m j.succ ≤ r)
    (hz : ∀ m ∈ Q.support, m 0 ≤ W)
    (hord : ∀ m ∈ Q.support, ∑ j : Fin (n + 1), (j : ℕ) * m j.succ ≤ W) :
    aeval (formalJets n F) Q ≠ 0 := by
  classical
  intro hzero
  have hstair : ∀ k, r * bnat k < bnat (k + 1) := fun k =>
    lt_of_le_of_lt (Nat.le_add_right _ _) (hW k)
  set Dg : (Fin (n+2) →₀ ℕ) → ℕ := fun m => ∑ j : Fin (n+1), m j.succ with hDgdef
  set Om : (Fin (n+2) →₀ ℕ) → ℕ := fun m => ∑ j : Fin (n+1), (j:ℕ) * m j.succ with hOmdef
  obtain ⟨m', hm'supp, hm'maxdeg⟩ :=
    Finset.exists_max_image Q.support Dg (MvPolynomial.support_nonempty.mpr hQ)
  set G := Q.support.filter (fun m => Dg m = Dg m' ∧ m 0 + Om m' = m' 0 + Om m) with hGdef
  have hm'G : m' ∈ G := Finset.mem_filter.mpr ⟨hm'supp, rfl, rfl⟩
  obtain ⟨m₀, hm₀G, hm₀max⟩ := Finset.exists_max_image G Om ⟨m', hm'G⟩
  have hm₀supp : m₀ ∈ Q.support := (Finset.mem_filter.mp hm₀G).1
  have hm₀z : m₀ 0 ≤ W := hz m₀ hm₀supp
  have hOm₀W : Om m₀ ≤ W := hord m₀ hm₀supp
  have hm₀cond : Dg m₀ = Dg m' ∧ m₀ 0 + Om m' = m' 0 + Om m₀ := (Finset.mem_filter.mp hm₀G).2
  have hGm₀ : ∀ m ∈ G, Dg m = Dg m₀ ∧ m 0 + Om m₀ = m₀ 0 + Om m := by
    intro m hm
    obtain ⟨_, hmD, hmκ⟩ := Finset.mem_filter.mp hm
    exact ⟨by rw [hmD, hm₀cond.1], by omega⟩
  have hDeg₀ : Dg m₀ ≤ r := hdeg m₀ hm₀supp
  have hstair₀ : ∀ k, (Dg m₀) * bnat k < bnat (k + 1) := fun k =>
    lt_of_le_of_lt (by gcongr) (hstair k)
  have hflatex : ∀ m ∈ G, ∃ ν : Fin (Dg m₀) → ℕ,
      (∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (m j.succ)
        = ∏ i : Fin (Dg m₀), (⇑(d⁄dX ℂ))^[ν i] F)
      ∧ Multiset.map ν (Finset.univ).val = ∑ j : Fin (n + 1), Multiset.replicate (m j.succ) (j : ℕ) :=
    fun m hm => flatten_jet_power_product_multiset' n F (fun j => m j.succ) (Dg m₀) (hGm₀ m hm).1
  choose! νf hνprod hνmulti using hflatex
  have hνsum : ∀ m ∈ G, ∑ i, νf m i = Om m := by
    intro m hm
    have e1 : ∑ i, νf m i = (Multiset.map (νf m) (Finset.univ).val).sum := by rw [Finset.sum]
    rw [e1, hνmulti m hm, Multiset.sum_sum]
    simp only [Multiset.sum_replicate, smul_eq_mul]
    rw [hOmdef]
    exact Finset.sum_congr rfl (fun j _ => by rw [Nat.mul_comm])
  have hOle_max : ∀ m ∈ G, ∑ t, νf m t ≤ ∑ t, νf m₀ t := by
    intro m hm
    rw [hνsum m hm, hνsum m₀ hm₀G]; exact hm₀max m hm
  have hmulti_inj : ∀ m ∈ G, ∀ m'' ∈ G,
      Multiset.map (νf m) (Finset.univ).val = Multiset.map (νf m'') (Finset.univ).val → m = m'' := by
    intro m hm m'' hm'' hmulti
    rw [hνmulti m hm, hνmulti m'' hm''] at hmulti
    have hexp : ∀ j : Fin (n + 1), m j.succ = m'' j.succ := by
      intro j
      have hcnt := congrArg (Multiset.count (j : ℕ)) hmulti
      simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Fin.val_injective.eq_iff] at hcnt
      exact hcnt
    obtain ⟨_, hκ⟩ := hGm₀ m hm
    obtain ⟨_, hκ''⟩ := hGm₀ m'' hm''
    have hOmeq : Om m = Om m'' := by rw [hOmdef]; exact Finset.sum_congr rfl (fun j _ => by rw [hexp j])
    have hz0 : m 0 = m'' 0 := by omega
    ext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
    · exact hz0
    · exact hexp k'
  have hdist_max : ∀ m ∈ G, (∃ σ : Equiv.Perm (Fin (Dg m₀)), ∀ j, νf m j = νf m₀ (σ j)) → m = m₀ := by
    rintro m hm ⟨σ, hσ⟩
    apply hmulti_inj m hm m₀ hm₀G
    have hσmap : Multiset.map (⇑σ) (Finset.univ.val) = Finset.univ.val := by
      have h := congrArg Finset.val (Finset.map_univ_equiv σ)
      simp only [Finset.map_val, Equiv.coe_toEmbedding] at h
      exact h
    have hfe : νf m = νf m₀ ∘ σ := funext hσ
    rw [hfe, ← Multiset.map_map, hσmap]
  set Φ := ∑ m ∈ G, MvPolynomial.C (MvPolynomial.coeff m Q) * (permSymbolPoly (νf m)).map (Int.castRingHom ℂ) with hΦdef
  have hΦne : Φ ≠ 0 :=
    combination_permSymbolPolyC_maxorder_ne_zero G νf (fun m => MvPolynomial.coeff m Q) hm₀G hOle_max
      hdist_max (MvPolynomial.mem_support_iff.mp hm₀supp)
  obtain ⟨NB, hNB⟩ := Filter.eventually_atTop.mp (hbtop.eventually_ge_atTop (2 * W))
  have hGsetinf : {i : ℕ | coeff (bnat i) F ≠ 0 ∧ NB ≤ i}.Infinite := by
    apply (hinf.sdiff (Set.finite_Iio NB)).mono
    intro i hi; exact ⟨hi.1, not_lt.mp hi.2⟩
  have hTinf : ((fun i => (bnat i : ℂ)) '' {i : ℕ | coeff (bnat i) F ≠ 0 ∧ NB ≤ i}).Infinite :=
    hGsetinf.image (fun a _ b _ h => hbnatinj (by exact_mod_cast h))
  obtain ⟨a, hainj, haT, haΦ⟩ := exists_injective_eval_ne_zero_field Φ hΦne hTinf
  choose M hMG hMeq using fun i => haT i
  have haM : a = fun i => ((bnat (M i) : ℂ)) := funext fun i => (hMeq i).symm
  have hMinj : Function.Injective M := fun i j h => hainj (by rw [← hMeq i, ← hMeq j, h])
  set A := ∑ i, bnat (M i) with hAdef
  have hbig : ∀ m ∈ G, ∀ i t, νf m t ≤ bnat (M i) := by
    intro m hm i t
    calc νf m t ≤ ∑ t, νf m t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      _ = Om m := hνsum m hm
      _ ≤ W := hord m (Finset.mem_filter.mp hm).1
      _ ≤ 2 * W := by omega
      _ ≤ bnat (M i) := hNB (M i) (hMG i).2
  have hOm₀A : Om m₀ ≤ A := by
    rw [← hνsum m₀ hm₀G, hAdef]; exact Finset.sum_le_sum (fun t _ => hbig m₀ hm₀G t t)
  set N := (A - Om m₀) + m₀ 0 with hNdef
  have hNval : N + Om m₀ = A + m₀ 0 := by rw [hNdef]; omega
  have hwin : ∑ m ∈ G, MvPolynomial.coeff m Q *
        coeff N ((PowerSeries.X) ^ (m 0) * ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (m j.succ))
      = (∏ i, coeff (bnat (M i)) F) * MvPolynomial.eval (fun i => (bnat (M i) : ℂ)) Φ := by
    rw [hΦdef, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hOmmA : Om m ≤ A := by
      rw [← hνsum m hm, hAdef]; exact Finset.sum_le_sum (fun t _ => hbig m hm t t)
    have hκ := (hGm₀ m hm).2
    have hm0N : m 0 ≤ N := by omega
    rw [hνprod m hm, coeff_X_pow_mul', if_pos hm0N]
    have hidx : N - m 0 = ∑ t, (bnat (M t) - νf m t) := by
      rw [Finset.sum_tsub_distrib Finset.univ (fun t _ => hbig m hm t t), hνsum m hm]; omega
    rw [hidx, coeff_distinct_index_eq_permanent hmono hb0 hstair₀ hbnatinj (νf m) hsupp M hMinj
      (hbig m hm), MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_map_permSymbolPoly_complex]
    ring
  have hvanish : ∑ m ∈ Q.support \ G, MvPolynomial.coeff m Q *
      coeff N ((PowerSeries.X) ^ (m 0) * ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (m j.succ)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_sdiff] at hm
    obtain ⟨hmsupp, hmnotG⟩ := hm
    suffices hcz : coeff N ((PowerSeries.X) ^ (m 0)
        * ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (m j.succ)) = 0 by rw [hcz, mul_zero]
    have hmz : m 0 ≤ W := hz m hmsupp
    by_cases hmN : m 0 ≤ N
    · obtain ⟨μm, hμprod, hμmulti⟩ := flatten_jet_power_product_multiset' n F (fun j => m j.succ) (Dg m) rfl
      rw [hμprod, coeff_X_pow_mul', if_pos hmN]
      have hμsum : ∑ i, μm i = Om m := by
        have e1 : ∑ i, μm i = (Multiset.map μm (Finset.univ).val).sum := by rw [Finset.sum]
        rw [e1, hμmulti, Multiset.sum_sum]
        simp only [Multiset.sum_replicate, smul_eq_mul]
        rw [hOmdef]; exact Finset.sum_congr rfl (fun j _ => by rw [Nat.mul_comm])
      have hDgmr : Dg m ≤ r := hdeg m hmsupp
      have hOmmW : Om m ≤ W := hord m hmsupp
      have hbigm : ∀ i t, μm t ≤ bnat (M i) := fun i t => by
        calc μm t ≤ ∑ i, μm i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
          _ = Om m := hμsum
          _ ≤ W := hOmmW
          _ ≤ 2 * W := by omega
          _ ≤ bnat (M i) := hNB (M i) (hMG i).2
      have hDgmle : Dg m ≤ Dg m₀ := by rw [hm₀cond.1]; exact hm'maxdeg m hmsupp
      have hOmmA : Om m ≤ A := by
        rcases Nat.eq_zero_or_pos (Dg m₀) with hz0 | hpos
        · have hDgm0 : Dg m = 0 := Nat.le_zero.mp (hz0 ▸ hDgmle)
          have hOmm0 : Om m = 0 := by
            rw [hOmdef]; apply Finset.sum_eq_zero; intro j _
            have hmj : m j.succ = 0 := by
              have h := hDgm0; rw [hDgdef] at h
              exact (Finset.sum_eq_zero_iff.mp h) j (Finset.mem_univ j)
            rw [hmj, Nat.mul_zero]
          omega
        · obtain ⟨i0⟩ := Fin.pos_iff_nonempty.mp hpos
          calc Om m ≤ W := hOmmW
            _ ≤ 2 * W := by omega
            _ ≤ bnat (M i0) := hNB (M i0) (hMG i0).2
            _ ≤ A := by
                rw [hAdef]
                exact Finset.single_le_sum (f := fun i => bnat (M i))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
      by_cases hKA : (N - m 0) + Om m = A
      · have hκ : m 0 + Om m₀ = m₀ 0 + Om m := by omega
        have hDne : Dg m₀ ≠ Dg m := by
          intro hDeq
          apply hmnotG
          refine Finset.mem_filter.mpr ⟨hmsupp, ?_, ?_⟩
          · rw [← hDeq, hm₀cond.1]
          · omega
        have hidx2 : N - m 0 = A - Om m := by omega
        rw [hidx2]
        exact coeff_distinct_wrong_degree_vanish hmono hb0 hWb hW hDeg₀ hDgmr hDne hμsum
          (by omega) hsupp M hMinj (hAdef ▸ hOmmA) (by omega)
      · exact coeff_distinct_vanish_window hmono hb0 hWb hW hDeg₀ hDgmr hsupp M hMinj
          (by rw [hμsum, ← hAdef]; exact hKA) (by rw [hμsum, ← hAdef]; omega)
          (by rw [hμsum, ← hAdef]; omega)
    · rw [coeff_X_pow_mul', if_neg hmN]
  have hcoeffN := coeff_aeval_eq_support_sum n N F Q
  rw [hzero, map_zero] at hcoeffN
  have hGsub : G ⊆ Q.support := Finset.filter_subset _ _
  rw [← Finset.sum_sdiff hGsub, hvanish, zero_add, hwin] at hcoeffN
  have hprodne : (∏ i, coeff (bnat (M i)) F) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hMG i).1)
  have hevalne : MvPolynomial.eval (fun i => (bnat (M i) : ℂ)) Φ ≠ 0 := by rw [← haM]; exact haΦ
  exact (mul_ne_zero hprodne hevalne) hcoeffN.symm

end GaloisForLFunctions
