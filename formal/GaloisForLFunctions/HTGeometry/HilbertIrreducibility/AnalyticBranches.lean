/-
# Analytic root branches at a regular value

`Lemma 3` of Coleman--Zwald.  At a parameter `s₀` where the leading coefficient survives and the
specialised fibre is separable, the `n` roots of `P(s, ·)` are analytic functions of `s` on a
neighbourhood of `s₀`, and near `s₀` they are pairwise distinct and exhaust the root multiset.

The analytic engine is the corpus' holomorphic implicit function theorem
`HolomorphicIFT.holo_implicit`, applied at each of the `n` simple roots of the fibre at `s₀`.
-/
import GaloisForLFunctions.U0.HolomorphicIFT

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial Filter Topology

/-- **Analytic branches at a regular value.** -/
theorem exists_analytic_branches {P : Polynomial (Polynomial ℂ)} {s₀ : ℂ} {n : ℕ}
    (hn : P.natDegree = n) (hlead : P.leadingCoeff.eval s₀ ≠ 0)
    (hsep : (P.map (Polynomial.evalRingHom s₀)).Separable) :
    ∃ u : Fin n → ℂ → ℂ, (∀ i, AnalyticAt ℂ (u i) s₀) ∧
      ∀ᶠ s in 𝓝 s₀, (Function.Injective fun i => u i s) ∧
        (P.map (Polynomial.evalRingHom s)).natDegree = n ∧
        (P.map (Polynomial.evalRingHom s)).roots
          = Multiset.map (fun i => u i s) (Finset.univ : Finset (Fin n)).val := by
  classical
  set P₀ : Polynomial ℂ := P.map (Polynomial.evalRingHom s₀) with hP₀
  have hlead' : (Polynomial.evalRingHom s₀) P.leadingCoeff ≠ 0 := hlead
  have hP₀deg : P₀.natDegree = n := by
    rw [hP₀, Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlead', hn]
  have hP₀ne : P₀ ≠ 0 := Polynomial.Separable.ne_zero hsep
  have hcard : Multiset.card P₀.roots = n := by
    rw [← hP₀deg]; exact IsAlgClosed.card_roots_eq_natDegree
  have hnodup : P₀.roots.Nodup := Polynomial.nodup_roots hsep
  have hfcard : P₀.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnodup, hcard]
  set e := Finset.equivFinOfCardEq hfcard with he
  set a : Fin n → ℂ := fun i => ((e.symm i : P₀.roots.toFinset) : ℂ) with ha
  have hainj : Function.Injective a := fun i j hij =>
    e.symm.injective (Subtype.ext hij)
  have haroot : ∀ i, P₀.IsRoot (a i) := by
    intro i
    have hm := (e.symm i).2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP₀ne] at hm
    exact hm
  have hderiv : ∀ i, (Polynomial.derivative P₀).eval (a i) ≠ 0 := by
    intro i hcon
    obtain ⟨A, B, hAB⟩ := hsep
    have hev := congrArg (Polynomial.eval (a i)) hAB
    have hr : Polynomial.eval (a i) P₀ = 0 := haroot i
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, hr, hcon,
      mul_zero, add_zero] at hev
    exact zero_ne_one hev
  -- the branches
  have hbranch : ∀ i : Fin n, ∃ r : ℂ → ℂ, AnalyticAt ℂ r s₀ ∧ r s₀ = a i ∧
      (∀ᶠ s in 𝓝 s₀, P.eval₂ (Polynomial.evalRingHom s) (r s) = 0) := by
    intro i
    have h0 : (fun q : ℂ × ℂ => P.eval₂ (Polynomial.evalRingHom q.1) q.2) (s₀, a i) = 0 := by
      have := haroot i
      rw [Polynomial.IsRoot, hP₀, Polynomial.eval_map] at this
      exact this
    have hfw : (fderiv ℂ (fun q : ℂ × ℂ => P.eval₂ (Polynomial.evalRingHom q.1) q.2)
        (s₀, a i)) (0, 1) ≠ 0 := by
      rw [HolomorphicIFT.partial_w_deriv, ← Polynomial.derivative_map]
      exact hderiv i
    exact HolomorphicIFT.holo_implicit (HolomorphicIFT.bivar_analytic P (s₀, a i)) h0 hfw
  choose u hua hu0 hurel using hbranch
  refine ⟨u, hua, ?_⟩
  -- pairwise separation near `s₀`
  have hsepev : ∀ᶠ s in 𝓝 s₀, ∀ i j : Fin n, i ≠ j → u i s ≠ u j s := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun s hs => absurd hij hs
    · have hne : u i s₀ ≠ u j s₀ := by
        rw [hu0 i, hu0 j]
        exact fun h => hij (hainj h)
      have hc : ContinuousAt (fun s => u i s - u j s) s₀ :=
        ((hua i).continuousAt).sub ((hua j).continuousAt)
      have hev := hc.eventually_ne (sub_ne_zero_of_ne hne)
      filter_upwards [hev] with s hs _
      exact sub_ne_zero.mp hs
  have hleadev : ∀ᶠ s in 𝓝 s₀, P.leadingCoeff.eval s ≠ 0 := by
    have hc : ContinuousAt (fun s => P.leadingCoeff.eval s) s₀ :=
      (P.leadingCoeff.continuous_aeval).continuousAt
    exact hc.eventually_ne hlead
  filter_upwards [hsepev, hleadev, Filter.eventually_all.2 hurel] with s hs1 hs0 hs3
  have hinj : Function.Injective fun i => u i s := by
    intro i j hij
    by_contra hne
    exact hs1 i j hne hij
  set Ps : Polynomial ℂ := P.map (Polynomial.evalRingHom s) with hPs
  have hlead0 : (Polynomial.evalRingHom s) P.leadingCoeff ≠ 0 := hs0
  have hdegs : Ps.natDegree = n := by
    rw [hPs, Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlead0, hn]
  have hPsne : Ps ≠ 0 := by
    intro hzero
    apply hs0
    have hc : Ps.coeff P.natDegree = P.leadingCoeff.eval s := by
      rw [hPs, Polynomial.coeff_map]; rfl
    rw [hzero, Polynomial.coeff_zero] at hc
    exact hc.symm
  refine ⟨hinj, hdegs, ?_⟩
  have hcards : Multiset.card Ps.roots = n := by
    rw [← hdegs]; exact IsAlgClosed.card_roots_eq_natDegree
  set M : Multiset ℂ := Multiset.map (fun i => u i s) (Finset.univ : Finset (Fin n)).val with hM
  have hMcard : Multiset.card M = n := by
    rw [hM, Multiset.card_map]
    simp
  have hMnodup : M.Nodup := Multiset.Nodup.map hinj (Finset.univ (α := Fin n)).nodup
  have hMle : M ≤ Ps.roots := by
    rw [Multiset.le_iff_count]
    intro x
    by_cases hx : x ∈ M
    · have h1 : Multiset.count x M = 1 := Multiset.count_eq_one_of_mem hMnodup hx
      obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hx
      have hroot : Ps.IsRoot x := by
        rw [← hi, Polynomial.IsRoot, hPs, Polynomial.eval_map]
        exact hs3 i
      have h2 : 1 ≤ Multiset.count x Ps.roots := by
        rw [Multiset.one_le_count_iff_mem, Polynomial.mem_roots hPsne]
        exact hroot
      omega
    · rw [Multiset.count_eq_zero_of_notMem hx]
      exact Nat.zero_le _
  exact (Multiset.eq_of_le_of_card_le hMle (by rw [hcards, hMcard])).symm

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
