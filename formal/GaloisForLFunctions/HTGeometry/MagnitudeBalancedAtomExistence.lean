import GaloisForLFunctions.HTGeometry.MagnitudeBalancedSymbolNonvanishing

/-!
# Eventual balanced nonzero atoms

A positive-jet-degree support monomial determines a nonzero fixed-shift
permanent symbol. An injective balanced diagonal of that symbol, with the
coefficient level fixed by the conserved shift, yields an appearing grouped
`aevalWeight` that is nonzero at every sufficiently large diagonal parameter.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section
theorem flatOrder_le_jetBound {n : ℕ} (e : Fin (n + 1) → ℕ)
    (t : Fin (∑ j, e j)) : flatOrder e t ≤ n := by
  rw [flatOrder]
  exact Nat.le_of_lt_succ
    (((Fintype.equivFinOfCardEq (by rw [Fintype.card_sigma]; simp :
      Fintype.card (Σ j : Fin (n + 1), Fin (e j)) = ∑ j, e j)).symm t).1.isLt)

/-- Every positive-jet-degree support monomial generates nonzero grouped weights on an eventual
injective balanced family of source tuples. -/
theorem exists_eventually_balanced_nonzero_aevalWeight {n : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support) (hD : 0 < jetMonomialDegree n anchor) :
    ∃ (δ : Fin (jetMonomialDegree n anchor) → ℕ), Function.Injective δ ∧
      ∃ Q₀ : ℕ, ∀ q ≥ Q₀,
        let s : Fin (jetMonomialDegree n anchor) → ℕ := fun i => q + δ i
        let N := (∑ i, s i) + anchor 0 - jetMonomialOrder n anchor
        key s ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
          aevalWeight n N Q (key s) ≠ 0 ∧
          balancedJetGroup n N (jetMonomialDegree n anchor) Q s =
            topShiftJetGroup n Q anchor := by
  classical
  let W := topShiftJetSymbol n Q anchor
  have hW : W ≠ 0 := topShiftJetSymbol_ne_zero ha
  obtain ⟨δ, hδinj, Qd, hQd⟩ := exists_injective_balanced_diagonal_ne_zero W hW
  let Zmax := Q.support.sup fun m => m 0
  let Q₀ := max Qd (max n (Zmax + jetMonomialOrder n anchor))
  refine ⟨δ, hδinj, Q₀, fun q hq => ?_⟩
  let s : Fin (jetMonomialDegree n anchor) → ℕ := fun i => q + δ i
  let N := (∑ i, s i) + anchor 0 - jetMonomialOrder n anchor
  have hqQd : Qd ≤ q := le_trans (le_max_left _ _) hq
  have hqn : n ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hqZ : Zmax + jetMonomialOrder n anchor ≤ q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  obtain ⟨i0⟩ : Nonempty (Fin (jetMonomialDegree n anchor)) :=
    Fin.pos_iff_nonempty.mp hD
  have hqsum : q ≤ ∑ i, s i := by
    calc
      q ≤ s i0 := by simp [s]
      _ ≤ ∑ i, s i := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i0)
  have horderSum : jetMonomialOrder n anchor ≤ ∑ i, s i := by
    have : jetMonomialOrder n anchor ≤ q := le_trans (Nat.le_add_left _ Zmax) hqZ
    exact this.trans hqsum
  have hNshift : N + jetMonomialOrder n anchor = (∑ i, s i) + anchor 0 := by
    dsimp [N]
    omega
  have hallN : ∀ m ∈ Q.support, m 0 ≤ N := by
    intro m hm
    have hmZ : m 0 ≤ Zmax := by
      dsimp [Zmax]
      exact Finset.le_sup (f := fun m => m 0) hm
    have hmOrder : m 0 + jetMonomialOrder n anchor ≤ q :=
      (Nat.add_le_add_right hmZ _).trans hqZ
    dsimp [N]
    omega
  have hG : balancedJetGroup n N (jetMonomialDegree n anchor) Q s =
      topShiftJetGroup n Q anchor := by
    ext m
    rw [balancedJetGroup, topShiftJetGroup, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hm, hmN, hdeg, heq⟩
      refine ⟨hm, hdeg, ?_⟩
      have hsub : N - m 0 + m 0 = N := Nat.sub_add_cancel hmN
      omega
    · rintro ⟨hm, hdeg, heq⟩
      have hmN := hallN m hm
      refine ⟨hm, hmN, hdeg, ?_⟩
      have hsub : N - m 0 + m 0 = N := Nat.sub_add_cancel hmN
      omega
  have hsInj : Function.Injective s := by
    intro i j hij
    apply hδinj
    dsimp [s] at hij
    omega
  have hdom : ∀ m : ↥(balancedJetGroup n N (jetMonomialDegree n anchor) Q s),
      ∀ i : Fin (jetMonomialDegree n anchor),
        ∀ t : Fin (jetMonomialDegree n m.1),
          flatOrder (fun j => m.1 j.succ) t ≤ s i := by
    intro m i t
    exact (flatOrder_le_jetBound (fun j => m.1 j.succ) t).trans
      (hqn.trans (by simp [s]))
  have hEval : MvPolynomial.eval (fun i => (s i : ℂ))
      (balancedJetSymbol n N (jetMonomialDegree n anchor) Q s) ≠ 0 := by
    rw [balancedJetSymbol_eq_topShiftJetSymbol s hG]
    exact hQd q hqQd
  have hw : aevalWeight n N Q (key s) ≠ 0 := by
    rw [aevalWeight_key_eq_balancedJetSymbol n N (jetMonomialDegree n anchor) Q s hsInj hdom]
    exact hEval
  have hfiber : ((sigmaIdx n N Q).filter (fun x => atomKeyOf n x = key s)).Nonempty := by
    by_contra hne
    apply hw
    rw [aevalWeight]
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp
  obtain ⟨x, hx⟩ := hfiber
  have hxsigma : x ∈ sigmaIdx n N Q := (Finset.mem_filter.mp hx).1
  have hxkey : atomKeyOf n x = key s := (Finset.mem_filter.mp hx).2
  refine ⟨?_, hw, hG⟩
  rw [← hxkey]
  exact Finset.mem_image_of_mem _ hxsigma

end

end GaloisForLFunctions

