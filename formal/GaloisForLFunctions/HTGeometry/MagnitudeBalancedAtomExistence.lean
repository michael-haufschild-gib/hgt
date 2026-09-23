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

/-- A nonzero multivariate polynomial has a nonzero evaluation at an injective
natural tuple whose coordinate sum lies in any prescribed residue class. -/
theorem exists_injective_nat_eval_ne_zero_modSum {D : ℕ} (hD : 0 < D)
    (W : MvPolynomial (Fin D) ℂ) (hW : W ≠ 0) (ρ : ℕ) :
    ∃ k : Fin D → ℕ, Function.Injective k ∧
      Nat.ModEq D (∑ i, k i) ρ ∧
      MvPolynomial.eval (fun i => (k i : ℂ)) W ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply hW
  let A := D ^ (2 : ℕ)
  let i0 : Fin D := ⟨0, hD⟩
  let b : Fin D → ℕ := fun i => if i = i0 then ρ % D else D * (i : ℕ)
  let S : Fin D → Set ℂ := fun i =>
    Set.range (fun a : ℕ => ((A * a + b i : ℕ) : ℂ))
  apply MvPolynomial.funext_set (p := W) (q := 0) S
  · intro i
    apply Set.infinite_range_of_injective
    intro a c hac
    change ((A * a + b i : ℕ) : ℂ) = ((A * c + b i : ℕ) : ℂ) at hac
    have hacNat : A * a + b i = A * c + b i := by exact_mod_cast hac
    have hmul : A * a = A * c := Nat.add_right_cancel hacNat
    exact Nat.eq_of_mul_eq_mul_left (by dsimp [A]; positivity) hmul
  · intro x hx
    choose a ha using fun i => hx i (Set.mem_univ i)
    let k : Fin D → ℕ := fun i => A * a i + b i
    have hb_lt : ∀ i, b i < A := by
      intro i
      by_cases hi : i = i0
      · subst i
        simp only [b, ↓reduceIte]
        have hr : ρ % D < D := Nat.mod_lt _ hD
        dsimp [A]
        nlinarith
      · simp only [b, hi]
        have hiD : (i : ℕ) < D := i.isLt
        dsimp [A]
        nlinarith
    have hb_inj : Function.Injective b := by
      intro i j hij
      by_cases hi : i = i0
      · subst i
        by_cases hj : j = i0
        · exact hj.symm
        · have hr : ρ % D < D := Nat.mod_lt _ hD
          have hjpos : 0 < (j : ℕ) := by
            apply Nat.pos_of_ne_zero
            intro h
            apply hj
            apply Fin.ext
            simpa [i0] using h
          simp only [b, ↓reduceIte, hj] at hij
          nlinarith
      · by_cases hj : j = i0
        · subst j
          have hr : ρ % D < D := Nat.mod_lt _ hD
          have hipos : 0 < (i : ℕ) := by
            apply Nat.pos_of_ne_zero
            intro h
            apply hi
            apply Fin.ext
            simpa [i0] using h
          simp only [b, hi, ↓reduceIte] at hij
          nlinarith
        · simp only [b, hi, hj] at hij
          apply Fin.ext
          exact Nat.eq_of_mul_eq_mul_left hD hij
    have hk : Function.Injective k := by
      intro i j hij
      have hmod := congrArg (fun n : ℕ => n % A) hij
      have hApos : 0 < A := by dsimp [A]; positivity
      have hbi := hb_lt i
      have hbj := hb_lt j
      have hAi : (A * a i + b i) % A = b i := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, zero_add,
          Nat.mod_eq_of_lt hbi]
        exact Nat.mod_eq_of_lt hbi
      have hAj : (A * a j + b j) % A = b j := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, zero_add,
          Nat.mod_eq_of_lt hbj]
        exact Nat.mod_eq_of_lt hbj
      have hmod' : (A * a i + b i) % A = (A * a j + b j) % A := by
        simpa only [k] using hmod
      rw [hAi, hAj] at hmod'
      exact hb_inj hmod'
    have hkmod : Nat.ModEq D (∑ i, k i) ρ := by
      have hi0 : Nat.ModEq D (k i0) ρ := by
        have hshape : k i0 = D * (D * a i0) + ρ % D := by
          simp [k, A, b, i0, pow_two, mul_assoc]
        rw [hshape]
        exact (Nat.ModEq.modulus_mul_add (m := D) (a := D * a i0) (b := ρ % D)).trans
          (Nat.mod_modEq ρ D)
      have hother : ∀ i ∈ Finset.univ, i ≠ i0 → Nat.ModEq D (k i) 0 := by
        intro i _ hi
        rw [Nat.modEq_zero_iff_dvd]
        refine ⟨(i : ℕ) + D * a i, ?_⟩
        simp [k, A, b, hi, pow_two]
        ring
      exact (Nat.sum_modEq_single (s := Finset.univ) (a := i0)
        (f := k) (by simp) hother).trans hi0
    have hxk : x = fun i => (k i : ℂ) := by
      funext i
      exact (ha i).symm
    rw [map_zero, hxk]
    exact hcon k hk hkmod

/-- Prescribed-residue balanced diagonal nonvanishing.  The offset sum can be
chosen in any residue class modulo the positive arity while retaining pairwise
distinct offsets and eventual nonvanishing along the whole diagonal. -/
theorem exists_injective_balanced_diagonal_ne_zero_modSum {D : ℕ} (hD : 0 < D)
    (W : MvPolynomial (Fin D) ℂ) (hW : W ≠ 0) (ρ : ℕ) :
    ∃ δ : Fin D → ℕ, Function.Injective δ ∧
      Nat.ModEq D (∑ i, δ i) ρ ∧ ∃ Q₀ : ℕ,
      ∀ q ≥ Q₀, MvPolynomial.eval (fun i => ((q + δ i : ℕ) : ℂ)) W ≠ 0 := by
  obtain ⟨δ, hδinj, hδmod, hδ⟩ :=
    exists_injective_nat_eval_ne_zero_modSum hD W hW ρ
  have hp0 : diagPoly W δ ≠ 0 := by
    intro h0
    apply hδ
    have h := diagPoly_eval W δ 0
    rw [h0, Polynomial.eval_zero] at h
    simpa using h.symm
  obtain ⟨Q₀, hQ₀⟩ := poly_eventually_ne_zero_nat (diagPoly W δ) hp0
  refine ⟨δ, hδinj, hδmod, Q₀, fun q hq hev => ?_⟩
  have hd := diagPoly_eval W δ (q : ℂ)
  have hcast : (fun i => (q : ℂ) + (δ i : ℂ)) =
      (fun i => ((q + δ i : ℕ) : ℂ)) := by
    funext i
    push_cast
    ring
  rw [hcast, hev] at hd
  exact hQ₀ q hq hd

/-- Every positive-jet-degree support monomial generates eventual balanced
nonzero grouped weights with the offset sum in an arbitrarily prescribed
residue class. -/
theorem exists_eventually_balanced_nonzero_aevalWeight_modSum {n : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support) (hD : 0 < jetMonomialDegree n anchor) (ρ : ℕ) :
    ∃ (δ : Fin (jetMonomialDegree n anchor) → ℕ), Function.Injective δ ∧
      Nat.ModEq (jetMonomialDegree n anchor) (∑ i, δ i) ρ ∧
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
  obtain ⟨δ, hδinj, hδmod, Qd, hQd⟩ :=
    exists_injective_balanced_diagonal_ne_zero_modSum hD W hW ρ
  let Zmax := Q.support.sup fun m => m 0
  let Q₀ := max Qd (max n (Zmax + jetMonomialOrder n anchor))
  refine ⟨δ, hδinj, hδmod, Q₀, fun q hq => ?_⟩
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
  obtain ⟨δ, hδinj, -, Q₀, hQ₀⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight_modSum ha hD 0
  exact ⟨δ, hδinj, Q₀, hQ₀⟩

end

end GaloisForLFunctions
