import GaloisForLFunctions.HTGeometry.BorelWeil.RankTwoVanishing

/-!
# Bott's theorem for `GL(2)`

For `N = 2` the Bruhat cover has two cells, so the Čech complex is the two-chart complex of the
fibre `ℙ¹` and the first cohomology is the cokernel of the difference map.  The splitting of the
intersection therefore says exactly that `H¹(G/B, L_λ)` vanishes whenever the weight pairs to at
least `−1` with the coroot; combined with the degree-zero results this is Bott's theorem in rank
one, apart from the identification of the nonvanishing case.

## Main results

* `flagCocycles_one_le_flagCoboundaries` — every `1`-cocycle is a coboundary when `d ≥ −1`.
* `flagCohomology_one_subsingleton` — `H¹(G/B, L_λ) = 0` for `d ≥ −1`.
* `flagCohomology_subsingleton_of_two_le` — `H^p(G/B, L_λ) = 0` for `p ≥ 2`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem one_ne_swapTwo : (1 : Equiv.Perm (Fin 2)) ≠ swapTwo := swapNext_ne_one zero_succ_lt_two

theorem card_perm_fin_two : Fintype.card (Equiv.Perm (Fin 2)) = 2 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  rfl

theorem eq_pair_of_card_two {I : Finset (Equiv.Perm (Fin 2))} (hI : I.card = 2) :
    I = {1, swapTwo} := by
  classical
  rw [← univ_perm_fin_two]
  exact Finset.eq_univ_of_card I (by rw [hI, card_perm_fin_two])

theorem erase_pair_left : ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))).erase 1 = {swapTwo} := by
  classical
  ext w
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨fun hw => hw.2.resolve_left hw.1, fun hw => ⟨by rw [hw]; exact fun hc => one_ne_swapTwo hc.symm,
    Or.inr hw⟩⟩

theorem erase_pair_right : ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))).erase swapTwo = {1} := by
  classical
  ext w
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨fun hw => hw.2.resolve_right hw.1, fun hw => ⟨by rw [hw]; exact one_ne_swapTwo, Or.inl hw⟩⟩

/-- The `0`-cochain with prescribed values on the two cells. -/
noncomputable def pairCochain (a b : FlagLoc 2 k) :
    Finset (Equiv.Perm (Fin 2)) → FlagLoc 2 k :=
  fun I => if I = {1} then a else if I = {swapTwo} then b else 0

theorem pairCochain_isFlagCochain {lam : Fin 2 → ℤ} {a b : FlagLoc 2 k}
    (ha : a ∈ cellSections 2 k {(1 : Equiv.Perm (Fin 2))} lam)
    (hb : b ∈ cellSections 2 k {swapTwo} lam) : IsFlagCochain lam 0 (pairCochain a b) := by
  classical
  constructor
  · intro I hI
    rw [pairCochain]
    have h1 : I ≠ {1} := fun hc => hI (by rw [hc, Finset.card_singleton])
    have h2 : I ≠ {swapTwo} := fun hc => hI (by rw [hc, Finset.card_singleton])
    rw [if_neg h1, if_neg h2]
  · intro I
    rw [pairCochain]
    by_cases h1 : I = {1}
    · rw [if_pos h1, h1]
      exact ha
    · rw [if_neg h1]
      by_cases h2 : I = {swapTwo}
      · rw [if_pos h2, h2]
        exact hb
      · rw [if_neg h2]
        exact Submodule.zero_mem _

theorem cechDModule_pairCochain_of_ne {a b : FlagLoc 2 k} {I : Finset (Equiv.Perm (Fin 2))}
    (hI : I.card ≠ 2) : cechDModule k (pairCochain a b) I = 0 := by
  classical
  refine Finset.sum_eq_zero fun u hu => ?_
  have hcard : (I.erase u).card = I.card - 1 := Finset.card_erase_of_mem hu
  have h1 : I.erase u ≠ {1} := by
    intro hc
    rw [hc, Finset.card_singleton] at hcard
    have hpos : 0 < I.card := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  have h2 : I.erase u ≠ {swapTwo} := by
    intro hc
    rw [hc, Finset.card_singleton] at hcard
    have hpos : 0 < I.card := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  rw [pairCochain, if_neg h1, if_neg h2, smul_zero]

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem cechDModule_pairCochain_pair (a b : FlagLoc 2 k) :
    cechDModule k (pairCochain a b) {1, swapTwo}
      = (cechSign ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))) 1 : k) • b
        + (cechSign ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))) swapTwo : k) • a := by
  classical
  have hb' : pairCochain a b ({swapTwo} : Finset (Equiv.Perm (Fin 2))) = b := by
    rw [pairCochain, if_neg (fun hc => one_ne_swapTwo (Finset.singleton_injective hc).symm),
      if_pos rfl]
  have ha' : pairCochain a b ({1} : Finset (Equiv.Perm (Fin 2))) = a := by
    rw [pairCochain, if_pos rfl]
  rw [cechDModule, Finset.sum_pair one_ne_swapTwo, erase_pair_left, erase_pair_right, ha', hb']

/-- **Every `1`-cocycle is a coboundary when the weight pairs to at least `−1`.** -/
theorem flagCocycles_one_le_flagCoboundaries {lam : Fin 2 → ℤ} (hd : -1 ≤ lam 0 - lam 1) :
    flagCocycles 2 k lam 1 ≤ flagCoboundaries 2 k lam 1 := by
  classical
  intro ω hω
  have hval : ω {1, swapTwo} ∈ cellSections 2 k ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))) lam :=
    hω.1.mem _
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (cellSections_pair_le_sup hd hval)
  have hzero : ∀ I : Finset (Equiv.Perm (Fin 2)), I.card ≠ 2 → ω I = 0 := by
    intro I hI
    exact hω.1.card I (by simpa using hI)
  rcases lt_trichotomy (1 : Equiv.Perm (Fin 2)) swapTwo with hlt | heq | hlt
  · refine ⟨pairCochain (-a) b, pairCochain_isFlagCochain (Submodule.neg_mem _ ha) hb, ?_⟩
    show cechDModule k (pairCochain (-a) b) = ω
    funext I
    by_cases hI : I.card = 2
    · have hIeq := eq_pair_of_card_two hI
      subst hIeq
      rw [cechDModule_pairCochain_pair, cechSign_pair_left (k := k) hlt,
        cechSign_pair_right (k := k) hlt, one_smul, neg_smul, one_smul, neg_neg, ← hab]
      exact add_comm b a
    · rw [cechDModule_pairCochain_of_ne hI, hzero I hI]
  · exact absurd heq one_ne_swapTwo
  · refine ⟨pairCochain a (-b), pairCochain_isFlagCochain ha (Submodule.neg_mem _ hb), ?_⟩
    show cechDModule k (pairCochain a (-b)) = ω
    funext I
    by_cases hI : I.card = 2
    · have hIeq := eq_pair_of_card_two hI
      subst hIeq
      have hs1 : (cechSign ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))) 1 : k) = -1 := by
        rw [Finset.pair_comm]
        exact cechSign_pair_right (k := k) hlt
      have hs2 : (cechSign ({1, swapTwo} : Finset (Equiv.Perm (Fin 2))) swapTwo : k) = 1 := by
        rw [Finset.pair_comm]
        exact cechSign_pair_left (k := k) hlt
      rw [cechDModule_pairCochain_pair, hs1, hs2, neg_smul, one_smul, neg_neg, one_smul, ← hab]
      exact add_comm b a
    · rw [cechDModule_pairCochain_of_ne hI, hzero I hI]

/-- **Vanishing of the first cohomology of the flag variety of `GL(2)`.** -/
theorem flagCohomology_one_subsingleton {lam : Fin 2 → ℤ} (hd : -1 ≤ lam 0 - lam 1) :
    Subsingleton (flagCohomology 2 k lam 1) := by
  classical
  have htop : Submodule.comap (flagCocycles 2 k lam 1).subtype (flagCoboundaries 2 k lam 1) = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    exact flagCocycles_one_le_flagCoboundaries hd z.2
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.inductionOn with
  | _ u =>
    induction y using Quotient.inductionOn with
    | _ v =>
      refine (Submodule.Quotient.eq _).mpr ?_
      rw [htop]
      trivial

/-- **Vanishing above the fibre degree.** -/
theorem flagCohomology_subsingleton_of_two_le {lam : Fin 2 → ℤ} {p : ℕ} (hp : 2 ≤ p) :
    Subsingleton (flagCohomology 2 k lam p) := by
  refine flagCohomology_subsingleton_of_card_lt ?_
  rw [card_perm_fin_two]
  omega

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {k : Type*} [Field k] [Infinite k]

theorem antitone_fin_two_iff {lam : Fin 2 → ℤ} : Antitone lam ↔ lam 1 ≤ lam 0 := by
  constructor
  · intro h
    exact h (by decide : (0 : Fin 2) ≤ 1)
  · intro h i j hij
    rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl
    · exact le_rfl
    · exact h
    · exact absurd hij (by decide)
    · exact le_rfl

/-- **Bott's theorem for `GL(2)`, dominant case.**  For a dominant weight the cohomology of `L_λ`
on the flag variety is concentrated in degree zero, where it is the Borel–Weil module. -/
theorem rankTwo_bott_dominant [CharZero k] {lam : Fin 2 → ℤ} (hlam : Antitone lam) :
    Nontrivial (flagCohomology 2 k lam 0)
      ∧ ∀ p : ℕ, 1 ≤ p → Subsingleton (flagCohomology 2 k lam p) := by
  refine ⟨flagCohomology_zero_nontrivial_iff_int lam |>.mpr hlam, fun p hp => ?_⟩
  rcases Nat.lt_or_ge p 2 with h | h
  · have hp1 : p = 1 := by omega
    subst hp1
    refine flagCohomology_one_subsingleton ?_
    have := antitone_fin_two_iff.mp hlam
    omega
  · exact flagCohomology_subsingleton_of_two_le h

/-- **Bott's theorem for `GL(2)`, singular case.**  If the weight pairs to `−1` with the coroot —
that is, `λ + ρ` is singular — then the cohomology of `L_λ` vanishes in every degree. -/
theorem rankTwo_bott_singular [CharZero k] {lam : Fin 2 → ℤ} (hsing : lam 0 - lam 1 = -1) :
    ∀ p : ℕ, Subsingleton (flagCohomology 2 k lam p) := by
  intro p
  match p with
  | 0 =>
      have hnot : ¬ Antitone lam := by
        rw [antitone_fin_two_iff]
        omega
      rw [← not_nontrivial_iff_subsingleton]
      intro hcon
      exact hnot ((flagCohomology_zero_nontrivial_iff_int lam).mp hcon)
  | 1 => exact flagCohomology_one_subsingleton (by omega)
  | (q + 2) => exact flagCohomology_subsingleton_of_two_le (by omega)

end GaloisForLFunctions.HTGeometry.BorelWeil
