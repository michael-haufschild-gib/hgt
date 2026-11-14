import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupMovesFinitelyManyZerosInDistinctPairsAtWill

/-!
# An involution with one flipped pair gives the flip of one pair up to one exchange

Let `G` be a group of signed permutations of finite support that contains every signed 3-cycle
and every double flip (`IsWindowedSignedGroup`). Let `σ ∈ G` be an involution that sends one
point `p` to its partner and no point of another pair to its partner: `σ` is the flip of the pair
of `p` times `k` exchanges `a ↔ b`, `a' ↔ b'` of two pairs.

**Theorem** (`IsWindowedSignedGroup.forall_hasFlip_or_forall_hasFlipExchange`). Either `G`
contains the flip of every single pair, or `G` contains, for all `q, c, d` in three distinct
pairs, the flip of the pair of `q` times the exchange of the pairs of `c` and `d`.

In both cases `G` contains an odd permutation of the points. Which case holds is the parity of
`k`, the sign of `σ` on the pairs.

Proof. Two exchanges `a ↔ b`, `c ↔ d` (with their mirrors) are the product of the signed 3-cycles
`a → b → c` and `b → c → d`, so they lie in `G`; removing them from `σ` lowers the number of moved
points (`hasFlip_or_hasFlipExchange_of_moved`). At the end `σ` is the flip alone or the flip
times one exchange. Triple transitivity carries the pairs to any prescribed ones.
-/

open Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

variable {Ω : Type*} {P : PairCoordinate Ω} {G : Subgroup (Perm Ω)}

/-- `G` contains the flip of the pair of `p`: an element that sends `p` to its partner and is the
identity off the pair. -/
def HasFlip (P : PairCoordinate Ω) (G : Subgroup (Perm Ω)) (p : Ω) : Prop :=
  ∃ T ∈ G, T p = P.flip p ∧ ∀ x, P.pair x ≠ P.pair p → T x = x

/-- `G` contains the flip of the pair of `p` times the exchange of the pairs of `a` and `b`: an
element that sends `p` to its partner, exchanges `a` and `b`, and is the identity off the three
pairs. -/
def HasFlipExchange (P : PairCoordinate Ω) (G : Subgroup (Perm Ω)) (p a b : Ω) : Prop :=
  ∃ T ∈ G, T p = P.flip p ∧ T a = b ∧ T b = a ∧
    ∀ x, P.pair x ≠ P.pair p → P.pair x ≠ P.pair a → P.pair x ≠ P.pair b → T x = x

namespace IsWindowedSignedGroup

variable (hG : IsWindowedSignedGroup P G)
include hG

theorem pair_inv_apply_ne {g : Perm Ω} (hg : g ∈ G) {x y : Ω} (h : P.pair x ≠ P.pair (g y)) :
    P.pair (g⁻¹ x) ≠ P.pair y := fun h' => h (by
  have h'' := (hG.pair_apply_eq_iff hg).mpr h'
  rwa [perm_apply_inv_self] at h'')

/-- An element of `G` that fixes a point fixes its partner. -/
theorem apply_eq_self_of_pair_eq {g : Perm Ω} (hg : g ∈ G) {t x : Ω} (ht : g t = t)
    (hx : P.pair x = P.pair t) : g x = x := by
  rcases (P.pair_eq_iff t x).mp hx.symm with h | h
  · rw [h]
    exact ht
  · rw [h, hG.comm g hg, ht]

/-- **Triple transitivity.** Three points in distinct pairs are moved to three points in distinct
pairs by one element of `G`. -/
theorem exists_apply_three {x y z x' y' z' : Ω} (hxy : P.pair x ≠ P.pair y)
    (hxz : P.pair x ≠ P.pair z) (hyz : P.pair y ≠ P.pair z) (hxy' : P.pair x' ≠ P.pair y')
    (hxz' : P.pair x' ≠ P.pair z') (hyz' : P.pair y' ≠ P.pair z') :
    ∃ g ∈ G, g x = x' ∧ g y = y' ∧ g z = z' := by
  have hinj : ∀ {u v w : Ω}, P.pair u ≠ P.pair v → P.pair u ≠ P.pair w → P.pair v ≠ P.pair w →
      Function.Injective fun i : Fin 3 => P.pair (![u, v, w] i) := by
    intro u v w huv huw hvw i j h
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨g, hg, h⟩ := hG.exists_forall_apply_eq (p := ![x, y, z]) (q := ![x', y', z'])
    (hinj hxy hxz hyz) (hinj hxy' hxz' hyz')
  exact ⟨g, hg, h 0, h 1, h 2⟩

/-- **Two exchanges lie in `G`.** For four points in distinct pairs, `G` contains the element
that exchanges `a ↔ b` and `c ↔ d` and is the identity off the four pairs: the product of the
signed 3-cycles `a → b → c` and `b → c → d`. -/
theorem exists_double_exchange {a b c d : Ω} (hab : P.pair a ≠ P.pair b)
    (hac : P.pair a ≠ P.pair c) (had : P.pair a ≠ P.pair d) (hbc : P.pair b ≠ P.pair c)
    (hbd : P.pair b ≠ P.pair d) (hcd : P.pair c ≠ P.pair d) :
    ∃ u ∈ G, u a = b ∧ u b = a ∧ u c = d ∧ u d = c ∧
      ∀ x, P.pair x ≠ P.pair a → P.pair x ≠ P.pair b → P.pair x ≠ P.pair c →
        P.pair x ≠ P.pair d → u x = x := by
  obtain ⟨T₁, hT₁, h1a, h1b, h1c, h1x⟩ := hG.hasSignedCycle hab hbc hac
  obtain ⟨T₂, hT₂, h2b, h2c, h2d, h2x⟩ := hG.hasSignedCycle hbc hcd hbd
  refine ⟨T₁ * T₂, G.mul_mem hT₁ hT₂, ?_, ?_, ?_, ?_, fun x hxa hxb hxc hxd => ?_⟩
  · show T₁ (T₂ a) = b
    rw [h2x a hab hac had, h1a]
  · show T₁ (T₂ b) = a
    rw [h2b, h1c]
  · show T₁ (T₂ c) = d
    rw [h2c, h1x d (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd)]
  · show T₁ (T₂ d) = c
    rw [h2d, h1b]
  · show T₁ (T₂ x) = x
    rw [h2x x hxb hxc hxd, h1x x hxa hxb hxc]

/-- **Removing the exchanges two at a time.** An element of `G` that sends `p` to its partner and
is, off the pair of `p`, an involution that fixes every pair it maps to itself, gives the flip of
the pair of `p` alone or times one exchange. Induction on the number of moved points. -/
theorem hasFlip_or_hasFlipExchange_of_moved {p : Ω} (n : ℕ) :
    ∀ σ ∈ G, {x | σ x ≠ x}.ncard < n → σ p = P.flip p →
      (∀ q, P.pair q ≠ P.pair p → σ (σ q) = q) →
      (∀ q, P.pair q ≠ P.pair p → P.pair (σ q) = P.pair q → σ q = q) →
      HasFlip P G p ∨ ∃ a b, P.pair a ≠ P.pair p ∧ P.pair b ≠ P.pair p ∧
        P.pair a ≠ P.pair b ∧ HasFlipExchange P G p a b := by
  induction n with
  | zero => exact fun σ _ hn => absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro σ hσ hn hp h2 h3
    -- no moved point off the pair of `p`: the flip alone
    by_cases hmove : ∀ x, P.pair x ≠ P.pair p → σ x = x
    · exact Or.inl ⟨σ, hσ, hp, hmove⟩
    push Not at hmove
    obtain ⟨a, hap, haσ⟩ := hmove
    have key : ∀ {x y : Ω}, P.pair x ≠ P.pair y → P.pair (σ x) ≠ P.pair (σ y) :=
      fun h h' => h ((hG.pair_apply_eq_iff hσ).mp h')
    have hσp : P.pair (σ p) = P.pair p := by rw [hp, P.pair_flip]
    have hbσ : σ (σ a) = a := h2 a hap
    have hbp : P.pair (σ a) ≠ P.pair p := fun h => key hap (h.trans hσp.symm)
    have hab : P.pair a ≠ P.pair (σ a) := fun h => haσ (h3 a hap h.symm)
    -- no further moved point: the flip times one exchange
    by_cases hmove2 : ∀ x, P.pair x ≠ P.pair p → P.pair x ≠ P.pair a →
        P.pair x ≠ P.pair (σ a) → σ x = x
    · exact Or.inr ⟨a, σ a, hap, hbp, hab, ⟨σ, hσ, hp, rfl, hbσ, hmove2⟩⟩
    push Not at hmove2
    obtain ⟨c, hcp, hca, hcb, hcσ⟩ := hmove2
    have hdσ : σ (σ c) = c := h2 c hcp
    have hdp : P.pair (σ c) ≠ P.pair p := fun h => key hcp (h.trans hσp.symm)
    have hcd : P.pair c ≠ P.pair (σ c) := fun h => hcσ (h3 c hcp h.symm)
    have hda : P.pair (σ c) ≠ P.pair a := by
      have h := key hcb
      rwa [hbσ] at h
    have hdb : P.pair (σ c) ≠ P.pair (σ a) := key hca
    -- the two exchanges `a ↔ σa`, `c ↔ σc` lie in `G`; remove them from `σ`
    obtain ⟨u, hu, hua, hub, huc, hud, hux⟩ :=
      hG.exists_double_exchange hab (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb) (Ne.symm hdb) hcd
    have hm : σ * u ∈ G := G.mul_mem hσ hu
    have e1 : (σ * u) a = a := by
      show σ (u a) = a
      rw [hua, hbσ]
    have e2 : (σ * u) (σ a) = σ a := by
      show σ (u (σ a)) = σ a
      rw [hub]
    have e3 : (σ * u) c = c := by
      show σ (u c) = c
      rw [huc, hdσ]
    have e4 : (σ * u) (σ c) = σ c := by
      show σ (u (σ c)) = σ c
      rw [hud]
    -- `σu` fixes the four pairs and agrees with `σ` off them
    have hfix : ∀ x, (P.pair x = P.pair a ∨ P.pair x = P.pair (σ a) ∨ P.pair x = P.pair c ∨
        P.pair x = P.pair (σ c)) → (σ * u) x = x := by
      rintro x (h | h | h | h)
      · exact hG.apply_eq_self_of_pair_eq hm e1 h
      · exact hG.apply_eq_self_of_pair_eq hm e2 h
      · exact hG.apply_eq_self_of_pair_eq hm e3 h
      · exact hG.apply_eq_self_of_pair_eq hm e4 h
    have hoff : ∀ x, ¬(P.pair x = P.pair a ∨ P.pair x = P.pair (σ a) ∨ P.pair x = P.pair c ∨
        P.pair x = P.pair (σ c)) → (σ * u) x = σ x := by
      intro x hx
      simp only [not_or] at hx
      show σ (u x) = σ x
      rw [hux x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2]
    have hσF : ∀ q, ¬(P.pair q = P.pair a ∨ P.pair q = P.pair (σ a) ∨ P.pair q = P.pair c ∨
        P.pair q = P.pair (σ c)) → ¬(P.pair (σ q) = P.pair a ∨ P.pair (σ q) = P.pair (σ a) ∨
          P.pair (σ q) = P.pair c ∨ P.pair (σ q) = P.pair (σ c)) := by
      intro q hq
      simp only [not_or] at hq ⊢
      obtain ⟨q1, q2, q3, q4⟩ := hq
      refine ⟨?_, key q1, ?_, key q3⟩
      · have h := key q2
        rwa [hbσ] at h
      · have h := key q4
        rwa [hdσ] at h
    refine ih (σ * u) hm ?_ ?_ (fun q hq => ?_) (fun q hq h => ?_)
    · -- fewer moved points: `a` is no longer moved
      refine lt_of_lt_of_le (Set.ncard_lt_ncard ⟨fun x hx => ?_, fun hsub => ?_⟩
        (hG.finite σ hσ)) (Nat.lt_succ_iff.mp hn)
      · by_cases hF : P.pair x = P.pair a ∨ P.pair x = P.pair (σ a) ∨ P.pair x = P.pair c ∨
            P.pair x = P.pair (σ c)
        · exact absurd (hfix x hF) hx
        · rw [Set.mem_setOf_eq, ← hoff x hF]
          exact hx
      · exact hsub (show a ∈ {x | σ x ≠ x} from haσ) e1
    · show σ (u p) = P.flip p
      rw [hux p (Ne.symm hap) (Ne.symm hbp) (Ne.symm hcp) (Ne.symm hdp), hp]
    · by_cases hF : P.pair q = P.pair a ∨ P.pair q = P.pair (σ a) ∨ P.pair q = P.pair c ∨
          P.pair q = P.pair (σ c)
      · rw [hfix q hF, hfix q hF]
      · rw [hoff q hF, hoff (σ q) (hσF q hF), h2 q hq]
    · by_cases hF : P.pair q = P.pair a ∨ P.pair q = P.pair (σ a) ∨ P.pair q = P.pair c ∨
          P.pair q = P.pair (σ c)
      · exact hfix q hF
      · rw [hoff q hF] at h ⊢
        exact h3 q hq h

/-- The flip of one pair gives the flip of every pair, by conjugation. -/
theorem hasFlip_of_hasFlip {p : Ω} (h : HasFlip P G p) (q : Ω) : HasFlip P G q := by
  obtain ⟨T, hT, hTp, hTx⟩ := h
  obtain ⟨g, hg, hgp, -⟩ :=
    hG.exists_apply_eq_of_fixed ∅ (x := p) (y := q) (by simp) (by simp)
  refine ⟨g * T * g⁻¹, G.mul_mem (G.mul_mem hg hT) (G.inv_mem hg), ?_, fun x hx => ?_⟩
  · show g (T (g⁻¹ q)) = P.flip q
    rw [← hgp, perm_inv_apply_self, hTp]
    exact hG.comm g hg p
  · show g (T (g⁻¹ x)) = x
    rw [hTx _ (hG.pair_inv_apply_ne hg (by rwa [hgp])), perm_apply_inv_self]

/-- One flip times one exchange gives all of them, by conjugation with triple transitivity. -/
theorem hasFlipExchange_of_hasFlipExchange {p a b : Ω} (hap : P.pair a ≠ P.pair p)
    (hbp : P.pair b ≠ P.pair p) (hab : P.pair a ≠ P.pair b) (h : HasFlipExchange P G p a b)
    {q c d : Ω} (hcq : P.pair c ≠ P.pair q) (hdq : P.pair d ≠ P.pair q)
    (hcd : P.pair c ≠ P.pair d) : HasFlipExchange P G q c d := by
  obtain ⟨T, hT, hTp, hTa, hTb, hTx⟩ := h
  obtain ⟨g, hg, hgp, hga, hgb⟩ := hG.exists_apply_three (Ne.symm hap) (Ne.symm hbp) hab
    (Ne.symm hcq) (Ne.symm hdq) hcd
  refine ⟨g * T * g⁻¹, G.mul_mem (G.mul_mem hg hT) (G.inv_mem hg), ?_, ?_, ?_,
    fun x hxq hxc hxd => ?_⟩
  · show g (T (g⁻¹ q)) = P.flip q
    rw [← hgp, perm_inv_apply_self, hTp]
    exact hG.comm g hg p
  · show g (T (g⁻¹ c)) = d
    rw [← hga, perm_inv_apply_self, hTa, hgb]
  · show g (T (g⁻¹ d)) = c
    rw [← hgb, perm_inv_apply_self, hTb, hga]
  · show g (T (g⁻¹ x)) = x
    rw [hTx _ (hG.pair_inv_apply_ne hg (by rwa [hgp])) (hG.pair_inv_apply_ne hg (by rwa [hga]))
      (hG.pair_inv_apply_ne hg (by rwa [hgb])), perm_apply_inv_self]

/-- **The flip of every pair, or the flip times one exchange for all triples of pairs.** Let
`σ ∈ G` be an involution that sends `p` to its partner and no point of another pair to its
partner. Then `G` contains the flip of every single pair, or, for all `q, c, d` in three distinct
pairs, the flip of the pair of `q` times the exchange of the pairs of `c` and `d`. -/
theorem forall_hasFlip_or_forall_hasFlipExchange {σ : Perm Ω} (hσ : σ ∈ G) {p : Ω}
    (hp : σ p = P.flip p) (hinv : ∀ q, σ (σ q) = q)
    (hoff : ∀ q, P.pair q ≠ P.pair p → σ q ≠ P.flip q) :
    (∀ q, HasFlip P G q) ∨ ∀ q c d, P.pair c ≠ P.pair q → P.pair d ≠ P.pair q →
      P.pair c ≠ P.pair d → HasFlipExchange P G q c d := by
  have h3 : ∀ q, P.pair q ≠ P.pair p → P.pair (σ q) = P.pair q → σ q = q := by
    intro q hq h
    rcases (P.pair_eq_iff q (σ q)).mp h.symm with h' | h'
    · exact h'
    · exact absurd h' (hoff q hq)
  rcases hG.hasFlip_or_hasFlipExchange_of_moved ({x | σ x ≠ x}.ncard + 1) σ hσ
    (Nat.lt_succ_self _) hp (fun q _ => hinv q) h3 with h | ⟨a, b, hap, hbp, hab, h⟩
  · exact Or.inl fun q => hG.hasFlip_of_hasFlip h q
  · exact Or.inr fun q c d hcq hdq hcd =>
      hG.hasFlipExchange_of_hasFlipExchange hap hbp hab h hcq hdq hcd

end IsWindowedSignedGroup

end GaloisForLFunctions.GaloisTheoryOfZeros
