import GaloisForLFunctions.GaloisTheoryOfZeros.AnInvolutionWithOneFlippedPairGivesTheFlipOfOnePairUpToOneExchange

/-!
# A signed group with the even permutations and a flip up to an exchange has index at most two

Let `G` be a group of signed permutations of finite support that contains every signed 3-cycle
and every double flip (`IsWindowedSignedGroup`), and the flip of every single pair or, for all
triples of pairs, the flip of one pair times the exchange of the other two. Let `w` be any
permutation that commutes with the involution and moves finitely many points.

* `IsWindowedSignedGroup.mem_or_mul_mem`: `w ∈ G` or `w e ∈ G`, for the exchange `e` of any two
  pairs.
* `IsWindowedSignedGroup.mem_or_mem_or_mul_inv_mem`: of two such permutations, one lies in `G` or
  their quotient does. So `G` has index at most two in the group of all signed permutations of
  finite support.
* `IsWindowedSignedGroup.conj_mem`: `G` is normal in that group.
* `IsWindowedSignedGroup.mem_of_exchange_mem`: if `G` contains one exchange, it is that group.

Proof. Signed 3-cycles and double flips of `G` remove the moved points of `w` off three reference
pairs `p₀, a, a'` one at a time (`exists_mul_fix_off_three`). On the three pairs a signed 3-cycle
returns the pair of `p₀` to itself; then `w` or `w e` maps each of the pairs of `a` and `a'` to
itself, and double flips with `p₀` make it the identity on them (`exists_mul_fix_off_one`). What
is left is the identity or the flip of the pair of `p₀`, and `G` contains that flip alone or
times `e` (`mem_or_mul_mem_of_fix_off_one`).
-/

open Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

variable {Ω : Type*} {P : PairCoordinate Ω} {G : Subgroup (Perm Ω)}

/-! ## Permutations that commute with the involution -/

section Signed

variable {w : Perm Ω} (hw : ∀ x, w (P.flip x) = P.flip (w x))
include hw

/-- A permutation that commutes with the involution maps pairs to pairs. -/
theorem pair_apply_eq_iff_of_comm {x y : Ω} :
    P.pair (w x) = P.pair (w y) ↔ P.pair x = P.pair y := by
  constructor
  · intro h
    rcases (P.pair_eq_iff (w x) (w y)).mp h with h' | h'
    · rw [w.injective h']
    · rw [← hw] at h'
      rw [w.injective h', P.pair_flip]
  · intro h
    rcases (P.pair_eq_iff x y).mp h with h' | h'
    · rw [h']
    · rw [h', hw, P.pair_flip]

/-- A permutation that commutes with the involution and fixes a point fixes its partner. -/
theorem apply_eq_self_of_comm {t x : Ω} (ht : w t = t) (hx : P.pair x = P.pair t) : w x = x := by
  rcases (P.pair_eq_iff t x).mp hx.symm with h | h
  · rw [h]
    exact ht
  · rw [h, hw, ht]

end Signed

section Exchange

variable {a a' : Ω} {e : Perm Ω}

/-- The exchange of two pairs is an involution. -/
theorem pairExchange_mul_self (hea : e a = a') (hea' : e a' = a)
    (he : ∀ x, e (P.flip x) = P.flip (e x))
    (heo : ∀ x, P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → e x = x) : e * e = 1 :=
  Perm.ext fun x => by
    show e (e x) = x
    by_cases hxa : P.pair x = P.pair a
    · rcases (P.pair_eq_iff a x).mp hxa.symm with h' | h'
      · rw [h', hea, hea']
      · rw [h', he, hea, he, hea']
    by_cases hxa' : P.pair x = P.pair a'
    · rcases (P.pair_eq_iff a' x).mp hxa'.symm with h' | h'
      · rw [h', hea', hea]
      · rw [h', he, hea', he, hea]
    · rw [heo x hxa hxa', heo x hxa hxa']

/-- **The exchange of two pairs.** If the involution has no fixed point, two points `a`, `a'` in
distinct pairs are exchanged, with their partners, by a permutation that commutes with the
involution and is the identity off the two pairs. -/
theorem exists_pairExchange (hflip : ∀ x, P.flip x ≠ x) (haa' : P.pair a ≠ P.pair a') :
    ∃ e : Perm Ω, e a = a' ∧ e a' = a ∧ (∀ x, e (P.flip x) = P.flip (e x)) ∧
      ∀ x, P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → e x = x := by
  classical
  have h2 : a ≠ P.flip a' := fun h => haa' (by rw [h, P.pair_flip])
  have h3 : P.flip a ≠ a' := fun h => haa' (by rw [← h, P.pair_flip])
  have ea : (swap a a' * swap (P.flip a) (P.flip a')) a = a' := by
    show swap a a' (swap (P.flip a) (P.flip a') a) = a'
    rw [swap_apply_of_ne_of_ne (a := P.flip a) (b := P.flip a') (x := a) (hflip a).symm h2,
      swap_apply_left]
  have ea' : (swap a a' * swap (P.flip a) (P.flip a')) a' = a := by
    show swap a a' (swap (P.flip a) (P.flip a') a') = a
    rw [swap_apply_of_ne_of_ne (a := P.flip a) (b := P.flip a') (x := a') (Ne.symm h3)
      (hflip a').symm, swap_apply_right]
  have efa : (swap a a' * swap (P.flip a) (P.flip a')) (P.flip a) = P.flip a' := by
    show swap a a' (swap (P.flip a) (P.flip a') (P.flip a)) = P.flip a'
    rw [swap_apply_left]
    exact swap_apply_of_ne_of_ne (Ne.symm h2) (hflip a')
  have efa' : (swap a a' * swap (P.flip a) (P.flip a')) (P.flip a') = P.flip a := by
    show swap a a' (swap (P.flip a) (P.flip a') (P.flip a')) = P.flip a
    rw [swap_apply_right]
    exact swap_apply_of_ne_of_ne (hflip a) h3
  have eo : ∀ x, P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' →
      (swap a a' * swap (P.flip a) (P.flip a')) x = x := fun x hx hx' => by
    show swap a a' (swap (P.flip a) (P.flip a') x) = x
    rw [swap_apply_of_ne_of_ne (a := P.flip a) (b := P.flip a') (x := x)
      (fun h => hx (by rw [h, P.pair_flip])) (fun h => hx' (by rw [h, P.pair_flip]))]
    exact swap_apply_of_ne_of_ne (fun h => hx (by rw [h])) (fun h => hx' (by rw [h]))
  refine ⟨_, ea, ea', fun x => ?_, eo⟩
  by_cases hxa : P.pair x = P.pair a
  · rcases (P.pair_eq_iff a x).mp hxa.symm with h | h
    · rw [h, efa, ea]
    · rw [h, P.flip_flip, ea, efa, P.flip_flip]
  by_cases hxa' : P.pair x = P.pair a'
  · rcases (P.pair_eq_iff a' x).mp hxa'.symm with h | h
    · rw [h, efa', ea']
    · rw [h, P.flip_flip, ea', efa', P.flip_flip]
  · rw [eo x hxa hxa',
      eo (P.flip x) (by rw [P.pair_flip]; exact hxa) (by rw [P.pair_flip]; exact hxa')]

end Exchange

/-- `G` contains the flip of every single pair, or the flip of one pair times the exchange of two
others for all triples of pairs. -/
def HasFlipUpToExchange (P : PairCoordinate Ω) (G : Subgroup (Perm Ω)) : Prop :=
  (∀ q, HasFlip P G q) ∨ ∀ q c d, P.pair c ≠ P.pair q → P.pair d ≠ P.pair q →
    P.pair c ≠ P.pair d → HasFlipExchange P G q c d

namespace IsWindowedSignedGroup

variable (hG : IsWindowedSignedGroup P G)
include hG

/-! ## The normal form of a signed permutation modulo `G` -/

/-- An element of `G` that returns a point of the pair of `q` to `q` and is the identity off the
pairs of `q` and `t`: the identity or the double flip. -/
theorem exists_apply_eq_of_pair_eq {q t : Ω} (hqt : P.pair q ≠ P.pair t) {y : Ω}
    (hy : P.pair y = P.pair q) :
    ∃ T ∈ G, T y = q ∧ ∀ x, P.pair x ≠ P.pair q → P.pair x ≠ P.pair t → T x = x := by
  rcases (P.pair_eq_iff q y).mp hy.symm with h | h
  · exact ⟨1, G.one_mem, h, fun _ _ _ => rfl⟩
  · obtain ⟨T, hT, hTq, -, hTo⟩ := hG.hasDoubleFlip hqt
    exact ⟨T, hT, by rw [h, hG.comm T hT, hTq, P.flip_flip], hTo⟩

/-- **Clearing the moved points off three pairs.** For a permutation `w` that commutes with the
involution, some `g ∈ G` makes `g w` the identity off the pairs of `p₀`, `a`, `a'`. Induction on
the number of the points off the three pairs that `w` moves. -/
theorem exists_mul_fix_off_three {p₀ a a' : Ω} (hpa : P.pair p₀ ≠ P.pair a) (n : ℕ) :
    ∀ w : Perm Ω, (∀ x, w (P.flip x) = P.flip (w x)) →
      {x | w x ≠ x ∧ P.pair x ≠ P.pair p₀ ∧ P.pair x ≠ P.pair a ∧
        P.pair x ≠ P.pair a'}.Finite →
      {x | w x ≠ x ∧ P.pair x ≠ P.pair p₀ ∧ P.pair x ≠ P.pair a ∧
        P.pair x ≠ P.pair a'}.ncard < n →
      ∃ g ∈ G, ∀ x, P.pair x ≠ P.pair p₀ → P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' →
        (g * w) x = x := by
  induction n with
  | zero => exact fun w _ _ hn => absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro w hw hfin hn
    by_cases hmove : ∀ x, P.pair x ≠ P.pair p₀ → P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' →
        w x = x
    · exact ⟨1, G.one_mem, hmove⟩
    push Not at hmove
    obtain ⟨x, hx1, hx2, hx3, hwx⟩ := hmove
    -- an element of `G` that returns `w x` to `x` and fixes the fixed points of `w` off the pairs
    obtain ⟨T, hT, hTx, hTfix⟩ : ∃ T ∈ G, T (w x) = x ∧ ∀ z, P.pair z ≠ P.pair p₀ →
        P.pair z ≠ P.pair a → w z = z → T z = z := by
      by_cases hy : P.pair (w x) = P.pair x
      · -- `w x` is the partner of `x`: the double flip with the pair of `p₀`
        obtain ⟨T, hT, hTy, hTo⟩ := hG.exists_apply_eq_of_pair_eq hx1 hy
        exact ⟨T, hT, hTy, fun z h1 _ hz =>
          hTo z (fun h => hwx (apply_eq_self_of_comm hw hz h.symm)) h1⟩
      · -- the signed 3-cycle `w x → x → u` through a reference pair
        obtain ⟨u, hu, hux, huR⟩ : ∃ u, P.pair u ≠ P.pair (w x) ∧ P.pair u ≠ P.pair x ∧
            (P.pair u = P.pair p₀ ∨ P.pair u = P.pair a) := by
          by_cases h : P.pair (w x) = P.pair p₀
          · exact ⟨a, by rw [h]; exact hpa.symm, Ne.symm hx2, Or.inr rfl⟩
          · exact ⟨p₀, Ne.symm h, Ne.symm hx1, Or.inl rfl⟩
        obtain ⟨T, hT, hTy, -, -, hTo⟩ := hG.hasSignedCycle hy (Ne.symm hux) (Ne.symm hu)
        refine ⟨T, hT, hTy, fun z h1 h2 hz => hTo z (fun h => ?_) (fun h => ?_) (fun h => ?_)⟩
        · exact hwx (w.injective (apply_eq_self_of_comm hw hz h.symm))
        · exact hwx (apply_eq_self_of_comm hw hz h.symm)
        · rcases huR with e | e
          · exact h1 (h.trans e)
          · exact h2 (h.trans e)
    -- `T w` moves fewer points off the three pairs
    have hsub : {z | (T * w) z ≠ z ∧ P.pair z ≠ P.pair p₀ ∧ P.pair z ≠ P.pair a ∧
        P.pair z ≠ P.pair a'} ⊂
        {z | w z ≠ z ∧ P.pair z ≠ P.pair p₀ ∧ P.pair z ≠ P.pair a ∧ P.pair z ≠ P.pair a'} := by
      refine ⟨fun z hz => ⟨fun e => hz.1 ?_, hz.2⟩, fun hss => ?_⟩
      · show T (w z) = z
        rw [e]
        exact hTfix z hz.2.1 hz.2.2.1 e
      · exact (hss ⟨hwx, hx1, hx2, hx3⟩).1 hTx
    obtain ⟨g, hg, hgfix⟩ := ih (T * w)
      (fun z => by
        show T (w (P.flip z)) = P.flip (T (w z))
        rw [hw, hG.comm T hT])
      (hfin.subset hsub.subset)
      (lt_of_lt_of_le (Set.ncard_lt_ncard hsub hfin) (Nat.lt_succ_iff.mp hn))
    exact ⟨g * T, G.mul_mem hg hT, fun z h1 h2 h3 => by
      rw [mul_assoc]
      exact hgfix z h1 h2 h3⟩

variable {p₀ a a' : Ω}

/-- A signed permutation that is the identity off three pairs and maps the pairs of `a` and `a'`
to themselves is, up to an element of `G`, the identity off the pair of `p₀`. -/
theorem exists_mul_fix_off_one_of_pairs (hpa : P.pair p₀ ≠ P.pair a)
    (hpa' : P.pair p₀ ≠ P.pair a') (haa' : P.pair a ≠ P.pair a') {v : Perm Ω}
    (hv : ∀ x, v (P.flip x) = P.flip (v x))
    (hvo : ∀ x, P.pair x ≠ P.pair p₀ → P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → v x = x)
    (hva : P.pair (v a) = P.pair a) (hva' : P.pair (v a') = P.pair a') :
    ∃ g ∈ G, ∀ x, P.pair x ≠ P.pair p₀ → (g * v) x = x := by
  obtain ⟨T₁, hT₁, h1a, h1o⟩ := hG.exists_apply_eq_of_pair_eq (Ne.symm hpa) hva
  obtain ⟨T₂, hT₂, h2a, h2o⟩ := hG.exists_apply_eq_of_pair_eq (Ne.symm hpa') hva'
  refine ⟨T₂ * T₁, G.mul_mem hT₂ hT₁, fun x hx => ?_⟩
  have hc : ∀ z, (T₂ * T₁ * v) (P.flip z) = P.flip ((T₂ * T₁ * v) z) := fun z => by
    show T₂ (T₁ (v (P.flip z))) = P.flip (T₂ (T₁ (v z)))
    rw [hv, hG.comm T₁ hT₁, hG.comm T₂ hT₂]
  have ha : (T₂ * T₁ * v) a = a := by
    show T₂ (T₁ (v a)) = a
    rw [h1a, h2o a haa' (Ne.symm hpa)]
  have ha' : (T₂ * T₁ * v) a' = a' := by
    show T₂ (T₁ (v a')) = a'
    rw [h1o (v a') (by rw [hva']; exact Ne.symm haa') (by rw [hva']; exact Ne.symm hpa'), h2a]
  by_cases hxa : P.pair x = P.pair a
  · exact apply_eq_self_of_comm hc ha hxa
  by_cases hxa' : P.pair x = P.pair a'
  · exact apply_eq_self_of_comm hc ha' hxa'
  show T₂ (T₁ (v x)) = x
  rw [hvo x hx hxa hxa', h1o x hxa hx, h2o x hxa' hx]

variable {e : Perm Ω}

/-- A signed permutation `w` that is the identity off three pairs and maps the pair of `p₀` to
itself: up to an element of `G`, `w` or `w e` is the identity off the pair of `p₀`. -/
theorem exists_mul_fix_off_one_of_pair (hpa : P.pair p₀ ≠ P.pair a)
    (hpa' : P.pair p₀ ≠ P.pair a') (haa' : P.pair a ≠ P.pair a') (hea : e a = a')
    (hea' : e a' = a) (he : ∀ x, e (P.flip x) = P.flip (e x))
    (heo : ∀ x, P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → e x = x) {w : Perm Ω}
    (hw : ∀ x, w (P.flip x) = P.flip (w x))
    (hwo : ∀ x, P.pair x ≠ P.pair p₀ → P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → w x = x)
    (hwp : P.pair (w p₀) = P.pair p₀) :
    ∃ g ∈ G, (∀ x, P.pair x ≠ P.pair p₀ → (g * w) x = x) ∨
      ∀ x, P.pair x ≠ P.pair p₀ → (g * w * e) x = x := by
  have key : ∀ {x y : Ω}, P.pair x ≠ P.pair y → P.pair (w x) ≠ P.pair (w y) :=
    fun h h' => h ((pair_apply_eq_iff_of_comm hw).mp h')
  -- a point is fixed or mapped into the three pairs
  have hR : ∀ x, P.pair (w x) = P.pair p₀ ∨ P.pair (w x) = P.pair a ∨
      P.pair (w x) = P.pair a' ∨ w x = x := by
    intro x
    by_contra h
    rw [not_or, not_or, not_or] at h
    exact h.2.2.2 (w.injective (hwo (w x) h.1 h.2.1 h.2.2.1))
  have hwa : P.pair (w a) = P.pair a ∨ P.pair (w a) = P.pair a' := by
    rcases hR a with h | h | h | h
    · exact absurd (h.trans hwp.symm) (key (Ne.symm hpa))
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl (by rw [h])
  have hwa' : P.pair (w a') = P.pair a ∨ P.pair (w a') = P.pair a' := by
    rcases hR a' with h | h | h | h
    · exact absurd (h.trans hwp.symm) (key (Ne.symm hpa'))
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (by rw [h])
  rcases hwa with h | h
  · -- each of the two pairs is mapped to itself
    have h' : P.pair (w a') = P.pair a' := by
      rcases hwa' with h' | h'
      · exact absurd (h.trans h'.symm) (key haa')
      · exact h'
    obtain ⟨g, hg, hgo⟩ := hG.exists_mul_fix_off_one_of_pairs hpa hpa' haa' hw hwo h h'
    exact ⟨g, hg, Or.inl hgo⟩
  · -- the two pairs are exchanged: `w e` maps each of them to itself
    have h' : P.pair (w a') = P.pair a := by
      rcases hwa' with h' | h'
      · exact h'
      · exact absurd (h.trans h'.symm) (key haa')
    obtain ⟨g, hg, hgo⟩ := hG.exists_mul_fix_off_one_of_pairs (v := w * e) hpa hpa' haa'
      (fun x => by
        show w (e (P.flip x)) = P.flip (w (e x))
        rw [he, hw])
      (fun x h1 h2 h3 => by
        show w (e x) = x
        rw [heo x h2 h3, hwo x h1 h2 h3])
      (by
        show P.pair (w (e a)) = P.pair a
        rw [hea]
        exact h')
      (by
        show P.pair (w (e a')) = P.pair a'
        rw [hea']
        exact h)
    exact ⟨g, hg, Or.inr fun x hx => by
      rw [mul_assoc]
      exact hgo x hx⟩

/-- **From three pairs to one.** For a signed permutation `w` that is the identity off three
pairs, some `g ∈ G` makes `g w` or `g w e` the identity off the pair of `p₀`. -/
theorem exists_mul_fix_off_one (hpa : P.pair p₀ ≠ P.pair a) (hpa' : P.pair p₀ ≠ P.pair a')
    (haa' : P.pair a ≠ P.pair a') (hea : e a = a') (hea' : e a' = a)
    (he : ∀ x, e (P.flip x) = P.flip (e x))
    (heo : ∀ x, P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → e x = x) {w : Perm Ω}
    (hw : ∀ x, w (P.flip x) = P.flip (w x))
    (hwo : ∀ x, P.pair x ≠ P.pair p₀ → P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → w x = x) :
    ∃ g ∈ G, (∀ x, P.pair x ≠ P.pair p₀ → (g * w) x = x) ∨
      ∀ x, P.pair x ≠ P.pair p₀ → (g * w * e) x = x := by
  -- a signed 3-cycle returns the pair of `p₀` to itself
  obtain ⟨T, hT, hTp, hTo⟩ : ∃ T ∈ G, P.pair (T (w p₀)) = P.pair p₀ ∧ ∀ x,
      P.pair x ≠ P.pair p₀ → P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → T x = x := by
    by_cases hp : P.pair (w p₀) = P.pair p₀
    · exact ⟨1, G.one_mem, hp, fun _ _ _ _ => rfl⟩
    have hmem : P.pair (w p₀) = P.pair a ∨ P.pair (w p₀) = P.pair a' := by
      by_contra h
      rw [not_or] at h
      exact hp (by rw [w.injective (hwo (w p₀) hp h.1 h.2)])
    rcases hmem with h | h
    · obtain ⟨T, hT, hTy, -, -, hTo⟩ := hG.hasSignedCycle (p := w p₀) (q := p₀) (r := a')
        hp hpa' (by rw [h]; exact haa')
      exact ⟨T, hT, by rw [hTy], fun x h1 h2 h3 => hTo x (by rw [h]; exact h2) h1 h3⟩
    · obtain ⟨T, hT, hTy, -, -, hTo⟩ := hG.hasSignedCycle (p := w p₀) (q := p₀) (r := a)
        hp hpa (by rw [h]; exact Ne.symm haa')
      exact ⟨T, hT, by rw [hTy], fun x h1 h2 h3 => hTo x (by rw [h]; exact h3) h1 h2⟩
  obtain ⟨g, hg, hgo⟩ := hG.exists_mul_fix_off_one_of_pair (w := T * w) hpa hpa' haa' hea hea'
    he heo
    (fun x => by
      show T (w (P.flip x)) = P.flip (T (w x))
      rw [hw, hG.comm T hT])
    (fun x h1 h2 h3 => by
      show T (w x) = x
      rw [hwo x h1 h2 h3, hTo x h1 h2 h3])
    hTp
  refine ⟨g * T, G.mul_mem hg hT, ?_⟩
  rcases hgo with h | h
  · exact Or.inl fun x hx => by
      rw [mul_assoc]
      exact h x hx
  · exact Or.inr fun x hx => by
      rw [mul_assoc g T w]
      exact h x hx

/-- **What is left on one pair.** A signed permutation `u` that is the identity off the pair of
`p₀` is the identity or the flip of that pair: `u ∈ G` or `u e ∈ G`. -/
theorem mem_or_mul_mem_of_fix_off_one (hpa : P.pair p₀ ≠ P.pair a)
    (hpa' : P.pair p₀ ≠ P.pair a') (hodd : HasFlip P G p₀ ∨ HasFlipExchange P G p₀ a a')
    (hea : e a = a') (hea' : e a' = a) (he : ∀ x, e (P.flip x) = P.flip (e x))
    (heo : ∀ x, P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → e x = x) {u : Perm Ω}
    (hu : ∀ x, u (P.flip x) = P.flip (u x)) (huo : ∀ x, P.pair x ≠ P.pair p₀ → u x = x) :
    u ∈ G ∨ u * e ∈ G := by
  have hup : u p₀ = p₀ ∨ u p₀ = P.flip p₀ := by
    by_contra h
    rw [not_or] at h
    have hne : P.pair (u p₀) ≠ P.pair p₀ := fun e' => by
      rcases (P.pair_eq_iff p₀ (u p₀)).mp e'.symm with h' | h'
      · exact h.1 h'
      · exact h.2 h'
    exact h.1 (u.injective (huo (u p₀) hne))
  rcases hup with h | h
  · -- the identity
    have h1 : u = 1 := Perm.ext fun x => by
      by_cases hx : P.pair x = P.pair p₀
      · exact apply_eq_self_of_comm hu h hx
      · exact huo x hx
    rw [h1]
    exact Or.inl G.one_mem
  rcases hodd with ⟨T, hT, hTp, hTo⟩ | ⟨T, hT, hTp, hTa, hTa', hTo⟩
  · -- the flip of the pair of `p₀`
    have h1 : u = T := Perm.ext fun x => by
      by_cases hx : P.pair x = P.pair p₀
      · rcases (P.pair_eq_iff p₀ x).mp hx.symm with h' | h'
        · rw [h', h, hTp]
        · rw [h', hu, hG.comm T hT, h, hTp]
      · rw [huo x hx, hTo x hx]
    rw [h1]
    exact Or.inl hT
  · -- the flip times the exchange
    have h1 : u * e = T := Perm.ext fun x => by
      show u (e x) = T x
      by_cases hxp : P.pair x = P.pair p₀
      · rw [heo x (by rw [hxp]; exact hpa) (by rw [hxp]; exact hpa')]
        rcases (P.pair_eq_iff p₀ x).mp hxp.symm with h' | h'
        · rw [h', h, hTp]
        · rw [h', hu, hG.comm T hT, h, hTp]
      by_cases hxa : P.pair x = P.pair a
      · rcases (P.pair_eq_iff a x).mp hxa.symm with h' | h'
        · rw [h', hea, hTa, huo a' (Ne.symm hpa')]
        · rw [h', he, hea, hG.comm T hT, hTa,
            huo (P.flip a') (by rw [P.pair_flip]; exact Ne.symm hpa')]
      by_cases hxa' : P.pair x = P.pair a'
      · rcases (P.pair_eq_iff a' x).mp hxa'.symm with h' | h'
        · rw [h', hea', hTa', huo a (Ne.symm hpa)]
        · rw [h', he, hea', hG.comm T hT, hTa',
            huo (P.flip a) (by rw [P.pair_flip]; exact Ne.symm hpa)]
      · rw [heo x hxa hxa', huo x hxp, hTo x hxp hxa hxa']
    rw [h1]
    exact Or.inr hT

/-! ## Index at most two -/

/-- **`G` or its coset by one exchange.** Every signed permutation `w` of finite support lies in
`G`, or `w e` does, for the exchange `e` of any two pairs. -/
theorem mem_or_mul_mem (hodd : HasFlipUpToExchange P G) (haa' : P.pair a ≠ P.pair a')
    (hea : e a = a') (hea' : e a' = a) (he : ∀ x, e (P.flip x) = P.flip (e x))
    (heo : ∀ x, P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → e x = x) {w : Perm Ω}
    (hw : ∀ x, w (P.flip x) = P.flip (w x)) (hfin : {x | w x ≠ x}.Finite) :
    w ∈ G ∨ w * e ∈ G := by
  -- a third pair
  obtain ⟨p₀, hp₀⟩ := hG.exists_pair_not_mem ({P.pair a, P.pair a'} : Finset ℤ)
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hp₀
  obtain ⟨hpa, hpa'⟩ := hp₀
  have hodd' : HasFlip P G p₀ ∨ HasFlipExchange P G p₀ a a' :=
    hodd.imp (fun h => h p₀) fun h => h p₀ a a' (Ne.symm hpa) (Ne.symm hpa') haa'
  obtain ⟨g₁, hg₁, h₁⟩ := hG.exists_mul_fix_off_three (a' := a') hpa _ w hw
    (hfin.subset fun x hx => hx.1) (Nat.lt_succ_self _)
  have hw₁ : ∀ x, (g₁ * w) (P.flip x) = P.flip ((g₁ * w) x) := fun x => by
    show g₁ (w (P.flip x)) = P.flip (g₁ (w x))
    rw [hw, hG.comm g₁ hg₁]
  obtain ⟨g₂, hg₂, h₂⟩ := hG.exists_mul_fix_off_one hpa hpa' haa' hea hea' he heo hw₁ h₁
  have hg : g₂ * g₁ ∈ G := G.mul_mem hg₂ hg₁
  have hc : ∀ x, (g₂ * g₁ * w) (P.flip x) = P.flip ((g₂ * g₁ * w) x) := fun x => by
    show g₂ (g₁ (w (P.flip x))) = P.flip (g₂ (g₁ (w x)))
    rw [hw, hG.comm g₁ hg₁, hG.comm g₂ hg₂]
  rcases h₂ with h | h
  · rcases hG.mem_or_mul_mem_of_fix_off_one hpa hpa' hodd' hea hea' he heo hc
      (fun x hx => by
        rw [mul_assoc]
        exact h x hx) with h' | h'
    · exact Or.inl ((G.mul_mem_cancel_left hg).mp h')
    · rw [mul_assoc] at h'
      exact Or.inr ((G.mul_mem_cancel_left hg).mp h')
  · have hce : ∀ x, (g₂ * g₁ * w * e) (P.flip x) = P.flip ((g₂ * g₁ * w * e) x) := fun x => by
      show g₂ (g₁ (w (e (P.flip x)))) = P.flip (g₂ (g₁ (w (e x))))
      rw [he, hw, hG.comm g₁ hg₁, hG.comm g₂ hg₂]
    rcases hG.mem_or_mul_mem_of_fix_off_one hpa hpa' hodd' hea hea' he heo hce
      (fun x hx => by
        rw [mul_assoc g₂ g₁ w]
        exact h x hx) with h' | h'
    · rw [mul_assoc] at h'
      exact Or.inr ((G.mul_mem_cancel_left hg).mp h')
    · rw [mul_assoc (g₂ * g₁ * w), pairExchange_mul_self hea hea' he heo, mul_one] at h'
      exact Or.inl ((G.mul_mem_cancel_left hg).mp h')

/-- **One exchange decides.** If `G` contains the exchange of two pairs, it contains every signed
permutation of finite support. -/
theorem mem_of_exchange_mem (hodd : HasFlipUpToExchange P G) (haa' : P.pair a ≠ P.pair a')
    (hea : e a = a') (hea' : e a' = a) (he : ∀ x, e (P.flip x) = P.flip (e x))
    (heo : ∀ x, P.pair x ≠ P.pair a → P.pair x ≠ P.pair a' → e x = x) (heG : e ∈ G)
    {w : Perm Ω} (hw : ∀ x, w (P.flip x) = P.flip (w x)) (hfin : {x | w x ≠ x}.Finite) :
    w ∈ G := by
  rcases hG.mem_or_mul_mem hodd haa' hea hea' he heo hw hfin with h | h
  · exact h
  · exact (G.mul_mem_cancel_right heG).mp h

/-- **Index at most two.** Of two signed permutations of finite support, one lies in `G` or
their quotient does. -/
theorem mem_or_mem_or_mul_inv_mem (hflip : ∀ x, P.flip x ≠ x) (hodd : HasFlipUpToExchange P G)
    {w₁ w₂ : Perm Ω} (hw₁ : ∀ x, w₁ (P.flip x) = P.flip (w₁ x))
    (hfin₁ : {x | w₁ x ≠ x}.Finite) (hw₂ : ∀ x, w₂ (P.flip x) = P.flip (w₂ x))
    (hfin₂ : {x | w₂ x ≠ x}.Finite) : w₁ ∈ G ∨ w₂ ∈ G ∨ w₁ * w₂⁻¹ ∈ G := by
  obtain ⟨a, ha⟩ := hG.surjective 0
  obtain ⟨a', ha'⟩ := hG.surjective 1
  have haa' : P.pair a ≠ P.pair a' := by
    rw [ha, ha']
    exact zero_ne_one
  obtain ⟨e, hea, hea', he, heo⟩ := exists_pairExchange hflip haa'
  rcases hG.mem_or_mul_mem hodd haa' hea hea' he heo hw₁ hfin₁ with h1 | h1
  · exact Or.inl h1
  rcases hG.mem_or_mul_mem hodd haa' hea hea' he heo hw₂ hfin₂ with h2 | h2
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ?_)
    have h := G.mul_mem h1 (G.inv_mem h2)
    rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left] at h

/-- **`G` is normal in the signed permutations of finite support.** -/
theorem conj_mem (hflip : ∀ x, P.flip x ≠ x) (hodd : HasFlipUpToExchange P G) {w : Perm Ω}
    (hw : ∀ x, w (P.flip x) = P.flip (w x)) (hfin : {x | w x ≠ x}.Finite) {g : Perm Ω}
    (hg : g ∈ G) : w * g * w⁻¹ ∈ G := by
  have hwg : ∀ x, (w * g) (P.flip x) = P.flip ((w * g) x) := fun x => by
    show w (g (P.flip x)) = P.flip (w (g x))
    rw [hG.comm g hg, hw]
  have hfin' : {x | (w * g) x ≠ x}.Finite :=
    ((hG.finite g hg).union hfin).subset fun x hx => by
      by_contra h
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
      exact hx (by
        show w (g x) = x
        rw [h.1, h.2])
  rcases hG.mem_or_mem_or_mul_inv_mem hflip hodd hwg hfin' hw hfin with h | h | h
  · have hw' : w ∈ G := (G.mul_mem_cancel_right hg).mp h
    exact G.mul_mem (G.mul_mem hw' hg) (G.inv_mem hw')
  · exact G.mul_mem (G.mul_mem h hg) (G.inv_mem h)
  · exact h

end IsWindowedSignedGroup

end GaloisForLFunctions.GaloisTheoryOfZeros
