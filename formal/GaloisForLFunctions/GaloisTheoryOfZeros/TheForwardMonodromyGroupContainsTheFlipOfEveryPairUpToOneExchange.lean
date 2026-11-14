import GaloisForLFunctions.GaloisTheoryOfZeros.TheCentreValueHasASimpleZeroAtAForwardTime
import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnAroundACollisionOfOnePairAtTheCentreFlipsExactlyOnePair
import GaloisForLFunctions.GaloisTheoryOfZeros.AnInvolutionWithOneFlippedPairGivesTheFlipOfOnePairUpToOneExchange

/-!
# The forward monodromy group contains the flip of every pair up to one exchange

Let `b` be a forward time off the branch times. The forward monodromy group `G₊(b)` consists of
signed permutations of finite support of the zeros of `H_b`, and it contains every signed 3-cycle
and every double flip.

**Theorem** (`forall_flip_or_forall_flip_exchange_mem_forwardMonodromy`). Either `G₊(b)` contains
the flip `p ↔ −p` of every single pair, or it contains, for all zeros `p, a, a'` in three
distinct pairs, the flip of `p` times the exchange `a ↔ a'`, `−a ↔ −a'`.

In both cases `G₊(b)` contains an odd permutation of the zeros
(`exists_mem_forwardMonodromy_flip_up_to_exchange`): the sign of the permutation of the zeros is
not trivial on `G₊(b)`. Which case holds is the sign, on the pairs, of the turn around a simple
zero of the centre value.

Proof. The centre value `c(τ) = H_τ(0)` has a simple zero at a forward time `τ₀`
(`exists_isCollision_center_two`). The turn around `τ₀` is an involution in `G₊(b)` that carries
exactly one pair to itself with the sign reversed
(`exists_mem_forwardMonodromy_involution_one_flip`). Its exchanges are removed two at a time by
signed 3-cycles (`IsWindowedSignedGroup.forall_hasFlip_or_forall_hasFlipExchange`).
-/

open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-- The pairs of the zeros of `H_b` carry a coordinate for which `G₊(b)` is a windowed signed
group that contains the flip of every single pair, or the flip of one pair times the exchange of
two others for all triples of pairs. -/
theorem exists_pairCoordinate_forall_hasFlip_or_forall_hasFlipExchange {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) :
    ∃ P : PairCoordinate {z : ℂ // complexHeat b z = 0}, (∀ x, P.flip x = fibreNeg b x) ∧
      IsWindowedSignedGroup P (forwardMonodromy b hb₀ hb) ∧
      ((∀ q, HasFlip P (forwardMonodromy b hb₀ hb) q) ∨ ∀ q c d, P.pair c ≠ P.pair q →
        P.pair d ≠ P.pair q → P.pair c ≠ P.pair d →
          HasFlipExchange P (forwardMonodromy b hb₀ hb) q c d) := by
  obtain ⟨τ₀, hτ₀, hcen⟩ := exists_isCollision_center_two 0
  obtain ⟨σ, hσ, p₀, hp₀, hinv, hoff⟩ :=
    exists_mem_forwardMonodromy_involution_one_flip hτ₀ hcen hb₀ hb
  obtain ⟨P, hP, hG⟩ := exists_pairCoordinate_isWindowedSignedGroup hb₀ hb
  have hne' : ∀ {x y : {z : ℂ // complexHeat b z = 0}}, P.pair x ≠ P.pair y →
      x ≠ y ∧ x ≠ fibreNeg b y := by
    intro x y h
    refine ⟨fun e => h (by rw [e]), fun e => h ?_⟩
    rw [e, ← hP, P.pair_flip]
  exact ⟨P, hP, hG, hG.forall_hasFlip_or_forall_hasFlipExchange hσ (p := p₀)
    (by rw [hP]; exact hp₀) hinv fun q hq => by rw [hP]; exact hoff q (hne' hq).1 (hne' hq).2⟩

/-- **The flip of every pair, or the flip times one exchange for all triples of pairs.** At a
forward time `b` off the branch times, `G₊(b)` contains the flip of every single pair, or it
contains, for all zeros `p, a, a'` in three distinct pairs, the element that exchanges `p ↔ −p`
and `a ↔ a'` and fixes every zero off the three pairs. -/
theorem forall_flip_or_forall_flip_exchange_mem_forwardMonodromy {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) :
    (∀ p : {z : ℂ // complexHeat b z = 0}, ∃ T ∈ forwardMonodromy b hb₀ hb,
        T p = fibreNeg b p ∧ ∀ x, x ≠ p → x ≠ fibreNeg b p → T x = x) ∨
      ∀ p a a' : {z : ℂ // complexHeat b z = 0}, a ≠ p → a ≠ fibreNeg b p → a' ≠ p →
        a' ≠ fibreNeg b p → a' ≠ a → a' ≠ fibreNeg b a →
        ∃ T ∈ forwardMonodromy b hb₀ hb, T p = fibreNeg b p ∧ T a = a' ∧ T a' = a ∧
          ∀ x, x ≠ p → x ≠ fibreNeg b p → x ≠ a → x ≠ fibreNeg b a → x ≠ a' →
            x ≠ fibreNeg b a' → T x = x := by
  obtain ⟨P, hP, -, hodd⟩ :=
    exists_pairCoordinate_forall_hasFlip_or_forall_hasFlipExchange hb₀ hb
  -- two zeros lie in distinct pairs iff they are neither equal nor opposite
  have hne : ∀ {x y : {z : ℂ // complexHeat b z = 0}}, x ≠ y → x ≠ fibreNeg b y →
      P.pair x ≠ P.pair y := by
    intro x y h1 h2 h
    rcases (P.pair_eq_iff y x).mp h.symm with h' | h'
    · exact h1 h'
    · exact h2 (h'.trans (hP y))
  rcases hodd with h | h
  · refine Or.inl fun p => ?_
    obtain ⟨T, hT, hTp, hTx⟩ := h p
    exact ⟨T, hT, by rw [← hP]; exact hTp, fun x hx hx' => hTx x (hne hx hx')⟩
  · refine Or.inr fun p a a' h1 h2 h3 h4 h5 h6 => ?_
    obtain ⟨T, hT, hTp, hTa, hTa', hTx⟩ :=
      h p a a' (hne h1 h2) (hne h3 h4) (Ne.symm (hne h5 h6))
    exact ⟨T, hT, by rw [← hP]; exact hTp, hTa, hTa', fun x x1 x2 x3 x4 x5 x6 =>
      hTx x (hne x1 x2) (hne x3 x4) (hne x5 x6)⟩

/-- **`G₊` contains the flip of a pair up to one exchange.** For all zeros `p, a, a'` of `H_b` in
three distinct pairs, `G₊(b)` contains an element that exchanges `p` and `−p`, fixes or exchanges
`a` and `a'`, and fixes every zero off the three pairs. It is an odd permutation of the zeros. -/
theorem exists_mem_forwardMonodromy_flip_up_to_exchange {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) {p a a' : {z : ℂ // complexHeat b z = 0}} (h1 : a ≠ p)
    (h2 : a ≠ fibreNeg b p) (h3 : a' ≠ p) (h4 : a' ≠ fibreNeg b p) (h5 : a' ≠ a)
    (h6 : a' ≠ fibreNeg b a) :
    ∃ T ∈ forwardMonodromy b hb₀ hb, T p = fibreNeg b p ∧
      (T a = a ∧ T a' = a' ∨ T a = a' ∧ T a' = a) ∧
        ∀ x, x ≠ p → x ≠ fibreNeg b p → x ≠ a → x ≠ fibreNeg b a → x ≠ a' →
          x ≠ fibreNeg b a' → T x = x := by
  rcases forall_flip_or_forall_flip_exchange_mem_forwardMonodromy hb₀ hb with h | h
  · obtain ⟨T, hT, hTp, hTx⟩ := h p
    exact ⟨T, hT, hTp, Or.inl ⟨hTx a h1 h2, hTx a' h3 h4⟩, fun x hx hx' _ _ _ _ => hTx x hx hx'⟩
  · obtain ⟨T, hT, hTp, hTa, hTa', hTx⟩ := h p a a' h1 h2 h3 h4 h5 h6
    exact ⟨T, hT, hTp, Or.inr ⟨hTa, hTa'⟩, hTx⟩

end GaloisForLFunctions.GaloisTheoryOfZeros
