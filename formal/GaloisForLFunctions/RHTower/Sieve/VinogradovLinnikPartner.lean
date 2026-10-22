import GaloisForLFunctions.RHTower.Sieve.VinogradovLinnikCount
import Mathlib.Algebra.BigOperators.ModEq

/-!
# Nested-congruence partners of a Vinogradov block

For a prime `p` and `k`-tuples in `[0, N)` whose entries are distinct modulo `p`, two blocks are
nested-compatible when their `j`-th power sums agree modulo `p^j` for each `j = 1..k`. When
`N < p^k`, the compatible partners of a fixed block embed into the solutions of Linnik's nested
power-sum congruences, so there are at most `k! p^(k(k-1)/2)` of them.

## Main results

- `VinogradovInjectiveBlock`, `vinogradovNestedCompatible`, `VinogradovCompatiblePartner`: blocks
  injective modulo `p`, the nested congruence relation, and the partners of a block.
- `vinogradovCompatiblePartnerEmbedding`: an embedding of the partners into
  `VinogradovLinnikSolution p k` at the block's nested signature.
- `card_vinogradovCompatiblePartner_le`: for prime `p`, `k < p` and `N < p^k`, a block has at most
  `k! · p^(k(k-1)/2)` compatible partners.

## Hypotheses

Unconditional. The count assumes `p` prime, `k < p` and `N < p^k`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- `k`-tuples in `[0, N)` whose entries are pairwise distinct modulo `p`. -/
def VinogradovInjectiveBlock (N p k : ℕ) :=
  {x : Fin k → Fin N //
    Function.Injective fun i => ((x i).val : ZMod p)}

noncomputable instance vinogradovInjectiveBlockFinite
    (N p k : ℕ) : Finite (VinogradovInjectiveBlock N p k) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance vinogradovInjectiveBlockFintype
    (N p k : ℕ) : Fintype (VinogradovInjectiveBlock N p k) := Fintype.ofFinite _

/-- Nested compatibility: `∑ x_i^j ≡ ∑ y_i^j (mod p^j)` for every `j = 1, ..., k`. -/
def vinogradovNestedCompatible {N p k : ℕ}
    (x y : VinogradovInjectiveBlock N p k) : Prop :=
  ∀ j : Fin k,
    (∑ i : Fin k, (x.1 i).val ^ (j.val + 1)) ≡
      ∑ i : Fin k, (y.1 i).val ^ (j.val + 1) [MOD p ^ (j.val + 1)]

/-- The blocks nested-compatible with a fixed block `x`. -/
def VinogradovCompatiblePartner {N p k : ℕ}
    (x : VinogradovInjectiveBlock N p k) :=
  {y : VinogradovInjectiveBlock N p k // vinogradovNestedCompatible x y}

noncomputable instance vinogradovCompatiblePartnerFinite
    {N p k : ℕ} (x : VinogradovInjectiveBlock N p k) :
    Finite (VinogradovCompatiblePartner x) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance vinogradovCompatiblePartnerFintype
    {N p k : ℕ} (x : VinogradovInjectiveBlock N p k) :
    Fintype (VinogradovCompatiblePartner x) := Fintype.ofFinite _

/-- Nested signature of a block: its `j`-th power sum reduced modulo `p^j`, for `j = 1, ..., k`. -/
def vinogradovBlockNestedSignature {N p k : ℕ} [NeZero p]
    (x : VinogradovInjectiveBlock N p k)
    (j : Fin k) : Fin (p ^ (j.val + 1)) :=
  ⟨(∑ i : Fin k, (x.1 i).val ^ (j.val + 1)) % p ^ (j.val + 1),
    Nat.mod_lt _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _)⟩

/-- For `N < p^k`, the full power signature modulo `p^k` of a block, reduced modulo `p^(j+1)`, is
the natural-number power sum of order `j + 1` reduced modulo `p^(j+1)`. -/
theorem vinogradovFullPowerSignature_val_mod
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hNp : N < p ^ k)
    (y : VinogradovInjectiveBlock N p k) (j : Fin k) :
    (vinogradovFullPowerSignature
      (⟨fun i => ((y.1 i).val : ZMod (p ^ k)), by
        intro i l h
        have hi : (y.1 i).val < p ^ k := (y.1 i).isLt.trans hNp
        have hl : (y.1 l).val < p ^ k := (y.1 l).isLt.trans hNp
        apply y.2
        simpa only [ZMod.cast_eq_val, ZMod.val_cast_of_lt hi,
          ZMod.val_cast_of_lt hl] using h⟩ :
          VinogradovLinnikTuple p k) j).val %
        p ^ (j.val + 1) =
      (∑ i : Fin k, (y.1 i).val ^ (j.val + 1)) % p ^ (j.val + 1) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  let z : ZMod (p ^ k) := ∑ i : Fin k,
    ((y.1 i).val : ZMod (p ^ k)) ^ (j.val + 1)
  have hcast :
      ((∑ i : Fin k, (y.1 i).val ^ (j.val + 1) : ℕ) : ZMod (p ^ k)) = z := by
    simp [z, Nat.cast_sum, Nat.cast_pow]
  have hmodpk := (ZMod.natCast_eq_natCast_iff'
    (∑ i : Fin k, (y.1 i).val ^ (j.val + 1)) z.val (p ^ k)).mp
      (hcast.trans z.natCast_zmod_val.symm)
  have hdvd : p ^ (j.val + 1) ∣ p ^ k := pow_dvd_pow p (by omega)
  have hsmall := Nat.ModEq.of_dvd hdvd hmodpk
  unfold Nat.ModEq at hsmall
  simpa [z, vinogradovFullPowerSignature] using hsmall.symm

/-- For prime `p` and `N < p^k`, the compatible partners of `x` embed into the Linnik solutions with
prescribed nested signature equal to that of `x`. -/
def vinogradovCompatiblePartnerEmbedding
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hNp : N < p ^ k)
    (x : VinogradovInjectiveBlock N p k) :
    VinogradovCompatiblePartner x ↪
      VinogradovLinnikSolution p k (vinogradovBlockNestedSignature x) where
  toFun y := ⟨
    ⟨fun i => ((y.1.1 i).val : ZMod (p ^ k)), by
      intro i l h
      have hi : (y.1.1 i).val < p ^ k := (y.1.1 i).isLt.trans hNp
      have hl : (y.1.1 l).val < p ^ k := (y.1.1 l).isLt.trans hNp
      apply y.1.2
      simpa only [ZMod.cast_eq_val, ZMod.val_cast_of_lt hi,
        ZMod.val_cast_of_lt hl] using h⟩,
    by
      intro j
      rw [vinogradovFullPowerSignature_val_mod hp hNp]
      change (∑ i : Fin k, (y.1.1 i).val ^ (j.val + 1)) % p ^ (j.val + 1) =
        (∑ i : Fin k, (x.1 i).val ^ (j.val + 1)) % p ^ (j.val + 1)
      exact (y.2 j).symm⟩
  inj' := by
    intro y z h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have hi := congrArg (fun w => ((w.1.1 i).val : ZMod (p ^ k))) h
    apply Fin.ext
    have hylt : (y.1.1 i).val < p ^ k := (y.1.1 i).isLt.trans hNp
    have hzlt : (z.1.1 i).val < p ^ k := (z.1.1 i).isLt.trans hNp
    simpa [ZMod.val_cast_of_lt hylt, ZMod.val_cast_of_lt hzlt] using
      congrArg ZMod.val hi

/-- For prime `p`, `k < p` and `N < p^k`, each block has at most `k! · p^(k(k-1)/2)`
nested-compatible partners. -/
theorem card_vinogradovCompatiblePartner_le
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hkp : k < p) (hNp : N < p ^ k)
    (x : VinogradovInjectiveBlock N p k) :
    Fintype.card (VinogradovCompatiblePartner x) ≤
      k.factorial * p ^ (k * (k - 1) / 2) := by
  letI : Fact p.Prime := ⟨hp⟩
  calc
    Fintype.card (VinogradovCompatiblePartner x) ≤
        Fintype.card (VinogradovLinnikSolution p k
          (vinogradovBlockNestedSignature x)) :=
      Fintype.card_le_of_embedding
        (vinogradovCompatiblePartnerEmbedding hp hNp x)
    _ ≤ k.factorial * p ^ (k * (k - 1) / 2) :=
      card_vinogradovLinnikSolution_le hkp _

end

end RHTower.Sieve

