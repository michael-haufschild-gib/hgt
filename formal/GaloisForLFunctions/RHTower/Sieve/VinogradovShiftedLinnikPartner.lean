import GaloisForLFunctions.RHTower.Sieve.VinogradovLinnikPartner
import GaloisForLFunctions.RHTower.Sieve.PowerSumTranslationRing

/-!
# Shifted Linnik partners of a Vinogradov block

Translating a block `x ∈ [0, N)^k` whose entries are distinct modulo the prime `p` by a residue `a`
gives a Linnik tuple `x - a` in `ZMod (p^k)`, still distinct modulo `p`. Two blocks are shifted
nested-compatible when their translates have equal `j`-th power sums modulo `p^j` for `j = 1..k`.
For `N < p^k` the shifted partners of a block embed into the solutions of Linnik's nested
congruences, so there are at most `k! p^(k(k-1)/2)` of them.

## Main results

- `vinogradovShiftedBlock`: the translate `x - a` as a Linnik tuple modulo `p^k`.
- `vinogradovShiftedNestedCompatible`, `VinogradovShiftedCompatiblePartner`: the shifted nested
  congruence relation and the partners of a block.
- `vinogradovShiftedCompatiblePartnerEmbedding`: an embedding of the partners into
  `VinogradovLinnikSolution p k` with the block's shifted nested signature.
- `card_vinogradovShiftedCompatiblePartner_le`: for prime `p`, `k < p` and `N < p^k`, at most
  `k! · p^(k(k-1)/2)` shifted partners.

## Hypotheses

Unconditional. The count assumes `p` prime, `k < p` and `N < p^k`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The translate `x - a` of a block injective modulo `p`, as a `k`-tuple in `ZMod (p^k)` with
distinct reductions modulo `p`. -/
def vinogradovShiftedBlock
    {N p k : ℕ} [NeZero p] (_hp : p.Prime) (hNp : N < p ^ k)
    (a : ZMod p) (x : VinogradovInjectiveBlock N p k) :
    VinogradovLinnikTuple p k :=
  ⟨fun i => ((x.1 i).val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k)), by
    intro i l h
    apply x.2
    have hk : k ≠ 0 := by
      intro hk
      subst k
      exact Fin.elim0 i
    let castp : ZMod (p ^ k) →+* ZMod p :=
      ZMod.castHom (dvd_pow_self p hk) (ZMod p)
    have h' : castp (((x.1 i).val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k))) =
        castp (((x.1 l).val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k))) := by
      simpa [castp, ZMod.castHom_apply] using h
    have h'' : ((x.1 i).val : ZMod p) - (a.val : ZMod p) =
        ((x.1 l).val : ZMod p) - (a.val : ZMod p) := by
      simpa only [map_sub, map_natCast] using h'
    exact sub_left_inj.mp h''⟩

/-- Shifted nested compatibility at `a`: `∑ (x_i - a)^j ≡ ∑ (y_i - a)^j (mod p^j)` for `j = 1..k`. -/
def vinogradovShiftedNestedCompatible
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hNp : N < p ^ k)
    (a : ZMod p) (x y : VinogradovInjectiveBlock N p k) : Prop :=
  ∀ j : Fin k,
    (vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a x) j).val %
        p ^ (j.val + 1) =
      (vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a y) j).val %
        p ^ (j.val + 1)

/-- The blocks that are shifted nested-compatible with a fixed block `x` at residue `a`. -/
def VinogradovShiftedCompatiblePartner
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hNp : N < p ^ k)
    (a : ZMod p) (x : VinogradovInjectiveBlock N p k) :=
  {y : VinogradovInjectiveBlock N p k //
    vinogradovShiftedNestedCompatible hp hNp a x y}

noncomputable instance vinogradovShiftedCompatiblePartnerFinite
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hNp : N < p ^ k)
    (a : ZMod p) (x : VinogradovInjectiveBlock N p k) :
    Finite (VinogradovShiftedCompatiblePartner hp hNp a x) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance vinogradovShiftedCompatiblePartnerFintype
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hNp : N < p ^ k)
    (a : ZMod p) (x : VinogradovInjectiveBlock N p k) :
    Fintype (VinogradovShiftedCompatiblePartner hp hNp a x) := Fintype.ofFinite _

/-- Nested signature of the shifted block: its `j`-th power sum reduced modulo `p^j`, `j = 1..k`. -/
def vinogradovShiftedBlockNestedSignature
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hNp : N < p ^ k)
    (a : ZMod p) (x : VinogradovInjectiveBlock N p k)
    (j : Fin k) : Fin (p ^ (j.val + 1)) :=
  ⟨(vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a x) j).val %
      p ^ (j.val + 1),
    Nat.mod_lt _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _)⟩

/-- For `N < p^k`, `y ↦ y - a` embeds the shifted partners of `x` into the Linnik solutions with the
shifted nested signature of `x`. -/
def vinogradovShiftedCompatiblePartnerEmbedding
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hNp : N < p ^ k)
    (a : ZMod p) (x : VinogradovInjectiveBlock N p k) :
    VinogradovShiftedCompatiblePartner hp hNp a x ↪
      VinogradovLinnikSolution p k
        (vinogradovShiftedBlockNestedSignature hp hNp a x) where
  toFun y := ⟨vinogradovShiftedBlock hp hNp a y.1, fun j => (y.2 j).symm⟩
  inj' := by
    intro y z h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have hi := congrArg (fun w => w.1.1 i) h
    change ((y.1.1 i).val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k)) =
      ((z.1.1 i).val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k)) at hi
    have hcast : ((y.1.1 i).val : ZMod (p ^ k)) =
        ((z.1.1 i).val : ZMod (p ^ k)) := sub_left_inj.mp hi
    apply Fin.ext
    have hylt : (y.1.1 i).val < p ^ k := (y.1.1 i).isLt.trans hNp
    have hzlt : (z.1.1 i).val < p ^ k := (z.1.1 i).isLt.trans hNp
    simpa [ZMod.val_cast_of_lt hylt, ZMod.val_cast_of_lt hzlt] using
      congrArg ZMod.val hcast

/-- For prime `p`, `k < p` and `N < p^k`, a block has at most `k! · p^(k(k-1)/2)` shifted
nested-compatible partners at any residue `a`. -/
theorem card_vinogradovShiftedCompatiblePartner_le
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hkp : k < p)
    (hNp : N < p ^ k) (a : ZMod p) (x : VinogradovInjectiveBlock N p k) :
    Fintype.card (VinogradovShiftedCompatiblePartner hp hNp a x) ≤
      k.factorial * p ^ (k * (k - 1) / 2) := by
  letI : Fact p.Prime := ⟨hp⟩
  calc
    Fintype.card (VinogradovShiftedCompatiblePartner hp hNp a x) ≤
        Fintype.card (VinogradovLinnikSolution p k
          (vinogradovShiftedBlockNestedSignature hp hNp a x)) :=
      Fintype.card_le_of_embedding
        (vinogradovShiftedCompatiblePartnerEmbedding hp hNp a x)
    _ ≤ k.factorial * p ^ (k * (k - 1) / 2) :=
      card_vinogradovLinnikSolution_le hkp _

end

end RHTower.Sieve

