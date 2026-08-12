import GaloisForLFunctions.RHTower.Sieve.VinogradovLinnikCount
import Mathlib.Algebra.BigOperators.ModEq

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def VinogradovInjectiveBlock (N p k : ℕ) :=
  {x : Fin k → Fin N //
    Function.Injective fun i => ((x i).val : ZMod p)}

noncomputable instance vinogradovInjectiveBlockFinite
    (N p k : ℕ) : Finite (VinogradovInjectiveBlock N p k) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance vinogradovInjectiveBlockFintype
    (N p k : ℕ) : Fintype (VinogradovInjectiveBlock N p k) := Fintype.ofFinite _

def vinogradovNestedCompatible {N p k : ℕ}
    (x y : VinogradovInjectiveBlock N p k) : Prop :=
  ∀ j : Fin k,
    (∑ i : Fin k, (x.1 i).val ^ (j.val + 1)) ≡
      ∑ i : Fin k, (y.1 i).val ^ (j.val + 1) [MOD p ^ (j.val + 1)]

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

def vinogradovBlockNestedSignature {N p k : ℕ} [NeZero p]
    (x : VinogradovInjectiveBlock N p k)
    (j : Fin k) : Fin (p ^ (j.val + 1)) :=
  ⟨(∑ i : Fin k, (x.1 i).val ^ (j.val + 1)) % p ^ (j.val + 1),
    Nat.mod_lt _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _)⟩

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

