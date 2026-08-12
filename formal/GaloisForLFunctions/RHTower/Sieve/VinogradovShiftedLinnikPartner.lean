import GaloisForLFunctions.RHTower.Sieve.VinogradovLinnikPartner
import GaloisForLFunctions.RHTower.Sieve.PowerSumTranslationRing

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

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

def vinogradovShiftedNestedCompatible
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hNp : N < p ^ k)
    (a : ZMod p) (x y : VinogradovInjectiveBlock N p k) : Prop :=
  ∀ j : Fin k,
    (vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a x) j).val %
        p ^ (j.val + 1) =
      (vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a y) j).val %
        p ^ (j.val + 1)

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

def vinogradovShiftedBlockNestedSignature
    {N p k : ℕ} [NeZero p] (hp : p.Prime) (hNp : N < p ^ k)
    (a : ZMod p) (x : VinogradovInjectiveBlock N p k)
    (j : Fin k) : Fin (p ^ (j.val + 1)) :=
  ⟨(vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a x) j).val %
      p ^ (j.val + 1),
    Nat.mod_lt _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _)⟩

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

