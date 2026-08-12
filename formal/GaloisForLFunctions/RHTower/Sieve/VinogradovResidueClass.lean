import GaloisForLFunctions.RHTower.Sieve.PowerSumAffineTransform
import GaloisForLFunctions.RHTower.Sieve.VinogradovBlockCorrelation
import Mathlib.Algebra.Order.Floor.Div

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def VinogradovResidueClass (N p : ℕ) (a : ZMod p) :=
  {n : Fin N // ((n.val : ℕ) : ZMod p) = a}

noncomputable instance vinogradovResidueClassFinite
    (N p : ℕ) (a : ZMod p) : Finite (VinogradovResidueClass N p a) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance vinogradovResidueClassFintype
    (N p : ℕ) (a : ZMod p) : Fintype (VinogradovResidueClass N p a) :=
  Fintype.ofFinite _

def vinogradovResidueQuotient {N p : ℕ} {a : ZMod p}
    (n : VinogradovResidueClass N p a) : ℕ := n.1.val / p

theorem vinogradovResidueClass_modEq
    {N p : ℕ} [NeZero p] {a : ZMod p}
    (n : VinogradovResidueClass N p a) : n.1.val ≡ a.val [MOD p] := by
  apply (ZMod.natCast_eq_natCast_iff' n.1.val a.val p).mp
  exact n.2.trans a.natCast_zmod_val.symm

theorem vinogradovResidue_decomposition
    {N p : ℕ} [NeZero p] {a : ZMod p}
    (n : VinogradovResidueClass N p a) :
    n.1.val = p * vinogradovResidueQuotient n + a.val := by
  have hmod := vinogradovResidueClass_modEq n
  unfold Nat.ModEq at hmod
  unfold vinogradovResidueQuotient
  calc
    n.1.val = n.1.val % p + p * (n.1.val / p) := (Nat.mod_add_div _ _).symm
    _ = a.val + p * (n.1.val / p) := by
      rw [hmod, Nat.mod_eq_of_lt a.val_lt]
    _ = p * (n.1.val / p) + a.val := Nat.add_comm _ _

theorem vinogradovResidueQuotient_lt_ceilDiv
    {N p : ℕ} [NeZero p] {a : ZMod p}
    (n : VinogradovResidueClass N p a) :
    vinogradovResidueQuotient n < N ⌈/⌉ p := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  by_contra hnot
  have hceil : N ⌈/⌉ p ≤ vinogradovResidueQuotient n := Nat.le_of_not_gt hnot
  have hNle : N ≤ p * vinogradovResidueQuotient n :=
    (ceilDiv_le_iff_le_mul hp).mp hceil
  have hmul : p * vinogradovResidueQuotient n ≤ n.1.val := by
    exact Nat.mul_div_le n.1.val p
  exact (Nat.not_le_of_lt n.1.isLt) (hNle.trans hmul)

def vinogradovResidueQuotientFin
    {N p : ℕ} [NeZero p] {a : ZMod p}
    (n : VinogradovResidueClass N p a) : Fin (N ⌈/⌉ p) :=
  ⟨vinogradovResidueQuotient n, vinogradovResidueQuotient_lt_ceilDiv n⟩

theorem vinogradovResidueQuotientFin_injective
    {N p : ℕ} [NeZero p] {a : ZMod p} :
    Function.Injective (vinogradovResidueQuotientFin :
      VinogradovResidueClass N p a → Fin (N ⌈/⌉ p)) := by
  intro m n h
  apply Subtype.ext
  apply Fin.ext
  have hdiv : m.1.val / p = n.1.val / p := congrArg Fin.val h
  exact Nat.ext_div_mod hdiv
    (vinogradovResidueClass_modEq m |>.trans
      (vinogradovResidueClass_modEq n).symm)

def vinogradovResidueQuotientEmbedding
    {N p : ℕ} [NeZero p] (a : ZMod p) :
    VinogradovResidueClass N p a ↪ Fin (N ⌈/⌉ p) :=
  ⟨vinogradovResidueQuotientFin, vinogradovResidueQuotientFin_injective⟩

theorem vinogradovResidue_powerSignature_affine
    {q N p k b : ℕ} [NeZero q] [NeZero p] (a : ZMod p)
    (u : Fin b → VinogradovResidueClass N p a) :
    vinogradovPowerSignatureMod q k (fun i => (u i).1) =
      powerSumAffineConstant q k b (a.val : ZMod q) +
        powerSumAffineLinearTransform q k (p : ZMod q) (a.val : ZMod q)
          (vinogradovPowerSignatureMod q k
            (fun i => vinogradovResidueQuotientFin (u i))) := by
  have haffine := powerSumAffine_signature (q := q) (k := k) (b := b)
    (p : ZMod q) (a.val : ZMod q)
    (fun i : Fin b => ((vinogradovResidueQuotient (u i) : ℕ) : ZMod q))
  change vinogradovPowerSignatureMod q k (fun i => (u i).1) =
    powerSumAffineConstant q k b (a.val : ZMod q) +
      powerSumAffineLinearTransform q k (p : ZMod q) (a.val : ZMod q)
        (fun j : Fin k => ∑ i : Fin b,
          ((vinogradovResidueQuotient (u i) : ℕ) : ZMod q) ^ (j.val + 1))
  rw [← haffine]
  funext j
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← Nat.cast_mul, ← Nat.cast_add]
  exact congrArg (fun z : ℕ => (z : ZMod q))
    (vinogradovResidue_decomposition (u i))

end

end RHTower.Sieve
