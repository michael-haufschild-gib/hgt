import GaloisForLFunctions.HTGeometry.EllipticGammaLogKernel
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Fin.Rev

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

def ellipticGammaResidueShuffle (m n : ℕ) :
    ((Fin m × Fin n) × (ℕ × ℕ)) ≃ ((ℕ × Fin m) × (ℕ × Fin n)) where
  toFun u := ((u.2.1, u.1.1), (u.2.2, u.1.2))
  invFun u := ((u.1.2, u.2.2), (u.1.1, u.2.1))
  left_inv u := by rcases u with ⟨⟨a, b⟩, ⟨j, k⟩⟩; rfl
  right_inv u := by rcases u with ⟨⟨j, a⟩, ⟨k, b⟩⟩; rfl

def ellipticGammaResidueEquiv (m n : ℕ) [NeZero m] [NeZero n] :
    ((Fin m × Fin n) × (ℕ × ℕ)) ≃ (ℕ × ℕ) :=
  (ellipticGammaResidueShuffle m n).trans
    ((Nat.divModEquiv m).prodCongr (Nat.divModEquiv n)).symm

@[simp] theorem ellipticGammaResidueEquiv_apply
    (m n : ℕ) [NeZero m] [NeZero n] (a : Fin m) (b : Fin n) (j k : ℕ) :
    ellipticGammaResidueEquiv m n ((a, b), (j, k)) =
      (j * m + a, k * n + b) := rfl

def ellipticGammaReverseResidueEquiv (m n : ℕ) [NeZero m] [NeZero n] :
    ((Fin m × Fin n) × (ℕ × ℕ)) ≃ (ℕ × ℕ) :=
  ((Fin.revPerm (n := m)).prodCongr (Fin.revPerm (n := n))).prodCongr
    (Equiv.refl (ℕ × ℕ)) |>.trans (ellipticGammaResidueEquiv m n)

theorem ellipticGammaBackwardArgument_residue
    {p q P x : ℂ} {m n : ℕ} (hp : p ^ m = P) (hq : q ^ n = P)
    (a : Fin m) (b : Fin n) (j k : ℕ) :
    ellipticGammaBackwardArgument p q x (j * m + a) (k * n + b) =
      ellipticGammaBackwardArgument P P (x * p ^ (a : ℕ) * q ^ (b : ℕ)) j k := by
  simp only [ellipticGammaBackwardArgument, pow_add]
  rw [show j * m = m * j by exact Nat.mul_comm _ _,
    show k * n = n * k by exact Nat.mul_comm _ _]
  simp only [pow_mul, hp, hq]
  ring

theorem ellipticGammaForwardArgument_reverse_residue
    {p q P x : ℂ} {m n : ℕ} [NeZero m] [NeZero n]
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hx : x ≠ 0)
    (hp : p ^ m = P) (hq : q ^ n = P)
    (a : Fin m) (b : Fin n) (j k : ℕ) :
    ellipticGammaForwardArgument p q x
        (j * m + (Fin.rev a : ℕ)) (k * n + (Fin.rev b : ℕ)) =
      ellipticGammaForwardArgument P P
        (x * p ^ (a : ℕ) * q ^ (b : ℕ)) j k := by
  have ha : (Fin.rev a : ℕ) + 1 + (a : ℕ) = m := by
    rw [Fin.val_rev]
    omega
  have hb : (Fin.rev b : ℕ) + 1 + (b : ℕ) = n := by
    rw [Fin.val_rev]
    omega
  have hpExp : p ^ (j * m + (Fin.rev a : ℕ) + 1) * p ^ (a : ℕ) = P ^ (j + 1) := by
    rw [← pow_add]
    have he : j * m + (Fin.rev a : ℕ) + 1 + (a : ℕ) = m * (j + 1) := by
      calc
        j * m + (Fin.rev a : ℕ) + 1 + (a : ℕ) = j * m + m := by omega
        _ = m * j + m := by rw [Nat.mul_comm j m]
        _ = m * (j + 1) := (Nat.mul_succ m j).symm
    rw [he, pow_mul, hp]
  have hqExp : q ^ (k * n + (Fin.rev b : ℕ) + 1) * q ^ (b : ℕ) = P ^ (k + 1) := by
    rw [← pow_add]
    have he : k * n + (Fin.rev b : ℕ) + 1 + (b : ℕ) = n * (k + 1) := by
      calc
        k * n + (Fin.rev b : ℕ) + 1 + (b : ℕ) = k * n + n := by omega
        _ = n * k + n := by rw [Nat.mul_comm k n]
        _ = n * (k + 1) := (Nat.mul_succ n k).symm
    rw [he, pow_mul, hq]
  rw [ellipticGammaForwardArgument, ellipticGammaForwardArgument]
  apply (div_eq_div_iff hx (mul_ne_zero (mul_ne_zero hx (pow_ne_zero _ hp0))
    (pow_ne_zero _ hq0))).2
  calc
    (p ^ (j * m + (Fin.rev a : ℕ) + 1) * q ^ (k * n + (Fin.rev b : ℕ) + 1)) *
          (x * p ^ (a : ℕ) * q ^ (b : ℕ)) =
        x * (p ^ (j * m + (Fin.rev a : ℕ) + 1) * p ^ (a : ℕ)) *
          (q ^ (k * n + (Fin.rev b : ℕ) + 1) * q ^ (b : ℕ)) := by ring
    _ = x * P ^ (j + 1) * P ^ (k + 1) := by rw [hpExp, hqExp]
    _ = (P ^ (j + 1) * P ^ (k + 1)) * x := by ring

/-- The numerator and denominator products in multiplicative coordinates. -/
def ellipticGammaMultiplicativeForwardProduct (p q x : ℂ) : ℂ :=
  tprod (fun jk : ℕ × ℕ =>
    1 - ellipticGammaForwardArgument p q x jk.1 jk.2)

def ellipticGammaMultiplicativeBackwardProduct (p q x : ℂ) : ℂ :=
  tprod (fun jk : ℕ × ℕ =>
    1 - ellipticGammaBackwardArgument p q x jk.1 jk.2)

def ellipticGammaMultiplicativeProduct (p q x : ℂ) : ℂ :=
  ellipticGammaMultiplicativeForwardProduct p q x /
    ellipticGammaMultiplicativeBackwardProduct p q x

theorem multipliable_ellipticGammaMultiplicativeForwardFactor
    {p q x : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    Multipliable (fun jk : ℕ × ℕ =>
      1 - ellipticGammaForwardArgument p q x jk.1 jk.2) := by
  have hs : Summable (fun jk : ℕ × ℕ =>
      ‖-ellipticGammaForwardArgument p q x jk.1 jk.2‖) := by
    simpa only [norm_neg] using summable_norm_ellipticGammaForwardArgument hp hq
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hs

theorem multipliable_ellipticGammaMultiplicativeBackwardFactor
    {p q x : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    Multipliable (fun jk : ℕ × ℕ =>
      1 - ellipticGammaBackwardArgument p q x jk.1 jk.2) := by
  have hs : Summable (fun jk : ℕ × ℕ =>
      ‖-ellipticGammaBackwardArgument p q x jk.1 jk.2‖) := by
    simpa only [norm_neg] using summable_norm_ellipticGammaBackwardArgument hp hq
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hs

@[simp] theorem ellipticGammaReverseResidueEquiv_apply
    (m n : ℕ) [NeZero m] [NeZero n] (a : Fin m) (b : Fin n) (j k : ℕ) :
    ellipticGammaReverseResidueEquiv m n ((a, b), (j, k)) =
      (j * m + (Fin.rev a : ℕ), k * n + (Fin.rev b : ℕ)) := rfl

/-- The flattened numerator product of the finite equal-nome family.  Keeping the finite residue
index in the same unconditional product avoids an analytically irrelevant Fubini normalization. -/
def ellipticGammaCommensurableForwardFamilyProduct
    (p q P x : ℂ) (m n : ℕ) : ℂ :=
  tprod (fun u : (Fin m × Fin n) × (ℕ × ℕ) =>
    1 - ellipticGammaForwardArgument P P
      (x * p ^ (u.1.1 : ℕ) * q ^ (u.1.2 : ℕ)) u.2.1 u.2.2)

/-- The flattened denominator product of the finite equal-nome family. -/
def ellipticGammaCommensurableBackwardFamilyProduct
    (p q P x : ℂ) (m n : ℕ) : ℂ :=
  tprod (fun u : (Fin m × Fin n) × (ℕ × ℕ) =>
    1 - ellipticGammaBackwardArgument P P
      (x * p ^ (u.1.1 : ℕ) * q ^ (u.1.2 : ℕ)) u.2.1 u.2.2)

/-- The actual finite equal-nome family, represented by one unconditional flattened product. -/
def ellipticGammaCommensurableFamilyProduct
    (p q P x : ℂ) (m n : ℕ) : ℂ :=
  ellipticGammaCommensurableForwardFamilyProduct p q P x m n /
    ellipticGammaCommensurableBackwardFamilyProduct p q P x m n

theorem ellipticGammaMultiplicativeBackwardProduct_flattened_factorization
    {p q P x : ℂ} {m n : ℕ} [NeZero m] [NeZero n]
    (hp : p ^ m = P) (hq : q ^ n = P) :
    ellipticGammaMultiplicativeBackwardProduct p q x =
      ellipticGammaCommensurableBackwardFamilyProduct p q P x m n := by
  rw [ellipticGammaMultiplicativeBackwardProduct,
    ellipticGammaCommensurableBackwardFamilyProduct,
    ← (ellipticGammaResidueEquiv m n).tprod_eq
      (fun jk : ℕ × ℕ => 1 - ellipticGammaBackwardArgument p q x jk.1 jk.2)]
  apply tprod_congr
  rintro ⟨⟨a, b⟩, ⟨j, k⟩⟩
  rw [ellipticGammaResidueEquiv_apply,
    ellipticGammaBackwardArgument_residue hp hq]

theorem ellipticGammaMultiplicativeForwardProduct_flattened_factorization
    {p q P x : ℂ} {m n : ℕ} [NeZero m] [NeZero n]
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hx : x ≠ 0)
    (hp : p ^ m = P) (hq : q ^ n = P) :
    ellipticGammaMultiplicativeForwardProduct p q x =
      ellipticGammaCommensurableForwardFamilyProduct p q P x m n := by
  rw [ellipticGammaMultiplicativeForwardProduct,
    ellipticGammaCommensurableForwardFamilyProduct,
    ← (ellipticGammaReverseResidueEquiv m n).tprod_eq
      (fun jk : ℕ × ℕ => 1 - ellipticGammaForwardArgument p q x jk.1 jk.2)]
  apply tprod_congr
  rintro ⟨⟨a, b⟩, ⟨j, k⟩⟩
  rw [ellipticGammaReverseResidueEquiv_apply,
    ellipticGammaForwardArgument_reverse_residue hp0 hq0 hx hp hq]

/-- Exact Felder--Varchenko residue factorization, formalized without any convergence or
differential-algebraic assumption. -/
theorem ellipticGammaMultiplicativeProduct_flattened_factorization
    {p q P x : ℂ} {m n : ℕ} [NeZero m] [NeZero n]
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hx : x ≠ 0)
    (hp : p ^ m = P) (hq : q ^ n = P) :
    ellipticGammaMultiplicativeProduct p q x =
      ellipticGammaCommensurableFamilyProduct p q P x m n := by
  rw [ellipticGammaMultiplicativeProduct,
    ellipticGammaCommensurableFamilyProduct,
    ellipticGammaMultiplicativeForwardProduct_flattened_factorization hp0 hq0 hx hp hq,
    ellipticGammaMultiplicativeBackwardProduct_flattened_factorization hp hq]

end

end GaloisForLFunctions
