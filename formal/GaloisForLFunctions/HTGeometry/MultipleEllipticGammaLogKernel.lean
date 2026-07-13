import GaloisForLFunctions.HTGeometry.EllipticGammaLogKernel
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# The all-order multiple elliptic-gamma logarithmic kernel

For an arbitrary finite set of nomes, this module defines the parity-correct forward/backward
logarithmic summand of the multiple elliptic gamma product.  It proves exact finite telescoping in
every chosen nome coordinate: the surviving boundary is precisely the same construction on the
coordinate-deletion face, plus two terminal tails.  Thus the all-order hierarchy is derived from
the actual product atoms rather than assumed as a functional-equation interface.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def multipleEllipticGammaForwardArgument (p : ι → ℂ) (x : ℂ) (n : ι → ℕ) : ℂ :=
  (∏ i, p i ^ (n i + 1)) / x

def multipleEllipticGammaBackwardArgument (p : ι → ℂ) (x : ℂ) (n : ι → ℕ) : ℂ :=
  (∏ i, p i ^ n i) * x

def multipleEllipticGammaLogSign (ι : Type*) [Fintype ι] : ℂ :=
  (-1 : ℂ) ^ Fintype.card ι

def multipleEllipticGammaLogSummand (p : ι → ℂ) (x : ℂ) (n : ι → ℕ) : ℂ :=
  ellipticGammaLogAtom (multipleEllipticGammaForwardArgument p x n) +
    multipleEllipticGammaLogSign ι *
      ellipticGammaLogAtom (multipleEllipticGammaBackwardArgument p x n)

def multipleEllipticGammaMergeIndex (q : ι) (k : ℕ)
    (m : {i : ι // i ≠ q} → ℕ) : ι → ℕ := fun i =>
  if hi : i = q then k else m ⟨i, hi⟩

omit [Fintype ι] in
@[simp] theorem multipleEllipticGammaMergeIndex_self (q : ι) (k : ℕ)
    (m : {i : ι // i ≠ q} → ℕ) :
    multipleEllipticGammaMergeIndex q k m q = k := by
  simp [multipleEllipticGammaMergeIndex]

omit [Fintype ι] in
@[simp] theorem multipleEllipticGammaMergeIndex_ne (q : ι) (k : ℕ)
    (m : {i : ι // i ≠ q} → ℕ) (i : {i : ι // i ≠ q}) :
    multipleEllipticGammaMergeIndex q k m i = m i := by
  simp [multipleEllipticGammaMergeIndex, i.property]

/-- Split a multi-index into one chosen coordinate and the complementary face index. -/
def multipleEllipticGammaSplitIndex (q : ι) :
    (ι → ℕ) ≃ ℕ × ({i : ι // i ≠ q} → ℕ) where
  toFun n := (n q, fun i => n i)
  invFun km := multipleEllipticGammaMergeIndex q km.1 km.2
  left_inv n := by
    funext i
    by_cases hi : i = q
    · subst i
      simp
    · simp [multipleEllipticGammaMergeIndex, hi]
  right_inv km := by
    apply Prod.ext
    · simp
    · funext i
      simp

omit [Fintype ι] in
@[simp] theorem multipleEllipticGammaSplitIndex_symm_apply
    (q : ι) (km : ℕ × ({i : ι // i ≠ q} → ℕ)) :
    (multipleEllipticGammaSplitIndex q).symm km =
      multipleEllipticGammaMergeIndex q km.1 km.2 :=
  rfl

theorem multipleEllipticGammaLogSign_subtype_ne (q : ι) :
    multipleEllipticGammaLogSign {i : ι // i ≠ q} =
      -multipleEllipticGammaLogSign ι := by
  have hcard : Fintype.card ι = Fintype.card {i : ι // i ≠ q} + 1 := by
    simpa using (Fintype.card_congr (Equiv.optionSubtypeNe q)).symm
  rw [multipleEllipticGammaLogSign, multipleEllipticGammaLogSign, hcard, pow_succ]
  ring

theorem multipleEllipticGammaForwardArgument_mul_coordinate_zero
    (p : ι → ℂ) (x : ℂ) (q : ι) (m : {i : ι // i ≠ q} → ℕ)
    (hpq : p q ≠ 0) (hx : x ≠ 0) :
    multipleEllipticGammaForwardArgument p (p q * x)
        (multipleEllipticGammaMergeIndex q 0 m) =
      multipleEllipticGammaForwardArgument (fun i : {i : ι // i ≠ q} => p i) x m := by
  rw [multipleEllipticGammaForwardArgument, multipleEllipticGammaForwardArgument,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => p i ^ (multipleEllipticGammaMergeIndex q 0 m i + 1)) q]
  simp only [multipleEllipticGammaMergeIndex_self,
    multipleEllipticGammaMergeIndex_ne, zero_add, pow_one]
  field_simp [hpq, hx]

theorem multipleEllipticGammaForwardArgument_mul_coordinate_succ
    (p : ι → ℂ) (x : ℂ) (q : ι) (k : ℕ)
    (m : {i : ι // i ≠ q} → ℕ) (hpq : p q ≠ 0) (hx : x ≠ 0) :
    multipleEllipticGammaForwardArgument p (p q * x)
        (multipleEllipticGammaMergeIndex q (k + 1) m) =
      multipleEllipticGammaForwardArgument p x
        (multipleEllipticGammaMergeIndex q k m) := by
  rw [multipleEllipticGammaForwardArgument, multipleEllipticGammaForwardArgument,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => p i ^ (multipleEllipticGammaMergeIndex q (k + 1) m i + 1)) q,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => p i ^ (multipleEllipticGammaMergeIndex q k m i + 1)) q]
  simp only [multipleEllipticGammaMergeIndex_self,
    multipleEllipticGammaMergeIndex_ne]
  field_simp [hpq, hx]
  rw [pow_succ]
  ring

theorem multipleEllipticGammaBackwardArgument_mul_coordinate
    (p : ι → ℂ) (x : ℂ) (q : ι) (k : ℕ)
    (m : {i : ι // i ≠ q} → ℕ) :
    multipleEllipticGammaBackwardArgument p (p q * x)
        (multipleEllipticGammaMergeIndex q k m) =
      multipleEllipticGammaBackwardArgument p x
        (multipleEllipticGammaMergeIndex q (k + 1) m) := by
  rw [multipleEllipticGammaBackwardArgument, multipleEllipticGammaBackwardArgument,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => p i ^ multipleEllipticGammaMergeIndex q k m i) q,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => p i ^ multipleEllipticGammaMergeIndex q (k + 1) m i) q]
  simp only [multipleEllipticGammaMergeIndex_self,
    multipleEllipticGammaMergeIndex_ne]
  rw [pow_succ]
  ring

theorem multipleEllipticGammaBackwardArgument_coordinate_zero
    (p : ι → ℂ) (x : ℂ) (q : ι)
    (m : {i : ι // i ≠ q} → ℕ) :
    multipleEllipticGammaBackwardArgument p x
        (multipleEllipticGammaMergeIndex q 0 m) =
      multipleEllipticGammaBackwardArgument (fun i : {i : ι // i ≠ q} => p i) x m := by
  rw [multipleEllipticGammaBackwardArgument, multipleEllipticGammaBackwardArgument,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => p i ^ multipleEllipticGammaMergeIndex q 0 m i) q]
  simp only [multipleEllipticGammaMergeIndex_self,
    multipleEllipticGammaMergeIndex_ne, pow_zero, one_mul]

theorem multipleEllipticGammaLogSummand_mul_coordinate_zero
    (p : ι → ℂ) (x : ℂ) (q : ι) (m : {i : ι // i ≠ q} → ℕ)
    (hpq : p q ≠ 0) (hx : x ≠ 0) :
    multipleEllipticGammaLogSummand p (p q * x)
        (multipleEllipticGammaMergeIndex q 0 m) =
      ellipticGammaLogAtom
          (multipleEllipticGammaForwardArgument
            (fun i : {i : ι // i ≠ q} => p i) x m) +
        multipleEllipticGammaLogSign ι *
          ellipticGammaLogAtom
            (multipleEllipticGammaBackwardArgument p x
              (multipleEllipticGammaMergeIndex q 1 m)) := by
  rw [multipleEllipticGammaLogSummand,
    multipleEllipticGammaForwardArgument_mul_coordinate_zero p x q m hpq hx,
    multipleEllipticGammaBackwardArgument_mul_coordinate]

theorem multipleEllipticGammaLogSummand_mul_coordinate_succ
    (p : ι → ℂ) (x : ℂ) (q : ι) (k : ℕ)
    (m : {i : ι // i ≠ q} → ℕ) (hpq : p q ≠ 0) (hx : x ≠ 0) :
    multipleEllipticGammaLogSummand p (p q * x)
        (multipleEllipticGammaMergeIndex q (k + 1) m) =
      ellipticGammaLogAtom
          (multipleEllipticGammaForwardArgument p x
            (multipleEllipticGammaMergeIndex q k m)) +
        multipleEllipticGammaLogSign ι *
          ellipticGammaLogAtom
            (multipleEllipticGammaBackwardArgument p x
              (multipleEllipticGammaMergeIndex q (k + 2) m)) := by
  rw [multipleEllipticGammaLogSummand,
    multipleEllipticGammaForwardArgument_mul_coordinate_succ p x q k m hpq hx,
    multipleEllipticGammaBackwardArgument_mul_coordinate]

/-- Exact finite telescoping in any chosen nome coordinate of the all-order logarithmic kernel. -/
theorem multipleEllipticGammaLogSummand_sum_mul_coordinate
    (p : ι → ℂ) (x : ℂ) (q : ι) (m : {i : ι // i ≠ q} → ℕ)
    (hpq : p q ≠ 0) (hx : x ≠ 0) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
        multipleEllipticGammaLogSummand p (p q * x)
          (multipleEllipticGammaMergeIndex q k m)) -
      ∑ k ∈ Finset.range (N + 1),
        multipleEllipticGammaLogSummand p x
          (multipleEllipticGammaMergeIndex q k m) =
      multipleEllipticGammaLogSummand
          (fun i : {i : ι // i ≠ q} => p i) x m -
        ellipticGammaLogAtom
          (multipleEllipticGammaForwardArgument p x
            (multipleEllipticGammaMergeIndex q N m)) +
        multipleEllipticGammaLogSign ι *
          ellipticGammaLogAtom
            (multipleEllipticGammaBackwardArgument p x
              (multipleEllipticGammaMergeIndex q (N + 1) m)) := by
  induction N with
  | zero =>
      simp only [Nat.zero_add, Finset.sum_range_one]
      rw [multipleEllipticGammaLogSummand_mul_coordinate_zero p x q m hpq hx]
      simp only [multipleEllipticGammaLogSummand]
      rw [multipleEllipticGammaBackwardArgument_coordinate_zero,
        multipleEllipticGammaLogSign_subtype_ne]
      ring
  | succ N ih =>
      calc
        (∑ k ∈ Finset.range (N.succ + 1),
              multipleEllipticGammaLogSummand p (p q * x)
                (multipleEllipticGammaMergeIndex q k m)) -
            ∑ k ∈ Finset.range (N.succ + 1),
              multipleEllipticGammaLogSummand p x
                (multipleEllipticGammaMergeIndex q k m) =
          ((∑ k ∈ Finset.range (N + 1),
                multipleEllipticGammaLogSummand p (p q * x)
                  (multipleEllipticGammaMergeIndex q k m)) -
              ∑ k ∈ Finset.range (N + 1),
                multipleEllipticGammaLogSummand p x
                  (multipleEllipticGammaMergeIndex q k m)) +
            (multipleEllipticGammaLogSummand p (p q * x)
                (multipleEllipticGammaMergeIndex q (N + 1) m) -
              multipleEllipticGammaLogSummand p x
                (multipleEllipticGammaMergeIndex q (N + 1) m)) := by
          conv_lhs =>
            congr
            · rw [show N.succ + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ]
            · rw [show N.succ + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ]
          ring
        _ = multipleEllipticGammaLogSummand
              (fun i : {i : ι // i ≠ q} => p i) x m -
            ellipticGammaLogAtom
              (multipleEllipticGammaForwardArgument p x
                (multipleEllipticGammaMergeIndex q (N + 1) m)) +
            multipleEllipticGammaLogSign ι *
              ellipticGammaLogAtom
                (multipleEllipticGammaBackwardArgument p x
                  (multipleEllipticGammaMergeIndex q (N + 2) m)) := by
          rw [ih,
            multipleEllipticGammaLogSummand_mul_coordinate_succ p x q N m hpq hx]
          simp only [multipleEllipticGammaLogSummand]
          ring

end


end GaloisForLFunctions
