import GaloisForLFunctions.RHTower.Sieve.MaynardAggregateSelection
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Reindexing one Heath--Brown box as a finite Maynard factor family

A selected box contains Möbius factors, zeta factors, and one logarithmic factor.  This module
packages that heterogeneous product into one finite index type, proves the product identity
literally, and removes the signed binomial scalar with an explicit `2^k` loss.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

/-- Heterogeneous factor index of the box with packet index `m`. -/
abbrev HeathBrownBoxFactorIndex (k m : ℕ) :=
  Fin (k - m) ⊕ (Fin (k - m - 1) ⊕ Unit)

/-- Factor kind at each heterogeneous box index. -/
def heathBrownBoxFactorKind (k m : ℕ) : HeathBrownBoxFactorIndex k m → HeathBrownFactorKind
  | .inl _ => .moebius
  | .inr (.inl _) => .zeta
  | .inr (.inr _) => .log

/-- Dyadic exponent at each heterogeneous box index. -/
def heathBrownBoxFactorExponent {k m : ℕ}
    (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ) :
    HeathBrownBoxFactorIndex k m → ℕ
  | .inl i => a i
  | .inr (.inl i) => b i
  | .inr (.inr _) => q

/-- Unsigned literal product inside one signed Heath--Brown dyadic term. -/
def heathBrownDyadicCoreProduct
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (s : ℂ) : ℂ :=
  (∏ i, LSeries
      (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) (a i))) s) *
    (∏ i, LSeries
      (complexCoeff (arithmeticDyadicBlock
        (coeffTrunc (zeta : ArithmeticFunction ℝ) X) (b i))) s) *
    LSeries (complexCoeff (arithmeticDyadicBlock
      (coeffTrunc ArithmeticFunction.log X) q)) s

/-- The heterogeneous finite product is definitionally the three-part box core. -/
theorem heathBrownBoxFactorProduct_eq_core
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (s : ℂ) :
    (∏ i : HeathBrownBoxFactorIndex k m,
      LSeries (complexCoeff (arithmeticDyadicBlock
        (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
        (heathBrownBoxFactorExponent a b q i))) s) =
      heathBrownDyadicCoreProduct L X k m a b q s := by
  simp [HeathBrownBoxFactorIndex, heathBrownBoxFactorKind,
    heathBrownBoxFactorExponent, heathBrownFactorBase, heathBrownDyadicCoreProduct]
  ring

/-- A genuine packet term (`m<k`) has exactly `2(k-m)` individual factors. -/
theorem card_heathBrownBoxFactorIndex
    {k m : ℕ} (hm : m < k) :
    Fintype.card (HeathBrownBoxFactorIndex k m) = 2 * (k - m) := by
  simp [HeathBrownBoxFactorIndex]
  omega

/-- Signed term equals its scalar times the unsigned heterogeneous core. -/
theorem heathBrownDyadicTermProduct_eq_scalar_mul_core
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (s : ℂ) :
    heathBrownDyadicTermProduct L X k m a b q s =
      (-1 : ℂ) ^ (m + k + 1) * (k.choose m : ℂ) *
        heathBrownDyadicCoreProduct L X k m a b q s := rfl

/-- Exact norm cost of the signed binomial scalar. -/
theorem norm_heathBrownDyadicTermProduct_eq_choose_mul_core
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (s : ℂ) :
    ‖heathBrownDyadicTermProduct L X k m a b q s‖ =
      (k.choose m : ℝ) * ‖heathBrownDyadicCoreProduct L X k m a b q s‖ := by
  rw [heathBrownDyadicTermProduct_eq_scalar_mul_core, norm_mul, norm_mul]
  simp

/-- Aggregate-to-core selection with every combinatorial loss explicit and the binomial bounded by
`2^k`. -/
theorem exists_large_heathBrownDyadicCoreProduct
    (L X k : ℕ) (hk : 0 < k) (s : ℂ) {V : ℝ}
    (hlarge : V ≤ ‖heathBrownDyadicAggregate L X k s‖) :
    ∃ m ∈ Finset.range k,
      ∃ q ∈ Finset.range (Nat.log 2 X + 1),
        ∃ b ∈ dyadicChoiceSet (k - m - 1) X,
          ∃ a ∈ dyadicChoiceSet (k - m) L,
            V ≤ (k : ℝ) * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ (k - m)) *
              (((Nat.log 2 L + 1 : ℕ) : ℝ) ^ (k - m)) * (2 ^ k : ℝ) *
                ‖heathBrownDyadicCoreProduct L X k m a b q s‖ := by
  obtain ⟨m, hm, q, hq, b, hb, a, ha, hterm⟩ :=
    exists_large_heathBrownDyadicTermProduct_polylog L X k hk s hlarge
  refine ⟨m, hm, q, hq, b, hb, a, ha, hterm.trans ?_⟩
  rw [norm_heathBrownDyadicTermProduct_eq_choose_mul_core]
  have hchoose : (k.choose m : ℝ) ≤ (2 ^ k : ℝ) := by
    exact_mod_cast Nat.choose_le_two_pow k m
  let P : ℝ := (k : ℝ) * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ (k - m)) *
    (((Nat.log 2 L + 1 : ℕ) : ℝ) ^ (k - m))
  have hscalar : (k.choose m : ℝ) * ‖heathBrownDyadicCoreProduct L X k m a b q s‖ ≤
      (2 ^ k : ℝ) * ‖heathBrownDyadicCoreProduct L X k m a b q s‖ :=
    mul_le_mul_of_nonneg_right hchoose (norm_nonneg _)
  calc
    P * ((k.choose m : ℝ) * ‖heathBrownDyadicCoreProduct L X k m a b q s‖)
        ≤ P * ((2 ^ k : ℝ) * ‖heathBrownDyadicCoreProduct L X k m a b q s‖) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = (k : ℝ) * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ (k - m)) *
        (((Nat.log 2 L + 1 : ℕ) : ℝ) ^ (k - m)) * (2 ^ k : ℝ) *
          ‖heathBrownDyadicCoreProduct L X k m a b q s‖ := by
      dsimp [P]
      ring

/-- Group selection applied directly to the unsigned core of one selected box. -/
theorem exists_heathBrown_box_group_large
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (q : ℕ) (g : HeathBrownBoxFactorIndex k m → κ) (s : ℂ) (e : ℝ)
    (hlarge :
      (groupedDyadicLower (heathBrownBoxFactorExponent a b q) : ℝ) ^ e ≤
        ‖heathBrownDyadicCoreProduct L X k m a b q s‖) :
    ∃ j, ((groupedDyadicLower
        (fun i : GroupFibre g j => heathBrownBoxFactorExponent a b q i) : ℕ) : ℝ) ^ e ≤
      ‖∏ i : GroupFibre g j, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
          (heathBrownBoxFactorExponent a b q i))) s‖ := by
  apply exists_heathBrown_group_large L X (heathBrownBoxFactorKind k m)
    (heathBrownBoxFactorExponent a b q) g s e
  rwa [heathBrownBoxFactorProduct_eq_core]

end RHTower.Sieve
