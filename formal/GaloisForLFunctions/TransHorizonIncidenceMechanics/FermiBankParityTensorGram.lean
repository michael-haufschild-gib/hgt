import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiBooleanParityGram

/-!
# Product parity packets and their exact bank Gram law

Parity indicators on finitely many Boolean banks form nonnegative zero-one
packets. Packets with exactly one odd bank have disjoint coordinate supports.
The dependent finite product-sum identity factors their Gram into the existing
single-bank parity Gram forms, giving an exact formula for arbitrary local
real parameters. This is an algebraic tensor identity, not a positivity claim
for unrestricted local parameters.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

/-- Indicator of a prescribed parity in every finite bank. -/
def fermiBankParityPacket (b : I → Bool) (x : ∀ i, J i → Bool) : ℝ :=
  ∏ i, fermiBooleanParityIndicator (b i) (x i)

omit [DecidableEq I] [∀ i, DecidableEq (J i)] in
/-- A product of parity indicators is again a zero-one indicator. -/
theorem fermiBankParityPacket_zero_or_one (b : I → Bool) (x : ∀ i, J i → Bool) :
    fermiBankParityPacket b x = 0 ∨ fermiBankParityPacket b x = 1 := by
  apply Finset.prod_induction _ (fun a : ℝ => a = 0 ∨ a = 1)
  · rintro a c (ha | ha) (hc | hc) <;> simp [ha, hc]
  · exact Or.inr rfl
  · intro i _
    exact fermiBooleanParityIndicator_zero_or_one _ _

omit [∀ i, DecidableEq (J i)] in
/-- Different choices of the unique odd bank have disjoint coefficient supports. -/
theorem fermiBankParityPacket_oneHot_disjoint (j k : I) (hjk : j ≠ k)
    (x : ∀ i, J i → Bool) :
    fermiBankParityPacket (fun i => decide (i = j)) x *
      fermiBankParityPacket (fun i => decide (i = k)) x = 0 := by
  unfold fermiBankParityPacket
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  have hs := fermiBooleanParity_square (x j)
  have hz : fermiBooleanParityIndicator true (x j) *
      fermiBooleanParityIndicator false (x j) = 0 := by
    dsimp [fermiBooleanParityIndicator]
    nlinarith
  simpa [hjk] using hz

/-- Gram pairing of product parity packets under the product Boolean kernel. -/
def fermiBankParityGram (r : ∀ i, J i → ℝ) (b c : I → Bool) : ℝ :=
  ∑ x : ∀ i, J i → Bool, ∑ y : ∀ i, J i → Bool,
    fermiBankParityPacket b x * (∏ i, fermiBooleanGram (r i) (x i) (y i)) *
      fermiBankParityPacket c y

/-- Finite tensor factorization reuses the dependent product-sum identity. -/
theorem fermiBankParityGram_factorization (r : ∀ i, J i → ℝ) (b c : I → Bool) :
    fermiBankParityGram r b c =
      ∏ i, fermiBooleanGramForm (r i)
        (fermiBooleanParityIndicator (b i)) (fermiBooleanParityIndicator (c i)) := by
  unfold fermiBankParityGram fermiBankParityPacket fermiBooleanGramForm
  calc
    _ = ∑ x : ∀ i, J i → Bool, ∑ y : ∀ i, J i → Bool,
        ∏ i, fermiBooleanParityIndicator (b i) (x i) *
          fermiBooleanGram (r i) (x i) (y i) *
            fermiBooleanParityIndicator (c i) (y i) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.prod_mul_distrib]
    _ = ∑ x : ∀ i, J i → Bool, ∏ i, ∑ y : J i → Bool,
        fermiBooleanParityIndicator (b i) (x i) *
          fermiBooleanGram (r i) (x i) y * fermiBooleanParityIndicator (c i) y := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : J i → Bool) =>
        fermiBooleanParityIndicator (b i) (x i) *
          fermiBooleanGram (r i) (x i) y * fermiBooleanParityIndicator (c i) y)).symm
    _ = _ := (Fintype.prod_sum (fun i (x : J i → Bool) => ∑ y : J i → Bool,
      fermiBooleanParityIndicator (b i) x * fermiBooleanGram (r i) x y *
        fermiBooleanParityIndicator (c i) y)).symm

/-- Exact parity-bank Gram formula; every bank must have at least one coordinate. -/
theorem fermiBankParityGram_formula [∀ i, Nonempty (J i)]
    (r : ∀ i, J i → ℝ) (b c : I → Bool) :
    fermiBankParityGram r b c = ∏ i,
      (Fintype.card (J i → Bool) : ℝ) / 4 *
        ((∏ p : J i, (1 + r i p)) + (if b i = c i then 1 else -1) *
          ∏ p : J i, (1 - r i p)) := by
  rw [fermiBankParityGram_factorization]
  apply Finset.prod_congr rfl
  intro i _
  exact fermiBooleanParityIndicator_gram (r i) (b i) (c i)

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
