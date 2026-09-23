import GaloisForLFunctions.HTGeometry.CanonicalProduct

/-!
# Predicate splitting for indexed genus-one canonical products

An indexed genus-one canonical product with reciprocal-square summable nonzero
spectral points splits exactly over any predicate on its multiplicity index.
Both selected factors are defined directly as canonical products and are
entire. This is the analytic replacement for totalized pointwise division in
infinite Wiener--Hopf decompositions.
-/

open Complex Set
open scoped BigOperators

namespace RHTower

noncomputable section

variable {ι : Type*}

/-- Canonical product over indices selected by `p`. -/
def canonicalProductE1IndexedSelected
    (a : ι → ℂ) (p : ι → Prop) : ℂ → ℂ :=
  canonicalProductE1Indexed (fun i : {i // p i} => a i.1)

/-- Canonical product over indices complementary to `p`. -/
def canonicalProductE1IndexedComplement
    (a : ι → ℂ) (p : ι → Prop) : ℂ → ℂ :=
  canonicalProductE1Indexed (fun i : {i // ¬ p i} => a i.1)

theorem canonicalProductE1IndexedSelected_inv_sq_summable
    (a : ι → ℂ)
    (p : ι → Prop)
    (hsum : Summable (fun i : ι => 1 / ‖a i‖ ^ (2 : ℕ))) :
    Summable (fun i : {i // p i} => 1 / ‖a i.1‖ ^ (2 : ℕ)) :=
  hsum.comp_injective Subtype.val_injective

theorem canonicalProductE1IndexedComplement_inv_sq_summable
    (a : ι → ℂ)
    (p : ι → Prop)
    (hsum : Summable (fun i : ι => 1 / ‖a i‖ ^ (2 : ℕ))) :
    Summable (fun i : {i // ¬ p i} => 1 / ‖a i.1‖ ^ (2 : ℕ)) :=
  hsum.comp_injective Subtype.val_injective

/-- Every predicate-selected canonical factor is entire. -/
theorem canonicalProductE1IndexedSelected_analytic
    (a : ι → ℂ)
    (p : ι → Prop)
    (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i : ι => 1 / ‖a i‖ ^ (2 : ℕ))) :
    AnalyticOnNhd ℂ (canonicalProductE1IndexedSelected a p) Set.univ :=
  canonicalProductE1Indexed_analytic (fun i : {i // p i} => a i.1)
    (fun i => ha i.1)
    (canonicalProductE1IndexedSelected_inv_sq_summable a p hsum)

/-- Every complementary canonical factor is entire. -/
theorem canonicalProductE1IndexedComplement_analytic
    (a : ι → ℂ)
    (p : ι → Prop)
    (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i : ι => 1 / ‖a i‖ ^ (2 : ℕ))) :
    AnalyticOnNhd ℂ (canonicalProductE1IndexedComplement a p) Set.univ :=
  canonicalProductE1Indexed_analytic (fun i : {i // ¬ p i} => a i.1)
    (fun i => ha i.1)
    (canonicalProductE1IndexedComplement_inv_sq_summable a p hsum)

/-- Selected factor is nonzero away from its selected divisor. -/
theorem canonicalProductE1IndexedSelected_ne_zero
    (a : ι → ℂ)
    (p : ι → Prop)
    (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i : ι => 1 / ‖a i‖ ^ (2 : ℕ)))
    (z : ℂ)
    (haway : ∀ i : {i // p i}, z ≠ a i.1) :
    canonicalProductE1IndexedSelected a p z ≠ 0 :=
  canonicalProductE1Indexed_ne_zero
    (fun i : {i // p i} => a i.1)
    (fun i => ha i.1)
    (canonicalProductE1IndexedSelected_inv_sq_summable a p hsum)
    haway

/-- Complementary factor is nonzero away from its complementary divisor. -/
theorem canonicalProductE1IndexedComplement_ne_zero
    (a : ι → ℂ)
    (p : ι → Prop)
    (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i : ι => 1 / ‖a i‖ ^ (2 : ℕ)))
    (z : ℂ)
    (haway : ∀ i : {i // ¬ p i}, z ≠ a i.1) :
    canonicalProductE1IndexedComplement a p z ≠ 0 :=
  canonicalProductE1Indexed_ne_zero
    (fun i : {i // ¬ p i} => a i.1)
    (fun i => ha i.1)
    (canonicalProductE1IndexedComplement_inv_sq_summable a p hsum)
    haway

theorem canonicalProductE1IndexedSelected_multipliable
    (a : ι → ℂ)
    (p : ι → Prop)
    (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i : ι => 1 / ‖a i‖ ^ (2 : ℕ)))
    (z : ℂ) :
    Multipliable (fun i : {i // p i} => weierstrassE1 (z / a i.1)) := by
  let f : {i // p i} → ℂ := fun i => weierstrassE1 (z / a i.1) - 1
  have hfsum : Summable f :=
    (canonicalProductE1Indexed_sub_one_norm_summable
      (fun i : {i // p i} => a i.1)
      (fun i => ha i.1)
      (canonicalProductE1IndexedSelected_inv_sq_summable a p hsum) z).of_norm
  have hm : Multipliable (fun i => 1 + f i) :=
    Complex.multipliable_one_add_of_summable hfsum
  convert hm using 1
  ext i
  simp only [f]
  ring

theorem canonicalProductE1IndexedComplement_multipliable
    (a : ι → ℂ)
    (p : ι → Prop)
    (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i : ι => 1 / ‖a i‖ ^ (2 : ℕ)))
    (z : ℂ) :
    Multipliable (fun i : {i // ¬ p i} => weierstrassE1 (z / a i.1)) := by
  let f : {i // ¬ p i} → ℂ := fun i => weierstrassE1 (z / a i.1) - 1
  have hfsum : Summable f :=
    (canonicalProductE1Indexed_sub_one_norm_summable
      (fun i : {i // ¬ p i} => a i.1)
      (fun i => ha i.1)
      (canonicalProductE1IndexedComplement_inv_sq_summable a p hsum) z).of_norm
  have hm : Multipliable (fun i => 1 + f i) :=
    Complex.multipliable_one_add_of_summable hfsum
  convert hm using 1
  ext i
  simp only [f]
  ring

/- **Universal predicate-splitting law.** The full indexed canonical product is
the product of the factors selected by an arbitrary predicate and its
complement. Multiplicity copies are preserved by `Equiv.sumCompl`; no
enumeration or limiting exhaustion is used. -/
set_option maxHeartbeats 800000 in
theorem canonicalProductE1Indexed_eq_selected_mul_complement
    (a : ι → ℂ)
    (p : ι → Prop)
    (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i : ι => 1 / ‖a i‖ ^ (2 : ℕ)))
    (z : ℂ) :
    canonicalProductE1Indexed a z =
      canonicalProductE1IndexedSelected a p z *
        canonicalProductE1IndexedComplement a p z := by
  have hs := canonicalProductE1IndexedSelected_multipliable a p ha hsum z
  have hc := canonicalProductE1IndexedComplement_multipliable a p ha hsum z
  have hsplit :
      (∏' i : {i // p i}, weierstrassE1 (z / a i.1)) *
        (∏' i : {i // ¬ p i}, weierstrassE1 (z / a i.1)) =
        (∏' i : ι, weierstrassE1 (z / a i)) := by
    classical
    calc
      _ = ∏' x : ({i // p i} ⊕ {i // ¬ p i}),
          Sum.elim
            (fun i => weierstrassE1 (z / a i.1))
            (fun i => weierstrassE1 (z / a i.1)) x :=
        (Multipliable.tprod_sum hs hc).symm
      _ = _ := by
        let e := Equiv.sumCompl p
        have heq :
            (fun x => weierstrassE1 (z / a (e x))) =
              Sum.elim
                (fun i => weierstrassE1 (z / a i.1))
                (fun i => weierstrassE1 (z / a i.1)) := by
          funext x
          rcases x with i | i <;> rfl
        rw [← heq]
        exact e.tprod_eq (fun i => weierstrassE1 (z / a i))
  rw [canonicalProductE1Indexed, canonicalProductE1IndexedSelected,
    canonicalProductE1IndexedComplement, canonicalProductE1Indexed]
  exact hsplit.symm

end

end RHTower
