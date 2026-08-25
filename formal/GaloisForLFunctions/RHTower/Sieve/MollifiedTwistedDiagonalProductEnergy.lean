import GaloisForLFunctions.RHTower.Sieve.MollifiedTwistedMeanValueIcc

/-!
# Mollified diagonal as exact product-fibre energy

At zero twist the four-index mollified diagonal is exactly the Gram energy of the multiplicative
product fibres.  This is the coefficient-space form needed to separate short and long convolution
ranges without changing the arithmetic main term.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Finset
open GaloisForLFunctions.HTGeometry

/-- Coefficient obtained by grouping head/mollifier pairs with the same natural-number product. -/
def mollifiedProductCoeff
    (a u : ℕ → ℂ) (s q : Finset ℕ) (r : ℕ) : ℂ :=
  ∑ p ∈ (s ×ˢ q).filter (fun p => p.1 * p.2 = r), a p.1 * u p.2

/-- Gram pairing of two product-fibre coefficient families. -/
def mollifiedProductEnergy
    (a b u v : ℕ → ℂ) (s q : Finset ℕ) : ℂ :=
  ∑ r ∈ (s ×ˢ q).image (fun p => p.1 * p.2),
    mollifiedProductCoeff a u s q r *
      (starRingEnd ℂ) (mollifiedProductCoeff b v s q r)

/-- Four-index collision form, ordered as in the twisted diagonal. -/
def mollifiedProductCollisionSum
    (a b u v : ℕ → ℂ) (s q : Finset ℕ) : ℂ :=
  ∑ h ∈ q, ∑ k ∈ q, ∑ m ∈ s,
    ∑ n ∈ s.filter (fun n => n * k = m * h),
      (a m * u h) * (starRingEnd ℂ) (b n * v k)

theorem mollifiedTwistedDiagonal_zero_eq_collisionSum
    (a b u v : ℕ → ℂ) (s q : Finset ℕ) :
    mollifiedTwistedDiagonal a b u v s q 0 =
      mollifiedProductCollisionSum a b u v s q := by
  classical
  unfold mollifiedTwistedDiagonal mollifiedProductCollisionSum
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [twistedCoeff, neg_zero, Real.rpow_zero, mul_one,
    Complex.ofReal_one, map_mul]
  ring

private theorem sum_product_filter_eq
    (F : ℕ × ℕ → ℂ) (s q : Finset ℕ) (r : ℕ) :
    ∑ w ∈ (s ×ˢ q).filter (fun w => w.1 * w.2 = r), F w =
      ∑ k ∈ q, ∑ n ∈ s.filter (fun n => n * k = r), F (n, k) := by
  classical
  rw [Finset.sum_filter]
  rw [Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_filter]

theorem mollifiedProductEnergy_eq_collisionSum
    (a b u v : ℕ → ℂ) (s q : Finset ℕ) :
    mollifiedProductEnergy a b u v s q =
      mollifiedProductCollisionSum a b u v s q := by
  classical
  let P : Finset (ℕ × ℕ) := s ×ˢ q
  let prod : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  let term : (ℕ × ℕ) → (ℕ × ℕ) → ℂ := fun p w =>
    (a p.1 * u p.2) * (starRingEnd ℂ) (b w.1 * v w.2)
  have hmaps : ∀ p ∈ P, prod p ∈ P.image prod := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have henergy : mollifiedProductEnergy a b u v s q =
      ∑ r ∈ P.image prod, ∑ p ∈ P.filter (fun p => prod p = r),
        ∑ w ∈ P.filter (fun w => prod w = r), term p w := by
    unfold mollifiedProductEnergy mollifiedProductCoeff
    dsimp only [P, prod, term]
    apply Finset.sum_congr rfl
    intro r hr
    rw [map_sum]
    rw [Finset.sum_mul_sum]
  rw [henergy]
  have hreplace :
      (∑ r ∈ P.image prod, ∑ p ∈ P.filter (fun p => prod p = r),
        ∑ w ∈ P.filter (fun w => prod w = r), term p w) =
      ∑ r ∈ P.image prod, ∑ p ∈ P.filter (fun p => prod p = r),
        ∑ w ∈ P.filter (fun w => prod w = prod p), term p w := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro p hp
    have hpr : prod p = r := (Finset.mem_filter.mp hp).2
    rw [hpr]
  rw [hreplace]
  rw [Finset.sum_fiberwise_of_maps_to hmaps]
  dsimp only [mollifiedProductCollisionSum]
  rw [show P = s ×ˢ q by rfl]
  rw [Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sum_product_filter_eq]

/-- Exact zero-twist diagonal as product-fibre Gram energy. -/
theorem mollifiedTwistedDiagonal_zero_eq_productEnergy
    (a b u v : ℕ → ℂ) (s q : Finset ℕ) :
    mollifiedTwistedDiagonal a b u v s q 0 =
      mollifiedProductEnergy a b u v s q := by
  rw [mollifiedTwistedDiagonal_zero_eq_collisionSum,
    mollifiedProductEnergy_eq_collisionSum]

/-- A self-paired product-fibre Gram energy is a sum of real squared moduli. -/
theorem mollifiedProductEnergy_self_eq_sum_normSq
    (a u : ℕ → ℂ) (s q : Finset ℕ) :
    mollifiedProductEnergy a a u u s q =
      ∑ r ∈ (s ×ˢ q).image (fun p => p.1 * p.2),
        ((Complex.normSq (mollifiedProductCoeff a u s q r) : ℝ) : ℂ) := by
  unfold mollifiedProductEnergy
  apply Finset.sum_congr rfl
  intro r hr
  exact Complex.mul_conj _

/-- The self-paired zero-twist diagonal on initial ranges is manifestly a finite square energy. -/
theorem mollifiedTwistedDiagonalIcc_zero_self_eq_sum_normSq
    (a u : ℕ → ℂ) (L M : ℕ) :
    mollifiedTwistedDiagonalIcc a a u u L M 0 =
      ∑ r ∈ ((Finset.Icc 1 L) ×ˢ (Finset.Icc 1 M)).image
          (fun p => p.1 * p.2),
        ((Complex.normSq
          (mollifiedProductCoeff a u (Finset.Icc 1 L) (Finset.Icc 1 M) r) : ℝ) : ℂ) := by
  rw [← mollifiedTwistedDiagonal_eq_Icc]
  rw [mollifiedTwistedDiagonal_zero_eq_productEnergy]
  exact mollifiedProductEnergy_self_eq_sum_normSq a u (Finset.Icc 1 L) (Finset.Icc 1 M)

end RHTower.Sieve
