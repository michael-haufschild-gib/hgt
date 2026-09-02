import GaloisForLFunctions.RHTower.Sieve.KloostermanCompleteColumnCorrelation

/-!
# Complete distinct-modulus Kloosterman column correlation

Complete Kloosterman columns of unequal positive moduli are exactly orthogonal over one product
period.  Block the physical frequency as `m = a + rj`.  The second column is constant in `j`,
while every unit frequency in the first column has a nontrivial additive character because
`q ∤ r`.  Additive-character orthogonality kills that block.  If instead `q ∣ r`, unequal moduli
give `r ∤ q`, and Hermitian symmetry reverses the argument.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private theorem natCast_ne_zero_of_not_dvd
    (q r : ℕ) [NeZero q] (hqr : ¬ q ∣ r) : (r : ZMod q) ≠ 0 := by
  intro hr
  have hr' : (r : ZMod q) = (0 : ℕ) := by simpa using hr
  have hmod : r ≡ 0 [MOD q] :=
    ZMod.natCast_eq_natCast_iff r 0 q |>.mp hr'
  exact hqr (Nat.modEq_zero_iff_dvd.mp hmod)

private theorem neg_natCast_mul_unit_ne_zero
    (q r : ℕ) [NeZero q] (hqr : ¬ q ∣ r) (x : (ZMod q)ˣ) :
    -(r : ZMod q) * (x : ZMod q) ≠ 0 := by
  intro hx
  have hr : -(r : ZMod q) = 0 := by
    calc
      -(r : ZMod q) = (-(r : ZMod q) * (x : ZMod q)) *
          ((x⁻¹ : (ZMod q)ˣ) : ZMod q) := by simp [mul_assoc]
      _ = 0 := by rw [hx, zero_mul]
  exact natCast_ne_zero_of_not_dvd q r hqr (neg_eq_zero.mp hr)

private theorem sum_star_kloostermanSum_arithmeticProgression_eq_zero
    (q r : ℕ) [NeZero q] (hqr : ¬ q ∣ r) (a : ℕ) (n : ZMod q) :
    (∑ j : ZMod q,
      star (kloostermanSum q ((a + r * j.val : ℕ) : ZMod q) n)) = 0 := by
  simp_rw [star_kloostermanSum]
  unfold kloostermanSum kloostermanPhase
  rw [Finset.sum_comm]
  apply Fintype.sum_eq_zero
  intro x
  have hfactor (j : ZMod q) :
      ZMod.stdAddChar
          (-((a + r * j.val : ℕ) : ZMod q) * (x : ZMod q) +
            -n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) =
        ZMod.stdAddChar
            (-(a : ZMod q) * (x : ZMod q) +
              -n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) *
          ZMod.stdAddChar (j * (-(r : ZMod q) * (x : ZMod q))) := by
    rw [← AddChar.map_add_eq_mul]
    push_cast
    rw [show ((j.val : ℕ) : ZMod q) = j from ZMod.natCast_zmod_val j]
    congr 1
    ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum, sum_stdAddChar_mul]
  rw [if_neg (neg_natCast_mul_unit_ne_zero q r hqr x)]
  simp

/-- Complete cross-modulus column correlation over the common product period. -/
def kloostermanNaturalProductPeriodCorrelation
    (q r : ℕ) [NeZero q] [NeZero r] (n : ZMod q) (k : ZMod r) : ℂ :=
  ∑ m ∈ Finset.range (q * r),
    star (kloostermanSum q (m : ZMod q) n) *
      kloostermanSum r (m : ZMod r) k

/-- A common product period vanishes when the first modulus does not divide the second. -/
theorem kloostermanNaturalProductPeriodCorrelation_eq_zero_of_not_dvd
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : ¬ q ∣ r)
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalProductPeriodCorrelation q r n k = 0 := by
  unfold kloostermanNaturalProductPeriodCorrelation
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin q × Fin r ≃ Fin (q * r) := finProdFinEquiv
  calc
    (∑ m : Fin (q * r),
        star (kloostermanSum q (m.val : ZMod q) n) *
          kloostermanSum r (m.val : ZMod r) k) =
        ∑ p : Fin q × Fin r,
          star (kloostermanSum q ((p.2.val + r * p.1.val : ℕ) : ZMod q) n) *
            kloostermanSum r ((p.2.val + r * p.1.val : ℕ) : ZMod r) k := by
      rw [show (∑ m : Fin (q * r),
          star (kloostermanSum q (m.val : ZMod q) n) *
            kloostermanSum r (m.val : ZMod r) k) =
          ∑ p : Fin q × Fin r,
            star (kloostermanSum q ((e p).val : ZMod q) n) *
              kloostermanSum r ((e p).val : ZMod r) k from
        (e.sum_comp (fun m : Fin (q * r) =>
          star (kloostermanSum q (m.val : ZMod q) n) *
            kloostermanSum r (m.val : ZMod r) k)).symm]
      apply Fintype.sum_congr
      intro p
      simp [e, finProdFinEquiv]
    _ = ∑ a : Fin r, ∑ j : Fin q,
          star (kloostermanSum q ((a.val + r * j.val : ℕ) : ZMod q) n) *
            kloostermanSum r ((a.val + r * j.val : ℕ) : ZMod r) k := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = 0 := by
      apply Fintype.sum_eq_zero
      intro a
      have hmodr (j : Fin q) :
          ((a.val + r * j.val : ℕ) : ZMod r) = (a.val : ZMod r) := by
        push_cast
        rw [ZMod.natCast_self, zero_mul, add_zero]
      simp_rw [hmodr]
      rw [← Finset.sum_mul]
      have hfin (j : Fin q) : ZMod.finEquiv q j = (j.val : ZMod q) := by
        cases q with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ q =>
            apply ZMod.val_injective
            change j.val = j.val % (q + 1)
            rw [Nat.mod_eq_of_lt j.isLt]
      have hsum :
          (∑ j : Fin q,
            star (kloostermanSum q ((a.val + r * j.val : ℕ) : ZMod q) n)) = 0 := by
        have hsumZ :
            (∑ j : ZMod q,
              star (kloostermanSum q
                ((a.val : ZMod q) + (r : ZMod q) * j) n)) = 0 := by
          calc
            (∑ j : ZMod q,
                star (kloostermanSum q
                  ((a.val : ZMod q) + (r : ZMod q) * j) n)) =
                ∑ j : ZMod q,
                  star (kloostermanSum q
                    ((a.val + r * j.val : ℕ) : ZMod q) n) := by
              apply Fintype.sum_congr
              intro j
              push_cast
              rw [ZMod.natCast_zmod_val]
            _ = 0 :=
              sum_star_kloostermanSum_arithmeticProgression_eq_zero q r hqr a.val n
        calc
          (∑ j : Fin q,
              star (kloostermanSum q ((a.val + r * j.val : ℕ) : ZMod q) n)) =
              ∑ j : ZMod q,
                star (kloostermanSum q
                  ((a.val : ZMod q) + (r : ZMod q) * j) n) := by
            exact Fintype.sum_equiv (ZMod.finEquiv q)
              (fun j : Fin q =>
                star (kloostermanSum q ((a.val + r * j.val : ℕ) : ZMod q) n))
              (fun j : ZMod q =>
                star (kloostermanSum q
                  ((a.val : ZMod q) + (r : ZMod q) * j) n))
              (fun j => by
                push_cast
                rw [hfin j])
          _ = 0 := hsumZ
      rw [hsum]
      simp

/-- Product-period cross-correlation has the expected Hermitian symmetry. -/
theorem star_kloostermanNaturalProductPeriodCorrelation
    (q r : ℕ) [NeZero q] [NeZero r] (n : ZMod q) (k : ZMod r) :
    star (kloostermanNaturalProductPeriodCorrelation q r n k) =
      kloostermanNaturalProductPeriodCorrelation r q k n := by
  unfold kloostermanNaturalProductPeriodCorrelation
  change (starRingEnd ℂ)
      (∑ m ∈ Finset.range (q * r),
        star (kloostermanSum q (m : ZMod q) n) *
          kloostermanSum r (m : ZMod r) k) = _
  rw [map_sum]
  simpa only [Nat.mul_comm] using
    Finset.sum_congr rfl (fun m _hm => by
      rw [map_mul]
      simp
      ring)

/-- Complete Kloosterman columns of unequal moduli are orthogonal over one product period. -/
theorem kloostermanNaturalProductPeriodCorrelation_eq_zero_of_ne
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalProductPeriodCorrelation q r n k = 0 := by
  by_cases hdvd : q ∣ r
  · have hnot : ¬ r ∣ q := by
      intro hrev
      exact hqr (Nat.dvd_antisymm hdvd hrev)
    have hz := kloostermanNaturalProductPeriodCorrelation_eq_zero_of_not_dvd
      r q hnot k n
    have hstar := star_kloostermanNaturalProductPeriodCorrelation q r n k
    rw [hz] at hstar
    apply_fun star at hstar
    simpa using hstar
  · exact kloostermanNaturalProductPeriodCorrelation_eq_zero_of_not_dvd
      q r hdvd n k

end

end RHTower.Sieve
