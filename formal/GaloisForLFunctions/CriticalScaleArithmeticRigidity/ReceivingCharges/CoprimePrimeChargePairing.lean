import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeDilation

/-!
# The period Gram in mixed coprime receiving fibres

The weighted incidence identity reads the harmonic Gram of the two base
conductors. Its diagonal part is the scalar prime kernel; the discrepancy
and the mixed base-mode remainder have explicit small input costs.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  ArithmeticIntersectionTheory SignedArithmeticHodgeTheory

/-- The harmonic product of two normalized conductor modes has its exact period Gram. -/
theorem abs_normalizedMode_product_harmonic_sub_le {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
      (if m = l then 1 else 0) * (∑ n ∈ Icc 1 N, 1 / (n : ℝ))| ≤
        2 * (m : ℝ) * l := by
  have h := ramanujanPoleProfile_gram_error_le ⟨m, hm⟩ ⟨l, hl⟩ N
  change |(∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) -
    (if (⟨m, hm⟩ : ℕ+) = ⟨l, hl⟩ then 1 else 0) *
      (∑ n ∈ Icc 1 N, 1 / (n : ℝ))| ≤ 2 * (m : ℝ) * l at h
  have hp (n : ℕ) : ramanujanPoleProfile m n * ramanujanPoleProfile l n =
      normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ) := by
    rw [ramanujanPoleProfile, ramanujanPoleProfile, div_mul_div_comm, ← sq,
      Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa only [hp, Subtype.mk.injEq] using h

/-- Mixed coprime fibres differ from the scalar prime kernel only by vanishing moment costs. -/
theorem abs_jumpPairing_coprime_modes_sub_le {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hpm : ∀ p ∈ P, p.Coprime m)
    (hpl : ∀ p ∈ P, p.Coprime l) (b d : ℕ → ℝ) (N : ℕ) :
    |jumpPairing N (fun n => normalizedRamanujanMode m n * incidencePacket P b n)
        (fun n => normalizedRamanujanMode l n * incidencePacket P d n) -
      (if m = l then 1 else 0) * jumpPairing N (incidencePacket P b) (incidencePacket P d)| ≤
        2 * (m : ℝ) * l * (∑ p ∈ P, |b p * d p| * (Real.log p / p)) +
        ((m : ℝ) * (Real.log m + tameDifferent m) *
            (∑ n ∈ Icc 1 N, incidencePacket P b n ^ 2 / (n : ℝ)) +
          (l : ℝ) * (Real.log l + tameDifferent l) *
            (∑ n ∈ Icc 1 N, incidencePacket P d n ^ 2 / (n : ℝ))) / 2 := by
  let δ : ℝ := if m = l then 1 else 0
  let R := ∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
    (incidencePacket P b kn.2 * incidencePacket P d kn.2 *
      ((normalizedRamanujanMode m (kn.1 * kn.2) - normalizedRamanujanMode m kn.2) *
        (normalizedRamanujanMode l (kn.1 * kn.2) - normalizedRamanujanMode l kn.2)) / kn.2)
  have hR := abs_incidence_product_mixed_remainder_le N
    (incidencePacket P b) (incidencePacket P d)
    (normalizedRamanujanMode m) (normalizedRamanujanMode l)
    ((m : ℝ) * (Real.log m + tameDifferent m))
    ((l : ℝ) * (Real.log l + tameDifferent l))
    (normalizedMode_upward_square_le hm) (normalizedMode_upward_square_le hl)
  have hdiag :
      |(∑ p ∈ P, b p * d p * (Real.log p / p *
          ∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ))) -
        δ * (∑ p ∈ P, b p * d p *
          (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)))| ≤
        2 * (m : ℝ) * l * ∑ p ∈ P, |b p * d p| * (Real.log p / p) := by
    rw [mul_sum, ← sum_sub_distrib, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
    intro p _
    have hw : 0 ≤ Real.log p / (p : ℝ) :=
      div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    calc
      _ = (|b p * d p| * (Real.log p / p)) *
          |(∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
            δ * (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))| := by
        rw [show b p * d p * (Real.log p / p *
            ∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
            δ * (b p * d p * (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) =
            ((b p * d p) * (Real.log p / p)) *
              ((∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
                δ * (∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) by ring,
          abs_mul, abs_mul, abs_of_nonneg hw]
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (abs_normalizedMode_product_harmonic_sub_le hm hl (N / p))
          (mul_nonneg (abs_nonneg _) hw)).trans_eq (mul_comm _ _)
  rw [jumpPairing_incidence_products hP b d
    (normalizedRamanujanMode m) (normalizedRamanujanMode l)
    (fun p hp n => normalizedRamanujanMode_coprime_mul hm (hpm p hp) n)
    (fun p hp n => normalizedRamanujanMode_coprime_mul hl (hpl p hp) n),
    jumpPairing_incidencePacket_diagonal hP]
  calc
    _ = |((∑ p ∈ P, b p * d p * (Real.log p / p *
        ∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ))) -
        δ * (∑ p ∈ P, b p * d p *
          (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)))) + R| := by
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hdiag hR)

#print axioms abs_normalizedMode_product_harmonic_sub_le
#print axioms abs_jumpPairing_coprime_modes_sub_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
