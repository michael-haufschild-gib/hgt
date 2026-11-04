import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.WeightedPrimeIncidenceEnergy
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceDilationPairing

/-!
# Exact energy splitting in a coprime fibre

A Mangoldt-supported dilation changes at most one prime incidence.
If the fibre is invariant under those primes, its jump and the prime-packet
jump have disjoint support. The product energy therefore splits exactly
into a weighted prime diagonal and a nonnegative fixed-fibre remainder.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- Coprime invariance removes the cross increment from the weighted product rule. -/
theorem incidence_product_jump {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (b e : ℕ → ℝ)
    (hinv : ∀ p ∈ P, ∀ n, e (p * n) = e n) (k n : ℕ) :
    Λ k * (e (k * n) * incidencePacket P b (k * n) - e n * incidencePacket P b n) =
      Λ k * (e n * (incidencePacket P b (k * n) - incidencePacket P b n) +
        incidencePacket P b n * (e (k * n) - e n)) := by
  by_cases hΛ : Λ k = 0
  · simp only [hΛ, zero_mul]
  have hk := vonMangoldt_ne_zero_iff.mp hΛ
  have hF := incidencePacket_dilation_jump hP b hk n
  by_cases hp : k.minFac ∈ P
  · have he := invariant_on_prime_tower (hP _ hp) hk (Nat.minFac_dvd k) e (hinv _ hp) n
    rw [he]
    ring
  · have hzero : incidencePacket P b (k * n) = incidencePacket P b n := by
      have hnot : ¬ (k.minFac ∈ P ∧ ¬ k.minFac ∣ n) := fun h => hp h.1
      rw [if_neg hnot] at hF
      exact sub_eq_zero.mp hF
    rw [hzero]
    ring

private theorem incidence_product_edge {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (b e : ℕ → ℝ)
    (hinv : ∀ p ∈ P, ∀ n, e (p * n) = e n) (k n : ℕ) :
    Λ k * (e (k * n) * incidencePacket P b (k * n) - e n * incidencePacket P b n) ^ 2 =
      Λ k * (e n ^ 2 * (incidencePacket P b (k * n) - incidencePacket P b n) ^ 2 +
        incidencePacket P b n ^ 2 * (e (k * n) - e n) ^ 2) := by
  by_cases hΛ : Λ k = 0
  · simp only [hΛ, zero_mul]
  have hk := vonMangoldt_ne_zero_iff.mp hΛ
  have hF := incidencePacket_dilation_jump hP b hk n
  by_cases hp : k.minFac ∈ P
  · have he := invariant_on_prime_tower (hP _ hp) hk (Nat.minFac_dvd k) e (hinv _ hp) n
    rw [he]
    ring
  · have hzero : incidencePacket P b (k * n) = incidencePacket P b n := by
      have hnot : ¬ (k.minFac ∈ P ∧ ¬ k.minFac ∣ n) := fun h => hp h.1
      rw [if_neg hnot] at hF
      exact sub_eq_zero.mp hF
    rw [hzero]
    ring

/-- A coprime fibre has an exact weighted prime diagonal and a separate base-conductor energy. -/
theorem jumpEnergy_incidence_product {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (b e : ℕ → ℝ)
    (hinv : ∀ p ∈ P, ∀ n, e (p * n) = e n) (N : ℕ) :
    jumpEnergy N (fun n => e n * incidencePacket P b n) =
      (∑ p ∈ P, b p ^ 2 *
        (Real.log p / p * ∑ n ∈ Icc 1 (N / p), e n ^ 2 / (n : ℝ))) +
      ∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
        (incidencePacket P b kn.2 ^ 2 * (e (kn.1 * kn.2) - e kn.2) ^ 2 / kn.2) := by
  have hedge (k n : ℕ) :
      Λ k / k * ((e (k * n) * incidencePacket P b (k * n) - e n * incidencePacket P b n) ^ 2 / n) =
      Λ k / k * (e n ^ 2 *
        ((incidencePacket P b (k * n) - incidencePacket P b n) *
          (incidencePacket P b (k * n) - incidencePacket P b n)) / n) +
      Λ k / k * (incidencePacket P b n ^ 2 * (e (k * n) - e n) ^ 2 / n) := by
    calc
      _ = (Λ k *
          (e (k * n) * incidencePacket P b (k * n) - e n * incidencePacket P b n) ^ 2) /
            ((k : ℝ) * n) := by ring
      _ = _ := by rw [incidence_product_edge hP b e hinv]; ring
  simp only [jumpEnergy, hedge, sum_add_distrib]
  rw [weighted_primeIncidence_packet_pairing hP b b (fun n => e n ^ 2)
    (fun p hp n => by rw [hinv p hp n]) N]
  simp only [← sq]

/-- A bounded upward square row makes the fixed-fibre remainder cost only harmonic input mass. -/
theorem incidence_product_remainder_le (N : ℕ) (F e : ℕ → ℝ) (C : ℝ)
    (hrow : ∀ Y n, (∑ k ∈ Icc 1 Y,
      Λ k / k * (e (k * n) - e n) ^ 2) ≤ C) :
    (∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
      (F kn.2 ^ 2 * (e (kn.1 * kn.2) - e kn.2) ^ 2 / kn.2)) ≤
      C * ∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ) := by
  rw [sum_dilationPairs_eq N (fun k n =>
    Λ k / k * (F n ^ 2 * (e (k * n) - e n) ^ 2 / n)), mul_sum]
  apply sum_le_sum
  intro n _
  calc
    _ = (F n ^ 2 / (n : ℝ)) *
        ∑ k ∈ Icc 1 (N / n), Λ k / k * (e (k * n) - e n) ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (F n ^ 2 / (n : ℝ)) * C :=
      mul_le_mul_of_nonneg_left (hrow (N / n) n) (by positivity)
    _ = _ := mul_comm _ _

#print axioms jumpEnergy_incidence_product
#print axioms incidence_product_jump
#print axioms incidence_product_remainder_le

private theorem incidence_product_mixed_edge {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (b d e f : ℕ → ℝ)
    (he : ∀ p ∈ P, ∀ n, e (p * n) = e n)
    (hf : ∀ p ∈ P, ∀ n, f (p * n) = f n) (k n : ℕ) :
    Λ k * (e (k * n) * incidencePacket P b (k * n) - e n * incidencePacket P b n) *
      (f (k * n) * incidencePacket P d (k * n) - f n * incidencePacket P d n) =
    Λ k * (e n * f n *
      ((incidencePacket P b (k * n) - incidencePacket P b n) *
        (incidencePacket P d (k * n) - incidencePacket P d n)) +
      incidencePacket P b n * incidencePacket P d n *
        ((e (k * n) - e n) * (f (k * n) - f n))) := by
  by_cases hΛ : Λ k = 0
  · simp only [hΛ, zero_mul]
  have hk := vonMangoldt_ne_zero_iff.mp hΛ
  by_cases hp : k.minFac ∈ P
  · rw [invariant_on_prime_tower (hP _ hp) hk (Nat.minFac_dvd k) e (he _ hp) n,
      invariant_on_prime_tower (hP _ hp) hk (Nat.minFac_dvd k) f (hf _ hp) n]
    ring
  · have hnot : ¬ (k.minFac ∈ P ∧ ¬ k.minFac ∣ n) := fun h => hp h.1
    have hb := incidencePacket_dilation_jump hP b hk n
    have hd := incidencePacket_dilation_jump hP d hk n
    rw [if_neg hnot] at hb hd
    rw [sub_eq_zero.mp hb, sub_eq_zero.mp hd]
    ring

/-- Mixed fibre energies retain the period Gram weight and the exact base-mode remainder. -/
theorem jumpPairing_incidence_products {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (b d e f : ℕ → ℝ)
    (he : ∀ p ∈ P, ∀ n, e (p * n) = e n)
    (hf : ∀ p ∈ P, ∀ n, f (p * n) = f n) (N : ℕ) :
    jumpPairing N (fun n => e n * incidencePacket P b n)
      (fun n => f n * incidencePacket P d n) =
      (∑ p ∈ P, b p * d p *
        (Real.log p / p * ∑ n ∈ Icc 1 (N / p), e n * f n / (n : ℝ))) +
      ∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
        (incidencePacket P b kn.2 * incidencePacket P d kn.2 *
          ((e (kn.1 * kn.2) - e kn.2) * (f (kn.1 * kn.2) - f kn.2)) / kn.2) := by
  have hedge (k n : ℕ) :
      Λ k / k *
        ((e (k * n) * incidencePacket P b (k * n) - e n * incidencePacket P b n) *
          (f (k * n) * incidencePacket P d (k * n) - f n * incidencePacket P d n) / n) =
      Λ k / k * (e n * f n *
        ((incidencePacket P b (k * n) - incidencePacket P b n) *
          (incidencePacket P d (k * n) - incidencePacket P d n)) / n) +
      Λ k / k * (incidencePacket P b n * incidencePacket P d n *
        ((e (k * n) - e n) * (f (k * n) - f n)) / n) := by
    calc
      _ = (Λ k *
          (e (k * n) * incidencePacket P b (k * n) - e n * incidencePacket P b n) *
          (f (k * n) * incidencePacket P d (k * n) - f n * incidencePacket P d n)) /
            ((k : ℝ) * n) := by ring
      _ = _ := by rw [incidence_product_mixed_edge hP b d e f he hf]; ring
  simp only [jumpPairing, hedge, sum_add_distrib]
  rw [weighted_primeIncidence_packet_pairing hP b d (fun n => e n * f n)
    (fun p hp n => by rw [he p hp n, hf p hp n]) N]

#print axioms jumpPairing_incidence_products

/-- Mixed base-mode remainders are paid by the two harmonic input squares. -/
theorem abs_incidence_product_mixed_remainder_le (N : ℕ) (F G e f : ℕ → ℝ) (C D : ℝ)
    (he : ∀ Y n, (∑ k ∈ Icc 1 Y,
      Λ k / k * (e (k * n) - e n) ^ 2) ≤ C)
    (hf : ∀ Y n, (∑ k ∈ Icc 1 Y,
      Λ k / k * (f (k * n) - f n) ^ 2) ≤ D) :
    |∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
      (F kn.2 * G kn.2 *
        ((e (kn.1 * kn.2) - e kn.2) * (f (kn.1 * kn.2) - f kn.2)) / kn.2)| ≤
      (C * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
        D * (∑ n ∈ Icc 1 N, G n ^ 2 / (n : ℝ))) / 2 := by
  have hpoint (k n : ℕ) :
      |Λ k / k * (F n * G n * ((e (k * n) - e n) * (f (k * n) - f n)) / n)| ≤
      (Λ k / k * (F n ^ 2 * (e (k * n) - e n) ^ 2 / n) +
        Λ k / k * (G n ^ 2 * (f (k * n) - f n) ^ 2 / n)) / 2 := by
    have hsq : |(F n * (e (k * n) - e n)) * (G n * (f (k * n) - f n))| ≤
        ((F n * (e (k * n) - e n)) ^ 2 + (G n * (f (k * n) - f n)) ^ 2) / 2 := by
      have h := sq_nonneg (|F n * (e (k * n) - e n)| - |G n * (f (k * n) - f n)|)
      rw [abs_mul]
      nlinarith only [h, sq_abs (F n * (e (k * n) - e n)),
        sq_abs (G n * (f (k * n) - f n))]
    have hw : 0 ≤ Λ k / k / (n : ℝ) := by positivity
    calc
      _ = (Λ k / k / (n : ℝ)) *
          |(F n * (e (k * n) - e n)) * (G n * (f (k * n) - f n))| := by
        rw [show Λ k / k * (F n * G n * ((e (k * n) - e n) * (f (k * n) - f n)) / n) =
          (Λ k / k / (n : ℝ)) *
            ((F n * (e (k * n) - e n)) * (G n * (f (k * n) - f n))) by ring,
          abs_mul, abs_of_nonneg hw]
      _ ≤ _ := (mul_le_mul_of_nonneg_left hsq hw).trans_eq (by ring)
  refine ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun kn _ => hpoint kn.1 kn.2)).trans ?_
  simpa only [div_eq_mul_inv, ← sum_mul, sum_add_distrib] using div_le_div_of_nonneg_right
    (add_le_add (incidence_product_remainder_le N F e C he)
      (incidence_product_remainder_le N G f D hf)) zero_le_two

#print axioms abs_incidence_product_mixed_remainder_le

end GaloisForLFunctions.ArithmeticCouplingTheory
