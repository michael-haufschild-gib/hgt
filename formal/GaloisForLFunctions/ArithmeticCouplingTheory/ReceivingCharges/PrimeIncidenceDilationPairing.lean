import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceDilationEnergy

/-!
# Exact mixed dilation pairing of prime-incidence packets

Polarization keeps the finite cofactor harmonic mass. Distinct prime
coordinates are orthogonal even before taking a horizon limit, and
subtracting either harmonic mean changes no mixed dilation pairing.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- The bilinear dilation form, with the same finite horizon as `jumpEnergy`. -/
def jumpPairing (N : ℕ) (F G : ℕ → ℝ) : ℝ :=
  ∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
    ((F (kn.1 * kn.2) - F kn.2) * (G (kn.1 * kn.2) - G kn.2) / kn.2)

theorem jumpPairing_self (N : ℕ) (F : ℕ → ℝ) :
    jumpPairing N F F = jumpEnergy N F := by
  simp only [jumpPairing, jumpEnergy, sq]

/-- Literal finite polarization requires no positivity or limiting hypothesis. -/
theorem jumpPairing_polarization (N : ℕ) (F G : ℕ → ℝ) :
    2 * jumpPairing N F G =
      jumpEnergy N (fun n => F n + G n) - jumpEnergy N F - jumpEnergy N G := by
  simp only [jumpPairing, jumpEnergy]
  rw [← sum_sub_distrib, ← sum_sub_distrib, mul_sum]
  exact sum_congr rfl fun kn _ => by ring

/-- Either constant subtraction is invisible to every finite dilation pairing. -/
theorem jumpPairing_sub_const (N : ℕ) (F G : ℕ → ℝ) (a b : ℝ) :
    jumpPairing N (fun n => F n - a) (fun n => G n - b) = jumpPairing N F G := by
  unfold jumpPairing
  exact sum_congr rfl fun kn _ => by ring

/-- The exact mixed prime-incidence form is diagonal with cofactor harmonic weights. -/
theorem jumpPairing_incidencePacket_diagonal {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (b d : ℕ → ℝ) (N : ℕ) :
    jumpPairing N (incidencePacket P b) (incidencePacket P d) =
      ∑ p ∈ P, b p * d p *
        (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)) := by
  have hadd : (fun n => incidencePacket P b n + incidencePacket P d n) =
      incidencePacket P (fun p => b p + d p) := by
    funext n
    simp only [incidencePacket, add_mul, sum_add_distrib]
  have h := jumpPairing_polarization N (incidencePacket P b) (incidencePacket P d)
  rw [hadd, jumpEnergy_incidencePacket_diagonal hP,
    jumpEnergy_incidencePacket_diagonal hP, jumpEnergy_incidencePacket_diagonal hP] at h
  have halgebra :
      (∑ p ∈ P, (b p + d p) ^ 2 *
        (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) -
      (∑ p ∈ P, b p ^ 2 *
        (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) -
      (∑ p ∈ P, d p ^ 2 *
        (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) =
      2 * ∑ p ∈ P, b p * d p *
        (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun p _ => by ring
  linarith only [h, halgebra]

/-- Disjoint prime bands have exactly zero mixed dilation energy after centering. -/
theorem jumpPairing_disjoint_incidence_eq_zero {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (b d : ℕ → ℝ)
    (hbd : ∀ p ∈ P, b p * d p = 0) (N : ℕ) (a e : ℝ) :
    jumpPairing N (fun n => incidencePacket P b n - a)
      (fun n => incidencePacket P d n - e) = 0 := by
  rw [jumpPairing_sub_const, jumpPairing_incidencePacket_diagonal hP]
  exact sum_eq_zero fun p hp => by rw [hbd p hp, zero_mul]

#print axioms jumpPairing_incidencePacket_diagonal
#print axioms jumpPairing_disjoint_incidence_eq_zero

end GaloisForLFunctions.ArithmeticCouplingTheory
