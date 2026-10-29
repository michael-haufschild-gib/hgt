import GaloisForLFunctions.CompletedArithmeticForms.FinitePackets
import GaloisForLFunctions.BezoutValuationIncidence.BrownianBridgeLawOfThePrimeBlockAndCodimensionNoGo

/-!
# Actual prime packet reserve and Schur payment

The first-jump window of a prime block with zero mass and log moment contains the
normalized arithmetic bridge. Its completed conductor reserve therefore controls the
coefficient norm in the actual energy-centered prime form. A mixed coupling is paid by
the local variation of its zero-boundary extension, with all prime cross terms retained.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open BezoutValuationIncidence

private theorem primeBlock_nodes (S : Finset Nat.Primes) {P : ℕ}
    (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P) :
    ∀ p ∈ S, (p : ℕ) ∈ Ico 1 (2 * P + 2) := by
  intro p hp
  have h := hS p hp
  exact mem_Ico.mpr ⟨p.property.pos, by omega⟩

private theorem prime_bridge_normalization (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    {Q : ℕ} (hQ : 0 < Q) :
    (∑ p ∈ S, ∑ q ∈ S, a p * a q * bridgeKernel Q (p : ℕ) (q : ℕ)) / Q =
      ∑ p ∈ S, ∑ q ∈ S, a p * a q *
        (((min (p : ℕ) (q : ℕ) : ℕ) : ℝ) - ((p : ℕ) : ℝ) * (q : ℕ) / Q) := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [sum_div]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun q _ => ?_
  unfold bridgeKernel
  field_simp

/-- The actual prime form contains the normalized completed conductor energy. -/
theorem divisorGramEnergy_le_primePacket (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    {P : ℕ} (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P)
    (hA : primePacketMass S a = 0) (hL : primePacketLogMoment S a = 0) :
    divisorGramEnergy (2 * P + 2) (packetCoefficient S (fun p => (p : ℕ)) a) /
        ((2 * P + 2 : ℕ) : ℝ) ≤ primePacketBilinear S S a a := by
  rw [divisorGramEnergy_packetCoefficient S _ a (by omega) (primeBlock_nodes S hS),
    prime_bridge_normalization S a (by omega)]
  exact brownianBridge_le_primePacketBilinear S a hS hA hL

/-- A uniform coefficient reserve for the actual neutral prime-block form. -/
theorem primePacket_coefficient_reserve (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    {P : ℕ} (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P)
    (hA : primePacketMass S a = 0) (hL : primePacketLogMoment S a = 0) :
    (∑ p ∈ S, a p ^ 2) ≤ 4 * primePacketBilinear S S a a := by
  have hQ : 0 < 2 * P + 2 := by omega
  have hQr : (0 : ℝ) < (2 * P + 2 : ℕ) := by exact_mod_cast hQ
  have h := packetBridge_coercive S (fun p => (p : ℕ)) a hQ (primeBlock_nodes S hS)
    (fun _ _ _ _ heq => Subtype.val_injective heq)
  rw [← divisorGramEnergy_packetCoefficient S _ a hQ (primeBlock_nodes S hS)] at h
  have hs := divisorGramEnergy_le_primePacket S a hS hA hL
  have hc := div_mul_cancel₀
    (divisorGramEnergy (2 * P + 2) (packetCoefficient S (fun p => (p : ℕ)) a)) hQr.ne'
  have hm := mul_nonneg hQr.le (sq_nonneg (∑ p ∈ S, a p))
  have hup := mul_nonneg hQr.le (sub_nonneg.mpr hs)
  by_contra hn
  have hp := mul_pos hQr (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [h, hc, hm, hup, hp]

/-- The actual prime source pays every linear coupling by a concrete local variation cost. -/
theorem primePacket_schur_bound (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    {P : ℕ} (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P)
    (hA : primePacketMass S a = 0) (hL : primePacketLogMoment S a = 0)
    (b : ℕ → ℝ) :
    2 * (∑ p ∈ S, a p * b (p : ℕ)) - primePacketBilinear S S a a ≤
      dirichletEnergy (2 * P + 2) (interiorExtension (2 * P + 2) b) := by
  have h := packetBridge_schur_bound S (fun p => (p : ℕ)) a (by omega)
    (primeBlock_nodes S hS) b
  rw [← divisorGramEnergy_packetCoefficient S _ a (by omega) (primeBlock_nodes S hS)] at h
  have hs := divisorGramEnergy_le_primePacket S a hS hA hL
  linarith only [h, hs]

#print axioms divisorGramEnergy_le_primePacket
#print axioms primePacket_coefficient_reserve
#print axioms primePacket_schur_bound

end GaloisForLFunctions.CompletedArithmeticForms
