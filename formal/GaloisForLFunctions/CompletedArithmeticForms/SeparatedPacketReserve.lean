import GaloisForLFunctions.CompletedArithmeticForms.PrimePacketSchur

/-!
# Separation strengthens the actual prime-packet reserve

Nonadjacent arithmetic support has Dirichlet energy exactly twice its coefficient
square mass. The attained arithmetic Schur payment converts this identity into a
half reserve. Oddness transfers the improvement to the actual neutral prime block.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open BezoutValuationIncidence

theorem packetCoefficient_zero_outside {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (a : ι → ℝ) {Q r : ℕ} (hk : ∀ i ∈ s, k i ∈ Ico 1 Q)
    (hr : r ∉ Ico 1 Q) : packetCoefficient s k a r = 0 := by
  apply sum_eq_zero
  intro i hi
  exact if_neg (fun h => hr (by simpa only [h] using hk i hi))

theorem packetCoefficient_adjacent_mul_eq_zero {ι : Type*} (s : Finset ι)
    (k : ι → ℕ) (a : ι → ℝ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, k i + 1 ≠ k j) (r : ℕ) :
    packetCoefficient s k a r * packetCoefficient s k a (r + 1) = 0 := by
  classical
  simp only [packetCoefficient, sum_mul, mul_sum]
  apply sum_eq_zero
  intro i hi
  apply sum_eq_zero
  intro j hj
  by_cases hri : r = k i
  · have hrj : r + 1 ≠ k j := by simpa only [hri] using hsep i hi j hj
    simp only [if_neg hrj, mul_zero]
  · simp only [if_neg hri, zero_mul]

/-- Zero-boundary nonadjacent support has an exact, rather than estimated, variation energy. -/
theorem dirichletEnergy_separated {Q : ℕ} (hQ : 0 < Q) (b : ℕ → ℝ)
    (hb0 : b 0 = 0) (hbQ : b Q = 0)
    (hsep : ∀ r ∈ range Q, b r * b (r + 1) = 0) :
    dirichletEnergy Q b = 2 * ∑ r ∈ Ico 1 Q, b r ^ 2 := by
  have hshift : (∑ r ∈ range Q, b (r + 1) ^ 2) = ∑ r ∈ range Q, b r ^ 2 := by
    have h := Finset.sum_range_sub' (fun r => b r ^ 2) Q
    simp only [sum_sub_distrib, hb0, hbQ, zero_pow (by omega), sub_self] at h
    exact (sub_eq_zero.mp h).symm
  have hinterior : (∑ r ∈ Ico 1 Q, b r ^ 2) = ∑ r ∈ range Q, b r ^ 2 := by
    rw [sum_Ico_eq_sub (fun r => b r ^ 2) hQ]
    simp [hb0]
  calc
    _ = ∑ r ∈ range Q, (b (r + 1) ^ 2 + b r ^ 2) := by
      apply sum_congr rfl
      intro r hr
      nlinarith only [hsep r hr]
    _ = _ := by rw [sum_add_distrib, hshift, hinterior]; ring

/-- Distinct nonadjacent arithmetic indices double the uniform coefficient reserve. -/
theorem packetBridge_separated_reserve {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (a : ι → ℝ) {Q : ℕ} (hQ : 0 < Q) (hk : ∀ i ∈ s, k i ∈ Ico 1 Q)
    (hinj : Set.InjOn k s) (hsep : ∀ i ∈ s, ∀ j ∈ s, k i + 1 ≠ k j) :
    (∑ i ∈ s, a i ^ 2) ≤
      2 * ((∑ i ∈ s, ∑ j ∈ s, a i * a j * bridgeKernel Q (k i) (k j)) / Q) := by
  let C := packetCoefficient s k a
  have hext : interiorExtension Q C = C := by
    funext r
    by_cases hr : r ∈ Ico 1 Q
    · simp only [interiorExtension, if_pos hr]
    · rw [interiorExtension, if_neg hr, packetCoefficient_zero_outside s k a hk hr]
  have hC0 : C 0 = 0 := packetCoefficient_zero_outside s k a hk (by simp)
  have hCQ : C Q = 0 := packetCoefficient_zero_outside s k a hk (by simp)
  have hD : dirichletEnergy Q C = 2 * ∑ i ∈ s, a i ^ 2 := by
    rw [dirichletEnergy_separated hQ C hC0 hCQ
      (fun r _ => packetCoefficient_adjacent_mul_eq_zero s k a hsep r)]
    rw [packetCoefficient_sq_mass s k a hk hinj]
  have hpair : (∑ i ∈ s, a i * ((1 / 2 : ℝ) * C (k i))) =
      (1 / 2 : ℝ) * ∑ i ∈ s, a i ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [packetCoefficient_at s k a hinj hi]
    ring
  have h := packetBridge_schur_bound s k a hQ hk (fun r => (1 / 2 : ℝ) * C r)
  rw [hpair, interiorExtension_mul, hext, dirichletEnergy_mul, hD] at h
  linarith only [h]

/-- The actual neutral prime source has a half coefficient reserve throughout odd prime blocks. -/
theorem primePacket_odd_coefficient_reserve (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    {P : ℕ} (hP : 2 ≤ P) (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P)
    (hA : primePacketMass S a = 0) (hL : primePacketLogMoment S a = 0) :
    (∑ p ∈ S, a p ^ 2) ≤ 2 * primePacketBilinear S S a a := by
  have hk : ∀ p ∈ S, (p : ℕ) ∈ Ico 1 (2 * P + 2) := by
    intro p hp
    have h := hS p hp
    exact mem_Ico.mpr ⟨p.property.pos, by omega⟩
  have hsep : ∀ p ∈ S, ∀ q ∈ S, (p : ℕ) + 1 ≠ (q : ℕ) := by
    intro p hp q hq heq
    have hpgt := (hS p hp).1
    have hqgt := (hS q hq).1
    have hpodd := p.property.eq_two_or_odd.resolve_left (by omega)
    have hqodd := q.property.eq_two_or_odd.resolve_left (by omega)
    omega
  have h := packetBridge_separated_reserve S (fun p => (p : ℕ)) a (by omega) hk
    (fun _ _ _ _ heq => Subtype.val_injective heq) hsep
  rw [← divisorGramEnergy_packetCoefficient S _ a (by omega) hk] at h
  have hs := divisorGramEnergy_le_primePacket S a hS hA hL
  linarith only [h, hs]

#print axioms packetBridge_separated_reserve
#print axioms primePacket_odd_coefficient_reserve

end GaloisForLFunctions.CompletedArithmeticForms
