import GaloisForLFunctions.CompletedArithmeticForms.DirichletSchurCost

/-!
# Arithmetic packets, collisions, and mixed couplings

Finite packets enter the completed conductor form through their sums at equal arithmetic
indices. This identifies the exact collision radical, preserves coefficient coercivity on
distinct indices, and transfers the Dirichlet Schur payment to arbitrary interior packets.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- Coefficients sharing an arithmetic index contribute through their total mass. -/
def packetCoefficient {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a : ι → ℝ)
    (r : ℕ) : ℝ :=
  ∑ i ∈ s, if r = k i then a i else 0

/-- Fiber summation preserves every linear coupling depending on the arithmetic index. -/
theorem packetCoefficient_pairing {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a : ι → ℝ)
    {Q : ℕ} (hk : ∀ i ∈ s, k i ∈ Ico 1 Q) (b : ℕ → ℝ) :
    (∑ r ∈ Ico 1 Q, packetCoefficient s k a r * b r) =
      ∑ i ∈ s, a i * b (k i) := by
  classical
  simp only [packetCoefficient, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  simp [ite_mul, hk i hi]

theorem packetCoefficient_at {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a : ι → ℝ)
    (hinj : Set.InjOn k s) {i : ι} (hi : i ∈ s) :
    packetCoefficient s k a (k i) = a i := by
  classical
  unfold packetCoefficient
  rw [sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : k i ≠ k j := fun h => hji (hinj hi hj h).symm
    simp only [if_neg hne]
  · exact fun h => (h hi).elim

/-- Distinct arithmetic indices preserve the coefficient square norm exactly. -/
theorem packetCoefficient_sq_mass {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a : ι → ℝ)
    {Q : ℕ} (hk : ∀ i ∈ s, k i ∈ Ico 1 Q) (hinj : Set.InjOn k s) :
    (∑ r ∈ Ico 1 Q, packetCoefficient s k a r ^ 2) = ∑ i ∈ s, a i ^ 2 := by
  calc
    _ = ∑ r ∈ Ico 1 Q, packetCoefficient s k a r * packetCoefficient s k a r := by
      simp only [pow_two]
    _ = ∑ i ∈ s, a i * packetCoefficient s k a (k i) :=
      packetCoefficient_pairing s k a hk _
    _ = _ := sum_congr rfl fun i hi => by rw [packetCoefficient_at s k a hinj hi, pow_two]

theorem bridgePotential_packetCoefficient {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (a : ι → ℝ) {Q : ℕ} (hk : ∀ i ∈ s, k i ∈ Ico 1 Q) (r : ℕ) :
    bridgePotential Q (packetCoefficient s k a) r =
      ∑ i ∈ s, a i * bridgeKernel Q r (k i) := by
  unfold bridgePotential
  conv_lhs => arg 2; ext j; rw [mul_comm]
  exact packetCoefficient_pairing s k a hk _

/-- The full arithmetic bridge on a packet is its completed conductor energy after aggregation. -/
theorem divisorGramEnergy_packetCoefficient {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (a : ι → ℝ) {Q : ℕ} (hQ : 0 < Q) (hk : ∀ i ∈ s, k i ∈ Ico 1 Q) :
    divisorGramEnergy Q (packetCoefficient s k a) =
      ∑ i ∈ s, ∑ j ∈ s, a i * a j * bridgeKernel Q (k i) (k j) := by
  rw [divisorGramEnergy_eq_sum_potential hQ, packetCoefficient_pairing s k a hk]
  refine sum_congr rfl fun i _ => ?_
  rw [bridgePotential_packetCoefficient s k a hk, mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- Equal-index cancellations are the entire radical of an interior arithmetic packet. -/
theorem packetBridge_eq_zero_iff {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (a : ι → ℝ) {Q : ℕ} (hQ : 0 < Q) (hk : ∀ i ∈ s, k i ∈ Ico 1 Q) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * bridgeKernel Q (k i) (k j)) = 0 ↔
      ∀ r ∈ Ico 1 Q, packetCoefficient s k a r = 0 := by
  rw [← divisorGramEnergy_packetCoefficient s k a hQ hk,
    divisorGramEnergy_eq_zero_iff hQ]

/-- The coefficient reserve survives irregular arithmetic spacing without loss. -/
theorem packetBridge_coercive {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (a : ι → ℝ) {Q : ℕ} (hQ : 0 < Q) (hk : ∀ i ∈ s, k i ∈ Ico 1 Q)
    (hinj : Set.InjOn k s) :
    (Q : ℝ) * ((∑ i ∈ s, a i) ^ 2 + ∑ i ∈ s, a i ^ 2) ≤
      4 * ∑ i ∈ s, ∑ j ∈ s, a i * a j * bridgeKernel Q (k i) (k j) := by
  have h := divisorGramEnergy_coercive hQ (packetCoefficient s k a)
  have hmass := packetCoefficient_pairing s k a hk (fun _ => 1)
  simp only [mul_one] at hmass
  rw [hmass, packetCoefficient_sq_mass s k a hk hinj,
    divisorGramEnergy_packetCoefficient s k a hQ hk] at h
  exact h

/-- A normalized arithmetic packet pays its complete mixed coupling in local variation. -/
theorem packetBridge_schur_bound {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (a : ι → ℝ) {Q : ℕ} (hQ : 0 < Q) (hk : ∀ i ∈ s, k i ∈ Ico 1 Q)
    (b : ℕ → ℝ) :
    2 * (∑ i ∈ s, a i * b (k i)) -
        (∑ i ∈ s, ∑ j ∈ s, a i * a j * bridgeKernel Q (k i) (k j)) / Q ≤
      dirichletEnergy Q (interiorExtension Q b) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h := bridgeSchur_bound hQ (packetCoefficient s k a) (fun r => (Q : ℝ) * b r)
  rw [packetCoefficient_pairing s k a hk, divisorGramEnergy_packetCoefficient s k a hQ hk,
    bridgeSchurCost_mul, bridgeSchurCost] at h
  have hpair : (∑ i ∈ s, a i * ((Q : ℝ) * b (k i))) =
      (Q : ℝ) * ∑ i ∈ s, a i * b (k i) := by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  have hcost (D : ℝ) : (Q : ℝ) ^ 2 * (D / Q) = (Q : ℝ) * D := by
    field_simp
  rw [hpair, hcost] at h
  have hcancel := div_mul_cancel₀
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * bridgeKernel Q (k i) (k j)) hQr.ne'
  by_contra hn
  have hp := mul_pos hQr (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [h, hcancel, hp]

#print axioms packetBridge_eq_zero_iff
#print axioms packetBridge_coercive
#print axioms packetBridge_schur_bound

end GaloisForLFunctions.CompletedArithmeticForms
