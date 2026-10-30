import GaloisForLFunctions.CompletedArithmeticForms.IrregularGreen
import GaloisForLFunctions.CompletedArithmeticForms.PrimePacketSchur

/-!
# Arithmetic restriction has an optimal Dirichlet extension

The normalized completed conductor potential extends prescribed values at irregular
integer nodes with exactly their reciprocal-gap energy. Every other zero-boundary
extension has at least this energy. Restriction and extension therefore preserve
the exact dual cost, including both endpoint gaps.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

private theorem interpolation_period_pos {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0) : 0 < k N := by
  have h := hk (Nat.zero_le N) (Nat.le_refl N) hN
  simpa only [h0] using h

private theorem interpolation_nodes {N : ℕ} {k : ℕ → ℕ}
    (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0) :
    ∀ i ∈ Ico 1 N, k i ∈ Ico 1 (k N) := by
  intro i hi
  rcases mem_Ico.mp hi with ⟨hi0, hiN⟩
  have hleft := hk (Nat.zero_le N) hiN.le hi0
  rw [h0] at hleft
  exact mem_Ico.mpr ⟨hleft, hk hiN.le (Nat.le_refl N) hiN⟩

/-- The canonical extension is the full arithmetic potential of the irregular second difference. -/
def meshInterpolation (N : ℕ) (k : ℕ → ℕ) (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  (k N : ℝ)⁻¹ * bridgePotential (k N)
    (packetCoefficient (Ico 1 N) k (meshDifference k b)) r

/-- The full potential restricts literally to the irregular arithmetic potential. -/
theorem meshInterpolation_at_node {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (b : ℕ → ℝ) (i : ℕ) :
    meshInterpolation N k b (k i) = meshPotential N k (meshDifference k b) i := by
  have hQ : (k N : ℝ) ≠ 0 := by exact_mod_cast (interpolation_period_pos hN hk h0).ne'
  rw [meshInterpolation, bridgePotential_packetCoefficient _ _ _ (interpolation_nodes hk h0),
    mul_sum]
  unfold meshPotential
  refine sum_congr rfl fun j _ => ?_
  simp only [bridgeKernel, meshKernel, Nat.cast_min]
  field_simp

theorem meshInterpolation_values {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    ∀ i, i ≤ N → meshInterpolation N k b (k i) = b i := by
  intro i hi
  rw [meshInterpolation_at_node hN hk h0]
  exact meshPotential_inverse hN hk h0 b hb0 hbN i hi

theorem meshInterpolation_zero (N : ℕ) (k : ℕ → ℕ) (b : ℕ → ℝ) :
    meshInterpolation N k b 0 = 0 := by
  rw [meshInterpolation, bridgePotential_zero, mul_zero]

theorem meshInterpolation_endpoint (N : ℕ) (k : ℕ → ℕ) (b : ℕ → ℝ) :
    meshInterpolation N k b (k N) = 0 := by
  rw [meshInterpolation, bridgePotential_endpoint, mul_zero]

/-- Green energy of a normalized complete arithmetic potential equals its source energy. -/
theorem dirichletEnergy_normalized_bridgePotential {Q : ℕ} (hQ : 0 < Q) (a : ℕ → ℝ) :
    dirichletEnergy Q (fun r => (Q : ℝ)⁻¹ * bridgePotential Q a r) =
      divisorGramEnergy Q a / Q := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hD : dirichletEnergy Q (bridgePotential Q a) = (Q : ℝ) * divisorGramEnergy Q a := by
    rw [← sum_mul_dirichletDifference hQ (bridgePotential Q a)
      (bridgePotential_zero Q a) (bridgePotential_endpoint Q a),
      divisorGramEnergy_eq_sum_potential hQ, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [bridgePotential_dirichletDifference Q a hi]
    ring
  rw [dirichletEnergy_mul, hD]
  field_simp

/-- The arithmetic extension attains the exact reciprocal-gap cost. -/
theorem dirichletEnergy_meshInterpolation {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    dirichletEnergy (k N) (meshInterpolation N k b) = meshDirichletEnergy N k b := by
  unfold meshInterpolation
  rw [dirichletEnergy_normalized_bridgePotential (interpolation_period_pos hN hk h0),
    ← meshGram_eq_completed hN hk h0, meshGram_difference hN hk h0 b hb0 hbN]

private theorem dirichletEnergy_zero_extension {Q : ℕ} (u : ℕ → ℝ)
    (hu0 : u 0 = 0) (huQ : u Q = 0) :
    dirichletEnergy Q (interiorExtension Q u) = dirichletEnergy Q u := by
  have he : ∀ r, r ≤ Q → interiorExtension Q u r = u r := by
    intro r hr
    by_cases hi : r ∈ Ico 1 Q
    · exact if_pos hi
    · rw [interiorExtension, if_neg hi]
      have hbd : r = 0 ∨ r = Q := by
        simp only [mem_Ico] at hi
        omega
      rcases hbd with rfl | rfl
      · exact hu0.symm
      · exact huQ.symm
  apply sum_congr rfl
  intro r hr
  have hrQ := mem_range.mp hr
  rw [he r hrQ.le, he (r + 1) (by omega)]

/-- No extension to omitted integer indices can reduce the arithmetic gap payment. -/
theorem meshDirichletEnergy_le_extension {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (b u : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0)
    (hu0 : u 0 = 0) (huQ : u (k N) = 0)
    (hu : ∀ i ∈ Ico 1 N, u (k i) = b i) :
    meshDirichletEnergy N k b ≤ dirichletEnergy (k N) u := by
  have hQ := interpolation_period_pos hN hk h0
  have hnodes := interpolation_nodes hk h0
  have h := packetBridge_schur_bound (Ico 1 N) k (meshDifference k b) hQ hnodes u
  rw [← divisorGramEnergy_packetCoefficient _ _ _ hQ hnodes,
    ← meshGram_eq_completed hN hk h0,
    meshGram_difference hN hk h0 b hb0 hbN,
    dirichletEnergy_zero_extension u hu0 huQ] at h
  have hp : (∑ i ∈ Ico 1 N, meshDifference k b i * u (k i)) =
      meshDirichletEnergy N k b := by
    calc
      _ = ∑ i ∈ Ico 1 N, b i * meshDifference k b i :=
        sum_congr rfl fun i hi => by rw [hu i hi]; ring
      _ = _ := sum_mul_meshDifference hN k b hb0 hbN
  rw [hp] at h
  linarith only [h]

/-- Restriction has an attained minimum-energy extension with no loss in any arithmetic gap. -/
theorem meshDirichletEnergy_isLeast_extension {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    IsLeast {r : ℝ | ∃ u : ℕ → ℝ, u 0 = 0 ∧ u (k N) = 0 ∧
      (∀ i ∈ Ico 1 N, u (k i) = b i) ∧ r = dirichletEnergy (k N) u}
      (meshDirichletEnergy N k b) := by
  constructor
  · refine ⟨meshInterpolation N k b, meshInterpolation_zero N k b,
      meshInterpolation_endpoint N k b, ?_, ?_⟩
    · intro i hi
      exact meshInterpolation_values hN hk h0 b hb0 hbN i (mem_Ico.mp hi).2.le
    · exact (dirichletEnergy_meshInterpolation hN hk h0 b hb0 hbN).symm
  · rintro r ⟨u, hu0, huQ, hu, rfl⟩
    exact meshDirichletEnergy_le_extension hN hk h0 b u hb0 hbN hu0 huQ hu

/-- The actual neutral prime source pays prescribed couplings by their arithmetic gap energy. -/
theorem primePacket_mesh_schur_bound (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    {P N : ℕ} {k : ℕ → ℕ} (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N))
    (h0 : k 0 = 0) (hQ : k N = 2 * P + 2)
    (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P)
    (hA : BezoutValuationIncidence.primePacketMass S a = 0)
    (hL : BezoutValuationIncidence.primePacketLogMoment S a = 0)
    (j : Nat.Primes → ℕ) (hj : ∀ p ∈ S, j p ∈ Ico 1 N)
    (hnode : ∀ p ∈ S, k (j p) = (p : ℕ))
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    2 * (∑ p ∈ S, a p * b (j p)) -
      BezoutValuationIncidence.primePacketBilinear S S a a ≤ meshDirichletEnergy N k b := by
  have h := primePacket_schur_bound S a hS hA hL (meshInterpolation N k b)
  rw [← hQ, dirichletEnergy_zero_extension _ (meshInterpolation_zero N k b)
    (meshInterpolation_endpoint N k b), dirichletEnergy_meshInterpolation hN hk h0 b hb0 hbN] at h
  have hp : (∑ p ∈ S, a p * meshInterpolation N k b (p : ℕ)) =
      ∑ p ∈ S, a p * b (j p) := by
    refine sum_congr rfl fun p hp => ?_
    rw [← hnode p hp, meshInterpolation_values hN hk h0 b hb0 hbN (j p)
      (mem_Ico.mp (hj p hp)).2.le]
  rwa [hp] at h

#print axioms meshInterpolation_values
#print axioms dirichletEnergy_meshInterpolation
#print axioms meshDirichletEnergy_isLeast_extension
#print axioms primePacket_mesh_schur_bound

end GaloisForLFunctions.CompletedArithmeticForms
