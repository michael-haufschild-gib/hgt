import GaloisForLFunctions.HTGeometry.FinitePassiveResponse

/-!
# Finite KMS purity, energy gauge, and tensor normalization

This file records three exact quantum-statistical value relations for the generic finite KMS
infrastructure.

* The Gibbs purity is the order-two replica ratio `Z(2β) / Z(β)²`.  The full squared mass of the
  symmetric KMS/Wightman half-density is one, and its diagonal squared mass is the Gibbs purity.
* Adding a constant to every energy changes only the unnormalized partition.  Gibbs weights,
  KMS/Wightman values, Liouvillian moments, and passive responses are invariant.
* Independent finite systems with additive product energy have factorized partition functions,
  Gibbs weights, Wightman half-densities, product-observable intensities, and purities.

The purity/free-energy relation is the order-two specialization of the thermal Rényi relation;
see J. C. Baez, *Rényi Entropy and Free Energy*, Entropy 13 (2011), 1434--1452, and A. Iwaki and
C. Hotta, *Purity of thermal mixed quantum states*, Phys. Rev. B 106 (2022), 094409.
The rank-one convolution and Gibbs-marginal laws are the coefficient form of the canonical
thermofield-double purification of a Gibbs state; see Y. Takahashi and H. Umezawa, *Thermo field
dynamics*, Collective Phenomena 2 (1975), 55--80, and T. Barthel, arXiv:1708.09349.

All statements apply to arbitrary nonempty finite Hamiltonian spectra.  No arithmetic or zeta
hypothesis occurs in this module.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Order-two purity of a canonical finite Gibbs state. -/
def finiteGibbsPurity {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) : ℝ :=
  ∑ a, finiteGibbsStateWeight β energy a ^ (2 : ℕ)

/-- **Finite thermal replica value.**  Gibbs purity is the partition ratio `Z(2β) / Z(β)²`. -/
theorem finiteGibbsPurity_eq_partitionRatio
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) :
    finiteGibbsPurity β energy =
      finiteGibbsPartition (2 * β) energy /
        finiteGibbsPartition β energy ^ (2 : ℕ) := by
  rw [finiteGibbsPurity]
  simp_rw [finiteGibbsStateWeight, div_pow]
  rw [← Finset.sum_div]
  congr 1
  rw [finiteGibbsPartition]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Every nonempty finite Gibbs state has strictly positive purity. -/
theorem finiteGibbsPurity_pos
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) :
    0 < finiteGibbsPurity β energy := by
  rw [finiteGibbsPurity_eq_partitionRatio]
  exact div_pos (finiteGibbsPartition_pos (2 * β) energy)
    (sq_pos_of_pos (finiteGibbsPartition_pos β energy))

/-- Gibbs purity is at most one. -/
theorem finiteGibbsPurity_le_one
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) :
    finiteGibbsPurity β energy ≤ 1 := by
  classical
  rw [finiteGibbsPurity]
  calc
    (∑ a, finiteGibbsStateWeight β energy a ^ (2 : ℕ)) ≤
        ∑ a, finiteGibbsStateWeight β energy a := by
      apply Finset.sum_le_sum
      intro a ha
      have hpos := finiteGibbsStateWeight_pos β energy a
      have hle : finiteGibbsStateWeight β energy a ≤ 1 := by
        rw [← sum_finiteGibbsStateWeight_eq_one β energy]
        exact Finset.single_le_sum
          (fun b _ => (finiteGibbsStateWeight_pos β energy b).le) ha
      nlinarith
    _ = 1 := sum_finiteGibbsStateWeight_eq_one β energy

/-- The maximally mixed value `1 / dim` is the universal finite-dimensional purity floor. -/
theorem one_div_card_le_finiteGibbsPurity
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) :
    1 / (Fintype.card α : ℝ) ≤ finiteGibbsPurity β energy := by
  have hcard : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hcard, finiteGibbsPurity]
  have h := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ)
    (f := fun a : α => finiteGibbsStateWeight β energy a)
  rw [sum_finiteGibbsStateWeight_eq_one β energy] at h
  simpa [mul_comm] using h

/-- The KMS/Wightman half-density kernel has unit Frobenius mass. -/
theorem sum_sq_finiteKMSWightmanWeight_eq_one
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) :
    ∑ a, ∑ b, finiteKMSWightmanWeight β energy a b ^ (2 : ℕ) = 1 := by
  calc
    (∑ a, ∑ b, finiteKMSWightmanWeight β energy a b ^ (2 : ℕ)) =
        ∑ a, finiteGibbsStateWeight β energy a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_sq_finiteKMSWightmanWeight_eq_stateWeight β energy a
    _ = 1 := sum_finiteGibbsStateWeight_eq_one β energy

/-- The diagonal Frobenius mass of the KMS half-density is exactly Gibbs purity. -/
theorem sum_sq_diag_finiteKMSWightmanWeight_eq_purity
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) :
    ∑ a, finiteKMSWightmanWeight β energy a a ^ (2 : ℕ) =
      finiteGibbsPurity β energy := by
  simp_rw [finiteKMSWightmanWeight_self]
  rfl

/-- Diagonal KMS mass in partition-function coordinates. -/
theorem sum_sq_diag_finiteKMSWightmanWeight_eq_partitionRatio
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) :
    ∑ a, finiteKMSWightmanWeight β energy a a ^ (2 : ℕ) =
      finiteGibbsPartition (2 * β) energy /
        finiteGibbsPartition β energy ^ (2 : ℕ) := by
  rw [sum_sq_diag_finiteKMSWightmanWeight_eq_purity,
    finiteGibbsPurity_eq_partitionRatio]

/-- **Thermofield linear-entropy law.**  The squared mass of the genuinely off-diagonal
thermofield transitions is exactly the order-two linear entropy of the Gibbs state.

This is the coefficient form of the canonical-purification identity
`1 - Tr (rho^(2 : ℕ))`: the full thermofield projector has unit Frobenius mass, while its diagonal
mass is the Gibbs purity. -/
theorem sum_offDiagonal_sq_finiteKMSWightmanWeight_eq_one_sub_purity
    {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (β : ℝ) (energy : α → ℝ) :
    (∑ a, ∑ b ∈ Finset.univ.erase a,
        finiteKMSWightmanWeight β energy a b ^ (2 : ℕ)) =
      1 - finiteGibbsPurity β energy := by
  classical
  have hrow : ∀ a : α,
      (∑ b ∈ Finset.univ.erase a,
          finiteKMSWightmanWeight β energy a b ^ (2 : ℕ)) =
        finiteGibbsStateWeight β energy a -
          finiteGibbsStateWeight β energy a ^ (2 : ℕ) := by
    intro a
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun b => finiteKMSWightmanWeight β energy a b ^ (2 : ℕ))
      (Finset.mem_univ a)
    have htotal := sum_sq_finiteKMSWightmanWeight_eq_stateWeight
      β energy a
    change finiteKMSWightmanWeight β energy a a ^ (2 : ℕ) +
      (∑ b ∈ Finset.univ.erase a,
        finiteKMSWightmanWeight β energy a b ^ (2 : ℕ)) =
      ∑ b, finiteKMSWightmanWeight β energy a b ^ (2 : ℕ) at hsplit
    rw [finiteKMSWightmanWeight_self] at hsplit
    linarith
  simp_rw [hrow]
  rw [Finset.sum_sub_distrib, sum_finiteGibbsStateWeight_eq_one]
  rfl

/-- The thermofield off-diagonal mass is nonnegative, so the linear-entropy value is
nonnegative without a separate purity estimate. -/
theorem zero_le_one_sub_finiteGibbsPurity_of_thermofield
    {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (β : ℝ) (energy : α → ℝ) :
    0 ≤ 1 - finiteGibbsPurity β energy := by
  rw [← sum_offDiagonal_sq_finiteKMSWightmanWeight_eq_one_sub_purity
    β energy]
  positivity

/-- At zero inverse temperature, the partition is the state-space cardinality. -/
theorem finiteGibbsPartition_zero
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    finiteGibbsPartition 0 energy = Fintype.card α := by
  simp [finiteGibbsPartition]

/-- The zero-inverse-temperature state saturates the maximally mixed purity floor. -/
theorem finiteGibbsPurity_zero
    {α : Type*} [Fintype α] [Nonempty α] (energy : α → ℝ) :
    finiteGibbsPurity 0 energy = 1 / (Fintype.card α : ℝ) := by
  rw [finiteGibbsPurity_eq_partitionRatio, mul_zero,
    finiteGibbsPartition_zero]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by positivity
  field_simp

/-! ## Energy-origin gauge -/

/-- Shifting the energy origin rescales the finite partition by the common Boltzmann factor. -/
theorem finiteGibbsPartition_add_const
    {α : Type*} [Fintype α]
    (β c : ℝ) (energy : α → ℝ) :
    finiteGibbsPartition β (fun a => energy a + c) =
      Real.exp (-β * c) * finiteGibbsPartition β energy := by
  rw [finiteGibbsPartition, finiteGibbsPartition]
  simp_rw [show ∀ a, -β * (energy a + c) = -β * c + -β * energy a by
    intro a; ring, Real.exp_add]
  rw [← Finset.mul_sum]

/-- Normalized Gibbs probabilities do not depend on the chosen energy origin. -/
theorem finiteGibbsStateWeight_add_const
    {α : Type*} [Fintype α] [Nonempty α]
    (β c : ℝ) (energy : α → ℝ) (a : α) :
    finiteGibbsStateWeight β (fun x => energy x + c) a =
      finiteGibbsStateWeight β energy a := by
  rw [finiteGibbsStateWeight, finiteGibbsStateWeight,
    finiteGibbsPartition_add_const]
  rw [show -β * (energy a + c) = -β * c + -β * energy a by ring,
    Real.exp_add]
  field_simp [Real.exp_ne_zero]

/-- Symmetric KMS/Wightman half-densities do not depend on the chosen energy origin. -/
theorem finiteKMSWightmanWeight_add_const
    {α : Type*} [Fintype α] [Nonempty α]
    (β c : ℝ) (energy : α → ℝ) (a b : α) :
    finiteKMSWightmanWeight β (fun x => energy x + c) a b =
      finiteKMSWightmanWeight β energy a b := by
  rw [finiteKMSWightmanWeight, finiteKMSWightmanWeight,
    finiteGibbsPartition_add_const]
  have harg : -β * (((energy a + c) + (energy b + c)) / 2) =
      -β * c + -β * ((energy a + energy b) / 2) := by ring
  rw [harg, Real.exp_add]
  field_simp [Real.exp_ne_zero]

/-- Gibbs purity is invariant under a common energy shift. -/
theorem finiteGibbsPurity_add_const
    {α : Type*} [Fintype α] [Nonempty α]
    (β c : ℝ) (energy : α → ℝ) :
    finiteGibbsPurity β (fun x => energy x + c) =
      finiteGibbsPurity β energy := by
  simp only [finiteGibbsPurity, finiteGibbsStateWeight_add_const]

/-- Canonical KMS transition intensities are energy-origin gauge invariant. -/
theorem finiteKMSWightmanTransitionIntensity_add_const
    {α : Type*} [Fintype α] [Nonempty α]
    (β c : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) :
    finiteKMSWightmanTransitionIntensity β (fun x => energy x + c) amplitude a b =
      finiteKMSWightmanTransitionIntensity β energy amplitude a b := by
  rw [finiteKMSWightmanTransitionIntensity, finiteKMSWightmanTransitionIntensity,
    wightmanTransitionIntensity, wightmanTransitionIntensity,
    finiteKMSWightmanWeight_add_const]

/-- Every canonical finite KMS Liouvillian moment is energy-origin gauge invariant. -/
theorem thermalGapMoment_finiteKMS_add_const
    {α : Type*} [Fintype α] [Nonempty α]
    (β c : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (k : ℕ) :
    thermalGapMoment
        (finiteKMSWightmanTransitionIntensity β (fun x => energy x + c) amplitude)
        (fun x => energy x + c) k =
      thermalGapMoment
        (finiteKMSWightmanTransitionIntensity β energy amplitude) energy k := by
  simp only [thermalGapMoment, finiteKMSWightmanTransitionIntensity_add_const]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 2
  ring

/-- The canonical finite KMS passive response is energy-origin gauge invariant. -/
theorem finiteTransitionPassiveResponse_finiteKMS_add_const
    {α : Type*} [Fintype α] [Nonempty α]
    (β c : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (z : ℂ) :
    finiteTransitionPassiveResponse
        (finiteKMSWightmanTransitionIntensity β (fun x => energy x + c) amplitude)
        (fun x => energy x + c) z =
      finiteTransitionPassiveResponse
        (finiteKMSWightmanTransitionIntensity β energy amplitude) energy z := by
  simp only [finiteTransitionPassiveResponse,
    finiteKMSWightmanTransitionIntensity_add_const]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 3
  ring

/-! ## Independent-system tensor factorization -/

/-- Additive Hamiltonian on a product of two independent finite state spaces. -/
def finiteTensorEnergy {α γ : Type*}
    (energyA : α → ℝ) (energyB : γ → ℝ) : α × γ → ℝ :=
  fun x => energyA x.1 + energyB x.2

/-- The partition function of independent finite systems factors. -/
theorem finiteGibbsPartition_tensor
    {α γ : Type*} [Fintype α] [Fintype γ]
    (β : ℝ) (energyA : α → ℝ) (energyB : γ → ℝ) :
    finiteGibbsPartition β (finiteTensorEnergy energyA energyB) =
      finiteGibbsPartition β energyA * finiteGibbsPartition β energyB := by
  rw [finiteGibbsPartition, Fintype.sum_prod_type]
  calc
    (∑ a, ∑ b, Real.exp (-β * finiteTensorEnergy energyA energyB (a, b))) =
        ∑ a, ∑ b, Real.exp (-β * energyA a) * Real.exp (-β * energyB b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Real.exp_add]
      congr 1
      simp only [finiteTensorEnergy]
      ring
    _ = (∑ a, Real.exp (-β * energyA a)) *
        ∑ b, Real.exp (-β * energyB b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ = finiteGibbsPartition β energyA * finiteGibbsPartition β energyB := rfl

/-- Normalized Gibbs probabilities of independent finite systems factor. -/
theorem finiteGibbsStateWeight_tensor
    {α γ : Type*} [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ]
    (β : ℝ) (energyA : α → ℝ) (energyB : γ → ℝ) (a : α) (b : γ) :
    finiteGibbsStateWeight β (finiteTensorEnergy energyA energyB) (a, b) =
      finiteGibbsStateWeight β energyA a * finiteGibbsStateWeight β energyB b := by
  rw [finiteGibbsStateWeight, finiteGibbsStateWeight, finiteGibbsStateWeight,
    finiteGibbsPartition_tensor]
  rw [show -β * finiteTensorEnergy energyA energyB (a, b) =
      -β * energyA a + -β * energyB b by simp [finiteTensorEnergy]; ring,
    Real.exp_add]
  field_simp [ne_of_gt (finiteGibbsPartition_pos β energyA),
    ne_of_gt (finiteGibbsPartition_pos β energyB)]

/-- Symmetric KMS half-densities of independent finite systems factor. -/
theorem finiteKMSWightmanWeight_tensor
    {α γ : Type*} [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ]
    (β : ℝ) (energyA : α → ℝ) (energyB : γ → ℝ)
    (a b : α) (c d : γ) :
    finiteKMSWightmanWeight β (finiteTensorEnergy energyA energyB) (a, c) (b, d) =
      finiteKMSWightmanWeight β energyA a b *
        finiteKMSWightmanWeight β energyB c d := by
  rw [finiteKMSWightmanWeight, finiteKMSWightmanWeight, finiteKMSWightmanWeight,
    finiteGibbsPartition_tensor]
  have harg :
      -β * ((finiteTensorEnergy energyA energyB (a, c) +
        finiteTensorEnergy energyA energyB (b, d)) / 2) =
        -β * ((energyA a + energyA b) / 2) +
          -β * ((energyB c + energyB d) / 2) := by
    simp only [finiteTensorEnergy]
    ring
  rw [harg, Real.exp_add]
  field_simp [ne_of_gt (finiteGibbsPartition_pos β energyA),
    ne_of_gt (finiteGibbsPartition_pos β energyB)]

/-- Product observables have factorized canonical KMS transition intensities. -/
theorem finiteKMSWightmanTransitionIntensity_tensor
    {α γ : Type*} [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ]
    (β : ℝ) (energyA : α → ℝ) (energyB : γ → ℝ)
    (amplitudeA : α → α → ℂ) (amplitudeB : γ → γ → ℂ)
    (a b : α) (c d : γ) :
    finiteKMSWightmanTransitionIntensity β (finiteTensorEnergy energyA energyB)
        (fun x y => amplitudeA x.1 y.1 * amplitudeB x.2 y.2) (a, c) (b, d) =
      finiteKMSWightmanTransitionIntensity β energyA amplitudeA a b *
        finiteKMSWightmanTransitionIntensity β energyB amplitudeB c d := by
  rw [finiteKMSWightmanTransitionIntensity, finiteKMSWightmanTransitionIntensity,
    finiteKMSWightmanTransitionIntensity, wightmanTransitionIntensity,
    wightmanTransitionIntensity, wightmanTransitionIntensity,
    finiteKMSWightmanWeight_tensor, Complex.normSq_mul]
  ring

/-- Gibbs purity is multiplicative under independent finite-system composition. -/
theorem finiteGibbsPurity_tensor
    {α γ : Type*} [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ]
    (β : ℝ) (energyA : α → ℝ) (energyB : γ → ℝ) :
    finiteGibbsPurity β (finiteTensorEnergy energyA energyB) =
      finiteGibbsPurity β energyA * finiteGibbsPurity β energyB := by
  rw [finiteGibbsPurity, Fintype.sum_prod_type]
  simp_rw [finiteGibbsStateWeight_tensor, mul_pow]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [finiteGibbsPurity, finiteGibbsPurity]

/-- **Independent-system linear-entropy composition.**  Off-diagonal thermofield mass obeys
the inclusion--exclusion law `L(A tensor B) = L(A) + L(B) - L(A) L(B)`.  This is the exact
linear-entropy counterpart of multiplicativity of Gibbs purity. -/
theorem sum_offDiagonal_sq_finiteKMSWightmanWeight_tensor
    {α γ : Type*} [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ]
    [DecidableEq α] [DecidableEq γ]
    (β : ℝ) (energyA : α → ℝ) (energyB : γ → ℝ) :
    (∑ x, ∑ y ∈ Finset.univ.erase x,
        finiteKMSWightmanWeight β (finiteTensorEnergy energyA energyB) x y ^ (2 : ℕ)) =
      (∑ a, ∑ b ∈ Finset.univ.erase a,
          finiteKMSWightmanWeight β energyA a b ^ (2 : ℕ)) +
        (∑ c, ∑ d ∈ Finset.univ.erase c,
          finiteKMSWightmanWeight β energyB c d ^ (2 : ℕ)) -
        (∑ a, ∑ b ∈ Finset.univ.erase a,
          finiteKMSWightmanWeight β energyA a b ^ (2 : ℕ)) *
        (∑ c, ∑ d ∈ Finset.univ.erase c,
          finiteKMSWightmanWeight β energyB c d ^ (2 : ℕ)) := by
  simp_rw [sum_offDiagonal_sq_finiteKMSWightmanWeight_eq_one_sub_purity,
    finiteGibbsPurity_tensor]
  ring

end

end HTGeometry
