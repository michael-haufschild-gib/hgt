import GaloisForLFunctions.HTGeometry.ReplicaActionCrowdingShortcutLaw

/-!
# All-order traceless replica cancellation

Complex spectral coefficients with zero sum have zero total paired replica
mass at every positive order.  More strongly, the signed mass of any replica
sector is the negative of its complement.  This is the cancellation erased
when target amplitudes are replaced by positive absolute weights.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Multinomial amplitude of one replica multiplicity vector for complex,
possibly signed spectral coefficients. -/
def complexReplicaMultiplicityAmplitude
    {I : Type*} [Fintype I]
    (coefficient : I → ℂ) (p : I → ℕ) : ℂ :=
  (Nat.multinomial Finset.univ p : ℂ) *
    ∏ i, coefficient i ^ p i

theorem sum_complexReplicaMultiplicityAmplitude_eq_sum_pow
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (n : ℕ) :
    (∑ p ∈ Finset.univ.piAntidiag n,
      complexReplicaMultiplicityAmplitude coefficient p) =
        (∑ i, coefficient i) ^ n := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  rfl

/-- Paired coefficient in the absolute-square replica expansion. -/
def complexReplicaPairAmplitude
    {I : Type*} [Fintype I]
    (coefficient : I → ℂ) (p q : I → ℕ) : ℂ :=
  complexReplicaMultiplicityAmplitude coefficient p *
    starRingEnd ℂ (complexReplicaMultiplicityAmplitude coefficient q)

theorem sum_complexReplicaPairAmplitude_eq_normSq_sum_pow
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (n : ℕ) :
    (∑ p ∈ Finset.univ.piAntidiag n,
      ∑ q ∈ Finset.univ.piAntidiag n,
        complexReplicaPairAmplitude coefficient p q) =
      (∑ i, coefficient i) ^ n *
        starRingEnd ℂ ((∑ i, coefficient i) ^ n) := by
  classical
  unfold complexReplicaPairAmplitude
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp_rw [← map_sum]
  rw [sum_complexReplicaMultiplicityAmplitude_eq_sum_pow]

/-- Signed mass retained by an arbitrary sector of paired replica
multiplicities. -/
def complexReplicaSectorMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (n : ℕ)
    (relation : (I → ℕ) → (I → ℕ) → Prop) : ℂ := by
  classical
  exact ∑ p ∈ Finset.univ.piAntidiag n,
    ∑ q ∈ Finset.univ.piAntidiag n,
      if relation p q then complexReplicaPairAmplitude coefficient p q else 0

theorem complexReplicaSectorMass_add_complement
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (n : ℕ)
    (relation : (I → ℕ) → (I → ℕ) → Prop) :
    complexReplicaSectorMass coefficient n relation +
        complexReplicaSectorMass coefficient n (fun p q => ¬ relation p q) =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          complexReplicaPairAmplitude coefficient p q := by
  classical
  unfold complexReplicaSectorMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : relation p q <;> simp [h]

/-- **All-order traceless sector cancellation.**  If the one-copy complex
coefficients sum to zero, every positive-order replica sector is exactly the
negative of its complement. -/
theorem complexReplicaSectorMass_eq_neg_complement_of_sum_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    {coefficient : I → ℂ} (hcoefficient : ∑ i, coefficient i = 0)
    {n : ℕ} (hn : 0 < n)
    (relation : (I → ℕ) → (I → ℕ) → Prop) :
    complexReplicaSectorMass coefficient n relation =
      -complexReplicaSectorMass coefficient n (fun p q => ¬ relation p q) := by
  have htotal := complexReplicaSectorMass_add_complement coefficient n relation
  rw [sum_complexReplicaPairAmplitude_eq_normSq_sum_pow,
    hcoefficient, zero_pow hn.ne'] at htotal
  simp only [map_zero, mul_zero] at htotal
  exact eq_neg_of_add_eq_zero_left htotal

end GaloisForLFunctions.HTGeometry
