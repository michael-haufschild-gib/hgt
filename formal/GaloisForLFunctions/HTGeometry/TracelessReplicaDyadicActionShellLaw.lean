import GaloisForLFunctions.HTGeometry.DyadicGaussianActionShellCertificate
import GaloisForLFunctions.HTGeometry.TracelessReplicaCancellationLaw

/-!
# Traceless-replica dyadic action-shell law

The universal dyadic Gaussian shell certificate is specialized to the
signed paired multiplicities of an arbitrary finite replica expansion.  This
identifies its zero-action plateau with the exact replica-collision sector and
turns every excess above that plateau into a large collision-free action
shell, subject only to the finite replica gap.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Finite dictionary of ordered multiplicity pairs at replica order `n`. -/
def complexReplicaPairSupport
    (I : Type*) [Fintype I] [DecidableEq I]
    (n : ℕ) : Finset ((I → ℕ) × (I → ℕ)) :=
  Finset.univ.piAntidiag n ×ˢ Finset.univ.piAntidiag n

/-- Signed coefficient attached to an ordered replica-multiplicity pair. -/
def complexReplicaPairCoefficient
    {I : Type*} [Fintype I]
    (coefficient : I → ℂ) (pair : (I → ℕ) × (I → ℕ)) : ℂ :=
  complexReplicaPairAmplitude coefficient pair.1 pair.2

/-- Forward-minus-backward replica energy of one multiplicity pair. -/
def complexReplicaPairDetuning
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (pair : (I → ℕ) × (I → ℕ)) : ℝ :=
  replicaMultiplicityEnergy energy pair.1 -
    replicaMultiplicityEnergy energy pair.2

/-- Gaussian-smoothed signed paired replica mass. -/
def complexReplicaGaussianActionMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ)
    (n : ℕ) (time : ℝ) : ℂ :=
  gaussianActionHeatPacket (complexReplicaPairSupport I n)
    (complexReplicaPairCoefficient coefficient)
    (complexReplicaPairDetuning energy) time

/-- Exact zero-action collision plateau of the signed replica packet. -/
def complexReplicaGaussianCollisionPlateau
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ) (n : ℕ) : ℂ :=
  zeroActionSpectralPacket (complexReplicaPairSupport I n)
    (complexReplicaPairCoefficient coefficient)
    (complexReplicaPairDetuning energy)

/-- Difference of signed replica action mass at adjacent dyadic scales. -/
def complexReplicaDyadicActionWavelet
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ)
    (n : ℕ) (time : ℝ) : ℂ :=
  dyadicGaussianActionWavelet (complexReplicaPairSupport I n)
    (complexReplicaPairCoefficient coefficient)
    (complexReplicaPairDetuning energy) time

/-- The abstract packet value is the expected nested paired-replica sum. -/
theorem complexReplicaGaussianActionMass_eq_pair_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ)
    (n : ℕ) (time : ℝ) :
    complexReplicaGaussianActionMass coefficient energy n time =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          complexReplicaPairAmplitude coefficient p q *
            gaussianObserverActionKernel
              (time * (replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q)) := by
  classical
  unfold complexReplicaGaussianActionMass gaussianActionHeatPacket
    complexReplicaPairSupport complexReplicaPairCoefficient
    complexReplicaPairDetuning
  rw [Finset.sum_product]

/-- The zero-action plateau is exactly the equal-replica-energy sector. -/
theorem complexReplicaGaussianCollisionPlateau_eq_sectorMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ) (n : ℕ) :
    complexReplicaGaussianCollisionPlateau coefficient energy n =
      complexReplicaSectorMass coefficient n
        (fun p q => replicaMultiplicityEnergy energy p =
          replicaMultiplicityEnergy energy q) := by
  classical
  unfold complexReplicaGaussianCollisionPlateau zeroActionSpectralPacket
    complexReplicaPairSupport complexReplicaPairCoefficient
    complexReplicaPairDetuning complexReplicaSectorMass
  rw [Finset.sum_filter]
  rw [show
      (∑ x ∈ Finset.univ.piAntidiag n ×ˢ Finset.univ.piAntidiag n,
        if replicaMultiplicityEnergy energy x.1 -
            replicaMultiplicityEnergy energy x.2 = 0
        then complexReplicaPairAmplitude coefficient x.1 x.2 else 0) =
      ∑ x ∈ Finset.univ.piAntidiag n ×ˢ Finset.univ.piAntidiag n,
        if replicaMultiplicityEnergy energy x.1 =
            replicaMultiplicityEnergy energy x.2
        then complexReplicaPairAmplitude coefficient x.1 x.2 else 0 by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases heq : replicaMultiplicityEnergy energy x.1 =
          replicaMultiplicityEnergy energy x.2
      · simp [heq]
      · have hsub : replicaMultiplicityEnergy energy x.1 -
            replicaMultiplicityEnergy energy x.2 ≠ 0 := sub_ne_zero.mpr heq
        simp [heq, hsub]]
  rw [Finset.sum_product]

/-- For zero-sum one-copy coefficients, the collision plateau is exactly the
negative of the noncollision sector.  No positive near-action mass is charged
to this common recurrence channel. -/
theorem complexReplicaGaussianCollisionPlateau_eq_neg_noncollision
    {I : Type*} [Fintype I] [DecidableEq I]
    {coefficient : I → ℂ} (hcoefficient : ∑ i, coefficient i = 0)
    (energy : I → ℝ) {n : ℕ} (hn : 0 < n) :
    complexReplicaGaussianCollisionPlateau coefficient energy n =
      -complexReplicaSectorMass coefficient n
        (fun p q => replicaMultiplicityEnergy energy p ≠
          replicaMultiplicityEnergy energy q) := by
  rw [complexReplicaGaussianCollisionPlateau_eq_sectorMass]
  exact complexReplicaSectorMass_eq_neg_complement_of_sum_eq_zero
    hcoefficient hn
      (fun p q => replicaMultiplicityEnergy energy p =
        replicaMultiplicityEnergy energy q)

/-- **Replica collision erasure.**  The dyadic reporter contains only pairs
with nonzero replica-energy detuning. -/
theorem complexReplicaDyadicActionWavelet_eq_noncollision_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ)
    (n : ℕ) (time : ℝ) :
    complexReplicaDyadicActionWavelet coefficient energy n time =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          if replicaMultiplicityEnergy energy p =
              replicaMultiplicityEnergy energy q
          then 0
          else complexReplicaPairAmplitude coefficient p q *
            (gaussianObserverActionKernel
                (time * (replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q)) -
              gaussianObserverActionKernel
                ((2 * time) * (replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q))) := by
  classical
  unfold complexReplicaDyadicActionWavelet
  rw [dyadicGaussianActionWavelet_eq_nonzero_sum]
  unfold complexReplicaPairSupport complexReplicaPairCoefficient
    complexReplicaPairDetuning
  rw [show
      (∑ x ∈ Finset.univ.piAntidiag n ×ˢ Finset.univ.piAntidiag n,
        if replicaMultiplicityEnergy energy x.1 -
            replicaMultiplicityEnergy energy x.2 = 0
        then 0 else
          complexReplicaPairAmplitude coefficient x.1 x.2 *
            (gaussianObserverActionKernel
                (time * (replicaMultiplicityEnergy energy x.1 -
                  replicaMultiplicityEnergy energy x.2)) -
              gaussianObserverActionKernel
                ((2 * time) * (replicaMultiplicityEnergy energy x.1 -
                  replicaMultiplicityEnergy energy x.2)))) =
      ∑ x ∈ Finset.univ.piAntidiag n ×ˢ Finset.univ.piAntidiag n,
        if replicaMultiplicityEnergy energy x.1 =
            replicaMultiplicityEnergy energy x.2
        then 0 else
          complexReplicaPairAmplitude coefficient x.1 x.2 *
            (gaussianObserverActionKernel
                (time * (replicaMultiplicityEnergy energy x.1 -
                  replicaMultiplicityEnergy energy x.2)) -
              gaussianObserverActionKernel
                ((2 * time) * (replicaMultiplicityEnergy energy x.1 -
                  replicaMultiplicityEnergy energy x.2))) by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases heq : replicaMultiplicityEnergy energy x.1 =
          replicaMultiplicityEnergy energy x.2
      · simp [heq]
      · have hsub : replicaMultiplicityEnergy energy x.1 -
            replicaMultiplicityEnergy energy x.2 ≠ 0 := sub_ne_zero.mpr heq
        simp [heq, hsub]]
  rw [Finset.sum_product]

/-- **Replica dyadic action telescope.**  Shell reporters reconstruct the
whole finite-scale change of signed replica action mass. -/
theorem sum_complexReplicaDyadicActionWavelet_eq_sub
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ)
    (n : ℕ) (time : ℝ) (levels : ℕ) :
    (∑ j ∈ Finset.range levels,
      complexReplicaDyadicActionWavelet coefficient energy n
        ((2 : ℝ) ^ j * time)) =
      complexReplicaGaussianActionMass coefficient energy n time -
        complexReplicaGaussianActionMass coefficient energy n
          ((2 : ℝ) ^ levels * time) := by
  exact sum_dyadicGaussianActionWavelet_eq_sub
    (complexReplicaPairSupport I n)
    (complexReplicaPairCoefficient coefficient)
    (complexReplicaPairDetuning energy) time levels

/-- Total variation of all signed paired replica coefficients. -/
def complexReplicaPairTotalVariation
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (n : ℕ) : ℝ :=
  ∑ pair ∈ complexReplicaPairSupport I n,
    ‖complexReplicaPairCoefficient coefficient pair‖

/-- The total variation of one multinomial replica layer is exactly the
`n`th power of the one-copy coefficient variation. -/
theorem sum_norm_complexReplicaMultiplicityAmplitude_eq_pow
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (n : ℕ) :
    (∑ p ∈ Finset.univ.piAntidiag n,
      ‖complexReplicaMultiplicityAmplitude coefficient p‖) =
        (∑ i, ‖coefficient i‖) ^ n := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  apply Finset.sum_congr rfl
  intro p hp
  unfold complexReplicaMultiplicityAmplitude
  rw [norm_mul, norm_prod]
  simp only [norm_natCast, norm_pow]

/-- **Exact paired-replica variation law.**  The apparent paired-dictionary
prefactor is not an uncontrolled double sum: it is precisely the `2n`th power
of one-copy total variation. -/
theorem complexReplicaPairTotalVariation_eq_pow
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (n : ℕ) :
    complexReplicaPairTotalVariation coefficient n =
      (∑ i, ‖coefficient i‖) ^ (2 * n) := by
  classical
  unfold complexReplicaPairTotalVariation complexReplicaPairSupport
    complexReplicaPairCoefficient complexReplicaPairAmplitude
  rw [Finset.sum_product]
  simp only [norm_mul, RCLike.norm_conj]
  calc
    (∑ p ∈ Finset.univ.piAntidiag n,
      ∑ q ∈ Finset.univ.piAntidiag n,
        ‖complexReplicaMultiplicityAmplitude coefficient p‖ *
          ‖complexReplicaMultiplicityAmplitude coefficient q‖) =
        (∑ p ∈ Finset.univ.piAntidiag n,
          ‖complexReplicaMultiplicityAmplitude coefficient p‖) *
        (∑ q ∈ Finset.univ.piAntidiag n,
          ‖complexReplicaMultiplicityAmplitude coefficient q‖) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = (∑ i, ‖coefficient i‖) ^ n *
        (∑ i, ‖coefficient i‖) ^ n := by
      rw [sum_norm_complexReplicaMultiplicityAmplitude_eq_pow]
    _ = (∑ i, ‖coefficient i‖) ^ (2 * n) := by
      rw [← pow_add]
      congr 1
      omega

/-- **Signed-replica inverse shell certificate.**  Any Gaussian replica
excess above the exact collision plateau forces one large collision-free
dyadic action shell. -/
theorem exists_large_complexReplicaDyadicActionWavelet
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ) (n : ℕ)
    {time gap η : ℝ} {levels : ℕ}
    (htime : 0 < time) (hgap : 0 < gap) (hη : 0 ≤ η)
    (hlevels : 0 < levels)
    (hdetuning :
      ∀ p ∈ Finset.univ.piAntidiag n,
        ∀ q ∈ Finset.univ.piAntidiag n,
          replicaMultiplicityEnergy energy p ≠
              replicaMultiplicityEnergy energy q →
            gap ≤ |replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q|)
    (hexcess : η ≤
      ‖complexReplicaGaussianActionMass coefficient energy n time -
        complexReplicaGaussianCollisionPlateau coefficient energy n‖)
    (htail :
      complexReplicaPairTotalVariation coefficient n *
          Real.exp (-((((2 : ℝ) ^ levels * time) * gap) ^ 2) / 2) ≤
        η / 2) :
    ∃ j ∈ Finset.range levels,
      η / (2 * (levels : ℝ)) ≤
        ‖complexReplicaDyadicActionWavelet coefficient energy n
          ((2 : ℝ) ^ j * time)‖ := by
  apply exists_large_dyadicGaussianActionWavelet
    (complexReplicaPairSupport I n)
    (complexReplicaPairCoefficient coefficient)
    (complexReplicaPairDetuning energy)
    htime hgap hη hlevels
  · intro pair hpair hne
    unfold complexReplicaPairSupport at hpair
    rw [Finset.mem_product] at hpair
    unfold complexReplicaPairDetuning at hne ⊢
    exact hdetuning pair.1 hpair.1 pair.2 hpair.2 (sub_ne_zero.mp hne)
  · exact hexcess
  · exact htail

/-- Explicit form of the inverse shell certificate: its terminal prefactor is
the `2n`th power of one-copy total variation, with no hidden paired-replica
constant. -/
theorem exists_large_complexReplicaDyadicActionWavelet_of_oneCopyVariation
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ) (n : ℕ)
    {time gap η : ℝ} {levels : ℕ}
    (htime : 0 < time) (hgap : 0 < gap) (hη : 0 ≤ η)
    (hlevels : 0 < levels)
    (hdetuning :
      ∀ p ∈ Finset.univ.piAntidiag n,
        ∀ q ∈ Finset.univ.piAntidiag n,
          replicaMultiplicityEnergy energy p ≠
              replicaMultiplicityEnergy energy q →
            gap ≤ |replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q|)
    (hexcess : η ≤
      ‖complexReplicaGaussianActionMass coefficient energy n time -
        complexReplicaGaussianCollisionPlateau coefficient energy n‖)
    (htail :
      (∑ i, ‖coefficient i‖) ^ (2 * n) *
          Real.exp (-((((2 : ℝ) ^ levels * time) * gap) ^ 2) / 2) ≤
        η / 2) :
    ∃ j ∈ Finset.range levels,
      η / (2 * (levels : ℝ)) ≤
        ‖complexReplicaDyadicActionWavelet coefficient energy n
          ((2 : ℝ) ^ j * time)‖ := by
  apply exists_large_complexReplicaDyadicActionWavelet
    coefficient energy n htime hgap hη hlevels hdetuning hexcess
  rw [complexReplicaPairTotalVariation_eq_pow]
  exact htail

end GaloisForLFunctions.HTGeometry
