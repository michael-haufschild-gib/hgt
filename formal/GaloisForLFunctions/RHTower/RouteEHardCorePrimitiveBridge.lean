import GaloisForLFunctions.RHTower.RouteEHardCoreWalshSpectrum

/-!
# Exact primitive-pair bridge for the Route E hard-core field

For any finite prime-indexed source, coprime exclusion is the joint Bernoulli
law of the hard-core transition. An explicit Radon amplifier cancels its
nonuniform masses, making the disjoint primitive-pair quadratic form exactly
an alternating biased-Walsh energy. This retains, rather than bounds, the
literal signed source. No physical Gamma-shell estimate follows from it.
-/

open scoped BigOperators

namespace RHTower
open HTGeometry.ConstraintFrameRelativity
open GaloisForLFunctions.HTGeometry

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Trinary local mass: neither colour, left only, or right only. -/
def routeEHardCoreLocalJointMass (p : ι → ℝ) (S T : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then (if i ∈ T then 0 else 1 / (p i + 1))
  else if i ∈ T then 1 / (p i + 1) else (p i - 1) / (p i + 1)

/-- Full coprime-exclusion pair mass. -/
def routeEHardCoreJointMass (p : ι → ℝ) (S T : Finset ι) : ℝ :=
  ∏ i, routeEHardCoreLocalJointMass p S T i

/-- Vacuum normalizer of the finite trinary field. -/
def routeEHardCoreExclusionNormalizer (p : ι → ℝ) : ℝ :=
  ∏ i, (p i - 1) / (p i + 1)

/-- Radon amplifier recovering counting measure on disjoint subset pairs. -/
def routeEHardCorePrimitiveAmplifier (p : ι → ℝ) (S : Finset ι) : ℝ :=
  ∏ i, if i ∈ S then p i - 1 else 1

omit [Fintype ι] in
private theorem localJointMass_reweight (p : ι → ℝ)
    (hp1 : ∀ i, p i + 1 ≠ 0)
    (S T : Finset ι) (i : ι) (h : i ∉ S ∨ i ∉ T) :
    routeEHardCoreLocalJointMass p S T i *
      (if i ∈ S then p i - 1 else 1) *
      (if i ∈ T then p i - 1 else 1) =
        (p i - 1) / (p i + 1) := by
  rcases h with hs | ht
  · by_cases hti : i ∈ T
    · simp [routeEHardCoreLocalJointMass, hs, hti]
      field_simp [hp1 i]
    · simp [routeEHardCoreLocalJointMass, hs, hti]
  · by_cases hsi : i ∈ S
    · simp [routeEHardCoreLocalJointMass, hsi, ht]
      field_simp [hp1 i]
    · simp [routeEHardCoreLocalJointMass, hsi, ht]

private theorem jointMass_reweight_of_disjoint (p : ι → ℝ)
    (hp1 : ∀ i, p i + 1 ≠ 0)
    (S T : Finset ι) (hST : Disjoint S T) :
    routeEHardCoreJointMass p S T * routeEHardCorePrimitiveAmplifier p S *
      routeEHardCorePrimitiveAmplifier p T =
        routeEHardCoreExclusionNormalizer p := by
  unfold routeEHardCoreJointMass routeEHardCoreExclusionNormalizer
    routeEHardCorePrimitiveAmplifier
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  apply localJointMass_reweight p hp1
  by_cases hs : i ∈ S
  · exact Or.inr (Finset.disjoint_left.mp hST hs)
  · exact Or.inl hs

private theorem jointMass_zero_of_not_disjoint (p : ι → ℝ)
    (S T : Finset ι) (hST : ¬ Disjoint S T) :
    routeEHardCoreJointMass p S T = 0 := by
  have h : ∃ i, i ∈ S ∧ i ∈ T := by
    simpa [Finset.disjoint_left] using hST
  rcases h with ⟨i, his, hit⟩
  unfold routeEHardCoreJointMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [routeEHardCoreLocalJointMass, his, hit]

/-- Exact pointwise Radon identity, including zero on overlapping pairs. -/
theorem routeEHardCoreJointMass_reweight (p : ι → ℝ)
    (hp1 : ∀ i, p i + 1 ≠ 0)
    (S T : Finset ι) :
    routeEHardCoreJointMass p S T * routeEHardCorePrimitiveAmplifier p S *
      routeEHardCorePrimitiveAmplifier p T =
        if Disjoint S T then routeEHardCoreExclusionNormalizer p else 0 := by
  by_cases hST : Disjoint S T
  · simp only [hST, ite_true]
    exact jointMass_reweight_of_disjoint p hp1 S T hST
  · simp only [hST, ite_false]
    rw [jointMass_zero_of_not_disjoint p S T hST]
    ring

/-- The product trinary mass is exactly the joint law of the Markov transition
already diagonalized in `RouteEHardCoreWalshSpectrum`. -/
theorem routeEHardCoreJointMass_eq_bernoulliWeights (p : ι → ℝ)
    (hp : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0)
    (S T : Finset ι) :
    routeEHardCoreJointMass p S T =
      bernoulliWeight (fun i => 1 / (p i + 1)) S *
        bernoulliWeight (routeEHardCoreTransition p S) T := by
  have hsplit (r : ι → ℝ) (U : Finset ι) :
      bernoulliWeight r U = ∏ i, if i ∈ U then r i else 1 - r i := by
    have hfilter : (Finset.univ.filter fun i => i ∉ U) = Uᶜ := by
      ext i
      simp
    simpa [bernoulliWeight, hfilter] using
      (Finset.prod_ite (s := Finset.univ) (p := fun i => i ∈ U)
        r (fun i => 1 - r i)).symm
  rw [hsplit, hsplit, ← Finset.prod_mul_distrib]
  unfold routeEHardCoreJointMass
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T
  all_goals
    simp only [routeEHardCoreLocalJointMass, hs, ht, ite_true, ite_false,
      routeEHardCoreTransition]
    field_simp [hp i, hp1 i]; ring

/-- **Exact primitive-pair spectral bridge.** Any real primitive subset source
`a` has a disjoint-pair quadratic sum equal to signed Walsh-grade energy after
the explicit Radon amplifier. The physical Möbius/Gamma source is one possible
`a`; this identity does not supply its required odd/even grade inequality. -/
theorem routeEHardCorePrimitiveQuadratic_eq_walshSpectrum
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (a : Finset ι → ℝ) :
    let q : ι → ℝ := fun i => 1 / (p i + 1)
    routeEHardCoreExclusionNormalizer p *
      (∑ S : Finset ι, ∑ T : Finset ι,
        if Disjoint S T then a S * a T else 0) =
      ∑ K : Finset ι,
        (∏ i ∈ K, -(1 / p i)) *
          (biasedWalshCoefficient q
            (fun S => routeEHardCorePrimitiveAmplifier p S * a S) K) ^ 2 := by
  let q : ι → ℝ := fun i => 1 / (p i + 1)
  let f : Finset ι → ℝ := fun S => routeEHardCorePrimitiveAmplifier p S * a S
  have hp0 : ∀ i, p i ≠ 0 := fun i => ne_of_gt (by linarith [hp i])
  have hp1 : ∀ i, p i + 1 ≠ 0 := fun i => ne_of_gt (by linarith [hp i])
  have hpair :
      bernoulliExp q (fun S => f S * routeEHardCoreOperator p f S) =
        ∑ S : Finset ι, ∑ T : Finset ι,
          routeEHardCoreJointMass p S T * f S * f T := by
    unfold bernoulliExp routeEHardCoreOperator
    apply Finset.sum_congr rfl
    intro S hS
    unfold bernoulliExp
    change bernoulliWeight q S *
      (f S * ∑ T : Finset ι,
        bernoulliWeight (routeEHardCoreTransition p S) T * f T) = _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [routeEHardCoreJointMass_eq_bernoulliWeights p hp0 hp1 S T]
    dsimp only [q, f]
    ring
  have hsum :
      (∑ S : Finset ι, ∑ T : Finset ι,
          routeEHardCoreJointMass p S T * f S * f T) =
        routeEHardCoreExclusionNormalizer p *
          (∑ S : Finset ι, ∑ T : Finset ι,
            if Disjoint S T then a S * a T else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    dsimp only [f]
    calc
      routeEHardCoreJointMass p S T *
          (routeEHardCorePrimitiveAmplifier p S * a S) *
          (routeEHardCorePrimitiveAmplifier p T * a T) =
          (routeEHardCoreJointMass p S T *
            routeEHardCorePrimitiveAmplifier p S *
            routeEHardCorePrimitiveAmplifier p T) * (a S * a T) := by ring
      _ = (if Disjoint S T then routeEHardCoreExclusionNormalizer p else 0) *
          (a S * a T) := by
          rw [routeEHardCoreJointMass_reweight p hp1 S T]
      _ = routeEHardCoreExclusionNormalizer p *
          (if Disjoint S T then a S * a T else 0) := by
          split_ifs <;> ring
  dsimp only
  rw [← hsum, ← hpair]
  exact routeEHardCoreQuadratic_eq_walshSpectrum p
    (fun i => by linarith [hp i]) f

/-- Closed finite-prime version of the primitive-pair spectral bridge. -/
theorem routeEHardCorePrimePrimitiveQuadratic_eq_walshSpectrum
    (P : Finset Nat.Primes)
    (a : Finset {p : Nat.Primes // p ∈ P} → ℝ) :
    let v : {p : Nat.Primes // p ∈ P} → ℝ := fun i => ((i.1 : ℕ) : ℝ)
    let q : {p : Nat.Primes // p ∈ P} → ℝ := fun i => 1 / (v i + 1)
    routeEHardCoreExclusionNormalizer v *
      (∑ S : Finset {p : Nat.Primes // p ∈ P},
        ∑ T : Finset {p : Nat.Primes // p ∈ P},
          if Disjoint S T then a S * a T else 0) =
      ∑ K : Finset {p : Nat.Primes // p ∈ P},
        (∏ i ∈ K, -(1 / v i)) *
          (biasedWalshCoefficient q
            (fun S => routeEHardCorePrimitiveAmplifier v S * a S) K) ^ 2 := by
  classical
  exact routeEHardCorePrimitiveQuadratic_eq_walshSpectrum
    (p := fun i : {p : Nat.Primes // p ∈ P} => ((i.1 : ℕ) : ℝ))
    (fun i => by exact_mod_cast i.1.2.one_lt) a

end
end RHTower
