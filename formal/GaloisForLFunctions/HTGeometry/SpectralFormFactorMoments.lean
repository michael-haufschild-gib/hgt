import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

/-!
# Exact spectral-form-factor moments and their exponential limit

For a uniform weight vector the replica permutation floor is a pure combinatorial constant: the
sum of squared multinomial coefficients over multiplicity vectors of fixed total, divided by the
dimension raised to the replica order.  A maximally projective spectrum therefore has every
long-time moment of its normalized spectral form factor equal to that constant.

The constant is squeezed between the falling-factorial fraction times the factorial and the
factorial itself, because the total multinomial mass is the number of words and each multinomial is
at most the factorial, while the squarefree multiplicity vectors alone already contribute the
falling factorial.  Hence every moment converges to the factorial, the moment sequence of the
unit-mean exponential law.
-/

open Filter Finset Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Combinatorics

/-- The number of ordered pairs of length-`m` words over `D` letters with equal letter
histogram. -/
def replicaPairCount (D m : ℕ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin D)).piAntidiag m, (Nat.multinomial Finset.univ p : ℝ) ^ (2 : ℕ)

/-- The exact long-time moment constant of the normalized spectral form factor. -/
def sffMoment (D m : ℕ) : ℝ := replicaPairCount D m / (D : ℝ) ^ m

private theorem multinomial_le_factorial {α : Type*} (s : Finset α) (f : α → ℕ) :
    Nat.multinomial s f ≤ Nat.factorial (∑ i ∈ s, f i) := by
  refine Nat.le_of_dvd (Nat.factorial_pos _) ⟨∏ i ∈ s, Nat.factorial (f i), ?_⟩
  rw [← Nat.multinomial_spec s f]
  ring

private theorem sum_multinomial_piAntidiag (D m : ℕ) :
    ∑ p ∈ (Finset.univ : Finset (Fin D)).piAntidiag m,
      (Nat.multinomial Finset.univ p : ℝ) = (D : ℝ) ^ m := by
  have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin D)) (fun _ => (1 : ℝ)) m
  simp at h
  simpa using h.symm

/-- The squared multinomial mass is at most the factorial times the word count. -/
theorem replicaPairCount_le (D m : ℕ) :
    replicaPairCount D m ≤ (Nat.factorial m : ℝ) * (D : ℝ) ^ m := by
  rw [replicaPairCount, ← sum_multinomial_piAntidiag D m, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hsum : ∑ i : Fin D, p i = m := (Finset.mem_piAntidiag.mp hp).1
  have hle : (Nat.multinomial Finset.univ p : ℝ) ≤ (Nat.factorial m : ℝ) := by
    have := multinomial_le_factorial (Finset.univ : Finset (Fin D)) p
    rw [hsum] at this
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ (Nat.multinomial Finset.univ p : ℝ) := Nat.cast_nonneg _
  nlinarith [hle, hnn]

/-- The multiplicity vector of a subset has multinomial coefficient the factorial of its
cardinality. -/
theorem multinomial_indicator {D : ℕ} (S : Finset (Fin D)) :
    Nat.multinomial Finset.univ (fun i => if i ∈ S then 1 else 0) =
      Nat.factorial S.card := by
  classical
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin D))
    (fun i => if i ∈ S then 1 else 0)
  have hprod : (∏ i : Fin D, Nat.factorial (if i ∈ S then 1 else 0)) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases h : i ∈ S <;> simp [h]
  have hsum : (∑ i : Fin D, (if i ∈ S then 1 else 0 : ℕ)) = S.card := by
    simp
  rw [hprod, one_mul, hsum] at hspec
  exact hspec

/-- The squarefree multiplicity vectors alone contribute the falling factorial. -/
theorem le_replicaPairCount (D m : ℕ) :
    (D.choose m : ℝ) * (Nat.factorial m : ℝ) ^ (2 : ℕ) ≤ replicaPairCount D m := by
  classical
  set ind : Finset (Fin D) → (Fin D → ℕ) := fun S i => if i ∈ S then 1 else 0 with hind
  have hinj : ∀ S ∈ (Finset.univ : Finset (Fin D)).powersetCard m,
      ∀ S' ∈ (Finset.univ : Finset (Fin D)).powersetCard m, ind S = ind S' → S = S' := by
    intro S _ S' _ h
    ext i
    have hi := congrFun h i
    rw [hind] at hi
    by_cases hS : i ∈ S <;> by_cases hS' : i ∈ S' <;> simp [hS, hS'] at hi ⊢
  have hmem : ∀ S ∈ (Finset.univ : Finset (Fin D)).powersetCard m,
      ind S ∈ (Finset.univ : Finset (Fin D)).piAntidiag m := by
    intro S hS
    refine Finset.mem_piAntidiag.mpr ⟨?_, fun i _ => Finset.mem_univ i⟩
    have hcard : S.card = m := (Finset.mem_powersetCard.mp hS).2
    rw [hind]
    show (∑ i : Fin D, (if i ∈ S then 1 else 0 : ℕ)) = m
    rw [← hcard]
    simp
  have hsub : ((Finset.univ : Finset (Fin D)).powersetCard m).image ind ⊆
      (Finset.univ : Finset (Fin D)).piAntidiag m := by
    intro p hp
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hp
    exact hmem S hS
  have hcount : ((Finset.univ : Finset (Fin D)).powersetCard m).card = D.choose m := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  calc (D.choose m : ℝ) * (Nat.factorial m : ℝ) ^ (2 : ℕ)
      = ∑ _S ∈ (Finset.univ : Finset (Fin D)).powersetCard m, (Nat.factorial m : ℝ) ^ (2 : ℕ) := by
        rw [Finset.sum_const, hcount, nsmul_eq_mul]
    _ = ∑ S ∈ (Finset.univ : Finset (Fin D)).powersetCard m,
          (Nat.multinomial Finset.univ (ind S) : ℝ) ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [hind, multinomial_indicator S, (Finset.mem_powersetCard.mp hS).2]
    _ = ∑ p ∈ ((Finset.univ : Finset (Fin D)).powersetCard m).image ind,
          (Nat.multinomial Finset.univ p : ℝ) ^ (2 : ℕ) := by
        rw [Finset.sum_image hinj]
    _ ≤ replicaPairCount D m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

theorem replicaPairCount_nonneg (D m : ℕ) : 0 ≤ replicaPairCount D m := by
  refine Finset.sum_nonneg fun p _ => by positivity

theorem sffMoment_le' (D m : ℕ) : sffMoment D m ≤ (Nat.factorial m : ℝ) := by
  by_cases hD : (D : ℝ) ^ m = 0
  · rw [sffMoment, hD, div_zero]
    positivity
  · have hpos : (0 : ℝ) < (D : ℝ) ^ m :=
      lt_of_le_of_ne (by positivity) (Ne.symm hD)
    rw [sffMoment, div_le_iff₀ hpos]
    exact replicaPairCount_le D m

theorem sffMoment_le (D m : ℕ) (hD : 0 < D) : sffMoment D m ≤ (Nat.factorial m : ℝ) := by
  have hD0 : (0 : ℝ) < (D : ℝ) ^ m := by
    have : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    positivity
  rw [sffMoment, div_le_iff₀ hD0]
  exact replicaPairCount_le D m

theorem le_sffMoment (D m : ℕ) (hD : 0 < D) :
    (Nat.factorial m : ℝ) * ((D.descFactorial m : ℝ) / (D : ℝ) ^ m) ≤ sffMoment D m := by
  have hD0 : (0 : ℝ) < (D : ℝ) ^ m := by
    have : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    positivity
  rw [sffMoment, le_div_iff₀ hD0]
  have hfac : (Nat.factorial m : ℝ) * ((D.descFactorial m : ℝ) / (D : ℝ) ^ m) * (D : ℝ) ^ m =
      (Nat.factorial m : ℝ) * (D.descFactorial m : ℝ) := by
    field_simp
  rw [hfac]
  have hd : (D.descFactorial m : ℝ) = (Nat.factorial m : ℝ) * (D.choose m : ℝ) := by
    have := Nat.descFactorial_eq_factorial_mul_choose D m
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  rw [hd]
  have h := le_replicaPairCount D m
  nlinarith [h]

end Combinatorics

section Limit

/-- The falling factorial dominates the shifted power. -/
private theorem pow_sub_le_descFactorial (D m : ℕ) : (D - m) ^ m ≤ D.descFactorial m := by
  rw [Nat.descFactorial_eq_prod_range]
  calc (D - m) ^ m = ∏ _i ∈ Finset.range m, (D - m) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range m, (D - i) := by
        refine Finset.prod_le_prod' fun i hi => ?_
        have := Finset.mem_range.mp hi
        omega

private theorem tendsto_descFactorial_div_pow (m : ℕ) :
    Tendsto (fun D : ℕ => (D.descFactorial m : ℝ) / (D : ℝ) ^ m) atTop (𝓝 1) := by
  have hlow : Tendsto (fun D : ℕ => (1 - (m : ℝ) / (D : ℝ)) ^ m) atTop (𝓝 1) := by
    have hdiv : Tendsto (fun D : ℕ => (m : ℝ) / (D : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (m : ℝ))).div_atTop
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hone : Tendsto (fun D : ℕ => 1 - (m : ℝ) / (D : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hdiv
    simpa using hone.pow m
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (m + 1)] with D hD
    have hD0 : (0 : ℝ) < (D : ℝ) := by
      have : 0 < D := by omega
      exact_mod_cast this
    have hDm : m ≤ D := by omega
    have hcast : ((D - m : ℕ) : ℝ) = (D : ℝ) - (m : ℝ) := by
      exact_mod_cast Nat.cast_sub (R := ℝ) hDm
    have hkey : ((D - m : ℕ) : ℝ) ^ m ≤ (D.descFactorial m : ℝ) := by
      exact_mod_cast pow_sub_le_descFactorial D m
    rw [hcast] at hkey
    have hpow : (0 : ℝ) < (D : ℝ) ^ m := by positivity
    rw [le_div_iff₀ hpow]
    have hexp : (1 - (m : ℝ) / (D : ℝ)) ^ m * (D : ℝ) ^ m =
        ((D : ℝ) - (m : ℝ)) ^ m := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [hexp]
    exact hkey
  · filter_upwards [eventually_gt_atTop 0] with D hD
    have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have hpow : (0 : ℝ) < (D : ℝ) ^ m := by positivity
    rw [div_le_one hpow]
    have := Nat.descFactorial_le_pow D m
    exact_mod_cast this

/-- **The moment constants converge to the factorials.**  Every long-time moment of the normalized
spectral form factor converges, as the dimension grows, to the corresponding moment of the unit-mean
exponential law. -/
theorem tendsto_sffMoment (m : ℕ) :
    Tendsto (fun D : ℕ => sffMoment D m) atTop (𝓝 (Nat.factorial m : ℝ)) := by
  have hlow : Tendsto
      (fun D : ℕ => (Nat.factorial m : ℝ) * ((D.descFactorial m : ℝ) / (D : ℝ) ^ m))
      atTop (𝓝 (Nat.factorial m : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (Nat.factorial m : ℝ))).mul
      (tendsto_descFactorial_div_pow m)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with D hD
    exact le_sffMoment D m hD
  · filter_upwards [eventually_gt_atTop 0] with D hD
    exact sffMoment_le D m hD

end Limit

section UniformWeight

/-- The uniform permutation floor is the moment constant divided by the dimension raised to the
replica order. -/
theorem fidelityReplicaPermutationFloor_uniform (D m : ℕ) :
    fidelityReplicaPermutationFloor (fun _ : Fin D => ((D : ℝ))⁻¹) m =
      replicaPairCount D m / (D : ℝ) ^ (2 * m) := by
  classical
  rw [fidelityReplicaPermutationFloor, replicaPairCount, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hsum : ∑ i : Fin D, p i = m := (Finset.mem_piAntidiag.mp hp).1
  have hprod : (∏ i : Fin D, ((D : ℝ))⁻¹ ^ p i) = ((D : ℝ))⁻¹ ^ m := by
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  rw [fidelityReplicaMultiplicityWeight, hprod, two_mul, pow_add, inv_pow, div_eq_mul_inv,
    mul_inv]
  ring

/-- The moment constant is the uniform permutation floor scaled by the dimension raised to the
replica order. -/
theorem sffMoment_eq (D m : ℕ) (hD : 0 < D) :
    sffMoment D m =
      (D : ℝ) ^ m * fidelityReplicaPermutationFloor (fun _ : Fin D => ((D : ℝ))⁻¹) m := by
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [fidelityReplicaPermutationFloor_uniform, sffMoment, two_mul, pow_add]
  field_simp

/-- The normalized spectral form factor of a finite real spectrum. -/
def normalizedSpectralFormFactor {D : ℕ} (energy : Fin D → ℝ) (t : ℝ) : ℂ :=
  (D : ℂ) * finiteSpectralSurvivalFidelity (fun _ : Fin D => ((D : ℝ))⁻¹) energy t

/-- Symmetric long-time mean of the `m`th power of the normalized spectral form factor. -/
def normalizedSpectralFormFactorMean {D : ℕ} (energy : Fin D → ℝ) (m : ℕ) (T : ℝ) : ℂ :=
  (2 * T : ℂ)⁻¹ * ∫ t : ℝ in -T..T, normalizedSpectralFormFactor energy t ^ m

theorem normalizedSpectralFormFactorMean_eq {D : ℕ} (energy : Fin D → ℝ) (m : ℕ) (T : ℝ) :
    normalizedSpectralFormFactorMean energy m T =
      (D : ℂ) ^ m *
        finiteSpectralSurvivalFidelityMean (fun _ : Fin D => ((D : ℝ))⁻¹) energy m T := by
  rw [normalizedSpectralFormFactorMean, finiteSpectralSurvivalFidelityMean]
  have hpow : ∀ t : ℝ, normalizedSpectralFormFactor energy t ^ m =
      (D : ℂ) ^ m *
        finiteSpectralSurvivalFidelity (fun _ : Fin D => ((D : ℝ))⁻¹) energy t ^ m := by
    intro t
    rw [normalizedSpectralFormFactor, mul_pow]
  simp_rw [hpow]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- **Exact spectral-form-factor moments.**  For a maximally projective spectrum every long-time
moment of the normalized spectral form factor is the purely combinatorial moment constant, with no
dependence on the spectrum beyond maximal projective rank. -/
theorem normalizedSpectralFormFactorMean_tendsto {D : ℕ} (hD : 0 < D) (energy : Fin D → ℝ)
    (hmax : MaximallyProjectiveEnergy energy) (m : ℕ) :
    Tendsto (normalizedSpectralFormFactorMean energy m) atTop
      (𝓝 ((sffMoment D m : ℝ) : ℂ)) := by
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hweight : ∀ _i : Fin D, 0 < ((D : ℝ))⁻¹ := fun _ => by positivity
  have hfloor : fidelityReplicaCollisionMass (fun _ : Fin D => ((D : ℝ))⁻¹) energy m =
      fidelityReplicaPermutationFloor (fun _ : Fin D => ((D : ℝ))⁻¹) m :=
    (all_fidelityReplicaCollisionMass_eq_floor_iff hweight energy).2 hmax m
  have hmean := finiteSpectralSurvivalFidelityMean_tendsto_collisionMass
    (fun _ : Fin D => ((D : ℝ))⁻¹) energy m
  rw [hfloor] at hmean
  have hlim := (tendsto_const_nhds (x := ((D : ℂ) ^ m))).mul hmean
  have heq : ((D : ℂ) ^ m) *
      ((fidelityReplicaPermutationFloor (fun _ : Fin D => ((D : ℝ))⁻¹) m : ℝ) : ℂ) =
      ((sffMoment D m : ℝ) : ℂ) := by
    rw [sffMoment_eq D m hD]
    push_cast
    ring
  rw [heq] at hlim
  refine hlim.congr fun T => ?_
  rw [normalizedSpectralFormFactorMean_eq]

end UniformWeight

end

end GaloisForLFunctions.HTGeometry
