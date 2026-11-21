import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoherentShiftReadings

/-!
# Saturation of prime annihilation readings

Reciprocal prime masses and equality in Cauchy–Schwarz at the primes
determine the coherent amplitude on every composite in any multiplicative
operator representation.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology
open _root_.RHTower.PrimeCoShift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem sqrt_size_pos (n : ℕ+) : 0 < Real.sqrt (n : ℕ) :=
  Real.sqrt_pos.mpr (Nat.cast_pos.mpr n.pos)

private theorem singleton_size (χ : ℕ+ →* Circle) (n : ℕ+) :
    ‖singletonAmplitude χ n‖^2 = 1 / ((n : ℕ) : ℝ) := by
  change ‖(χ n : ℂ) / (Real.sqrt (n : ℕ) : ℂ)‖^2 = _
  rw [norm_div, div_pow, Circle.norm_coe, one_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sqrt_size_pos n), Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Equality in the unit-vector Cauchy bound gives the measured eigenvalue itself. -/
private theorem measured_eigenvector (v y : E) (hv : ‖v‖ = 1)
    (h : ‖inner ℂ v y‖ = ‖y‖) : y = inner ℂ v y • v := by
  have hv' : v ≠ 0 := by
    intro he
    rw [he, norm_zero] at hv
    exact zero_ne_one hv
  have hcs : ‖inner ℂ v y‖ = ‖v‖ * ‖y‖ := by rw [hv, one_mul, h]
  have hor : v = 0 ∨ y = (inner ℂ v y / inner ℂ v v) • v :=
    ((norm_inner_eq_norm_tfae ℂ v y).out 0 1).mp hcs
  have hunit : inner ℂ v v = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hv]
    simp
  simpa only [hunit, div_one] using hor.resolve_left hv'

private theorem extend_prime_equations (T : ℕ+ →* (E →L[ℂ] E)) (v : E) (χ : ℕ+ →* Circle)
    (hp : ∀ p : Nat.Primes, T (p : ℕ+) v = singletonAmplitude χ (p : ℕ+) • v) (n : ℕ+) :
    T n v = singletonAmplitude χ n • v := by
  let S : Submonoid ℕ+ := {
    carrier := {a | T a v = coherentFactor χ 1 a • v}
    one_mem' := by simp [coherentFactor, energy]
    mul_mem' := by
      intro a b ha hb
      change T a v = _ at ha
      change T b v = _ at hb
      change T (a*b) v = _ • v
      rw [map_mul, mul_apply_eq_comp, hb, map_smul, ha, smul_smul, coherentFactor_mul χ 1 a b,
        mul_comm (coherentFactor χ 1 b)]
  }
  have hall : n ∈ S := by
    rw [← n.prod_factorMultiset]
    apply S.multiset_prod_mem
    intro a ha
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp ha
    change T (p : ℕ+) v = coherentFactor χ 1 (p : ℕ+) • v
    rw [coherentFactor_one_temperature, hp]
  change T n v = coherentFactor χ 1 n • v at hall
  rwa [coherentFactor_one_temperature] at hall

/-- Reciprocal range masses and maximal coherence at primes are equivalent to a
unique character of all shell labels on the observed vector. -/
theorem prime_saturation_iff_unique_character (T : ℕ+ →* (E →L[ℂ] E))
    (Ω : {v : E // ‖v‖ = 1}) :
    (∀ p : Nat.Primes, ‖T (p : ℕ+) Ω.val‖^2 = 1 / ((p : ℕ) : ℝ) ∧
      ‖inner ℂ Ω.val (T (p : ℕ+) Ω.val)‖ = ‖T (p : ℕ+) Ω.val‖) ↔
    ∃! χ : ℕ+ →* Circle, ∀ n, T n Ω.val = singletonAmplitude χ n • Ω.val := by
  have hread (z : ℂ) : inner ℂ Ω.val (z • Ω.val) = z := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, Ω.property]
    simp
  constructor
  · intro h
    let c (p : Nat.Primes) := inner ℂ Ω.val (T (p : ℕ+) Ω.val)
    let ω (p : Nat.Primes) : Circle := ⟨c p * (Real.sqrt (p : ℕ) : ℂ),
      mem_sphere_zero_iff_norm.mpr (by
        apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
        change ‖c p * (Real.sqrt (p : ℕ) : ℂ)‖^2 = _
        rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _),
          show ‖c p‖ = _ from (h p).2, (h p).1, one_pow,
          one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr p.property.ne_zero)])⟩
    obtain ⟨χ, hχ⟩ := prime_phase_coordinates.surjective ω
    have he (p : Nat.Primes) : singletonAmplitude χ (p : ℕ+) = c p := by
      change (χ (p : ℕ+) : ℂ) / (Real.sqrt (p : ℕ) : ℂ) = c p
      rw [show χ (p : ℕ+) = ω p from congrFun hχ p]
      exact mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (sqrt_size_pos (p : ℕ+)).ne')
    have hprime (p : Nat.Primes) : T (p : ℕ+) Ω.val = singletonAmplitude χ (p : ℕ+) • Ω.val := by
      rw [he]
      exact measured_eigenvector _ _ Ω.property (h p).2
    refine ⟨χ, extend_prime_equations T Ω.val χ hprime, fun ψ hψ => ?_⟩
    apply prime_phase_coordinates.injective
    funext p
    apply Circle.ext
    have hsame := (congrArg (inner ℂ Ω.val) (hψ (p : ℕ+)).symm).trans
      (congrArg (inner ℂ Ω.val) (hprime p))
    simp only [hread] at hsame
    exact (div_left_inj' (Complex.ofReal_ne_zero.mpr (sqrt_size_pos (p : ℕ+)).ne')).mp hsame
  · rintro ⟨χ, h, _⟩ p
    rw [h, hread, norm_smul, Ω.property, mul_one, singleton_size]
    exact ⟨rfl, rfl⟩

/-- Complex readings of the annihilators at 2 and 3 determine both the real
critical exponent and the Hamiltonian time. -/
theorem two_coShift_readings_iff (t : ℝ) (s : ℂ) :
    (∀ n ∈ ({2,3} : Finset ℕ+), Tendsto
      (fun β => coherentReading (clockPhase t) β (primeCoShift n)) atPartitionPole (𝓝 (heat s n))) ↔
      s = timeParameter t := by
  have hlim (n : ℕ+) : Tendsto (fun β => coherentReading (clockPhase t) β (primeCoShift n))
      atPartitionPole (𝓝 (heat (timeParameter t) n)) := by
    have h := coShift_ratio_boundary (clockPhase t) 1 n
    have h1 (β : TraceTemperature) : coherentReading (clockPhase t) β (primeCoShift 1) = 1 := by
      rw [coherentReading_coShift (clockPhase t) β 1]
      simp [coherentFactor, energy]
    simpa only [h1, div_one, clock_refinement_eq_heat, heatRefinement,
      show heat (timeParameter t) 1 = 1 by simp [heat, energy]] using h
  constructor
  · intro h
    exact two_prime_heat_injective (Prod.ext
      (tendsto_nhds_unique (h 2 (by simp)) (hlim 2))
      (tendsto_nhds_unique (h 3 (by simp)) (hlim 3)))
  · rintro rfl n _
    exact hlim n

#print axioms prime_saturation_iff_unique_character
#print axioms two_coShift_readings_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
