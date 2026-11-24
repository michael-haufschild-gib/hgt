import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.PrimeReturns
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.CyclicPhase
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.Realization

/-! # A phase measurement of pure prime occupations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open MeasureTheory Filter Topology
open _root_.RHTower.PrimeCoShift
open scoped ENNReal

/-- All finite-order phases, a measurable countable union of closed return sets. -/
def torsionPhases : Set Circle := ⋃ k : ℕ+, {z : Circle | (z:ℂ)^k.val = 1}

theorem measurableSet_torsionPhases : MeasurableSet torsionPhases := by
  have hc (k : ℕ+) : IsClosed {z : Circle | (z:ℂ)^k.val = 1} :=
    isClosed_eq (continuous_subtype_val.pow _) continuous_const
  exact MeasurableSet.iUnion fun k => (hc k).measurableSet

theorem prime_clock_torsion_iff (r : ℕ+) (p : Nat.Primes) (j : ℕ) (n : ℕ+) :
    occupationPhase (cyclicTime r p j) n ∈ torsionPhases ↔ n ∈ Set.range (primeRayLabel p) := by
  rw [torsionPhases,Set.mem_iUnion]
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨h,he,_⟩ := (prime_clock_return_iff r p j n k.pos).mp hk
    exact ⟨h,he.symm⟩
  · rintro ⟨h,rfl⟩
    let D : ℕ+ := ⟨clockDenominator r j,clockDenominator_pos r j⟩
    exact ⟨D,(prime_clock_return_iff r p j _ D.pos).mpr ⟨h,rfl,dvd_mul_right _ _⟩⟩

private theorem phaseLaw_apply (v : MissingWave) (t : ℝ) {s : Set Circle} (hs : MeasurableSet s) :
    (occupationPhaseLaw v t : Measure Circle) s =
      ∑' n, s.indicator (fun _ => ENNReal.ofReal (occupationProbability v n)) (occupationPhase t n) := by
  change (Measure.sum _) s = _
  rw [Measure.sum_apply _ hs]
  apply tsum_congr
  intro n
  rw [Measure.smul_apply,Measure.dirac_apply' _ hs]
  by_cases h : occupationPhase t n ∈ s <;> simp [Set.indicator,h,smul_eq_mul]

/-- The probability of observing a torsion phase is exactly the total occupation probability on the prime ray. -/
theorem torsion_mass_eq_prime_ray (r : ℕ+) (p : Nat.Primes) (j : ℕ) (v : MissingWave) :
    (occupationPhaseLaw v (cyclicTime r p j) : Measure Circle) torsionPhases =
      ∑' h : ℕ, ENNReal.ofReal (occupationProbability v (primeRayLabel p h)) := by
  rw [phaseLaw_apply v _ measurableSet_torsionPhases]
  let w (n : ℕ+) := torsionPhases.indicator (fun _ => ENNReal.ofReal (occupationProbability v n))
    (occupationPhase (cyclicTime r p j) n)
  have hz (n : ℕ+) (hn : n ∉ Set.range (primeRayLabel p)) : w n = 0 := by
    simp [w,Set.indicator,prime_clock_torsion_iff,hn]
  change ∑' n, w n = _
  have hsupport : Function.support w ⊆ Set.range (primeRayLabel p) := by
    intro n hn
    by_contra h
    exact hn (hz n h)
  rw [← (primeRayLabel_injective p).tsum_eq hsupport]
  apply tsum_congr
  intro h
  simp [w,Set.indicator,prime_clock_torsion_iff]

theorem prime_ray_carried_by_torsion (r : ℕ+) (p : Nat.Primes) (j : ℕ) (v : MissingWave)
    (hv : onPrimeRay p v.val) : (occupationPhaseLaw v (cyclicTime r p j) : Measure Circle) torsionPhasesᶜ = 0 := by
  rw [phaseLaw_apply v _ measurableSet_torsionPhases.compl]
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  by_cases h : n ∈ Set.range (primeRayLabel p)
  · simp [Set.indicator,(prime_clock_torsion_iff r p j n).mpr h]
  · simp [Set.indicator,(raySupportedLaw_iff p v).mpr hv n h]

/-- Inserting a different elementary species removes every finite-order phase, for any initial state. -/
theorem other_prime_avoids_torsion (r : ℕ+) (p q : Nat.Primes) (hpq : p ≠ q) (j : ℕ) (v : MissingWave) :
    (occupationPhaseLaw (insertedWave (primePNat q) v) (cyclicTime r p j) : Measure Circle) torsionPhases = 0 := by
  rw [torsion_mass_eq_prime_ray]
  apply ENNReal.tsum_eq_zero.mpr
  intro h
  have hn : primeRayLabel p h ∉ Set.range (fun x : ℕ+ => primePNat q*x) := by
    rintro ⟨x,hx⟩
    have hd : q.val ∣ p.val^h := ⟨x.val,(congrArg PNat.val hx).symm⟩
    exact hpq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.property p.property).mp (q.property.dvd_of_dvd_pow hd)).symm)
  rw [insertedWave_probability,insertedMass_off _ _ _ hn,ENNReal.ofReal_zero]

theorem cyclic_law_carried_by_torsion (r : ℕ+) {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) :
    (cyclicPhaseLaw r δ h₀ h₁ : Measure Circle) torsionPhasesᶜ = 0 := by
  have ht (k : ℕ) : clockRoot r^k ∈ torsionPhases := by
    apply Set.mem_iUnion.mpr
    refine ⟨r,?_⟩
    change ((clockRoot r^k:Circle):ℂ)^r.val = 1
    rw [Circle.coe_pow,← pow_mul,Nat.mul_comm,pow_mul,(clockRoot_primitive r).pow_eq_one,one_pow]
  change (∑ k ∈ Finset.range r.val, ENNReal.ofReal (rootShare r δ+(if k = 0 then δ else 0)) •
    Measure.dirac (clockRoot r^k) : Measure Circle) torsionPhasesᶜ = 0
  rw [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Measure.smul_apply,Measure.dirac_apply' _ measurableSet_torsionPhases.compl]
  simp [Set.indicator,ht]

#print axioms measurableSet_torsionPhases
#print axioms prime_clock_torsion_iff
#print axioms torsion_mass_eq_prime_ray
#print axioms prime_ray_carried_by_torsion
#print axioms other_prime_avoids_torsion
#print axioms cyclic_law_carried_by_torsion

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
