import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.ThermalDuality
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.ZetaDivisor
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CompositionRigidity

/-!
# Probability conservation as a high-temperature composition law

A finite nonzero overlap of complementary cutoff heats detects the same
dual temperatures as the divisor channels on prime shells 2 and 3. The
zero set of the physical joint partition then gives a thermal criterion
for the Riemann hypothesis.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

open Filter Set
open scoped Topology ComplexConjugate

def reading (t : ExceptionalTime) (j : ℕ) (a : ℝ) (s : ℂ) (v : ℝ) :=
  (v:ℂ)^s*(cutoffHeat t j a v:ℂ)

def overlap (t : ExceptionalTime) (j : ℕ) (a : ℝ) (w s : ℂ) (v : ℝ) :=
  conj (reading t j a w v)*reading t j a s (((tailRadix t j).val:ℝ)*v)

theorem thermal_limit_iff (t : ExceptionalTime) (j : ℕ) (a : ℝ) (w s L : ℂ) :
    (L ≠ 0 ∧ Tendsto (overlap t j a w s) (𝓝[>] 0) (𝓝 L)) ↔
      w = 1-conj s ∧ L = ((tailRadix t j).val:ℂ)^s := by
  let C := clockRadix t j
  have he : overlap t j a w s =ᶠ[𝓝[>] 0] cross C a w s := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv' : 0 < v := hv
    have hcv : 0 < (C.val:ℝ)*v := mul_pos (by exact_mod_cast zero_lt_one.trans C.property) hv'
    rw [overlap,cross,amplitude_cpow C a w ⟨v,hv'⟩,amplitude_cpow C a s ⟨_,hcv⟩,reading,reading,
      cutoffHeat_eq,cutoffHeat_eq]
  rw [tendsto_congr' he]
  exact cross_limit_iff C a w s L

/-- The continuum high-temperature measurement and the two discrete prime tests are equivalent. -/
theorem thermal_iff_two_primes (t : ExceptionalTime) (j : ℕ) (a : ℝ) (w s : ℂ) :
    (∃ L : ℂ, L ≠ 0 ∧ Tendsto (overlap t j a w s) (𝓝[>] 0) (𝓝 L)) ↔
      ∀ n ∈ ({2,3} : Finset ℕ+), ∑ d ∈ (n:ℕ).divisors, conj (channel w n d)*channel s n d = 1 := by
  rw [dual_on_two_primes_iff]
  constructor
  · rintro ⟨L,hL⟩
    exact ((thermal_limit_iff t j a w s L).mp hL).1
  · intro hw
    exact ⟨_,(thermal_limit_iff t j a w s _).mpr ⟨hw,rfl⟩⟩

/-- A nonzero finite thermal self-overlap characterizes isometry on the full prime gas. -/
theorem thermal_iff_isometry (t : ExceptionalTime) (j : ℕ) (a : ℝ) (s : ℂ) :
    (∃ L : ℂ, L ≠ 0 ∧ Tendsto (overlap t j a s s) (𝓝[>] 0) (𝓝 L)) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [thermal_iff_two_primes,dual_on_two_primes_iff,self_dual_iff,split_isometric_iff]

/-- Every open-strip zero of the joint partition has finite nonzero thermal self-overlap exactly under RH. -/
theorem rh_iff_thermal_at_joint_zeros (t : ExceptionalTime) (j : ℕ) (a : ℝ) :
    RiemannHypothesis ↔ ∀ s : {z : ℂ // 0 < z.re ∧ z.re < 1}, continued s.val = 0 →
      ∃ L : ℂ, L ≠ 0 ∧ Tendsto (overlap t j a s.val s.val) (𝓝[>] 0) (𝓝 L) := by
  simp only [thermal_iff_isometry,split_isometric_iff]
  constructor
  · intro rh s hs
    have hz := (positive_zero_iff ⟨s.val,s.property.1⟩).mp hs
    apply rh s.val hz
    · rintro ⟨n,hn⟩
      have hp := s.property.1
      rw [hn] at hp
      norm_num [Complex.mul_re] at hp
      linarith only [hp,Nat.cast_nonneg (α := ℝ) n]
    · intro h
      have hp := s.property.2
      rw [h,Complex.one_re] at hp
      exact hp.false
  · intro hall
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro s hs h₁ hz
    have h₀ : 0 < s.re := by linarith only [hs]
    exact hs.ne' (hall ⟨s,h₀,h₁⟩ ((positive_zero_iff ⟨s,h₀⟩).mpr hz))

#print axioms thermal_limit_iff
#print axioms thermal_iff_two_primes
#print axioms thermal_iff_isometry
#print axioms rh_iff_thermal_at_joint_zeros

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
