import GaloisForLFunctions.HTGeometry.HilbertExteriorPairFactorization
import GaloisForLFunctions.RHTower.SoninCalkinNormBound
import GaloisForLFunctions.RHTower.SoninTwoParticlePrimeCoherence
import GaloisForLFunctions.RHTower.XiPrimeSeamPairAsymptotics

/-!
# The ordered Sonin prime-pair seam is one exterior tensor, and it is Calkin-faithful

Let `C_p = -p^{-1/2} L_p` be the positive Euler-normalized even Sonin corner and let `a_p` be
complex prime potentials.  For a finite prime set `F` the two one-particle sections are

`A_F(a) = ∑_{p∈F} a_p C_p`,  `B_F = ∑_{p∈F} C_p`,

and the ordered two-particle difference section factors exactly as

`W_F(a) = ∑_{p,q∈F} (a_p − a_q)(C_p ⊗ C_q) = A_F(a) ⊗ B_F − B_F ⊗ A_F(a)`.

Combining this with the tensor-square Calkin lower bound gives the seam estimate

`√(∑_{p,q∈F} |a_p − a_q|²/(pq)) ≤ ‖A_F(a) ⊗ B_F − B_F ⊗ A_F(a) − K‖`

for every compact `K` on the completed even Sonin tensor square: the complete pair coboundary is a
decomposable rank-two exterior tensor whose Calkin norm still sees the whole reciprocal-prime pair
energy.
-/

namespace RHTower

open Filter Topology UniformSpace
open scoped BigOperators TensorProduct

set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

noncomputable section

/-- `(1)`: the `a`-weighted one-particle even Sonin section `A_F(a) = ∑_{p∈F} a_p C_p`. -/
def evenSoninWeightedSection (t : ℝ) (u : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    evenSubspace →L[ℂ] evenSubspace :=
  ∑ p ∈ s, u p • evenPositiveEulerSoninCorner t (p : ℝ) (one_lt_prime_real p)

/-- `(1)`: the universal one-particle even Sonin section `B_F = ∑_{p∈F} C_p`. -/
def evenSoninUniversalSection (t : ℝ) (s : Finset Nat.Primes) :
    evenSubspace →L[ℂ] evenSubspace :=
  ∑ p ∈ s, evenPositiveEulerSoninCorner t (p : ℝ) (one_lt_prime_real p)

/-- **`(3)`: the ordered Sonin prime-pair seam is one exterior tensor.**  The complete pair
coboundary is `A_F(a) ⊗ B_F − B_F ⊗ A_F(a)`; the diagonal coefficients vanish automatically. -/
theorem soninPrimePairSection_eq_exterior (t : ℝ) (u : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    soninPrimePairSection t u s =
      (TensorProduct.mapL (evenSoninWeightedSection t u s) (evenSoninUniversalSection t s)
        - TensorProduct.mapL (evenSoninUniversalSection t s)
            (evenSoninWeightedSection t u s)).completion := by
  rw [soninPrimePairSection]
  congr 1
  rw [evenSoninWeightedSection, evenSoninUniversalSection,
    ← HTGeometry.sum_sub_smul_mapL s u
      (fun p => evenPositiveEulerSoninCorner t (p : ℝ) (one_lt_prime_real p))]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [TensorProduct.mapL_smul_left]

/-- **`(4)`--`(5)`: the exterior seam is Calkin-faithful.**  For every compact operator `K` on the
completed even Sonin tensor square, the Calkin norm of the decomposable exterior tensor dominates
the square root of the reciprocal-prime pair energy. -/
theorem sqrt_primePairDifferenceEnergy_le_norm_exterior_sub_compact
    (t : ℝ) (ht : 0 < t) (u : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (K : Completion (evenSubspace ⊗[ℂ] evenSubspace) →L[ℂ]
      Completion (evenSubspace ⊗[ℂ] evenSubspace)) (hK : IsCompactOperator K) :
    Real.sqrt (primePairDifferenceEnergy u s) ≤
      ‖(TensorProduct.mapL (evenSoninWeightedSection t u s) (evenSoninUniversalSection t s)
          - TensorProduct.mapL (evenSoninUniversalSection t s)
              (evenSoninWeightedSection t u s)).completion - K‖ := by
  rw [← soninPrimePairSection_eq_exterior]
  exact sqrt_primePairDifferenceEnergy_le_norm_soninPrimePairSection_sub_compact t ht u s K hK

/-- **`(8)` endpoint hypothesis form: uniformly Calkin-bounded exterior seams force all-prime
coherence.**  If the decomposable exterior tensors of the two one-particle sections stay a bounded
Calkin distance from the compact operators, the prime potential is constant. -/
theorem sonin_exterior_calkin_bounded_imp_constant (t : ℝ) (ht : 0 < t) (u : Nat.Primes → ℂ)
    (hbdd : ∃ B : ℝ, ∀ s : Finset Nat.Primes,
      ∃ K : Completion (evenSubspace ⊗[ℂ] evenSubspace) →L[ℂ]
        Completion (evenSubspace ⊗[ℂ] evenSubspace),
        IsCompactOperator K ∧
          ‖(TensorProduct.mapL (evenSoninWeightedSection t u s) (evenSoninUniversalSection t s)
              - TensorProduct.mapL (evenSoninUniversalSection t s)
                  (evenSoninWeightedSection t u s)).completion - K‖ ≤ B) :
    ∃ c : ℂ, ∀ p, u p = c := by
  refine sonin_prime_pair_calkin_bounded_imp_constant t ht u ?_
  obtain ⟨B, hB⟩ := hbdd
  refine ⟨B, fun s => ?_⟩
  obtain ⟨K, hK, hle⟩ := hB s
  exact ⟨K, hK, by rwa [soninPrimePairSection_eq_exterior]⟩

/-- `(4)`--`(5)` in essential-norm form: the essential norm of the finite ordered prime pair section
dominates the square root of the reciprocal-prime pair energy. -/
theorem sqrt_primePairDifferenceEnergy_le_essentialNorm_soninPrimePairSection
    (t : ℝ) (ht : 0 < t) (u : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    Real.sqrt (primePairDifferenceEnergy u s) ≤
      essentialNorm (soninPrimePairSection t u s) :=
  le_essentialNorm _ _ fun K hK =>
    sqrt_primePairDifferenceEnergy_le_norm_soninPrimePairSection_sub_compact t ht u s K hK

/-- `(7)`: the Calkin distance `D_F^∧(ρ)` of the canonical Xi seam exterior section. -/
def xiSeamExteriorCalkinDistance (t : ℝ) (rho : ℂ) (s : Finset Nat.Primes) : ℝ :=
  essentialNorm
    (soninPrimePairSection t (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s)

/-- The reciprocal-prime mass of a finite prime set is nonnegative. -/
theorem primeReciprocalMass_nonneg (s : Finset Nat.Primes) : 0 ≤ primeReciprocalMass s := by
  refine Finset.sum_nonneg fun p _ => ?_
  positivity

/-- The normalized canonical pair energy is dominated by the squared normalized Calkin distance of
the exterior seam. -/
theorem primePairDifferenceEnergy_div_mass_le_sq_calkinDistance_div_sqrt_mass
    (t : ℝ) (ht : 0 < t) (rho : ℂ) (s : Finset Nat.Primes) :
    primePairDifferenceEnergy
        (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s /
        primeReciprocalMass s ≤
      (xiSeamExteriorCalkinDistance t rho s / Real.sqrt (primeReciprocalMass s)) ^ (2 : ℕ) := by
  set u : Nat.Primes → ℂ := fun p => orbitwiseNatPrimeSeamCharge (p : ℕ) rho with hu
  have hM : 0 ≤ primeReciprocalMass s := primeReciprocalMass_nonneg s
  have hE0 : 0 ≤ primePairDifferenceEnergy u s := primePairDifferenceEnergy_nonneg u s
  have hsqrt := sqrt_primePairDifferenceEnergy_le_essentialNorm_soninPrimePairSection t ht u s
  have hEsq : primePairDifferenceEnergy u s ≤ xiSeamExteriorCalkinDistance t rho s ^ (2 : ℕ) := by
    have hid := Real.sq_sqrt hE0
    have hnn := Real.sqrt_nonneg (primePairDifferenceEnergy u s)
    have : Real.sqrt (primePairDifferenceEnergy u s) ≤ xiSeamExteriorCalkinDistance t rho s :=
      hsqrt
    nlinarith
  rw [div_pow, Real.sq_sqrt hM]
  rcases eq_or_lt_of_le hM with h0 | hpos
  · rw [← h0, div_zero, div_zero]
  · gcongr

/-- **`(8)`: sub-root Calkin growth of the exterior seam forces the critical-line equation.** -/
theorem re_eq_half_of_xiSeamExteriorCalkinDistance_submass (t : ℝ) (ht : 0 < t) {rho : ℂ}
    (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hsub : Filter.Tendsto
      (fun s : Finset Nat.Primes =>
        xiSeamExteriorCalkinDistance t rho s / Real.sqrt (primeReciprocalMass s))
      Filter.atTop (nhds 0)) :
    rho.re = 1 / 2 := by
  refine re_eq_half_of_orbitwisePrimeSeamPairEnergySubmass hstrip ?_
  have hsq : Filter.Tendsto
      (fun s : Finset Nat.Primes =>
        (xiSeamExteriorCalkinDistance t rho s / Real.sqrt (primeReciprocalMass s)) ^ (2 : ℕ))
      Filter.atTop (nhds 0) := by
    have := hsub.pow 2
    simpa using this
  refine squeeze_zero (fun s => ?_) (fun s => ?_) hsq
  · exact div_nonneg (primePairDifferenceEnergy_nonneg _ s) (primeReciprocalMass_nonneg s)
  · exact primePairDifferenceEnergy_div_mass_le_sq_calkinDistance_div_sqrt_mass t ht rho s

/-- **`(8)` global endpoint: sub-root Calkin growth of the exterior seam on every actual Xi divisor
fibre implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_xiSeamExteriorCalkinSubmass (t : ℝ) (ht : 0 < t)
    (h : ∀ rho : XiDivisorSupport, Filter.Tendsto
      (fun s : Finset Nat.Primes =>
        xiSeamExteriorCalkinDistance t (rho : ℂ) s / Real.sqrt (primeReciprocalMass s))
      Filter.atTop (nhds 0)) :
    RiemannHypothesis := by
  refine xiPrimeSeamPairEnergySubmass_iff_riemannHypothesis.mp fun rho => ?_
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  refine (orbitwisePrimeSeamPairEnergySubmass_iff_re_eq_half hstrip).mpr ?_
  exact re_eq_half_of_xiSeamExteriorCalkinDistance_submass t ht hstrip (h rho)

end

end RHTower
