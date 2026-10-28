import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterRemovesTheModulusEulerFactors
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsContinuePastTheLineReOne

/-!
# The positive residue of the trivial Hecke character

Deleting the Euler factors in the modulus multiplies the Dedekind-zeta residue by
`∏_{p ∣ m} (1 - 1/Np)`. Every factor is positive. Comparing the residue limits identifies
the density from ray-class lattice counting with this explicit positive residue.
-/

noncomputable section

open NumberField IsDedekindDomain Filter
open scoped Classical Topology

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- The finite Euler correction to the residue at one. -/
def modulusEulerResidueFactor : ℝ :=
  ∏ v ∈ (finite_primes_dvd 𝔪).toFinset, (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)

theorem modulusEulerResidueFactor_pos : 0 < modulusEulerResidueFactor 𝔪 := by
  apply Finset.prod_pos
  intro v _
  have hv : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self 1)
      (ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot)
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hv)

/-- The deleted Euler factors tend to their real values at one. -/
theorem tendsto_modulusEulerFactors :
    Tendsto (fun s : ℝ => ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))))
      (𝓝[>] 1) (𝓝 (modulusEulerResidueFactor 𝔪 : ℂ)) := by
  have hcont : Continuous (fun s : ℝ => ∏ v ∈ (finite_primes_dvd 𝔪).toFinset,
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) := by
    apply continuous_finsetProd
    intro v _
    apply continuous_const.sub
    apply Complex.continuous_ofReal.neg.const_cpow
    left
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  convert (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds using 1
  simp [modulusEulerResidueFactor, Complex.cpow_neg]

/-- The residue equals the Dedekind-zeta residue times the finite Euler correction. -/
theorem tendsto_sub_one_mul_heckeL_one_explicit :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * heckeL 𝔪 1 s) (𝓝[>] 1)
      (𝓝 ((dedekindZeta_residue K * modulusEulerResidueFactor 𝔪 : ℝ) : ℂ)) := by
  have h := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).mul
    (tendsto_modulusEulerFactors 𝔪)
  rw [Complex.ofReal_mul]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [heckeL_one_eq_dedekindZeta_mul 𝔪 (by simpa using hs), mul_assoc]

/-- The density furnished by ray-class counting is the explicit Euler-corrected residue. -/
theorem heckeDensity_eq_dedekindZeta_residue_mul :
    heckeDensity 𝔪 = dedekindZeta_residue K * modulusEulerResidueFactor 𝔪 := by
  apply Complex.ofReal_injective
  exact tendsto_nhds_unique (tendsto_sub_one_mul_heckeL_one (𝔪 := 𝔪))
    (tendsto_sub_one_mul_heckeL_one_explicit 𝔪)

/-- The trivial Hecke character has a strictly positive residue at one. -/
theorem heckeDensity_pos : 0 < heckeDensity 𝔪 := by
  rw [heckeDensity_eq_dedekindZeta_residue_mul]
  exact mul_pos (dedekindZeta_residue_pos K) (modulusEulerResidueFactor_pos 𝔪)

/-- Every ray class has positive ideal density. -/
theorem rayDensity_pos : 0 < rayDensity 𝔪 := by
  have h := heckeDensity_pos 𝔪
  rw [heckeDensity] at h
  exact pos_of_mul_pos_right h (Nat.cast_nonneg _)

end GaloisForLFunctions.HeckeLFunctions
