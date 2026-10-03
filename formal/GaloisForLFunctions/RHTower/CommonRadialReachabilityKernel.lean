import GaloisForLFunctions.RHTower.CommonRadialSubunitHarmonicCompletion
import GaloisForLFunctions.HTGeometry.PrimeClockGammaTotality
import GaloisForLFunctions.HTGeometry.PrimeHodgeReachabilityProperness

/-!
# Faithfulness of the common-radial prime–Hodge reachability

The common-radial reachability `W_d` and its adjoint synthesis `W_d*` both have trivial kernel
**(CRSHC.4)**.  Each prime column of `W_d*` is a nonzero multiple of the Gamma-coherent vector
`r e^{-r log p}`; these vectors are total, so `ker W_d = 0`.  `W_d W_d* = A_d` with `A_d` injective
gives `ker W_d* = 0`.
-/

open MeasureTheory Set Filter
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

/-- The prime column `g_p` of the common-radial synthesis is the positive multiple
`scale_p √(Λ(p)/p) · r e^{-r log p}`. -/
theorem commonRadialPrimeField_coeFn (a : {d : ℝ // 0 < d}) (p : Nat.Primes) :
    (commonRadialPrimeField a p : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] fun L =>
      ((commonRadialPrimeScale a p *
        Real.sqrt (ArithmeticFunction.vonMangoldt (p : ℕ) / (p : ℕ)) : ℝ) : ℂ) *
          ((L * Real.exp (-(Real.log (p : ℝ) * L)) : ℝ) : ℂ) := by
  have hmem := memLp_routePBurnolHalfLine (continuous_routePPrimitiveBurnolWindowFeature (p, 0) 0)
    (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature (p, 0) 0)
  have hcoe : (routePPrimitiveBurnolWindowFeatureLp (p, 0) 0 : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      routePPrimitiveBurnolWindowFeature (p, 0) 0 := hmem.coeFn_toLp
  filter_upwards [Lp.coeFn_smul (commonRadialPrimeScale a p : ℂ)
    (routePPrimitiveBurnolWindowFeatureLp (p, 0) 0), hcoe] with L h1 h2
  rw [commonRadialPrimeField, h1, Pi.smul_apply, h2, smul_eq_mul, routePPrimitiveBurnolWindowFeature,
    xiWardCubicBurnolWindowConormalFeature_eq, routePXiBaseConormalResidueFeature,
    routePPrimitiveBurnolSpectralPoint, finiteVonMangoldtDepthOneAmplitude, xiGammaEulerValuationNat,
    xiGammaEulerPrimitiveLogFrequency, xiGammaEulerValuationNat]
  simp only [zero_add, pow_one, Complex.ofReal_zero, mul_zero, add_zero]
  push_cast
  ring_nf

/-- `g_p` is a nonzero multiple of the Gamma-coherent vector at the prime clock `log p`. -/
theorem commonRadialPrimeField_eq_smul_gammaCoherentVector (a : {d : ℝ // 0 < d})
    (p : Nat.Primes) :
    ∃ c : ℝ, c ≠ 0 ∧
      commonRadialPrimeField a p = (c : ℂ) • gammaCoherentVector 3 (primeClock_pos p) := by
  have hlog := primeClock_pos p
  set s : ℝ := Real.sqrt ((2 * Real.log (p : ℝ)) ^ 3 / ((3 - 1).factorial : ℝ)) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hΛ : 0 < ArithmeticFunction.vonMangoldt (p : ℕ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime p.property]
    exact Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hA : 0 < Real.sqrt (ArithmeticFunction.vonMangoldt (p : ℕ) / (p : ℕ)) :=
    Real.sqrt_pos.2 (div_pos hΛ (by exact_mod_cast p.property.pos))
  refine ⟨commonRadialPrimeScale a p * Real.sqrt (ArithmeticFunction.vonMangoldt (p : ℕ) / (p : ℕ))
    / s, (div_pos (mul_pos (commonRadialPrimeScale_pos a p) hA) hs).ne', ?_⟩
  refine Lp.ext ?_
  filter_upwards [commonRadialPrimeField_coeFn a p, Lp.coeFn_smul (_ : ℂ)
    (gammaCoherentVector 3 (primeClock_pos p)), gammaCoherentVector_ae 3 (primeClock_pos p),
    ae_restrict_mem measurableSet_Ioi] with L h1 h2 h3 hL
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, gammaCoherentProfile]
  have hL' : (0 : ℝ) < L := hL
  rw [show ((3 : ℕ) : ℝ) - 1 = 2 by norm_num, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  rw [← hsdef]
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  push_cast
  field_simp

/-- **(CRSHC.4)** `ker W_d = 0`. -/
theorem commonRadialPrimeReachability_injective (a : {d : ℝ // 0 < d}) :
    Function.Injective (commonRadialPrimeReachability a) := by
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  refine eq_zero_of_forall_inner_gammaCoherentVector_eq_zero 3 ∅ h fun p _ => ?_
  have h1 := inner_basis_commonRadialPrimeReachability a p h
  rw [hh, inner_zero_right] at h1
  obtain ⟨c, hc, hfield⟩ := commonRadialPrimeField_eq_smul_gammaCoherentVector a p
  rw [hfield, inner_smul_left, Complex.conj_ofReal] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left (Complex.ofReal_ne_zero.2 hc)

/-- **(CRSHC.4)** `ker W_d* = 0`: `W_d W_d* = A_d` is injective. -/
theorem commonRadialPrimeSynthesis_injective (a : {d : ℝ // 0 < d}) :
    Function.Injective (commonRadialPrimeSynthesis a) := by
  intro x y hxy
  apply normalizedStokesPrimeOperator_injective a.property
  rw [← commonRadialPrimeReachability_comp_synthesis, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hxy]

end

end RHTower
