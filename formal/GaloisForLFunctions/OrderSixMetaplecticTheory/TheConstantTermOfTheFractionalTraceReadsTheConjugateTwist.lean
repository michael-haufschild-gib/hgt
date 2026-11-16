import GaloisForLFunctions.OrderSixMetaplecticTheory.TheFractionalTracePhasesSumToJacobiAndGaussSums

/-!
# The constant term of the fractional trace reads the conjugate twist

For the projected theta function θ_s (Fourier series Σ_k b(v, k) e(ξ_kz)) and an odd primary prime q, the constant
term of the fractional trace is (`integral_sourceFracTrace`)

∫_P Tr G(z, v) dz = |P| (Σ_k b(v, k)b(v, −k)(N² + N − J + NJ[q ∣ k])
    + N² χ(−4)χ(9)⁻¹ Σ_k b(v/N, k)b(v/N, −k) g_χ(k)),

g_χ(k) = Σ_u χ(u)ψ(uk) the cubic Gauss sum at k, J the Jacobi sum of χ and the quadratic character:

* the cusp ∞ (G itself) reads the q-divisible frequencies: N Σ_{q ∣ k};
* the N − 1 middle cusps read N − J + (J − 1)N[q ∣ k] (Jacobi phases), their high points cancel;
* the cusp 0 reads N²Σ_k plus the low points of low points, whose Gauss sums g_χ(k) = χ̄(k)g_χ make the
  **conjugate twist** Σ_k χ̄(k)b(v/N, k)b(v/N, −k).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### Products of translated cusp series -/

theorem summable_mul_neg {c d : O → ℂ} (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖))
    (φ : O → ℂ) (hφ : ∀ k, ‖φ k‖ ≤ 1) : Summable (fun k => c k * d (-k) * φ k) := by
  have h := (summable_conv_family hc hd).prod_factor 0
  refine Summable.of_norm_bounded h fun k => ?_
  simp only [zero_sub, norm_mul]
  exact mul_le_of_le_one_right (by positivity) (hφ k)

/-- **Parseval for translates.** ∫_P S_c(z + α)S_d(z + β) = |P| Σ_k c(k)d(−k)e(ξ_k(α − β)). -/
theorem integral_translate_mul (c d : O → ℂ) (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖))
    (α β : ℂ) :
    ∫ z in periodDomain, cuspCharacterSeries c (z + α) * cuspCharacterSeries d (z + β) =
      periodArea * ∑' k : O, c k * d (-k) * tracePhase (cuspFrequency k * (α - β)) := by
  set c' : O → ℂ := fun h => c h * tracePhase (cuspFrequency h * α)
  set d' : O → ℂ := fun h => d h * tracePhase (cuspFrequency h * β)
  have hc' : Summable (fun h => ‖c' h‖) := by simpa only [c', norm_mul, tracePhase_norm, mul_one] using hc
  have hd' : Summable (fun h => ‖d' h‖) := by simpa only [d', norm_mul, tracePhase_norm, mul_one] using hd
  simp_rw [cuspCharacterSeries_translate]
  change ∫ z in periodDomain, cuspCharacterSeries c' z * cuspCharacterSeries d' z = _
  simp_rw [cuspCharacterSeries_mul hc' hd']
  rw [PrimaryPrime.integral_cuspCharacterSeries _ (summable_cuspConv hc' hd')]
  congr 1
  unfold cuspConv
  refine tsum_congr fun k => ?_
  simp only [c', d', zero_sub, cuspFrequency, map_neg]
  rw [mul_sub, AddChar.map_sub_eq_div,
    show -ringComplex k / (3 * ringComplex traceLambda) * β = -(ringComplex k / (3 * ringComplex traceLambda) * β) by ring,
    AddChar.map_neg_eq_inv]
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
