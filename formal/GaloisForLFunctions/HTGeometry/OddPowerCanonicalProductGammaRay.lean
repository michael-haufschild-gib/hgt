import GaloisForLFunctions.HTGeometry.RationalPowerNormDichotomy
import GaloisForLFunctions.HTGeometry.GammaWeierstrassCanonicalProduct

/-!
# The odd-exponent canonical product as a reciprocal-Gamma ray product

For an odd exponent `p ≥ 3` the `p`-fold root-of-unity norm of `W_1` is `W_p` in the variable `z^p`,
and the Euler–Mascheroni gauges cancel because the `p`-th roots of unity sum to zero.  Hence

`W_p(z^p) = ∏_{j<p} Γ(ω^j z + 1)⁻¹`,

a finite reciprocal-Gamma product at `p` distinct *scales*.  Because differential algebraicity is
invariant under `z ↦ z^p`, the hypertranscendence of `W_p` is *equivalent* to that of the ray
product.  This isolates the exact remaining analytic input of the integer-exponent dichotomy: for
even `p` the roots of unity pair off and the product collapses to elementary sine factors, while for
odd `p ≥ 3` no pairing exists and the multi-scale reciprocal-Gamma product must be treated directly.
-/

namespace HTGeometry

open GaloisForLFunctions

/-- **Ray-product form of the odd-exponent canonical product.** -/
theorem powerCanonicalProduct_odd_pow_eq {p : ℕ} (hp : 1 < p) (hodd : Odd p) {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) (z : ℂ) :
    powerCanonicalProduct (p : ℝ) (z ^ p)
      = ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹ := by
  have hppos : 0 < p := by omega
  have hsign : ((-1 : ℂ)) ^ (p + 1) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    subst hk
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
    norm_num
  have hratio : ((p : ℝ) / (p : ℝ)) = 1 := by
    have hpR : ((p : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hppos.ne'
    field_simp
  have hnorm := prod_powerCanonicalProduct_primitiveRoot hppos hppos hω z
  rw [hratio, hsign, one_mul] at hnorm
  rw [← hnorm]
  have hterm : ∀ j ∈ Finset.range p,
      powerCanonicalProduct 1 (ω ^ j * z)
        = Complex.exp (-((Real.eulerMascheroniConstant : ℂ) * (ω ^ j * z)))
          * (Complex.Gamma (ω ^ j * z + 1))⁻¹ := fun j _ => powerCanonicalProduct_one_eq _
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib]
  have hgauge : ∏ j ∈ Finset.range p,
      Complex.exp (-((Real.eulerMascheroniConstant : ℂ) * (ω ^ j * z))) = 1 := by
    rw [← Complex.exp_sum]
    have hzero : ∑ j ∈ Finset.range p,
        -((Real.eulerMascheroniConstant : ℂ) * (ω ^ j * z)) = 0 := by
      have hsum : ∑ j ∈ Finset.range p, ω ^ j = 0 := hω.geom_sum_eq_zero hp
      calc ∑ j ∈ Finset.range p, -((Real.eulerMascheroniConstant : ℂ) * (ω ^ j * z))
          = -((Real.eulerMascheroniConstant : ℂ) * z) * ∑ j ∈ Finset.range p, ω ^ j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hsum, mul_zero]
    rw [hzero, Complex.exp_zero]
  rw [hgauge, one_mul]

/-- **The odd-exponent open core, isolated.**  For odd `p ≥ 3` the canonical product `W_p` is
hypertranscendental exactly when the reciprocal-Gamma ray product at the `p`-th roots of unity is. -/
theorem hypertranscendental_powerCanonicalProduct_odd_iff {p : ℕ} (hp : 1 < p) (hodd : Odd p)
    {ω : ℂ} (hω : IsPrimitiveRoot ω p) :
    Hypertranscendental (powerCanonicalProduct (p : ℝ))
      ↔ Hypertranscendental
          (fun z : ℂ => ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹) := by
  have hppos : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
  have hfun : (fun z : ℂ => ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹)
      = fun z : ℂ => powerCanonicalProduct (p : ℝ) ((1 : ℂ) * z ^ p) := by
    funext z
    rw [one_mul]
    exact (powerCanonicalProduct_odd_pow_eq hp hodd hω z).symm
  rw [hfun, Hypertranscendental, Hypertranscendental,
    differentiallyAlgebraic_comp_const_mul_pow_iff
      (analyticOnNhd_powerCanonicalProduct hpR) one_ne_zero hppos]

end HTGeometry

