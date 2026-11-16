import GaloisForLFunctions.OrderSixMetaplecticTheory.Arithmetic.ConductorNormalization
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.HeckeLFunctionsAndReciprocals

/-!
# Exact zeta normalization of the prime dilate factors

Primary primes represent exactly the unramified prime ideals. The normalized
spectral factor at `s` is `1-N(p)^(2-3s)`, so its product is `1/Z₀(3s-2)`
for `Re s > 1`. At `4/3`, the conductor correction is `9/(8 ζ_K(2))`.
The inverse residue products tend to `Z₀(2)`, and the actual cubic Gauss
phases preserve the limiting modulus.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.OrderSixMetaplecticTheory
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein

namespace PrimaryPrime

/-- The prime ideal represented by a primary prime. -/
def toPrimeIdeal (P : PrimaryPrime) : HeckeIdealSeries.PrimeIdeal :=
  ⟨Ideal.span {P.p}, Ideal.prime_of_isPrime
    (Ideal.span_singleton_eq_bot.not.mpr P.ne_zero)
    ((Ideal.span_singleton_prime P.ne_zero).mpr P.prime)⟩

theorem toPrimeIdeal_injective : Function.Injective toPrimeIdeal := by
  intro P Q h
  apply p_injective
  have he := congrArg (fun I : HeckeIdealSeries.PrimeIdeal => primaryIdealGenerator I.val) h
  simpa only [toPrimeIdeal, primaryIdealGenerator_span P.p P.ne_zero P.primary,
    primaryIdealGenerator_span Q.p Q.ne_zero Q.primary] using he

/-- Precisely the prime ideals admitting a primary generator occur. -/
theorem mem_range_toPrimeIdeal (I : HeckeIdealSeries.PrimeIdeal) :
    I ∈ Set.range toPrimeIdeal ↔ primaryIdealGenerator I.val ≠ 0 := by
  constructor
  · rintro ⟨P, rfl⟩
    change primaryIdealGenerator (Ideal.span {P.p}) ≠ 0
    rw [primaryIdealGenerator_span P.p P.ne_zero P.primary]
    exact P.ne_zero
  · intro hI
    have hspec := primaryIdealGenerator_spec I.val hI
    have hp : Prime (primaryIdealGenerator I.val) := by
      apply (Ideal.span_singleton_prime hI).mp
      rw [hspec.1]
      exact Ideal.isPrime_of_prime I.property
    exact ⟨⟨primaryIdealGenerator I.val, hp, hspec.2⟩, Subtype.ext hspec.1⟩

theorem unramifiedNormWeight_toPrimeIdeal (P : PrimaryPrime) (s : ℂ) :
    unramifiedNormWeight s P.toPrimeIdeal.val = (P.conductorNorm : ℂ) ^ (-s) := by
  apply unramifiedNormWeight_of_good
  change primaryIdealGenerator (Ideal.span {P.p}) ≠ 0
  rw [primaryIdealGenerator_span P.p P.ne_zero P.primary]
  exact P.ne_zero

/-- The actual spectral factor with its norm power and two first-order factors removed. -/
def normalizedDilateFactor (P : PrimaryPrime) (s : ℂ) : ℂ :=
  P.dilateFactor s * ((‖ringComplex P.p‖ : ℂ) * (‖ringComplex P.p‖ : ℂ) ^ (-s)) *
    (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * ((‖ringComplex P.p‖ : ℂ) ^ (-s)) ^ 3) ^ 2

/-- The remaining square-power correction is an Euler factor at `3s-2`. -/
theorem normalizedDilateFactor_eq (P : PrimaryPrime) (s : ℂ) (hs : 2 / 3 < s.re) :
    P.normalizedDilateFactor s = 1 - (P.conductorNorm : ℂ) ^ (2 - 3 * s) := by
  have hN : (P.conductorNorm : ℂ) =
      (‖ringComplex P.p‖ : ℂ) * (‖ringComplex P.p‖ : ℂ) := by
    exact_mod_cast P.conductorNorm_cast.trans (pow_two _)
  have hpower :
      ((‖ringComplex P.p‖ : ℂ) ^ 2 * ((‖ringComplex P.p‖ : ℂ) ^ (-s)) ^ 3) ^ 2 =
        (P.conductorNorm : ℂ) ^ (2 - 3 * s) := by
    calc
      _ = (‖ringComplex P.p‖ : ℂ) ^ 4 *
          ((‖ringComplex P.p‖ : ℂ) ^ (-s)) ^ 6 := by ring
      _ = (‖ringComplex P.p‖ : ℂ) ^ ((4 : ℂ) + 6 * (-s)) := by
        rw [Complex.cpow_add _ _ P.rho_ne_zero]
        rw [Complex.cpow_ofNat]
        congr 1
        simpa only [Nat.cast_ofNat] using
          (Complex.cpow_nat_mul (‖ringComplex P.p‖ : ℂ) 6 (-s)).symm
      _ = _ := by
        rw [hN, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
          ← Complex.cpow_add _ _ P.rho_ne_zero]
        congr 1
        ring
  rw [normalizedDilateFactor, ← hpower]
  linear_combination
    (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * ((‖ringComplex P.p‖ : ℂ) ^ (-s)) ^ 3) *
      P.dilateFactor_mul s hs

end PrimaryPrime

/-- The primary-prime Euler product omits exactly the ramified prime of norm three. -/
theorem primaryPrime_eulerProduct (s : ℂ) (hs : 1 < s.re) :
    (∏' P : PrimaryPrime, (1 - (P.conductorNorm : ℂ) ^ (-s))) =
      (unramifiedIdealZeta s)⁻¹ := by
  have hsum : Summable (fun I : HeckeIdealSeries.PrimeIdeal =>
      ‖unramifiedNormWeight s I.val‖) :=
    (unramifiedNormWeight_summable_norm s hs).comp_injective Subtype.val_injective
  have heuler := HeckeIdealSeries.mobiusPrimeCoeff_euler (unramifiedNormWeight s) hsum
  have heuler' : unramifiedMobiusSeries s =
      ∏' I : HeckeIdealSeries.PrimeIdeal, (1 - unramifiedNormWeight s I.val) := by
    simpa only [HeckeIdealSeries.mobiusPrimeCoeff, IdealEuler.primeValueHom_eq,
      unramifiedMobiusSeries] using heuler
  have hreindex := PrimaryPrime.toPrimeIdeal_injective.tprod_eq
    (f := fun I : HeckeIdealSeries.PrimeIdeal => 1 - unramifiedNormWeight s I.val) (by
      intro I hI
      apply (PrimaryPrime.mem_range_toPrimeIdeal I).mpr
      intro hz
      have hone : 1 - unramifiedNormWeight s I.val = 1 := by
        rw [unramifiedNormWeight_of_bad s I.val hz, sub_zero]
      exact hI hone)
  simp only [PrimaryPrime.unramifiedNormWeight_toPrimeIdeal] at hreindex
  exact hreindex.trans (heuler'.symm.trans (unramifiedMobiusSeries_eq_inv s hs))

theorem primaryPrime_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimaryPrime => 1 - (P.conductorNorm : ℂ) ^ (-s))
      (unramifiedIdealZeta s)⁻¹ := by
  have hsum := ((unramifiedNormWeight_summable_norm s hs).comp_injective
    (show Function.Injective (fun I : HeckeIdealSeries.PrimeIdeal => I.val) from
      Subtype.val_injective)).comp_injective PrimaryPrime.toPrimeIdeal_injective
  change Summable (fun P : PrimaryPrime =>
    ‖unramifiedNormWeight s P.toPrimeIdeal.val‖) at hsum
  simp only [PrimaryPrime.unramifiedNormWeight_toPrimeIdeal] at hsum
  have hm : Multipliable (fun P : PrimaryPrime => 1 - (P.conductorNorm : ℂ) ^ (-s)) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimaryPrime => ‖-((P.conductorNorm : ℂ) ^ (-s))‖) by
        simpa only [norm_neg] using hsum)
  simpa only [primaryPrime_eulerProduct s hs] using hm.hasProd

/-- Normalized actual spectral factors have the reciprocal unramified zeta product. -/
theorem normalizedDilateFactor_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimaryPrime => P.normalizedDilateFactor s)
      (unramifiedIdealZeta (3 * s - 2))⁻¹ := by
  have hs' : 1 < (3 * s - 2).re := by
    norm_num
    linarith only [hs]
  apply (primaryPrime_eulerProduct_hasProd (3 * s - 2) hs').congr_fun
  intro P
  rw [P.normalizedDilateFactor_eq s (by linarith only [hs])]
  congr 2
  ring

/-- The bounded conductor correction has an exact unramified-zeta value. -/
theorem conductorSquareConstant_eq_inv_zeta :
    (conductorSquareConstant : ℂ) = (unramifiedIdealZeta 2)⁻¹ := by
  have h := conductorSquare_multipliable.hasProd.map
    Complex.ofRealHom Complex.continuous_ofReal
  have hlocal (P : PrimaryPrime) :
      1 - (P.conductorNorm : ℂ) ^ (-(2 : ℂ)) =
        ((1 - 1 / (P.conductorNorm : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.cpow_neg, show (2 : ℂ) = (2 : ℕ) by norm_num, Complex.cpow_natCast]
    push_cast
    simp only [one_div]
  have hp := (h.congr_fun hlocal).tprod_eq
  exact hp.symm.trans (primaryPrime_eulerProduct 2 (by norm_num))

/-- Restoring the ramified Euler factor identifies the correction with Dedekind zeta. -/
theorem conductorSquareConstant_eq_dedekindZeta :
    (conductorSquareConstant : ℂ) = 9 / (8 * NumberField.dedekindZeta K 2) := by
  rw [conductorSquareConstant_eq_inv_zeta,
    unramifiedIdealZeta_eq_dedekindZeta 2 (by norm_num), Complex.cpow_neg]
  norm_num [Complex.cpow_natCast, mul_inv_rev, div_eq_mul_inv]
  ring

/-- The normalized finite products of the actual dilate factors converge to reciprocal zeta. -/
theorem normalizedDilateProduct_tendsto :
    Filter.Tendsto normalizedDilateProduct Filter.atTop
      (nhds (unramifiedIdealZeta 2)⁻¹) := by
  have h := conductorSquare_multipliable.hasProd.map
    Complex.ofRealHom Complex.continuous_ofReal
  rw [← conductorSquareConstant_eq_inv_zeta]
  have hfun : normalizedDilateProduct = fun S : Finset PrimaryPrime =>
      ∏ P ∈ S, ((1 - 1 / (P.conductorNorm : ℝ) ^ 2 : ℝ) : ℂ) := by
    funext S
    rw [normalizedDilateProduct_eq]
    simp only [conductorSquareCorrection, Complex.ofReal_prod]
  rw [hfun]
  exact h

/-- The inverse normalization of the prime residue weights converges to zeta itself. -/
theorem normalizedDilateResidueProduct_tendsto :
    Filter.Tendsto normalizedDilateResidueProduct Filter.atTop
      (nhds (unramifiedIdealZeta 2)) := by
  have h := normalizedDilateProduct_tendsto.inv₀
    (inv_ne_zero (unramifiedIdealZeta_ne_zero 2 (by norm_num)))
  simpa only [inv_inv, ← normalizedDilateResidueProduct_eq] using h

/-- The actual Gauss phases preserve the limiting modulus of the cubic-twist residue products. -/
theorem normalizedCubicTwistResidueProduct_norm_tendsto :
    Filter.Tendsto (fun S => ‖normalizedCubicTwistResidueProduct S‖) Filter.atTop
      (nhds ‖unramifiedIdealZeta 2‖) := by
  simpa only [normalizedCubicTwistResidueProduct_norm] using
    normalizedDilateResidueProduct_tendsto.norm

#print axioms primaryPrime_eulerProduct
#print axioms normalizedDilateFactor_hasProd
#print axioms conductorSquareConstant_eq_dedekindZeta
#print axioms normalizedDilateProduct_tendsto
#print axioms normalizedDilateResidueProduct_tendsto
#print axioms normalizedCubicTwistResidueProduct_norm_tendsto
end GaloisForLFunctions.OrderSixMetaplecticTheory
