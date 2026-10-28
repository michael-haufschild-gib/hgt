import GaloisForLFunctions.HeckeLFunctions.NonzeroIdealsArePrimeExponentVectors
import GaloisForLFunctions.HeckeLFunctions.HeckeCharactersGiveConvergentLSeries
import GaloisForLFunctions.HTGeometry.OccupationEulerProduct
import GaloisForLFunctions.RHTower.NumberFieldFinitePlaceNormSummability

/-!
# Prime-ideal Euler products for Hecke L-series

The summand `ψ(I) N(I)⁻ˢ` is multiplicative on nonzero integral ideals. Unique ideal
factorization turns it into a monomial in the prime summands. Their absolute summability and
strict norm bound give an Euler product. Grouping the ideal sum by norm recovers `heckeL`.
-/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal
open scoped Classical nonZeroDivisors Topology

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K]
variable (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)

@[simp] theorem heckeValue_bot : heckeValue 𝔪 ψ ⊥ = 0 :=
  heckeValue_of_not_mem 𝔪 ψ (fun h => h.1 rfl)

@[simp] theorem heckeValue_one : heckeValue 𝔪 ψ 1 = 1 := by
  have hI : (1 : Ideal (𝓞 K)) ≠ ⊥ := one_ne_zero
  have hunit : idealUnit hI = 1 := by
    apply Units.ext
    rw [coe_idealUnit, Units.val_one, Ideal.one_eq_top, coeIdeal_top]
  have hm : idealUnit hI ∈ idealGroup 𝔪 := hunit.symm ▸ (idealGroup 𝔪).one_mem
  rw [heckeValue_of_mem 𝔪 ψ hI hm]
  have hsub : (⟨idealUnit hI, hm⟩ : idealGroup 𝔪) = 1 := Subtype.ext hunit
  rw [hsub, map_one, map_one, Units.val_one]

/-- The ideal summand, viewed as a multiplicative map on nonzero ideals. -/
def heckeIdealTerm (s : ℂ) : (Ideal (𝓞 K))⁰ →* ℂ where
  toFun I := heckeValue 𝔪 ψ I * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)
  map_one' := by
    change heckeValue 𝔪 ψ 1 * (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℂ) ^ (-s) = 1
    rw [heckeValue_one, map_one, Nat.cast_one, Complex.one_cpow, mul_one]
  map_mul' I J := by
    simp only [Submonoid.coe_mul, heckeValue_mul, map_mul, Nat.cast_mul]
    rw [Complex.natCast_mul_natCast_cpow]
    ring

/-- The ratio of the geometric Euler factor at a nonzero prime ideal. -/
def heckePrimeTerm (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  heckeValue 𝔪 ψ v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)

theorem norm_heckePrimeTerm_lt_one {s : ℂ} (hs : 1 < s.re)
    (v : HeightOneSpectrum (𝓞 K)) : ‖heckePrimeTerm 𝔪 ψ s v‖ < 1 := by
  have hv : 2 ≤ Ideal.absNorm v.asIdeal :=
    ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  have hv0 : 0 < Ideal.absNorm v.asIdeal := lt_of_lt_of_le (Nat.zero_lt_succ 1) hv
  calc ‖heckePrimeTerm 𝔪 ψ s v‖
      = ‖heckeValue 𝔪 ψ v.asIdeal‖ * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := norm_mul _ _
    _ ≤ ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (norm_heckeValue_le_one 𝔪 ψ _)
    _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hv0, Complex.neg_re]
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self 1) hv) (neg_neg_of_pos (lt_trans zero_lt_one hs))

theorem summable_norm_heckePrimeTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v => ‖heckePrimeTerm 𝔪 ψ s v‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (numberField_summable_finitePlace_norm_cpow (K := K) hs)
  intro v
  change ‖heckeValue 𝔪 ψ v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_heckeValue_le_one 𝔪 ψ _)

/-- Factorization turns the ideal summand into a monomial in the prime summands. -/
theorem heckeIdealTerm_idealOfPrimeExponents (s : ℂ)
    (ν : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    heckeIdealTerm 𝔪 ψ s (idealOfPrimeExponents ν) =
      HTGeometry.nomeMonomial (heckePrimeTerm 𝔪 ψ s) ν := by
  let P (v : HeightOneSpectrum (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
    ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have hprod : idealOfPrimeExponents ν = ∏ v ∈ ν.support, P v ^ ν v := by
    apply Subtype.ext
    simp [idealOfPrimeExponents, Finsupp.prod, P]
  rw [hprod, map_prod, HTGeometry.nomeMonomial, Finsupp.prod]
  apply Finset.prod_congr rfl
  intro v _
  rw [map_pow]
  rfl

/-- Absolute convergence of the sum over individual ideals, before grouping by norm. -/
theorem summable_norm_heckeIdealTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I => ‖heckeIdealTerm 𝔪 ψ s I‖) := by
  have h := (HTGeometry.summable_nomeMonomial_pow_iff 0 (heckePrimeTerm 𝔪 ψ s)
    (norm_heckePrimeTerm_lt_one 𝔪 ψ hs)).mpr (by
      simpa only [zero_add, pow_one] using summable_norm_heckePrimeTerm 𝔪 ψ hs)
  apply (primeExponentsIdealEquiv (K := K)).summable_iff.mp
  refine h.congr fun ν => ?_
  simp only [zero_add, pow_one]
  exact congrArg norm (heckeIdealTerm_idealOfPrimeExponents 𝔪 ψ s ν).symm

/-- Grouping the absolutely convergent ideal sum by norm gives the coefficient L-series. -/
theorem heckeL_eq_tsum_ideals {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 ψ s = ∑' I, heckeIdealTerm 𝔪 ψ s I := by
  let f (I : Ideal (𝓞 K)) : ℂ := heckeValue 𝔪 ψ I * (Ideal.absNorm I : ℂ) ^ (-s)
  have hsupport : Function.support f ⊆ (nonZeroDivisors (Ideal (𝓞 K)) : Set (Ideal (𝓞 K))) := by
    intro I hI
    apply mem_nonZeroDivisors_of_ne_zero
    intro hzero
    exact hI (by simp [f, hzero])
  have hall : HasSum f (∑' I, heckeIdealTerm 𝔪 ψ s I) :=
    (hasSum_subtype_iff_of_support_subset hsupport).mp
      (summable_norm_heckeIdealTerm 𝔪 ψ hs).of_norm.hasSum
  have hgroup := hall.tsum_fiberwise Ideal.absNorm
  have hterm (n : ℕ) :
      (∑' I : (Ideal.absNorm : Ideal (𝓞 K) → ℕ) ⁻¹' {n}, f I.1) =
      LSeries.term (heckeCoeff 𝔪 ψ) s n := by
    letI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq n).fintype
    change (∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, f I) = _
    rw [tsum_fintype, ← Finset.sum_subtype (idealsOfNorm K n)
      (fun _ => mem_idealsOfNorm) f]
    by_cases hn : n = 0
    · subst n
      rw [LSeries.term_zero]
      apply Finset.sum_eq_zero
      intro I hI
      have hI0 : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp (mem_idealsOfNorm.mp hI)
      simp [f, hI0]
    · rw [LSeries.term_of_ne_zero hn, heckeCoeff, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro I hI
      simp only [f, mem_idealsOfNorm.mp hI, Complex.cpow_neg, div_eq_mul_inv]
  rw [funext hterm] at hgroup
  exact hgroup.tsum_eq

/-- The prime-ideal Euler product converges to the Hecke L-series on `Re s > 1`. -/
theorem heckeL_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - heckePrimeTerm 𝔪 ψ s v)⁻¹)
      (heckeL 𝔪 ψ s) := by
  have h := HTGeometry.hasProd_inv_one_sub_nome (heckePrimeTerm 𝔪 ψ s)
    (norm_heckePrimeTerm_lt_one 𝔪 ψ hs) (summable_norm_heckePrimeTerm 𝔪 ψ hs)
  have hsum : (∑' ν, HTGeometry.nomeMonomial (heckePrimeTerm 𝔪 ψ s) ν) =
      heckeL 𝔪 ψ s := by
    rw [heckeL_eq_tsum_ideals 𝔪 ψ hs,
      ← (primeExponentsIdealEquiv (K := K)).tsum_eq (heckeIdealTerm 𝔪 ψ s)]
    exact tsum_congr fun ν => (heckeIdealTerm_idealOfPrimeExponents 𝔪 ψ s ν).symm
  exact hsum ▸ h

theorem heckeL_eulerProduct_tprod {s : ℂ} (hs : 1 < s.re) :
    ∏' v : HeightOneSpectrum (𝓞 K),
      (1 - heckeValue 𝔪 ψ v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ =
      heckeL 𝔪 ψ s :=
  (heckeL_eulerProduct_hasProd 𝔪 ψ hs).tprod_eq

/-- Every local Euler denominator is nonzero in the half-plane of absolute convergence. -/
theorem heckeEulerDenominator_ne_zero {s : ℂ} (hs : 1 < s.re)
    (v : HeightOneSpectrum (𝓞 K)) : 1 - heckePrimeTerm 𝔪 ψ s v ≠ 0 := by
  intro h
  have hterm : heckePrimeTerm 𝔪 ψ s v = 1 := (sub_eq_zero.mp h).symm
  have hnorm := norm_heckePrimeTerm_lt_one 𝔪 ψ hs v
  rw [hterm, norm_one] at hnorm
  exact lt_irrefl _ hnorm

/-- The product of the Euler denominators is the reciprocal of the Hecke L-series. -/
theorem heckeEulerDenominatorProduct_mul_heckeL {s : ℂ} (hs : 1 < s.re) :
    (∏' v : HeightOneSpectrum (𝓞 K), (1 - heckePrimeTerm 𝔪 ψ s v)) * heckeL 𝔪 ψ s = 1 := by
  have hsum : Summable (fun v => ‖-heckePrimeTerm 𝔪 ψ s v‖) := by
    simpa only [norm_neg] using summable_norm_heckePrimeTerm 𝔪 ψ hs
  have hprod : Multipliable (fun v => 1 - heckePrimeTerm 𝔪 ψ s v) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hsum
  have h := hprod.hasProd.mul (heckeL_eulerProduct_hasProd 𝔪 ψ hs)
  have hlocal (v : HeightOneSpectrum (𝓞 K)) :
      (1 - heckePrimeTerm 𝔪 ψ s v) * (1 - heckePrimeTerm 𝔪 ψ s v)⁻¹ = 1 :=
    mul_inv_cancel₀ (heckeEulerDenominator_ne_zero 𝔪 ψ hs v)
  simp only [hlocal] at h
  exact h.unique hasProd_one

/-- Hecke L-series do not vanish in their half-plane of absolute convergence. -/
theorem heckeL_ne_zero {s : ℂ} (hs : 1 < s.re) : heckeL 𝔪 ψ s ≠ 0 := by
  intro hzero
  have h := heckeEulerDenominatorProduct_mul_heckeL 𝔪 ψ hs
  rw [hzero, mul_zero] at h
  exact zero_ne_one h

end GaloisForLFunctions.HeckeLFunctions
