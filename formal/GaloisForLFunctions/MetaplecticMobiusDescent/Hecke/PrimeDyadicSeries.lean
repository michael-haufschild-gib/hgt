/-
Prime dyadic series adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.PrimeCounting.AnnularPrimeMass

/-!
# Prime dyadic series

Prime dyadic coefficients, polynomials and series with Euler bounds and bin costs
(`HeckePrimeDyadic`); eventual lower bounds of the ray prime normalizer; prime scale and twisted
modulus bounds.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Filter HeckeTauberian
namespace HeckeRayPrimes
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem analytic_family : PNT.RayAsymptotic.AnalyticFamily M
    (fun χ => LFunction (HeckeRayFamily.character M χ))
    (HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1) 1) := by
  refine ⟨?_, ?_, ?_, ?_, HeckeRayFamily.principal_pole_ne_zero M⟩
  · intro χ s hs
    exact LFunction_eq_series _ hs
  · intro χ s hs hpole
    rcases hpole with hχ | hs1
    · exact (HeckeRayFamily.character_entire M χ hχ).analyticAt s
    · apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
      filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with z hz0 hz1
      exact LFunction_differentiableAt _ hz0 (Or.inl hz1)
  · intro χ s hs hpole
    exact HeckeRayFamily.character_boundary_ne_zero M χ hs hpole.symm
  · apply PNT.RayAsymptotic.principalRegularization_analyticAt_of_local
      _ (HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1))
      ((HeckeOrigin.poleRemoved_entire _).analyticAt 1)
    filter_upwards [isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0)] with s hs0
    intro hs1
    exact (HeckeOrigin.poleRemoved_eq _ hs0 hs1).symm

theorem classCoeff_ratio_tendsto :
    Tendsto (fun N : ℕ => cumsum (PNT.RayAsymptotic.classCoeff M) N / N)
      atTop (𝓝 ((RayOrthogonality.rayCard M : ℝ)⁻¹)) :=
  PNT.RayAsymptotic.classCoeff_ratio_tendsto M (analytic_family M)

theorem quotientClassCoeff_ratio_tendsto
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H) :
    Tendsto (fun N : ℕ => cumsum (PNT.RayAsymptotic.quotientClassCoeff M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) :=
  PNT.RayAsymptotic.quotientClassCoeff_ratio_tendsto M H hH (analytic_family M)

theorem primeLogMass_ratio_tendsto :
    Tendsto (fun N : ℕ => PNT.IdealPrimeMass.primeLogMass (RayOrthogonality.principalIdeals M) N / N)
      atTop (𝓝 ((RayOrthogonality.rayCard M : ℝ)⁻¹)) :=
  PNT.IdealPrimeMass.primeLogMass_ratio_tendsto _ (classCoeff_ratio_tendsto M)

theorem quotientPrimeLogMass_ratio_tendsto
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H) :
    Tendsto (fun N : ℕ => PNT.IdealPrimeMass.primeLogMass (RayQuotient.identityClass M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) :=
  PNT.IdealPrimeMass.primeLogMass_ratio_tendsto _ (quotientClassCoeff_ratio_tendsto M H hH)

end HeckeRayPrimes

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open Filter MeasureTheory
open scoped Classical Topology ContDiff
namespace RayPrimeNormalizer
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def normalizer (S : Finset (Ideal O)) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  PNT.AnnularPrimeMass.weightedPrimeSumDeleted (RayQuotient.identityClass M H) S W x

include hH

theorem asymptotic (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1/6 : ℝ) * normalizer M H S W x)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹ * ∫ y : ℝ, W y * y ^ (-5/6 : ℝ))) :=
  PNT.AnnularPrimeMass.weightedPrimeSumDeleted_tendsto _ S
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp

theorem eventually_lower_bound (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1/6 : ℝ) / Real.log x ≤ normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_lower_bound _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

theorem eventually_pos (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 0 < normalizer M H S W x := by
  apply PNT.AnnularPrimeMass.weightedPrimeSumDeleted_eventually_pos _ S
    (show 0 < (RayQuotient.classNumber M H : ℝ)⁻¹ from inv_pos.mpr (by
      exact_mod_cast RayQuotient.classNumber_pos M H))
    (HeckeRayPrimes.quotientClassCoeff_ratio_tendsto M H hH) W hW hc hp hW0 hWne

end RayPrimeNormalizer

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeDeletionDerivative
open HeckeFamily HeckeDeletionBounds

theorem factor_deriv {N : ℝ} (hN : 0 < N) (a s : ℂ) :
    deriv (EulerFactors.factor N a) s = a*(N : ℂ)^(-s)*Complex.log (N : ℂ) := by
  have h := (hasDerivAt_const s (1 : ℂ)).sub
    (((hasDerivAt_id s).neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))).const_mul a)
  have h' : HasDerivAt (EulerFactors.factor N a)
      (a*(N : ℂ)^(-s)*Complex.log (N : ℂ)) s := by
    convert h using 1 <;> first | rfl | (dsimp; ring)
  exact h'.deriv

theorem factor_logDeriv_norm {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖logDeriv (EulerFactors.factor N a) s‖ ≤ localBound σ * Real.log N := by
  have hn0 : 0 < N := by linarith
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have ht := term_bound hσ hN ha hs
  have hδ : (2 : ℝ)^(-σ) ≤ 1 :=
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
  have hf := (factor_bounds hσ hN ha hs).2
  rw [logDeriv_apply, factor_deriv hn0, div_eq_mul_inv, norm_mul, norm_mul,
    ← Complex.ofReal_log hn0.le, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have hterm : ‖a*(N : ℂ)^(-s)‖ ≤ 1 := ht.trans hδ
  calc
    _ ≤ (1*Real.log N)*localBound σ := by gcongr
    _ = _ := by ring

theorem factors_logDeriv_norm (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖logDeriv (HeckeFiniteDeletion.factors M ψ) s‖ ≤
      localBound σ * Real.log ((HeckeDeletionBounds.radical M).absNorm : ℝ) := by
  have hp0 (P : HeckeIdealSeries.PrimeIdeal) : 0 < (P.val.absNorm : ℝ) := by
    have h := HeckeIdealSeries.prime_norm_two_le P
    exact_mod_cast (by omega : 0 < P.val.absNorm)
  have hp2 (P : HeckeIdealSeries.PrimeIdeal) : 2 ≤ (P.val.absNorm : ℝ) := by
    exact_mod_cast HeckeIdealSeries.prime_norm_two_le P
  have he : logDeriv (HeckeFiniteDeletion.factors M ψ) s =
      ∑ P ∈ HeckeIdealSeries.primeSet M,
        logDeriv (EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val)) s := by
    apply logDeriv_prod
    · intro P _
      exact EulerFactors.factor_ne_zero (by linarith [hp2 P]) (idealCoeff_norm_le_one ψ P.val)
        (hσ.trans_le hs)
    · intro P _
      exact EulerFactors.differentiable_factor (hp0 P) _ s
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ P ∈ HeckeIdealSeries.primeSet M, localBound σ*Real.log (P.val.absNorm : ℝ) := by
      apply Finset.sum_le_sum
      intro P _
      exact factor_logDeriv_norm hσ (hp2 P) (idealCoeff_norm_le_one ψ P.val) hs
    _ = localBound σ * Real.log ((HeckeDeletionBounds.radical M).absNorm : ℝ) := by
      rw [← Finset.mul_sum, ← Real.log_prod (fun P _ => (hp0 P).ne')]
      simp only [HeckeDeletionBounds.radical, HeckeIdealSeries.primeProduct, map_prod, Nat.cast_prod]

end HeckeDeletionDerivative

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace HeckePrimeDyadic
open HeckeFamily HeckeDyadic


def coefficient (χ : Character) (I : Ideal O) : ℂ :=
  (IdealMangoldt.value I : ℂ) * idealCoeff χ I

@[simp] theorem coefficient_zero (χ : Character) : coefficient χ 0 = 0 := by
  unfold coefficient
  rw [IdealMangoldt.value_zero, Complex.ofReal_zero, zero_mul]

def series (χ : Character) (s : ℂ) : ℂ := -deriv (LFunction χ) s / LFunction χ s

theorem series_eq_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    series χ s = ∑' I : NonzeroIdeal, coefficient χ I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, (IdealMangoldt.value I.val : ℂ) *
      IdealEuler.weighted (idealCoeff χ) s I.val) =
      ∑' I : Ideal O, (IdealMangoldt.value I : ℂ) * IdealEuler.weighted (idealCoeff χ) s I := by
    apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => (IdealMangoldt.value I : ℂ) * IdealEuler.weighted (idealCoeff χ) s I)
    intro I hI hi
    subst I
    exact hI (by
      change (IdealMangoldt.value 0 : ℂ) * IdealEuler.weighted (idealCoeff χ) s 0 = 0
      rw [IdealMangoldt.value_zero, Complex.ofReal_zero, zero_mul])
  change -deriv (LFunction χ) s / LFunction χ s = _
  rw [← HeckeLogDerivative.coeff_LSeries_eq χ hs]
  change LSeries (IdealLogDerivative.coeff (idealCoeff χ)) s = _
  rw [← IdealLogDerivative.mangoldt_series_eq_LSeries _ (idealCoeff_norm_le_one χ) s hs, ← he]
  apply tsum_congr
  intro I
  simp only [coefficient, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, fullIdealWeight]
  rw [if_neg I.property]
  simp only [HeckeDyadic.norm, Complex.ofReal_natCast, mul_assoc]

def twistedCoefficient (χ : Character) (σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ I.val * (norm I : ℂ)^(-shift σ freq)

theorem twisted_coefficient_summable (χ : Character) (c σ freq : ℝ)
    (hc : 1 < c+σ) :
    Summable (fun I : NonzeroIdeal => ‖twistedCoefficient χ σ freq I‖*(norm I)^(-c)) := by
  have hf := (IdealLogDerivative.mangoldt_weighted_summable_norm
    (idealCoeff χ) (idealCoeff_norm_le_one χ) ((c+σ : ℝ) : ℂ)
    (by simpa using hc)).comp_injective (Subtype.val_injective : Function.Injective
      (fun I : NonzeroIdeal => I.val))
  apply hf.congr
  intro I
  symm
  simp only [Function.comp_apply, twistedCoefficient, coefficient, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, fullIdealWeight,
    if_neg I.property, norm_mul]
  change (‖(IdealMangoldt.value I.val : ℂ)‖ * ‖idealCoeff χ I.val‖ *
      ‖(norm I : ℂ)^(-shift σ freq)‖) * (norm I)^(-c) =
    ‖(IdealMangoldt.value I.val : ℂ)‖ * (‖idealCoeff χ I.val‖ *
      ‖(norm I : ℂ)^(-((c+σ : ℝ) : ℂ))‖)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I),
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp only [Complex.neg_re, shift_re, Complex.ofReal_re]
  rw [mul_assoc, mul_assoc, ← Real.rpow_add (norm_pos I)]
  congr 3
  ring

def summand (χ : Character) (W : ℝ → ℂ) (D σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ I.val * W (norm I/D) * ((norm I/D : ℝ) : ℂ)^(-shift σ freq)

def polynomial (χ : Character) (W : ℝ → ℂ) (D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) * ∑' I : NonzeroIdeal, summand χ W D σ freq I

theorem twisted_series_eq (χ : Character) (σ freq : ℝ)
    {s : ℂ} (hs : 1 < (s+shift σ freq).re) :
    (∑' I : NonzeroIdeal, twistedCoefficient χ σ freq I*(norm I : ℂ)^(-s)) =
      series χ (s+shift σ freq) := by
  rw [series_eq_tsum χ hs]
  apply tsum_congr
  intro I
  unfold twistedCoefficient
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_pos I).ne')]
  congr 2
  ring

theorem polynomial_eq_weighted (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0 < D) :
    polynomial χ W D σ freq =
      (D : ℂ)^(shift σ freq-(1/2 : ℂ)) *
        ∑' I : NonzeroIdeal, twistedCoefficient χ σ freq I * W (norm I/D) := by
  have he (I : NonzeroIdeal) : summand χ W D σ freq I =
      (D : ℂ)^(shift σ freq) * (twistedCoefficient χ σ freq I * W (norm I/D)) := by
    unfold summand twistedCoefficient
    rw [positive_quotient_cpow_neg _ _ (norm_pos I) hD]
    ring
  unfold polynomial
  simp_rw [he]
  rw [tsum_mul_left, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 2
  ring

theorem polynomial_mellin (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hWs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (D c σ freq : ℝ) (hD : 0 < D) (hc : 1 < c+σ) :
    polynomial χ W D σ freq = (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
      mellin W ((c : ℂ)+t*Complex.I) *
        (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) *
          series χ (((c : ℂ)+t*Complex.I)+shift σ freq) := by
  rw [polynomial_eq_weighted χ W D σ freq hD]
  rw [weightedMellin_inversion norm norm_pos
    (twistedCoefficient χ σ freq) c (twisted_coefficient_summable χ c σ freq hc)
    W a b ha hWs hW D hD]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [twisted_series_eq χ σ freq (by simpa using hc)]
  have he : (D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I) =
      (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
    congr 1
    ring
  calc
    _ = mellin W ((c : ℂ)+t*Complex.I) *
        ((D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I)) *
          series χ (((c : ℂ)+t*Complex.I)+shift σ freq) := by ring
    _ = _ := by rw [he]

end HeckePrimeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
namespace HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def eulerBound (b : ℝ) : ℝ :=
  ∑' I : NonzeroIdeal, IdealMangoldt.value I.val * (norm I)^(-b)

theorem eulerBound_summable {b : ℝ} (hb : 1< b) :
    Summable (fun I : NonzeroIdeal => IdealMangoldt.value I.val * (norm I)^(-b)) := by
  have ha (I : Ideal O) : ‖IdealEuler.normWeight 0 I‖ ≤ 1 := by
    change ‖fullIdealWeight 0 I‖ ≤ 1
    by_cases hI : I = 0
    · rw [fullIdealWeight, if_pos hI, norm_zero]
      norm_num
    · rw [fullIdealWeight, if_neg hI]
      simp
  have hf := (IdealLogDerivative.mangoldt_weighted_summable_norm
    (IdealEuler.normWeight 0) ha (b : ℂ) (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NonzeroIdeal => I.val))
  apply hf.congr
  intro I
  symm
  simp only [Function.comp_apply, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, fullIdealWeight,
    if_neg I.property, neg_zero, Complex.cpow_zero, one_mul]
  change IdealMangoldt.value I.val * (norm I)^(-b) =
    ‖(IdealMangoldt.value I.val : ℂ) * (norm I : ℂ)^(-(b : ℂ))‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp

theorem series_norm_le (χ : Character) {b : ℝ} (hb : 1< b)
    {s : ℂ} (hs : b≤ s.re) : ‖series χ s‖ ≤ eulerBound b := by
  rw [series_eq_tsum χ (hb.trans_le hs)]
  have hbound (I : NonzeroIdeal) :
      ‖coefficient χ I.val * (norm I : ℂ)^(-s)‖ ≤
        IdealMangoldt.value I.val * (norm I)^(-b) := by
    rw [norm_mul]
    have hn : 1 ≤ norm I := by
      unfold HeckeDyadic.norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hc : ‖coefficient χ I.val‖ ≤ IdealMangoldt.value I.val := by
      rw [coefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (IdealMangoldt.value_nonneg _)]
      exact mul_le_of_le_one_right (IdealMangoldt.value_nonneg _) (idealCoeff_norm_le_one χ _)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re]
    exact mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))
      (Real.rpow_nonneg (norm_pos I).le _) (IdealMangoldt.value_nonneg _)

  have hf := (eulerBound_summable hb).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact (norm_tsum_le_tsum_norm hf).trans (hf.tsum_le_tsum hbound (eulerBound_summable hb))

end HeckePrimeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def integrand (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+HeckeDyadic.shift σ freq-(1/2 : ℂ)) *
    series χ (s+HeckeDyadic.shift σ freq)

theorem series_differentiableAt_nonprincipal (χ : Character) (hχ : χ.residue≠1)
    {s : ℂ} (hz : LFunction χ s≠0) : DifferentiableAt ℂ (series χ) s := by
  have h := (LFunction_entire_nonprincipal χ hχ).analyticAt s
  exact (h.deriv.neg.div h hz).differentiableAt

theorem series_differentiableAt_right (χ : Character) {s : ℂ}
    (hs : 1< s.re) : DifferentiableAt ℂ (series χ) s := by
  have ha : AnalyticAt ℂ (LFunction χ) s := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (isOpen_lt continuous_const Complex.continuous_re)).2 ?_ s hs
    intro z hz
    exact (LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hz) (Or.inl (by intro h; norm_num [h] at hz))).differentiableWithinAt
  exact (ha.deriv.neg.div ha (LFunction_ne_zero_of_one_lt_re χ hs)).differentiableAt

theorem integrand_differentiableAt (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0< a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0< D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (series χ) (s+HeckeDyadic.shift σ freq)) :
    DifferentiableAt ℂ (integrand χ W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (HeckeDyadic.shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (HeckeDyadic.shift σ freq))

theorem integrand_norm (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0< D) (s : ℂ) :
    ‖integrand χ W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ (s+HeckeDyadic.shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem integrand_vertical_integrable (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0< a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0< D) (hc : 1< c+σ) :
    Integrable (fun t : ℝ => integrand χ W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => integrand χ W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (integrand_differentiableAt χ W a b ha hWs hW D σ freq hD
      (series_differentiableAt_right χ (by simpa using hc))).continuousAt.comp
    fun_prop
  have hm := (compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*eulerBound (c+σ))).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [integrand_norm χ W D σ freq hD]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (series_norm_le χ hc (by simp))
  positivity

theorem finite_rectangle (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0< a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0< D)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+HeckeDyadic.shift σ freq)≠0) :
    (∫ t : ℝ in -T..T, integrand χ W D σ freq ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I))) := by
  have hhol : DifferentiableOn ℂ (integrand χ W D σ freq)
      (uIcc l r ×ℂ uIcc (-T) T) := by
    intro s hs
    exact (integrand_differentiableAt χ W a b ha hWs hW D σ freq hD
      (series_differentiableAt_nonprincipal χ hχ (hz s hs))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand χ W D σ freq) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, integrand χ W D σ freq ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem polynomial_finite_shift (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0< a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0< D) (hr : 1< r+σ) (hT : 0≤ T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+HeckeDyadic.shift σ freq)≠0) :
    polynomial χ W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ W D σ freq ((r : ℂ)+t*I)) = _
  rw [← integral_add_compl measurableSet_Icc
    (integrand_vertical_integrable χ W a b ha hWs hW D r σ freq hD hr)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T≤ T)]
  rw [finite_rectangle χ hχ W a b ha hWs hW D σ freq l r T hD hz]

end HeckePrimeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Set Metric Complex
namespace HeckePrimeDyadicControl
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

theorem logDeriv_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (hψs : LFunction ψ s ≠ 0) :
    logDeriv (LFunction χ) s = logDeriv (LFunction ψ) s +
      logDeriv (factors χ.modulus ψ) s := by
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have heq : LFunction χ =ᶠ[nhds s] (fun z => LFunction ψ z * factors χ.modulus ψ z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hz
  have hd : logDeriv (LFunction χ) s =
      logDeriv (fun z => LFunction ψ z * factors χ.modulus ψ z) s :=
    (heq.deriv.div heq).self_of_nhds
  rw [hd]
  exact logDeriv_mul s hψs (factors_ne_zero _ _ hs)
    (LFunction_entire_nonprincipal ψ hψ s) (factors_differentiable _ _ s)

theorem original_disk_control (e : ℝ) (he : 0< e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤ B ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ a t : ℝ,
      1/2≤ a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖logDeriv (LFunction χ) z‖ ≤ B*Real.log (complexity χ t) +
          localBound (1/2)*Real.log ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) := by
  obtain ⟨Dp,B,_,hB,hprimitive⟩ := HeckeLogarithmicActual.disk_control e 1 he he' (by norm_num)
  refine ⟨B,hB,?_⟩
  intro χ hχ a t ha ha' hzero z hz
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have hregular : regular ψ = LFunction ψ := regular_eq_nonprincipal ψ hψ
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    rw [hregular]
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hwp, hh, zero_mul]
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).2 z hz
  rw [hregular] at hbound
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := HeckeDeletionDerivative.factors_logDeriv_norm (1/2) (by norm_num)
    χ.modulus ψ hzre
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 < complexity ψ t := (Real.exp_pos 1).trans_le (complexity_ge_exp ψ t)
  rw [logDeriv_eq_of_mask χ ψ hmask hχ hzpos (by simpa [hregular] using hzeroψ z hz2)]
  apply (norm_add_le _ _).trans
  exact add_le_add (hbound.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hc0 hQ) hB)) hdel

theorem buffered_original_control (e : ℝ) (he : 0< e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤ B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e →
      ∀ (j : ι) (t : ℝ), |t| ≤ (3*i+2 : ℕ)*T →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖logDeriv (LFunction (χ j)) z‖ ≤ B*Real.log (complexity (χ j) t) +
          localBound (1/2)*Real.log ((HeckeDeletionBounds.radical (χ j).modulus).absNorm : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := original_disk_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j t ht z hz
  exact hbound (χ j) (hχ j) a t (by linarith) ha'
    (fun w hw => HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
      hmax j t ht (ball_subset_closedBall hw)) z hz

theorem buffered_rectangle_control (e : ℝ)
    (he : 0< e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤ B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)< a+2*e →
      ∀ (j : ι) (z : ℂ), a+8*e≤ z.re → z.re≤2 →
      |z.im|≤(3*i+2 : ℕ)*T →
      LFunction (χ j) z≠0 ∧
      ‖logDeriv (LFunction (χ j)) z‖≤
        B*Real.log (complexity (χ j) ((3*i+2 : ℕ)*T)) +
          localBound (1/2)*Real.log ((HeckeDeletionBounds.radical (χ j).modulus).absNorm : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := buffered_original_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j z hzl hzr hzi
  have hz6 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-8*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2 : ℂ)+z.im*I)=((z.re-2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : z.re-2≤0)]
    linarith
  have hz2 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-2*e) :=
    closedBall_subset_closedBall (by linarith) hz6
  refine ⟨HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
    hmax j z.im hzi hz2, ?_⟩
  apply (hbound χ hχ T a i hT ha ha' hmax j z.im hzi z hz6).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.log_le_log ((Real.exp_pos 1).trans_le (complexity_ge_exp _ _))
  unfold complexity
  have hH : 0 ≤ (3*i+2 : ℕ)*T := (abs_nonneg z.im).trans hzi
  rw [abs_of_nonneg hH]
  gcongr

end HeckePrimeDyadicControl

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem absolute_tail_bound (χ : Character) (W : ℝ → ℂ)
    (D r σ freq C T : ℝ) (n : ℕ) (hD : 0< D) (hr : 1< r+σ) (hC : 0≤ C) (hT : 0≤ T)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤ C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi := by
  apply rapid_tail_bound _ _ T n
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD.le _))
      (tsum_nonneg (fun I => mul_nonneg (IdealMangoldt.value_nonneg _) (Real.rpow_nonneg (norm_pos I).le _)))
  · exact hT
  · intro t
    rw [integrand_norm χ W D σ freq hD]
    have hb := series_norm_le χ hr (s := (r : ℂ)+t*I+shift σ freq) (by simp)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
      sub_self, add_zero]
    calc
      _ = ((1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖)*D^(r+σ-1/2)*
        ‖series χ ((r : ℂ)+t*I+shift σ freq)‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
        hb (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hD.le _))

theorem central_segment_bound (χ : Character) (W : ℝ → ℂ)
    (D l σ freq C K T : ℝ) (hD : 0< D) (hC : 0≤ C) (hK : 0≤ K) (hT : 0≤ T)
    (hm : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤ C)
    (hs : ∀ t ∈ Icc (-T) T, ‖series χ ((l : ℂ)+t*I+shift σ freq)‖≤ K) :
    ‖∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)‖ ≤
      C*D^(l+σ-1/2)*K*Real.pi := by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤ T)]
  have hint := integrable_inv_one_add_sq.const_mul (C*D^(l+σ-1/2)*K)
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ W D σ freq hD]
      have hb := weighted_two_to_cauchy (norm_nonneg _) t (hm t)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
        sub_self, add_zero]
      calc
        _ ≤ (C/(1+t^2))*D^(l+σ-1/2)*K :=
          mul_le_mul (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hD.le _))
            (hs t ⟨ht.1.le,ht.2⟩) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ ∫ t : ℝ, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem horizontal_join_bound (χ : Character) (W : ℝ → ℂ)
    (D σ freq l r y C K : ℝ) (n : ℕ)
    (hD : 1≤ D) (hlr : l≤ r) (hC : 0≤ C) (_hK : 0≤ K)
    (hm : ∀ x ∈ Icc l r, (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤ C)
    (hs : ∀ x ∈ Icc l r, ‖series χ ((x : ℂ)+y*I+shift σ freq)‖≤ K) :
    ‖∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+y*I)‖ ≤
      (C*D^(r+σ-1/2)*K/(1+|y|)^n)*|r-l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc l r := by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc hx
  have hb : ‖mellin W ((x : ℂ)+y*I)‖≤ C/(1+|y|)^n := by
    apply (le_div_iff₀ (by positivity : 0<(1+|y|)^n)).mpr
    simpa [mul_comm] using hm x hx'
  have hpow : D^(x+σ-1/2)≤ D^(r+σ-1/2) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith [hx'.2])
  rw [integrand_norm χ W D σ freq (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  calc
    _ ≤ (C/(1+|y|)^n)*D^(r+σ-1/2)*K :=
      mul_le_mul (mul_le_mul hb hpow (by positivity) (by positivity))
        (hs x hx') (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem polynomial_bound_of_rectangle (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0< a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤ D) (hlr : l≤ r) (hr : 1< r+σ) (hT : 0≤ T)
    (hC₂ : 0≤ C₂) (hCn : 0≤ Cn) (hK : 0≤ K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤ C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤ Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ (s+shift σ freq)‖≤ K) :
    ‖polynomial χ W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0< D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤ T)] using And.intro hx ht
  have hcentral := central_segment_bound χ W D l σ freq C₂ K T hDp hC₂ hK hT
    hm₂ (fun t ht => hs _ (hmem l t ⟨le_rfl,hlr⟩ ht))
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤ Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

end HeckePrimeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
open Set Metric MeasureTheory Complex
namespace HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeLogarithmic HeckeDeletionBounds

def binCost (B : ℝ) (χ : Character) (H : ℝ) : ℝ :=
  B*Real.log (complexity χ H) + localBound (1/2)*Real.log ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)

theorem binCost_nonneg {B : ℝ} (hB : 0≤ B) (χ : Character) (H : ℝ) : 0≤ binCost B χ H := by
  have hc : 1≤ complexity χ H :=
    (Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans (complexity_ge_exp χ H)
  have hr : (1 : ℝ)≤(HeckeDeletionBounds.radical χ.modulus).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  exact add_nonneg (mul_nonneg hB (Real.log_nonneg hc))
    (mul_nonneg (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le (Real.log_nonneg hr))

theorem polynomial_bound_in_bin (e : ℝ) (he : 0< e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤ B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)< a+2*e →
      ∀ (j : ι) (W : ℝ→ℂ) (α β : ℝ), 0<α → Function.support W⊆Icc α β →
      ContDiff ℝ ∞ W → ∀ D σ freq L C₂ Cn : ℝ, ∀ n : ℕ,
      1≤ D → 0≤ L → 0≤ C₂ → 0≤ Cn → |freq|+L≤(3*i+2 : ℕ)*T →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤ C₂) →
      (∀ x∈Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤ Cn) →
      ‖polynomial (χ j) W D σ freq‖ ≤ (1/(2*Real.pi))*
        (C₂*D^(a+8*e-1/2)*binCost B (χ j) ((3*i+2 : ℕ)*T)*Real.pi +
          2*(Cn*D^(3/2 : ℝ)*binCost B (χ j) ((3*i+2 : ℕ)*T)/(1+L)^n)*|2-a-8*e| +
          (Cn*D^(3/2 : ℝ)*eulerBound 2)/(1+L)^n*Real.pi) := by
  obtain ⟨B,hB,hbound⟩ := HeckePrimeDyadicControl.buffered_rectangle_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W α β hα hWs hW D σ freq L C₂ Cn n
    hD hL hC₂ hCn hfreq hm₂ hmn
  have hlr : a+8*e-σ≤2-σ := by linarith
  have hmem (s : ℂ) (hs : s ∈ (uIcc (a+8*e-σ) (2-σ) ×ℂ uIcc (-L) L)) :
      a+8*e≤(s+HeckeDyadic.shift σ freq).re ∧ (s+HeckeDyadic.shift σ freq).re≤2 ∧
        |(s+HeckeDyadic.shift σ freq).im|≤(3*i+2 : ℕ)*T := by
    convert HeckeDyadic.translated_rectangle_mem (a := a+2*e) (e := e)
      (by linarith) (by linarith) hlr hL hfreq hs using 1 ; ring_nf
  have hs (s : ℂ) (hs : s ∈ (uIcc (a+8*e-σ) (2-σ) ×ℂ uIcc (-L) L)) :=
    hbound χ hχ T a i hT ha ha' hmax j (s+HeckeDyadic.shift σ freq)
      (hmem s hs).1 (hmem s hs).2.1 (hmem s hs).2.2
  have hh := polynomial_bound_of_rectangle (χ j) (hχ j) W α β hα hWs hW
    D σ freq (a+8*e-σ) (2-σ) L C₂ Cn (binCost B (χ j) ((3*i+2 : ℕ)*T)) n
    hD hlr (by linarith) hL hC₂ hCn (binCost_nonneg hB _ _)
    hm₂ hmn (fun s h => (hs s h).1) (fun s h => by
      simpa only [series, neg_div, norm_neg, logDeriv_apply, binCost] using (hs s h).2)
  convert hh using 1 <;> first | rfl | (congr 1; ring_nf)

end HeckePrimeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds HeckeLogarithmic

theorem binCost_le_log (χ : Character) (B U H η : ℝ)
    (hB : 0≤ B) (hU : 2≤ U) (hQ : (χ.modulus.absNorm : ℝ)≤ U)
    (hheight : (3+|H|)^2≤ U^η) :
    binCost B χ H ≤ (B*(2+η)+localBound (1/2))*Real.log U := by
  have hUp : 0< U := by linarith
  have hcp : 0< complexity χ H := (Real.exp_pos 1).trans_le (complexity_ge_exp χ H)
  have hcomplex : complexity χ H ≤ 2*U^(1+η) := by
    unfold complexity
    calc
      2*(χ.modulus.absNorm : ℝ)*(3+|H|)^2 ≤ 2*U*U^η := by gcongr
      _ = _ := by rw [Real.rpow_add hUp, Real.rpow_one]; ring
  have hlog : Real.log (complexity χ H) ≤ (2+η)*Real.log U := by
    apply (Real.log_le_log hcp hcomplex).trans
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hUp _).ne', Real.log_rpow hUp]
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ)<2) hU
    nlinarith
  have hrad : 0<((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  have hrlog := Real.log_le_log hrad ((radical_norm_le_modulus χ).trans hQ)
  unfold binCost
  calc
    _ ≤ B*((2+η)*Real.log U)+localBound (1/2)*Real.log U :=
      add_le_add (mul_le_mul_of_nonneg_left hlog hB)
        (mul_le_mul_of_nonneg_left hrlog (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le)
    _ = _ := by ring

theorem binCost_le_power (χ : Character) (B U H η ε : ℝ)
    (hB : 0≤ B) (hU : 2≤ U) (hQ : (χ.modulus.absNorm : ℝ)≤ U)
    (hη : 0≤η) (hε : 0<ε) (hheight : (3+|H|)^2≤ U^η) :
    binCost B χ H ≤ ((B*(2+η)+localBound (1/2))/ε)*U^ε := by
  apply (binCost_le_log χ B U H η hB hU hQ hheight).trans
  have hc : 0≤ B*(2+η)+localBound (1/2) := by
    exact add_nonneg (mul_nonneg hB (by linarith))
      (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_rpow_div (by linarith : 0≤ U) hε) hc
  convert hh using 1 <;> first | rfl | ring

end HeckePrimeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds

theorem scaled_direct_bound (e κ η : ℝ) (he : 0< e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) :
    ∃ C : ℝ, 0< C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)< a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0< A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R σ freq V C₂ Cn : ℝ) (n : ℕ),
      2≤ U → (χ j).modulus.absNorm≤ U → 0≤ r → r≤ R → 0≤ V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^2≤ U^η → 0≤ C₂ → 0≤ Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤ C₂) →
      (∀ x ∈ Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤ Cn) →
      ‖polynomial (χ j) W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2+8*e)*r+κ)+C*Cn*U^(2*R+κ)/(1+V)^n := by
  obtain ⟨B,hB,hbound⟩ := polynomial_bound_in_bin e he he'
  let Cb := (B*(2+η)+localBound (1/2))/κ
  have hCb : 0< Cb := div_pos
    (add_pos_of_nonneg_of_pos (mul_nonneg hB (by linarith))
      (localBound_pos (by norm_num : (0 : ℝ)<1/2))) hκ
  let E := eulerBound 2
  have hE : 0≤ E := tsum_nonneg (fun I => mul_nonneg (IdealMangoldt.value_nonneg _) (Real.rpow_nonneg (norm_pos I).le _))
  let C := 1+Cb*Real.pi+4*Cb+E*Real.pi
  have hC : 0< C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B' hA hWs hW
    U r R σ freq V C₂ Cn n hU2 hQ hr hrR hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤ H := by dsimp [H]; positivity
  have hU : 1≤ U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0< U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤ U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j W A B' hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hC₂ hCn hfreq hm₂ hmn
  have hcost : binCost B (χ j) H ≤ Cb*U^κ :=
    binCost_le_power (χ j) B U H η κ hB hU2 hQ hη hκ (by rw [abs_of_nonneg hH]; exact hheight)
  have hcentral : (U^r)^(a+8*e-1/2)*binCost B (χ j) H ≤
      Cb*U^((a-1/2+8*e)*r+κ) := by
    calc
      _ ≤ (U^r)^(a+8*e-1/2)*(Cb*U^κ) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _)
      _ = _ := by rw [←Real.rpow_mul hUp.le, mul_left_comm, ←Real.rpow_add hUp]; congr 2; ring
  have hexternal : (U^r)^(3/2 : ℝ)*binCost B (χ j) H ≤ Cb*U^(2*R+κ) := by
    calc
      _ ≤ (U^r)^(3/2 : ℝ)*(Cb*U^κ) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _)
      _ = Cb*U^(r*(3/2)+κ) := by rw [←Real.rpow_mul hUp.le, mul_left_comm, ←Real.rpow_add hUp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)) hCb.le
  have hpow : (U^r)^(3/2 : ℝ)≤ U^(2*R+κ) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |2-a-8*e|≤2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hc : C₂*(U^r)^(a+8*e-1/2)*binCost B (χ j) H*Real.pi≤
      (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ) := by
    calc
      _ = (C₂*Real.pi)*((U^r)^(a+8*e-1/2)*binCost B (χ j) H) := by ring
      _ ≤ (C₂*Real.pi)*(Cb*U^((a-1/2+8*e)*r+κ)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*binCost B (χ j) H/(1+V)^n)*|2-a-8*e|≤
      (4*Cb)*Cn*U^(2*R+κ)/(1+V)^n := by
    calc
      _ = 2*Cn*((U^r)^(3/2 : ℝ)*binCost B (χ j) H)/(1+V)^n*|2-a-8*e| := by ring
      _ ≤ 2*Cn*(Cb*U^(2*R+κ))/(1+V)^n*2 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+κ)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤ binCost B (χ j) H := binCost_nonneg hB _ _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : Cb*Real.pi≤ C := by dsimp [C]; nlinarith only [hCb, mul_nonneg hE Real.pi_pos.le]
  have heC : 4*Cb+E*Real.pi≤ C := by dsimp [C]; nlinarith only [mul_nonneg hCb.le Real.pi_pos.le]
  calc
    _ ≤ (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ)+
        (4*Cb)*Cn*U^(2*R+κ)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ)+
        (4*Cb+E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end HeckePrimeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckePrimePowers
open HeckeFamily UniqueFactorizationMonoid

theorem nonprime_primePow_powerful {I : Ideal O} (hpow : IsPrimePow I) (hprime : ¬Prime I) :
    CompletedGauss.PowerfulIdeal I := by
  obtain ⟨P,k,hP,hk,rfl⟩ := hpow
  have hk2 : 2≤ k := by
    by_contra h
    have hk1 : k=1 := by omega
    subst k
    exact hprime (by simpa using hP)
  refine ⟨pow_ne_zero _ hP.ne_zero,?_⟩
  intro Q hQ
  rw [hP.irreducible.normalizedFactors_pow] at hQ ⊢
  have hQP := (Multiset.mem_replicate.mp hQ).2
  subst Q
  simpa using hk2

def logWeight (I : Ideal O) : ℝ := IdealMangoldt.value I / Real.log (Ideal.absNorm I)

theorem logWeight_nonneg (I : Ideal O) : 0≤ logWeight I :=
  div_nonneg (IdealMangoldt.value_nonneg _) (Real.log_natCast_nonneg _)

theorem logWeight_le_one (I : Ideal O) : logWeight I≤1 := by
  by_cases hlog : Real.log (Ideal.absNorm I)=0
  · simp [logWeight,hlog]
  · apply (div_le_one (lt_of_le_of_ne (Real.log_natCast_nonneg _) (Ne.symm hlog))).mpr
    exact IdealLogDerivative.value_le_log_norm I

theorem logWeight_prime {P : Ideal O} (hP : Prime P) : logWeight P=1 := by
  have hp2 : (2 : ℝ)≤ P.absNorm := by
    exact_mod_cast HeckeIdealSeries.prime_norm_two_le ⟨P,hP⟩
  have hp : 0< Real.log (P.absNorm : ℝ) := Real.log_pos (by linarith)
  rw [logWeight, PNT.IdealPrimeMass.value_prime hP, div_self hp.ne']

theorem logWeight_eq_zero {I : Ideal O} (hI : ¬IsPrimePow I) : logWeight I=0 := by
  simp only [logWeight, IdealMangoldt.value, if_neg hI, zero_div]

theorem sum_prime_extraction (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
      (∑ I∈S.filter Prime, idealCoeff χ I*f I) =
      ∑ I∈S.filter (fun I => IsPrimePow I ∧ ¬Prime I),
        (logWeight I : ℂ)*idealCoeff χ I*f I := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hP : Prime I
  · simp only [hP, ite_true, not_true_eq_false, and_false, ite_false,
      logWeight_prime hP, Complex.ofReal_one, one_mul, sub_self]
  · by_cases hp : IsPrimePow I
    · simp [hP,hp]
    · simp [hP,hp,logWeight_eq_zero hp]

theorem prime_extraction_error (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ ∀ (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ)
      (X B : ℝ), 1≤ X → 0≤ B →
      (∀ I∈S, (I.absNorm : ℝ)≤ X) → (∀ I∈S, ‖f I‖≤ B) →
      ‖(∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
        (∑ I∈S.filter Prime, idealCoeff χ I*f I)‖ ≤ C*X^(1/2+ε)*B := by
  obtain ⟨C,hC,hcount⟩ := CompletedGauss.powerful_ideal_count ε hε
  refine ⟨C,hC,?_⟩
  intro χ S f X B hX hB hnorm hf
  rw [sum_prime_extraction]
  let A := S.filter (fun I => IsPrimePow I ∧ ¬Prime I)
  have hA : (A.card : ℝ)≤ C*X^(1/2+ε) := by
    apply hcount A X hX
    intro I hI
    obtain ⟨hIS,hpow,hprime⟩ := Finset.mem_filter.mp hI
    exact ⟨nonprime_primePow_powerful hpow hprime,hnorm I hIS⟩
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _I∈A, B := by
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (logWeight_nonneg _)]
      have hcoeff : logWeight I*‖idealCoeff χ I‖≤1 :=
        (mul_le_of_le_one_right (logWeight_nonneg I) (idealCoeff_norm_le_one χ I)).trans
          (logWeight_le_one I)
      exact (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans
        (by simpa using hf I (Finset.mem_filter.mp hI).1)
    _ = (A.card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hA hB

end HeckePrimePowers

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open Filter
open scoped Topology
namespace HeckePrimeScale
open HeckeFamily

theorem log_scale_eventually (dmin rmin K : ℝ) (hd : 0< dmin) (hr : 0< rmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r : ℝ, dmin≤ d → rmin≤ r →
      K≤ Real.log ((Z^d)^r) := by
  have hlog : ∀ᶠ Z : ℝ in atTop, max 0 (K/(dmin*rmin))≤ Real.log Z :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlog,eventually_ge_atTop (1 : ℝ)] with Z hlog hZ
  intro d r hd' hr'
  have hZp : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  rw [Real.log_rpow (Real.rpow_pos_of_pos hZp _),Real.log_rpow hZp]
  have hp : 0< dmin*rmin := mul_pos hd hr
  have hk : K≤ dmin*rmin*Real.log Z := by
    have hh := (div_le_iff₀ hp).mp ((le_max_right 0 _).trans hlog)
    nlinarith
  have hprod : dmin*rmin≤ d*r := mul_le_mul hd' hr' hr.le (hd.trans_le hd').le
  have hl : 0≤ Real.log Z := (le_max_left _ _).trans hlog
  nlinarith [mul_le_mul_of_nonneg_right hprod hl]

theorem product_modulus_bound (χ ψ : Character) :
    (χ.product ψ).modulus.absNorm≤χ.modulus.absNorm*ψ.modulus.absNorm := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  exact FiniteConductor.absNorm_inf_le_mul χ.modulus ψ.modulus

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem twisted_modulus_bound (χ : Character) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤χ.modulus.absNorm*M.absNorm :=
  product_modulus_bound χ (HeckeRayQuotient.character M H hH θ)

theorem twisted_row_modulus_bound (χ : Character) (m u : O)
    (hχ : χ.modulus.absNorm≤ HeckeRowClosure.rowConductorBound (HeckeRayFamily.character M 1) m 1 u)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤
      M.absNorm^2*(Ideal.span {m}).absNorm*(Ideal.span {(72 : O)}).absNorm*(Ideal.span {u}).absNorm := by
  apply (twisted_modulus_bound M H hH χ θ).trans
  have hn := Nat.mul_le_mul_right M.absNorm hχ
  simpa [HeckeRowClosure.rowConductorBound,HeckeRayFamily.character,
    Character.ofResidue,pow_two,mul_assoc,mul_left_comm,mul_comm] using hn

end HeckePrimeScale

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
