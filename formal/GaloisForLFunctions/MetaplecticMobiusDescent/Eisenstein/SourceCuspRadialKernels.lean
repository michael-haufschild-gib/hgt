/-
Radial kernels of the source cusps adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.SourceCuspData

/-!
# Radial kernels of the source cusps

Every nonzero source frequency factors as unit, ramified power, squarefree part and cube.
The radial cusp coefficients `sourceCuspRadialCoefficient` and the full theta index give the
radial Bessel profile `radialBesselProfile` of each cusp family.
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

def finiteTwistCusp (c : O) (hc : c ≠ 0) (h : O ⧸ Ideal.span {c}) : SourceCuspDatum :=
  rationalSourceCusp (-3 * Quotient.out h) c hc

lemma finiteTwistCusp_point (c : O) (hc : c ≠ 0) (h : O ⧸ Ideal.span {c}) :
    (finiteTwistCusp c hc h).point = thetaFourierTranslation c h := by
  rw [finiteTwistCusp, rationalSourceCusp_point, thetaFourierTranslation]
  simp only [map_mul, map_neg, map_ofNat]

/-- Every finite twist reflects into the three actual cusp profiles with exact weights. -/
theorem traceTwistedBarProfile_reflection (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {c})] (φ : (O ⧸ Ideal.span {c}) → ℂ)
    (v : ℝ) (hv : 0 < v) :
    traceTwistedBarProfile c hc φ v =
      ∑ h, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ h *
        ((finiteTwistCusp c hc h).multiplier / (v : ℂ) ^ 2 *
          sourceCuspZFamily (finiteTwistCusp c hc h).index (finiteTwistCusp c hc h).dualPoint
            (((finiteTwistCusp c hc h).heightScale * v)⁻¹)) := by
  unfold traceTwistedBarProfile
  apply Finset.sum_congr rfl
  intro h hh
  rw [← finiteTwistCusp_point c hc h, (finiteTwistCusp c hc h).reflection v hv]

/-- Factoring the ramified prime leaves a unit times a primary ideal generator. -/
lemma exists_unit_lambda_primary_factor (h : O) (hh : h ≠ 0) :
    ∃ (u : Oˣ) (m : ℕ) (I : Ideal O), primaryIdealGenerator I ≠ 0 ∧
      h = ((u : O) * lambda ^ m) * primaryIdealGenerator I := by
  obtain ⟨⟨m, I⟩, he⟩ := lambdaFactorEquiv.surjective
    (⟨Ideal.span {h}, Ideal.span_singleton_eq_bot.not.mpr hh⟩ : NonzeroIdeal)
  have hs : Ideal.span {lambda ^ m * primaryIdealGenerator I.val} = Ideal.span {h} :=
    (lambdaFactor_generator_span m I).trans (congrArg Subtype.val he)
  obtain ⟨x, hx⟩ := Ideal.span_singleton_le_span_singleton.mp hs.ge
  obtain ⟨y, hy⟩ := Ideal.span_singleton_le_span_singleton.mp hs.le
  have hxy : y * x = (1 : O) := by
    apply mul_left_cancel₀ hh
    calc
      h * (y * x) = (lambda ^ m * primaryIdealGenerator I.val) * x := by rw [hy]; ring
      _ = h := hx.symm
      _ = h * 1 := (mul_one h).symm
  let u : Oˣ := ⟨x, y, by simpa only [mul_comm] using hxy, hxy⟩
  refine ⟨u, m, I.val, I.property, ?_⟩
  change h = (x * lambda ^ m) * primaryIdealGenerator I.val
  rw [hx]
  ring

/-- Vanishing at prime exponents congruent to two forces squarefree-times-cube support. -/
lemma ramifiedFunction_valuation_ne_two (F : O → ℂ)
    (hzero : ∀ p : O, Prime p → lambda ^ 2 ∣ p - 1 →
      ∀ h : O, ¬ p ∣ h → ∀ k : ℕ, k % 3 = 2 → F (h * p ^ k) = 0)
    (I P : Ideal O) (hI : primaryIdealGenerator I ≠ 0) (hP : P ∈ normalizedFactors I)
    (u : Oˣ) (m : ℕ) (hF : F (((u : O) * lambda ^ m) * primaryIdealGenerator I) ≠ 0) :
    (normalizedFactors I).count P % 3 ≠ 2 := by
  have hI0 := primaryIdealGenerator_ne_zero_ideal I hI
  have hprime := prime_of_normalized_factor P hP
  let p := primaryIdealPrime P
  have hp0 : p ≠ 0 := primaryIdealPrime_factor_ne_zero I P hI hP
  have hps := primaryIdealPrime_spec P hp0
  have hp : Prime p := primaryIdealPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
  obtain ⟨J, hJ, hnot⟩ := (FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hgen : primaryIdealGenerator I = p ^ (multiplicity P I) * primaryIdealGenerator J := by
    calc
      _ = primaryIdealGenerator (P ^ (multiplicity P I) * J) := congrArg primaryIdealGenerator hJ
      _ = _ := by
        rw [primaryIdealGenerator_mul, primaryIdealGenerator_pow]
        have he : primaryIdealGenerator P = p := by
          rw [← hps.2.2.1, primaryIdealGenerator_span p hp0 hps.2.2.2]
        rw [he]
  have hpd : ¬ p ∣ primaryIdealGenerator J := by
    intro hd
    have hgJ : primaryIdealGenerator J ≠ 0 := by
      intro hz
      exact hI (by rw [hgen, hz, mul_zero])
    apply hnot
    rw [Ideal.dvd_iff_le, ← hps.2.2.1, ← (primaryIdealGenerator_spec J hgJ).1,
      Ideal.span_singleton_le_span_singleton]
    exact hd
  have hbase : ¬ p ∣ ((u : O) * lambda ^ m) * primaryIdealGenerator J := by
    intro hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · exact hp.2.1 ((ramified_primary_coprime u m p hps.2.2.2).of_mul_left_right.symm.isUnit_of_dvd hd)
    · exact hpd hd
  have hcount := multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm : (multiplicity P I) % 3 = 2 := by rwa [hcount]
  apply hF
  rw [hgen, show ((u : O) * lambda ^ m) * (p ^ (multiplicity P I) * primaryIdealGenerator J) =
    (((u : O) * lambda ^ m) * primaryIdealGenerator J) * p ^ (multiplicity P I) by ring]
  exact hzero p hp hps.2.2.2 _ hbase _ hm

theorem ramifiedFunction_squarefree_cube_support (F : O → ℂ)
    (hzero : ∀ p : O, Prime p → lambda ^ 2 ∣ p - 1 →
      ∀ h : O, ¬ p ∣ h → ∀ k : ℕ, k % 3 = 2 → F (h * p ^ k) = 0)
    (h : O) (hh : h ≠ 0) (hF : F h ≠ 0) :
    ∃ (u : Oˣ) (m : ℕ) (I J : Ideal O), Squarefree I ∧
      primaryIdealGenerator I ≠ 0 ∧ primaryIdealGenerator J ≠ 0 ∧
      h = ((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3 := by
  obtain ⟨u, m, T, hT, he⟩ := exists_unit_lambda_primary_factor h hh
  have hFT : F (((u : O) * lambda ^ m) * primaryIdealGenerator T) ≠ 0 := by rwa [← he]
  have hv : ∀ P ∈ normalizedFactors T, (normalizedFactors T).count P % 3 ≠ 2 :=
    fun P hP => ramifiedFunction_valuation_ne_two F hzero T P hT hP u m hFT
  have hparts := thetaParts_mul_cube T (primaryIdealGenerator_ne_zero_ideal T hT) hv
  have hgen : primaryIdealGenerator T = primaryIdealGenerator (thetaSquarefreePart T) *
      (primaryIdealGenerator (thetaCubePart T)) ^ 3 := by
    calc
      _ = primaryIdealGenerator (thetaSquarefreePart T * thetaCubePart T ^ 3) :=
        congrArg primaryIdealGenerator hparts.symm
      _ = _ := by rw [primaryIdealGenerator_mul, primaryIdealGenerator_pow]
  have hA : primaryIdealGenerator (thetaSquarefreePart T) ≠ 0 := by
    intro hz
    exact hT (by rw [hgen, hz, zero_mul])
  have hB : primaryIdealGenerator (thetaCubePart T) ≠ 0 := by
    intro hz
    exact hT (by rw [hgen, hz, zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero])
  refine ⟨u, m, thetaSquarefreePart T, thetaCubePart T, thetaSquarefreePart_squarefree T, hA, hB, ?_⟩
  rw [he, hgen]
  ring

lemma rationalSourceResidualFourierCoefficient_prime_power_vanish (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) (k : ℕ) (hk : k % 3 = 2) :
    rationalSourceResidualFourierCoefficient (h * p ^ k) = 0 := by
  have hh : h ≠ 0 := fun hz => hph (hz ▸ dvd_zero p)
  rw [rationalSourceResidualFourierCoefficient_eq _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)),
    rationalSourceScatteringResidue_prime_power_table p hp hprimary h hph k, hk]
  norm_num

/-- All nonzero source frequencies have a unit, ramified, squarefree, and cube factorization. -/
theorem rationalSourceResidualFourierCoefficient_full_squarefree_cube_support
    (h : O) (hh : h ≠ 0) (hF : rationalSourceResidualFourierCoefficient h ≠ 0) :
    ∃ (u : Oˣ) (m : ℕ) (I J : Ideal O), Squarefree I ∧
      primaryIdealGenerator I ≠ 0 ∧ primaryIdealGenerator J ≠ 0 ∧
      h = ((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3 :=
  ramifiedFunction_squarefree_cube_support rationalSourceResidualFourierCoefficient
    rationalSourceResidualFourierCoefficient_prime_power_vanish h hh hF

theorem unramifiedCubicGaussSeries_lambda_pow (s : ℂ) (h : O) (n : ℕ) :
    unramifiedCubicGaussSeries s (h * lambda ^ n) =
      unramifiedCubicGaussSeries s (h * lambda ^ (n % 3)) := by
  apply tsum_congr
  intro I
  congr 1
  have hp := (primaryIdealGenerator_spec I.val I.property).2
  have hl : IsCoprime lambda (primaryIdealGenerator I.val) :=
    coprime_of_dvd_sub_one lambda _ ((show lambda ∣ lambda ^ 2 from ⟨lambda, by ring⟩).trans hp)
  have he : lambda ^ n = lambda ^ (n % 3) * (lambda ^ (n / 3)) ^ 3 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he, ← mul_assoc]
  exact cubicUnitGaussSum_cube_shift _ _ _ I.property hp hl.symm.pow_right

/-- Ramified powers in the unramified Gauss residue depend only on their exponent modulo three. -/
theorem unramifiedGaussResidue_lambda_pow (h : O) (n : ℕ) :
    unramifiedGaussResidue (h * lambda ^ n) = unramifiedGaussResidue (h * lambda ^ (n % 3)) := by
  have he := unramifiedGaussResidue_of_initial_relation (h * lambda ^ n) (h * lambda ^ (n % 3)) 0
    (fun _ => 1) (fun _ => 0) (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_const)
    continuousAt_const continuousAt_const (fun s _ _ => by
      simpa only [one_mul, zero_mul, add_zero] using unramifiedCubicGaussSeries_lambda_pow s h n)
  simpa only [one_mul, zero_mul, add_zero] using he

section
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

/-- A finite norm bound for all unit twists and ramified powers of one frequency. -/
def ramifiedResidueFamilyMass (h : O) : ℝ :=
  ∑ a : Oˣ × Fin 3, ‖unramifiedGaussResidue (h * (a.1 : O) * lambda ^ a.2.val)‖

lemma ramifiedResidueFamilyMass_nonneg (h : O) : 0 ≤ ramifiedResidueFamilyMass h :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma unramifiedGaussResidue_family_norm_le (h : O) (u : Oˣ) (n : ℕ) :
    ‖unramifiedGaussResidue (h * (u : O) * lambda ^ n)‖ ≤ ramifiedResidueFamilyMass h := by
  rw [unramifiedGaussResidue_lambda_pow]
  exact Finset.single_le_sum (a := (u, ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩))
    (s := Finset.univ) (f := fun a : Oˣ × Fin 3 =>
      ‖unramifiedGaussResidue (h * (a.1 : O) * lambda ^ a.2.val)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ _)

lemma unramifiedGaussResidue_unit_lambda_norm_le (u : Oˣ) (n : ℕ) :
    ‖unramifiedGaussResidue ((u : O) * lambda ^ n)‖ ≤ ramifiedResidueFamilyMass 1 := by
  simpa only [one_mul] using unramifiedGaussResidue_family_norm_le 1 u n

lemma ramifiedResidueFamilyMass_unit_lambda_le (u : Oˣ) (n : ℕ) :
    ramifiedResidueFamilyMass ((u : O) * lambda ^ n) ≤
      (Fintype.card (Oˣ × Fin 3) : ℝ) * ramifiedResidueFamilyMass 1 := by
  calc
    _ ≤ ∑ a : Oˣ × Fin 3, ramifiedResidueFamilyMass 1 := by
      apply Finset.sum_le_sum
      intro a ha
      have he : ((u : O) * lambda ^ n) * (a.1 : O) * lambda ^ a.2.val =
          ((u * a.1 : Oˣ) : O) * lambda ^ (n + a.2.val) := by
        rw [Units.val_mul, pow_add]
        ring
      rw [he]
      exact unramifiedGaussResidue_unit_lambda_norm_le _ _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end

lemma ramifiedNine_eq : (9 : O) = omega * lambda ^ 4 := by
  calc
    (9 : O) = 9 * omega ^ 3 := by rw [omega_primitive.pow_eq_one]; ring
    _ = omega * ((lambda ^ 2) ^ 2) := by rw [lambda_sq_eq]; ring
    _ = omega * lambda ^ 4 := by ring

lemma unramifiedGaussResidue_nine_norm_le (h : O) (u : Oˣ) (n : ℕ) :
    ‖unramifiedGaussResidue (9 * h * ((u : O) * lambda ^ n))‖ ≤ ramifiedResidueFamilyMass h := by
  have he : 9 * h * ((u : O) * lambda ^ n) = h * ((cuspOmegaUnit * u : Oˣ) : O) * lambda ^ (n + 4) := by
    rw [ramifiedNine_eq, Units.val_mul, cuspOmegaUnit_val, pow_add]
    ring
  rw [he]
  exact unramifiedGaussResidue_family_norm_le _ _ _

lemma rationalSourceResidualFourierCoefficient_prime_norm (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    ‖rationalSourceResidualFourierCoefficient (h * p)‖ = ‖rationalSourceResidualFourierCoefficient h‖ := by
  have hp9 := primary_prime_not_dvd_nine_frequency p hp hprimary h hph
  rw [rationalSourceResidualFourierCoefficient_prime_factor p hp hprimary h hph,
    norm_mul, norm_div, primeCubicGauss_two_eq_star p hp hprimary (9 * h) hp9, norm_star,
    cubicUnitGaussSum_prime_norm p hp hprimary (9 * h) hp9, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (ringComplex_ne_zero hp.ne_zero)), one_mul]

lemma primeProduct_norm_of {ι : Type*} (F : O → ℂ)
    (hF : ∀ p : O, Prime p → lambda ^ 2 ∣ p - 1 → ∀ h : O, ¬ p ∣ h → ‖F (h * p)‖ = ‖F h‖)
    (s : Finset ι) (p : ι → O) (hp : ∀ i ∈ s, Prime (p i))
    (hprimary : ∀ i ∈ s, lambda ^ 2 ∣ p i - 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (p i) (p j))
    (h : O) (hph : ∀ i ∈ s, ¬ p i ∣ h) :
    ‖F (h * (∏ i ∈ s, p i))‖ = ‖F h‖ := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, mul_one]
  | @insert i s hi ih =>
    have hpi := hp i (Finset.mem_insert_self _ _)
    have hpri := hprimary i (Finset.mem_insert_self _ _)
    have hc : IsCoprime (p i) (∏ j ∈ s, p j) := IsCoprime.prod_right (fun j hj =>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he; subst j; exact hi hj))
    have hpb : ¬ p i ∣ h * (∏ j ∈ s, p j) := by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd | hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.2.1 (hc.isUnit_of_dvd hd)
    rw [Finset.prod_insert hi, show h * (p i * (∏ j ∈ s, p j)) =
      (h * (∏ j ∈ s, p j)) * p i by ring, hF (p i) hpi hpri _ hpb]
    exact ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj => hprimary j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk hjk => hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj => hph j (Finset.mem_insert_of_mem hj))

/-- Removing the unramified squarefree part preserves coefficient norm; cubes contribute their absolute value. -/
theorem rationalSourceResidualFourierCoefficient_full_squarefree_cube_norm (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I)
    (u : Oˣ) (m : ℕ) :
    ‖rationalSourceResidualFourierCoefficient
      (((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)‖ =
      ‖ringComplex (primaryIdealGenerator J)‖ *
        ‖rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m)‖ := by
  rw [rationalSourceResidualFourierCoefficient_primary_cube _ hJ (primaryIdealGenerator_spec J hJ).2 _
    (mul_ne_zero (ramifiedElement_ne_zero u m) hI), norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  congr 1
  rw [primaryIdealGenerator_squarefree_support I hI hsq]
  apply primeProduct_norm_of rationalSourceResidualFourierCoefficient
    rationalSourceResidualFourierCoefficient_prime_norm
  · exact fun P hP => primaryIdealPrime_isPrime_of_mem I P hI hP
  · exact fun P hP => (primaryIdealPrime_spec P
      (primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  · exact primaryIdealPrime_support_coprime I hI
  · intro P hP hd
    have hp := primaryIdealPrime_isPrime_of_mem I P hI hP
    have hpp := (primaryIdealPrime_spec P
      (primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
    exact hp.2.1 ((ramified_primary_coprime u m _ hpp).of_mul_left_right.symm.isUnit_of_dvd hd)

lemma mellin_finiteLinearCombination {ι : Type*} [Fintype ι]
    (weight : ι → ℂ) (f : ι → ℝ → ℂ) (s : ℂ) (hc : ∀ i, MellinConvergent (f i) s) :
    mellin (fun v => ∑ i, weight i * f i v) s = ∑ i, weight i * mellin (f i) s := by
  have hi (i : ι) : Integrable (fun v : ℝ => (v : ℂ) ^ (s - 1) * (weight i * f i v))
      (volume.restrict (Set.Ioi 0)) := by
    have hh := (hc i).const_smul (weight i)
    simp only [MellinConvergent, smul_eq_mul, IntegrableOn] at hh
    convert! hh using 1
  unfold mellin
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall (fun v => by ring))

/-- Mellin reflection of a finite arithmetic twist, with all dual cusp transforms entire. -/
theorem traceTwistedBarProfile_mellin_reflection (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {c})] (φ : (O ⧸ Ideal.span {c}) → ℂ) (s : ℂ) :
    mellin (traceTwistedBarProfile c hc φ) (2 * s) =
      ∑ h, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ h *
        ((finiteTwistCusp c hc h).multiplier * ((finiteTwistCusp c hc h).heightScale : ℂ) ^ (2 - 2 * s) *
          mellin (sourceCuspZFamily (finiteTwistCusp c hc h).index (finiteTwistCusp c hc h).dualPoint) (2 - 2 * s)) := by
  change mellin (fun v => ∑ h, finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ h *
    cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (thetaFourierTranslation c h) v) (2 * s) = _
  rw [mellin_finiteLinearCombination
    (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) φ)
    (fun h => cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) (thetaFourierTranslation c h))
    (2 * s) (fun h => (conjugateSource_finite_twist_cusp_mellin_entire (Quotient.out h) c hc).1 (2 * s))]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← finiteTwistCusp_point c hc h, (finiteTwistCusp c hc h).mellin_reflection s]

lemma arithmeticResidueSum_ramified_norm_le (h : O) (u : Oˣ) (n : ℕ) (hn : 2 ≤ n) :
    ‖arithmeticResidueSum h ((u : O) * lambda ^ n)‖ ≤ (3 : ℝ) ^ n := by
  by_cases hz : arithmeticResidueSum h ((u : O) * lambda ^ n) = 0
  · rw [hz, norm_zero]
    positivity
  obtain ⟨k, hk⟩ := ramified_arithmetic_support h u n hn hz
  rw [ramified_arithmetic_character_test h k u n hn hk]
  split_ifs
  · rw [norm_mul, Complex.norm_natCast]
    have he : ‖residueAdditive k 3 1‖ = 1 := tracePhase_norm _
    rw [he, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · rw [norm_zero]
    positivity

lemma arithmeticResidueSum_norm_mul_primary (h b : O) (hb : lambda ^ 2 ∣ b - 1)
    (u : Oˣ) (n : ℕ) (hn : 2 ≤ n) :
    ‖arithmeticResidueSum (h * b) ((u : O) * lambda ^ n)‖ =
      ‖arithmeticResidueSum h ((u : O) * lambda ^ n)‖ := by
  have hc : IsCoprime ((u : O) * lambda ^ n) b := (ramified_primary_coprime u n b hb).of_mul_left_right
  have he := congrArg norm (arithmeticResidueSum_frequency_twist h ((u : O) * lambda ^ n) b
    (ramifiedElement_ne_zero u n) (ramifiedElement_level u n hn) ⟨hc, three_dvd_lambda_sq.trans hb⟩)
  simpa only [norm_mul, symbol_norm_one _ b hb hc, one_mul] using he

lemma ramifiedQuotientChar_mk (u : Oˣ) (n : ℕ) (x : O) :
    ramifiedQuotientChar u n (Ideal.Quotient.mk (Ideal.span {(3 : O)}) x) =
      ringComplex (symbol ((u : O) * lambda ^ n) (1 + 3 * x)) :=
  principalQuotientAddChar_mk 3 _ _ x

lemma ramifiedQuotientChar_apply_cube (u : Oˣ) (n : ℕ) (x : O ⧸ Ideal.span {(3 : O)}) :
    (ramifiedQuotientChar u n x) ^ 3 = 1 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [ramifiedQuotientChar_mk, ← map_pow,
    symbol_cube_of_isCoprime _ _ (lambda_sq_dvd_three.trans ⟨x, by ring⟩)
      (ramified_denominator_condition u n (1 + 3 * x) ⟨x, by ring⟩).1, map_one]

/-- Both signs can survive the ramified Fourier test only when the symbol character is trivial. -/
lemma ramifiedQuotientChar_eq_one_of_both_signs (h : O) (u : Oˣ) (n : ℕ) (hn : 2 ≤ n)
    (ha : arithmeticResidueSum h ((u : O) * lambda ^ n) ≠ 0)
    (hb : arithmeticResidueSum h (((-u : Oˣ) : O) * lambda ^ n) ≠ 0) :
    ramifiedQuotientChar u n = 1 := by
  obtain ⟨k, hk⟩ := ramified_arithmetic_support h u n hn ha
  have hk' : 3 * h = (((-u : Oˣ) : O) * lambda ^ n) * (-k) := by
    simp only [Units.val_neg, neg_mul, mul_neg, neg_neg]
    exact hk
  have hpos : ramifiedFrequencyChar k u n = 1 := by
    by_contra hc
    exact ha (by rw [ramified_arithmetic_character_test h k u n hn hk, if_neg hc])
  have hneg : ramifiedFrequencyChar (-k) u n = 1 := by
    by_contra hc
    exact hb (by rw [ramified_arithmetic_character_test h (-k) (-u) n hn hk',
      ramifiedFrequencyChar_neg_unit, if_neg hc])
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hp := congrArg (fun χ : AddChar (O ⧸ Ideal.span {(3 : O)}) ℂ => χ (Ideal.Quotient.mk _ x)) hpos
  have hm := congrArg (fun χ : AddChar (O ⧸ Ideal.span {(3 : O)}) ℂ => χ (Ideal.Quotient.mk _ x)) hneg
  change ramifiedQuotientChar u n (Ideal.Quotient.mk _ x) *
    residueTraceQuotientChar k 3 (by norm_num) (Ideal.Quotient.mk _ x) = 1 at hp
  change ramifiedQuotientChar u n (Ideal.Quotient.mk _ x) *
    residueTraceQuotientChar (-k) 3 (by norm_num) (Ideal.Quotient.mk _ x) = 1 at hm
  rw [residueTraceQuotientChar_three_phase] at hp hm
  rw [cuspFrequency_neg, neg_mul] at hm
  have ht : tracePhase (cuspFrequency k * ringComplex x) * tracePhase (-(cuspFrequency k * ringComplex x)) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  let q := ramifiedQuotientChar u n (Ideal.Quotient.mk (Ideal.span {(3 : O)}) x)
  have hq : q ^ 2 = 1 := by
    calc
      _ = q ^ 2 * (tracePhase (cuspFrequency k * ringComplex x) * tracePhase (-(cuspFrequency k * ringComplex x))) :=
        by rw [ht, mul_one]
      _ = (q * tracePhase (cuspFrequency k * ringComplex x)) *
          (q * tracePhase (-(cuspFrequency k * ringComplex x))) := by ring
      _ = 1 := by rw [hp, hm, one_mul]
  change q = 1
  calc
    q = q ^ 2 * q := by rw [hq, one_mul]
    _ = q ^ 3 := by ring
    _ = 1 := ramifiedQuotientChar_apply_cube u n _

lemma ramifiedQuotientChar_omegaUnit_one (j n : ℕ) :
    ramifiedQuotientChar (cuspOmegaUnit ^ j) n (Ideal.Quotient.mk _ (1 : O)) =
      ringComplex ((omega ^ 2) ^ j * omega ^ n) := by
  have hp : lambda ^ 2 ∣ (1 + 3 * (1 : O)) - 1 := lambda_sq_dvd_three.trans ⟨1, by ring⟩
  have harg : 1 + 3 * (1 : O) = primaryCoord 1 0 := by rw [primaryCoord_eq]; ring
  have ho : symbol omega (1 + 3 * (1 : O)) = omega ^ 2 := by
    rw [symbol_omega_eq_linearRay _ hp]
    rw [harg, linearRay_primaryCoord]
    norm_num [cubicExp]
    rfl
  have hl : symbol lambda (1 + 3 * (1 : O)) = omega := by
    rw [symbol_lambda_eq_linearRay _ hp]
    rw [harg, linearRay_primaryCoord]
    norm_num [cubicExp]
  rw [ramifiedQuotientChar_mk, Units.val_pow_eq_pow_val, cuspOmegaUnit_val,
    symbol_mul_numerator, symbol_pow_numerator _ _ hp,
    symbol_pow_numerator _ _ hp, ho, hl]

lemma ramifiedQuotientChar_omegaUnit_omega (j n : ℕ) :
    ramifiedQuotientChar (cuspOmegaUnit ^ j) n (Ideal.Quotient.mk _ omega) =
      ringComplex ((omega ^ 2) ^ j) := by
  have hp : lambda ^ 2 ∣ (1 + 3 * omega) - 1 := lambda_sq_dvd_three.trans ⟨omega, by ring⟩
  have harg : 1 + 3 * omega = primaryCoord 0 1 := by rw [primaryCoord_eq]; ring
  have ho : symbol omega (1 + 3 * omega) = omega ^ 2 := by
    rw [symbol_omega_eq_linearRay _ hp]
    rw [harg, linearRay_primaryCoord]
    norm_num [cubicExp]
    rfl
  have hl : symbol lambda (1 + 3 * omega) = 1 := by
    rw [symbol_lambda_eq_linearRay _ hp]
    rw [harg, linearRay_primaryCoord]
    norm_num [cubicExp]
  rw [ramifiedQuotientChar_mk, Units.val_pow_eq_pow_val, cuspOmegaUnit_val,
    symbol_mul_numerator, symbol_pow_numerator _ _ hp,
    symbol_pow_numerator _ _ hp, ho, hl, one_pow, mul_one]

/-- The ramified symbol character is trivial only for a real unit and an exponent divisible by three. -/
lemma ramifiedQuotientChar_trivial_exponents (j : Fin 3) (n : ℕ)
    (hchar : ramifiedQuotientChar (cuspOmegaUnit ^ j.val) n = 1) : j = 0 ∧ n % 3 = 0 := by
  have he := congrArg (fun χ : AddChar (O ⧸ Ideal.span {(3 : O)}) ℂ => χ (Ideal.Quotient.mk _ omega)) hchar
  rw [ramifiedQuotientChar_omegaUnit_omega, AddChar.one_apply] at he
  have hpow : (omega ^ 2) ^ j.val = 1 := ringComplex_injective (by simpa only [map_one] using he)
  have hj : j = 0 := by
    fin_cases j
    · rfl
    · have hs : omega ^ 2 = 1 := by simpa only [pow_one] using hpow
      have how : omega = 1 := by
        calc
          omega = omega ^ 2 * omega := by rw [hs, one_mul]
          _ = omega ^ 3 := by ring
          _ = 1 := omega_primitive.pow_eq_one
      exact (omega_primitive.ne_one (by decide) how).elim
    · have how : omega = 1 := by
        rw [show (omega ^ 2) ^ 2 = omega ^ 3 * omega by ring,
          omega_primitive.pow_eq_one, one_mul] at hpow
        exact hpow
      exact (omega_primitive.ne_one (by decide) how).elim
  refine ⟨hj, ?_⟩
  have he1 := congrArg (fun χ : AddChar (O ⧸ Ideal.span {(3 : O)}) ℂ => χ (Ideal.Quotient.mk _ (1 : O))) hchar
  rw [ramifiedQuotientChar_omegaUnit_one, AddChar.one_apply, hj] at he1
  simp only [Fin.val_zero, pow_zero, one_mul] at he1
  have hn : omega ^ n = omega ^ 0 := ringComplex_injective (by simpa only [pow_zero, map_one] using he1)
  have hm := ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mp hn
  rw [← omega_primitive.eq_orderOf] at hm
  simpa only [Nat.zero_mod] using hm

lemma ramifiedQuotientChar_neg_unit (u : Oˣ) (n : ℕ) :
    ramifiedQuotientChar (-u) n = ramifiedQuotientChar u n := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [ramifiedQuotientChar_mk, ramifiedQuotientChar_mk, Units.val_neg, neg_mul,
    symbol_neg_numerator _ _ (lambda_sq_dvd_three.trans ⟨x, by ring⟩)]

lemma ramifiedQuotientChar_two_ne_one (u : Oˣ) : ramifiedQuotientChar u 2 ≠ 1 := by
  obtain ⟨j, hj | hj⟩ := unit_eq_sign_omega u
  · have hu : u = cuspOmegaUnit ^ j.val := Units.ext (by simpa only [Units.val_pow_eq_pow_val, cuspOmegaUnit_val] using hj)
    rw [hu]
    intro hchar
    have hm := (ramifiedQuotientChar_trivial_exponents j 2 hchar).2
    norm_num at hm
  · have hu : u = -(cuspOmegaUnit ^ j.val) := Units.ext (by
      simpa only [Units.val_neg, Units.val_pow_eq_pow_val, cuspOmegaUnit_val] using hj)
    rw [hu, ramifiedQuotientChar_neg_unit]
    intro hchar
    have hm := (ramifiedQuotientChar_trivial_exponents j 2 hchar).2
    norm_num at hm

lemma residueTraceQuotientChar_eq_one_of_three_dvd (k : O) (hk : (3 : O) ∣ k) :
    residueTraceQuotientChar k 3 (by norm_num) = 1 := by
  rw [residueTraceQuotientChar_mulShift]
  have he : Ideal.Quotient.mk (Ideal.span {(3 : O)}) k = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hk)
  rw [he, AddChar.mulShift_zero]

/-- At frequencies divisible by three, the smallest ramified conductor contributes nothing. -/
lemma arithmeticResidueSum_lambda_sq_zero (h : O) (hh : (3 : O) ∣ h) (u : Oˣ) :
    arithmeticResidueSum h ((u : O) * lambda ^ 2) = 0 := by
  by_contra ha
  obtain ⟨k, hk⟩ := ramified_arithmetic_support h u 2 le_rfl ha
  let t : Oˣ := -(u * cuspOmegaUnit)
  have ht : (u : O) * lambda ^ 2 = 3 * (t : O) := by
    simp only [t, lambda_sq_eq, Units.val_neg, Units.val_mul, cuspOmegaUnit_val]
    ring
  rw [ht, mul_assoc] at hk
  have he : h = (t : O) * k := mul_left_cancel₀ (by norm_num : (3 : O) ≠ 0) hk
  have hdk : (3 : O) ∣ k := by
    have hd := dvd_mul_of_dvd_right hh (↑t⁻¹ : O)
    simpa [he, ← mul_assoc] using hd
  have hchar : ramifiedFrequencyChar k u 2 = 1 := by
    by_contra hc
    apply ha
    rw [ramified_arithmetic_character_test h k u 2 le_rfl (by rw [ht, mul_assoc]; exact hk), if_neg hc]
  rw [ramifiedFrequencyChar, residueTraceQuotientChar_eq_one_of_three_dvd k hdk, mul_one] at hchar
  exact ramifiedQuotientChar_two_ne_one u hchar

def lowRamifiedFrequency (a r : Fin 3) : O := omega ^ a.val * lambda ^ (r.val + 2)

lemma lowRamifiedFrequency_ne_zero (a r : Fin 3) : lowRamifiedFrequency a r ≠ 0 := by
  simpa only [lowRamifiedFrequency, Units.val_pow_eq_pow_val, cuspOmegaUnit_val] using
    ramifiedElement_ne_zero (cuspOmegaUnit ^ a.val) (r.val + 2)

lemma lowRamifiedFrequency_absNorm (a r : Fin 3) :
    Ideal.absNorm (Ideal.span {lowRamifiedFrequency a r}) = 3 ^ (r.val + 2) := by
  simpa only [lowRamifiedFrequency, Units.val_pow_eq_pow_val, cuspOmegaUnit_val] using
    ramifiedElement_absNorm (cuspOmegaUnit ^ a.val) (r.val + 2)

lemma lowRamifiedFrequency_three_dvd (a r : Fin 3) : (3 : O) ∣ lowRamifiedFrequency a r := by
  simpa only [lowRamifiedFrequency, Units.val_pow_eq_pow_val, cuspOmegaUnit_val] using
    ramifiedElement_level (cuspOmegaUnit ^ a.val) (r.val + 2) (by omega)

lemma lowRamifiedFrequency_arithmetic_vanish (a r : Fin 3) (u : Oˣ) (k : ℕ) (hk : 5 ≤ k) :
    arithmeticResidueSum (lowRamifiedFrequency a r) ((u : O) * lambda ^ (k + 2)) = 0 := by
  by_contra hA
  have hb := ramified_arithmetic_norm_bound _ (lowRamifiedFrequency_ne_zero a r) u (k + 2) (by omega) hA
  rw [lowRamifiedFrequency_absNorm] at hb
  have hlo : (3 : ℕ) ^ 7 ≤ 3 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hhi : (3 : ℕ) ^ (r.val + 2) ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at hlo hhi
  omega

lemma lowRamifiedFrequency_primary_vanish (a r : Fin 3) (b : O) (hb : lambda ^ 2 ∣ b - 1)
    (u : Oˣ) (k : ℕ) (hk : 5 ≤ k) :
    arithmeticResidueSum (lowRamifiedFrequency a r * b) ((u : O) * lambda ^ (k + 2)) = 0 := by
  apply norm_eq_zero.mp
  rw [arithmeticResidueSum_norm_mul_primary _ b hb u (k + 2) (by omega),
    lowRamifiedFrequency_arithmetic_vanish a r u k hk, norm_zero]

def signedOmegaUnit (p : Bool × Fin 3) : Oˣ :=
  if p.1 then -(cuspOmegaUnit ^ p.2.val) else cuspOmegaUnit ^ p.2.val

lemma omega_pow_fin_injective : Function.Injective (fun j : Fin 3 => omega ^ j.val) := by
  intro j k he
  have hm := ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mp he
  rw [← omega_primitive.eq_orderOf, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt k.isLt] at hm
  exact Fin.ext hm

lemma signedOmegaUnit_injective : Function.Injective signedOmegaUnit := by
  rintro ⟨s, j⟩ ⟨t, k⟩ he
  have hv := congrArg (fun u : Oˣ => (u : O)) he
  cases s <;> cases t
  · simp only [signedOmegaUnit, Bool.false_eq_true, if_false, Units.val_pow_eq_pow_val, cuspOmegaUnit_val] at hv
    exact congrArg (fun i : Fin 3 => (false, i)) (omega_pow_fin_injective hv)
  · simp only [signedOmegaUnit, Bool.false_eq_true, if_false, if_true, Units.val_neg,
      Units.val_pow_eq_pow_val, cuspOmegaUnit_val] at hv
    exact (halfPrimary_not_negative k.val (hv ▸ halfPrimary_omega_pow j.val)).elim
  · simp only [signedOmegaUnit, Bool.false_eq_true, if_false, if_true, Units.val_neg,
      Units.val_pow_eq_pow_val, cuspOmegaUnit_val] at hv
    exact (halfPrimary_not_negative j.val (hv.symm ▸ halfPrimary_omega_pow k.val)).elim
  · simp only [signedOmegaUnit, if_true, Units.val_neg, Units.val_pow_eq_pow_val, cuspOmegaUnit_val] at hv
    exact congrArg (fun i : Fin 3 => (true, i)) (omega_pow_fin_injective (neg_injective hv))

lemma signedOmegaUnit_surjective : Function.Surjective signedOmegaUnit := by
  intro u
  obtain ⟨j, hj | hj⟩ := unit_eq_sign_omega u
  · refine ⟨(false, j), Units.ext ?_⟩
    simpa only [signedOmegaUnit, Bool.false_eq_true, if_false, Units.val_pow_eq_pow_val, cuspOmegaUnit_val] using hj.symm
  · refine ⟨(true, j), Units.ext ?_⟩
    simpa only [signedOmegaUnit, if_true, Units.val_neg, Units.val_pow_eq_pow_val, cuspOmegaUnit_val] using hj.symm

def signedOmegaEquiv : Bool × Fin 3 ≃ Oˣ :=
  Equiv.ofBijective signedOmegaUnit ⟨signedOmegaUnit_injective, signedOmegaUnit_surjective⟩

lemma ramifiedQuotientChar_omegaUnit_ne_one (j : Fin 3) (n : ℕ) (hj : j ≠ 0) :
    ramifiedQuotientChar (cuspOmegaUnit ^ j.val) n ≠ 1 :=
  fun he => hj (ramifiedQuotientChar_trivial_exponents j n he).1

lemma ramifiedQuotientChar_omegaUnit_ne_one_of_mod (j : Fin 3) (n : ℕ) (hn : n % 3 ≠ 0) :
    ramifiedQuotientChar (cuspOmegaUnit ^ j.val) n ≠ 1 :=
  fun he => hn (ramifiedQuotientChar_trivial_exponents j n he).2

lemma arithmeticResidueSum_sign_pair_norm_le (h : O) (u : Oˣ) (n : ℕ) (hn : 2 ≤ n)
    (hchar : ramifiedQuotientChar u n ≠ 1) :
    ‖arithmeticResidueSum h ((u : O) * lambda ^ n)‖ +
      ‖arithmeticResidueSum h (((-u : Oˣ) : O) * lambda ^ n)‖ ≤ (3 : ℝ) ^ n := by
  by_cases ha : arithmeticResidueSum h ((u : O) * lambda ^ n) = 0
  · rw [ha, norm_zero, zero_add]
    exact arithmeticResidueSum_ramified_norm_le h (-u) n hn
  by_cases hb : arithmeticResidueSum h (((-u : Oˣ) : O) * lambda ^ n) = 0
  · rw [hb, norm_zero, add_zero]
    exact arithmeticResidueSum_ramified_norm_le h u n hn
  exact (hchar (ramifiedQuotientChar_eq_one_of_both_signs h u n hn ha hb)).elim

def ramifiedDecayRatio : ℝ := (3 : ℝ) ^ (-(1 / 3 : ℝ))

lemma ramifiedDecayRatio_pos : 0 < ramifiedDecayRatio := Real.rpow_pos_of_pos (by norm_num) _

lemma ramifiedDecayRatio_cube : ramifiedDecayRatio ^ 3 = (1 / 3 : ℝ) := by
  rw [ramifiedDecayRatio, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma ramifiedDecayRatio_le_seven_tenths : ramifiedDecayRatio ≤ 7 / 10 := by
  by_contra hn
  have hh : 7 / 10 < ramifiedDecayRatio := lt_of_not_ge hn
  have hp : 0 < (ramifiedDecayRatio - 7 / 10) *
      (ramifiedDecayRatio ^ 2 + (7 / 10) * ramifiedDecayRatio + 49 / 100) :=
    mul_pos (sub_pos.mpr hh) (by have := ramifiedDecayRatio_pos; positivity)
  nlinarith only [hp, ramifiedDecayRatio_cube]

lemma ramifiedWeight_norm_scalar (n : ℕ) :
    ‖((3 ^ n : ℕ) : ℂ) ^ (-(4 / 3 : ℂ))‖ * (3 : ℝ) ^ n = ramifiedDecayRatio ^ n := by
  have hcast : ((3 ^ n : ℕ) : ℂ) = (((3 : ℝ) ^ n : ℝ) : ℂ) := by norm_cast
  have hp : 0 < (3 : ℝ) ^ n := pow_pos (by norm_num) _
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hp,
    show (-(4 / 3 : ℂ)).re = -(4 / 3 : ℝ) by norm_num]
  calc
    _ = ((3 : ℝ) ^ n) ^ (-(1 / 3 : ℝ)) := by
      nth_rw 2 [← Real.rpow_one ((3 : ℝ) ^ n)]
      rw [← Real.rpow_add hp]
      congr 1
      norm_num
    _ = _ := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3), ramifiedDecayRatio,
        ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 3 : ℝ))) n,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring

def ramifiedRawWeight (h : O) (u : Oˣ) (k : ℕ) : ℂ :=
  ((3 ^ (k + 2) : ℕ) : ℂ) ^ (-(4 / 3 : ℂ)) * arithmeticResidueSum h ((u : O) * lambda ^ (k + 2))

lemma ramifiedRawWeight_norm_le (h : O) (u : Oˣ) (k : ℕ) :
    ‖ramifiedRawWeight h u k‖ ≤ ramifiedDecayRatio ^ (k + 2) := by
  rw [ramifiedRawWeight, norm_mul]
  exact (mul_le_mul_of_nonneg_left (arithmeticResidueSum_ramified_norm_le h u (k + 2) (by omega))
    (norm_nonneg _)).trans_eq (ramifiedWeight_norm_scalar _)

lemma ramifiedRawWeight_sign_pair_norm_le (h : O) (u : Oˣ) (k : ℕ)
    (hchar : ramifiedQuotientChar u (k + 2) ≠ 1) :
    ‖ramifiedRawWeight h u k‖ + ‖ramifiedRawWeight h (-u) k‖ ≤ ramifiedDecayRatio ^ (k + 2) := by
  rw [ramifiedRawWeight, ramifiedRawWeight, norm_mul, norm_mul, ← mul_add]
  exact (mul_le_mul_of_nonneg_left (arithmeticResidueSum_sign_pair_norm_le h u (k + 2) (by omega) hchar)
    (norm_nonneg _)).trans_eq (ramifiedWeight_norm_scalar _)

lemma ramifiedRawWeight_norm_mul_primary (h b : O) (hb : lambda ^ 2 ∣ b - 1) (u : Oˣ) (k : ℕ) :
    ‖ramifiedRawWeight (h * b) u k‖ = ‖ramifiedRawWeight h u k‖ := by
  simp only [ramifiedRawWeight, norm_mul, arithmeticResidueSum_norm_mul_primary h b hb u (k + 2) (by omega)]

lemma ramifiedRawWeight_zero_of_three_dvd (h : O) (hh : (3 : O) ∣ h) (u : Oˣ) :
    ramifiedRawWeight h u 0 = 0 := by
  rw [ramifiedRawWeight, zero_add, arithmeticResidueSum_lambda_sq_zero h hh u, mul_zero]

section
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

lemma ramifiedRawWeight_unit_sum (h : O) (k : ℕ) :
    (∑ u : Oˣ, ‖ramifiedRawWeight h u k‖) =
      ∑ j : Fin 3, (‖ramifiedRawWeight h (cuspOmegaUnit ^ j.val) k‖ +
        ‖ramifiedRawWeight h (-(cuspOmegaUnit ^ j.val)) k‖) := by
  have he := Fintype.sum_equiv signedOmegaEquiv
    (fun p : Bool × Fin 3 => ‖ramifiedRawWeight h (signedOmegaUnit p) k‖)
    (fun u : Oˣ => ‖ramifiedRawWeight h u k‖) (fun _ => rfl)
  rw [← he]
  simp [signedOmegaUnit, Fintype.sum_prod_type, Finset.sum_add_distrib, add_comm]

lemma ramifiedRawWeight_unit_sum_le_four (h : O) (k : ℕ) :
    (∑ u : Oˣ, ‖ramifiedRawWeight h u k‖) ≤ 4 * ramifiedDecayRatio ^ (k + 2) := by
  have h0 : ‖ramifiedRawWeight h (cuspOmegaUnit ^ (0 : Fin 3).val) k‖ +
      ‖ramifiedRawWeight h (-(cuspOmegaUnit ^ (0 : Fin 3).val)) k‖ ≤
        2 * ramifiedDecayRatio ^ (k + 2) := by
    have hh := add_le_add (ramifiedRawWeight_norm_le h (cuspOmegaUnit ^ 0) k)
      (ramifiedRawWeight_norm_le h (-(cuspOmegaUnit ^ 0)) k)
    convert! hh using 1 <;> simp only [Fin.val_zero, two_mul]
  have h1 := ramifiedRawWeight_sign_pair_norm_le h (cuspOmegaUnit ^ (1 : Fin 3).val) k
    (ramifiedQuotientChar_omegaUnit_ne_one 1 (k + 2) (by decide))
  have h2 := ramifiedRawWeight_sign_pair_norm_le h (cuspOmegaUnit ^ (2 : Fin 3).val) k
    (ramifiedQuotientChar_omegaUnit_ne_one 2 (k + 2) (by decide))
  rw [ramifiedRawWeight_unit_sum, Fin.sum_univ_three]
  linarith only [h0, h1, h2]

lemma ramifiedRawWeight_unit_sum_le_three (h : O) (k : ℕ) (hk : (k + 2) % 3 ≠ 0) :
    (∑ u : Oˣ, ‖ramifiedRawWeight h u k‖) ≤ 3 * ramifiedDecayRatio ^ (k + 2) := by
  rw [ramifiedRawWeight_unit_sum]
  calc
    _ ≤ ∑ j : Fin 3, ramifiedDecayRatio ^ (k + 2) := Finset.sum_le_sum (fun j _ =>
      ramifiedRawWeight_sign_pair_norm_le h (cuspOmegaUnit ^ j.val) k
        (ramifiedQuotientChar_omegaUnit_ne_one_of_mod j (k + 2) hk))
    _ = _ := by simp

/-- Sign-pair orthogonality makes the finite ramified remainder smaller than its leading coefficient. -/
theorem lowRamifiedRawWeight_sum (a r : Fin 3) (b : O) (hb : lambda ^ 2 ∣ b - 1) :
    (∑ u : Oˣ, ∑ k : Fin 5, ‖ramifiedRawWeight (lowRamifiedFrequency a r * b) u k.val‖) ≤ 2671 / 900 := by
  simp_rw [ramifiedRawWeight_norm_mul_primary _ b hb]
  let h := lowRamifiedFrequency a r
  have hzero : (∑ u : Oˣ, ‖ramifiedRawWeight h u 0‖) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [ramifiedRawWeight_zero_of_three_dvd h (lowRamifiedFrequency_three_dvd a r) u, norm_zero]
  have h1 := ramifiedRawWeight_unit_sum_le_four h 1
  have h2 := ramifiedRawWeight_unit_sum_le_three h 2 (by norm_num)
  have h3 := ramifiedRawWeight_unit_sum_le_three h 3 (by norm_num)
  have h4 := ramifiedRawWeight_unit_sum_le_four h 4
  change (∑ u : Oˣ, ‖ramifiedRawWeight h u 1‖) ≤ 4 * ramifiedDecayRatio ^ 3 at h1
  change (∑ u : Oˣ, ‖ramifiedRawWeight h u 2‖) ≤ 3 * ramifiedDecayRatio ^ 4 at h2
  change (∑ u : Oˣ, ‖ramifiedRawWeight h u 3‖) ≤ 3 * ramifiedDecayRatio ^ 5 at h3
  change (∑ u : Oˣ, ‖ramifiedRawWeight h u 4‖) ≤ 4 * ramifiedDecayRatio ^ 6 at h4
  have hsum : (∑ k : Fin 5, ∑ u : Oˣ, ‖ramifiedRawWeight h u k.val‖) =
      (∑ u : Oˣ, ‖ramifiedRawWeight h u 0‖) + (∑ u : Oˣ, ‖ramifiedRawWeight h u 1‖) +
      (∑ u : Oˣ, ‖ramifiedRawWeight h u 2‖) + (∑ u : Oˣ, ‖ramifiedRawWeight h u 3‖) +
      (∑ u : Oˣ, ‖ramifiedRawWeight h u 4‖) := by
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Finset.univ_eq_empty, Finset.sum_empty]
    ring
  have hp4 : ramifiedDecayRatio ^ 4 = (1 / 3 : ℝ) * ramifiedDecayRatio := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, ramifiedDecayRatio_cube, pow_one]
  have hp5 : ramifiedDecayRatio ^ 5 = (1 / 3 : ℝ) * ramifiedDecayRatio ^ 2 := by
    rw [show (5 : ℕ) = 3 + 2 from rfl, pow_add, ramifiedDecayRatio_cube]
  have hp6 : ramifiedDecayRatio ^ 6 = (1 / 9 : ℝ) := by
    rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, ramifiedDecayRatio_cube]
    norm_num
  have hsq : ramifiedDecayRatio ^ 2 ≤ 49 / 100 := by
    have hp := mul_nonneg (sub_nonneg.mpr ramifiedDecayRatio_le_seven_tenths)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 10) ramifiedDecayRatio_pos.le)
    nlinarith only [hp]
  change (∑ u : Oˣ, ∑ k : Fin 5, ‖ramifiedRawWeight h u k.val‖) ≤ _
  rw [Finset.sum_comm, hsum, hzero, zero_add]
  calc
    _ ≤ 4 * ramifiedDecayRatio ^ 3 + 3 * ramifiedDecayRatio ^ 4 +
        3 * ramifiedDecayRatio ^ 5 + 4 * ramifiedDecayRatio ^ 6 := by
      linarith only [h1, h2, h3, h4]
    _ = 16 / 9 + ramifiedDecayRatio + ramifiedDecayRatio ^ 2 := by
      rw [ramifiedDecayRatio_cube, hp4, hp5, hp6]
      ring
    _ ≤ 2671 / 900 := by linarith only [ramifiedDecayRatio_le_seven_tenths, hsq]

end

def ramifiedGaussWeight (h : O) (u : Oˣ) (k : ℕ) (s : ℂ) : ℂ :=
  ((3 ^ (k + 2) : ℕ) : ℂ) ^ (-s) * arithmeticResidueSum h ((u : O) * lambda ^ (k + 2))

lemma ramifiedGaussWeight_analyticAt (h : O) (u : Oˣ) (k : ℕ) (s : ℂ) :
    AnalyticAt ℂ (ramifiedGaussWeight h u k) s := by
  apply AnalyticAt.mul _ analyticAt_const
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  apply Eventually.of_forall
  intro z
  exact differentiableAt_id.neg.const_cpow (Or.inl (by
    exact_mod_cast (pow_ne_zero (k + 2) (by norm_num : (3 : ℕ) ≠ 0))))

section
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

/-- The finite ramified decomposition survives continuation to the actual scattering residue. -/
theorem nonzeroScatteringResidue_eq_finite_gauss (h : O) (hh : h ≠ 0) (N : ℕ)
    (hN : ramifiedFrequencyBound h + 1 ≤ N) :
    nonzeroScatteringResidue h =
      (∑ u : Oˣ, ∑ k ∈ Finset.range N, ramifiedRawWeight h u k *
        unramifiedGaussResidue (9 * h * ((u : O) * lambda ^ (k + 2)))) / ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) := by
  let index : Oˣ × Fin N → O := fun i => 9 * h * ((i.1 : O) * lambda ^ (i.2.val + 2))
  let coefficient : Oˣ × Fin N → ℂ → ℂ := fun i s =>
    cuspWhittakerHeightFactor s h * ramifiedGaussWeight h i.1 i.2.val s
  have he := finite_unramified_residue index coefficient
    (fun i s hs => (cuspWhittakerHeightFactor_analyticAt h s hs).mul (ramifiedGaussWeight_analyticAt h i.1 i.2.val s))
    (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
    (kernelCuspFourier h cubicEisensteinResidue)
    (fun s hs hi => kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num) s hs.ne' hi.ne')
    (kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num))
    (by
      intro s hs hi
      rw [kernelCuspFourierFamily_eq_upper h hh ⟨by linarith, hi⟩]
      dsimp only
      rw [scatteringCoefficient]
      have hv : ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) *
          (arithmeticDirichletSeries s h / ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) = arithmeticDirichletSeries s h := by
        field_simp [cusp_volume_ne_zero]
      rw [hv, arithmeticDirichletSeries_finite_gauss_of_bound s (by linarith) h hh N hN]
      simp only [tsum_fintype, Fintype.sum_prod_type, coefficient, index, ramifiedGaussWeight,
        Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Fin.sum_univ_eq_sum_range (fun k => cuspWhittakerHeightFactor s h *
        (((3 ^ (k + 2) : ℕ) : ℂ) ^ (-s) * arithmeticResidueSum h ((u : O) * lambda ^ (k + 2))) *
          unramifiedCubicGaussSeries s (9 * h * ((u : O) * lambda ^ (k + 2))))]
      apply Finset.sum_congr rfl
      intro k hk
      ring)
  have hsum : (∑ i : Oˣ × Fin N, coefficient i (4 / 3) * unramifiedGaussResidue (index i)) =
      cuspWhittakerHeightFactor (4 / 3) h *
        (∑ u : Oˣ, ∑ k ∈ Finset.range N, ramifiedRawWeight h u k *
          unramifiedGaussResidue (9 * h * ((u : O) * lambda ^ (k + 2)))) := by
    simp only [Fintype.sum_prod_type, coefficient, index, ramifiedGaussWeight, ramifiedRawWeight,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Fin.sum_univ_eq_sum_range (fun k => cuspWhittakerHeightFactor (4 / 3) h *
      (((3 ^ (k + 2) : ℕ) : ℂ) ^ (-(4 / 3 : ℂ)) * arithmeticResidueSum h ((u : O) * lambda ^ (k + 2))) *
        unramifiedGaussResidue (9 * h * ((u : O) * lambda ^ (k + 2))))]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum] at he
  rw [nonzeroScatteringResidue, he]
  field_simp [cusp_volume_ne_zero, cuspWhittakerHeightFactor_center_ne_zero h]

def lowRamifiedTransform (F : O → ℂ) (h : O) : ℂ :=
  3 * F (9 * h) + ∑ u : Oˣ, ∑ k : Fin 5,
    ramifiedRawWeight h u k.val * F (9 * h * ((u : O) * lambda ^ (k.val + 2)))

lemma nonzeroScatteringResidue_low (a r : Fin 3) (b : O) (hb : lambda ^ 2 ∣ b - 1) :
    nonzeroScatteringResidue (lowRamifiedFrequency a r * b) =
      (∑ u : Oˣ, ∑ k : Fin 5, ramifiedRawWeight (lowRamifiedFrequency a r * b) u k.val *
        unramifiedGaussResidue (9 * (lowRamifiedFrequency a r * b) * ((u : O) * lambda ^ (k.val + 2)))) /
          ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) := by
  let h := lowRamifiedFrequency a r * b
  let N := max (ramifiedFrequencyBound h + 1) 5
  rw [nonzeroScatteringResidue_eq_finite_gauss h
    (mul_ne_zero (lowRamifiedFrequency_ne_zero a r) (primary_ne_zero b hb)) N (le_max_left _ _)]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [Fin.sum_univ_eq_sum_range (fun k => ramifiedRawWeight h u k *
    unramifiedGaussResidue (9 * h * ((u : O) * lambda ^ (k + 2))))]
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
  intro k hk hk5
  have hz := lowRamifiedFrequency_primary_vanish a r b hb u k
    (by simpa only [Finset.mem_range, not_lt] using hk5)
  simp only [ramifiedRawWeight, h, hz, mul_zero, zero_mul]

end

lemma sourceRayPhase_of_three_dvd (h : O) (hh : (3 : O) ∣ h) : tracePhase (cuspFrequency h) = 1 := by
  obtain ⟨b, rfl⟩ := hh
  have he : cuspFrequency (3 * b) = cuspFrequency b * (3 * ringComplex 1) := by
    simp only [cuspFrequency, map_mul, map_ofNat, map_one]
    ring
  rw [he, cuspFrequency_period]

lemma rationalCuspPhaseSum_of_three_dvd (h : O) (hh : (3 : O) ∣ h) : rationalCuspPhaseSum h = 3 := by
  rw [rationalCuspPhaseSum, show cuspFrequency h * 2 = cuspFrequency h + cuspFrequency h by ring,
    AddChar.map_add_eq_mul, sourceRayPhase_of_three_dvd h hh]
  norm_num

section
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

theorem lowRamifiedTransform_actual (a r : Fin 3) (b : O) (hb : lambda ^ 2 ∣ b - 1) :
    lowRamifiedTransform unramifiedGaussResidue (lowRamifiedFrequency a r * b) =
      (4 * ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) *
        rationalSourceScatteringResidue (lowRamifiedFrequency a r * b) := by
  rw [rationalSourceScatteringResidue,
    if_neg (mul_ne_zero (lowRamifiedFrequency_ne_zero a r) (primary_ne_zero b hb)),
    oppositeCuspResidue_eq_unramified,
    rationalCuspPhaseSum_of_three_dvd _ (dvd_mul_of_dvd_left (lowRamifiedFrequency_three_dvd a r) b),
    nonzeroScatteringResidue_low a r b hb]
  unfold lowRamifiedTransform
  field_simp [cusp_volume_ne_zero]
  ring

lemma lowRamifiedTransform_sub (F G : O → ℂ) (h : O) :
    lowRamifiedTransform (fun x => F x - G x) h = lowRamifiedTransform F h - lowRamifiedTransform G h := by
  simp only [lowRamifiedTransform, mul_sub, Finset.sum_sub_distrib]
  ring

lemma ramifiedRawWeight_frequency_cube (h p : O) (hp : lambda ^ 2 ∣ p - 1) (u : Oˣ) (k : ℕ) :
    ramifiedRawWeight (h * p ^ 3) u k = ramifiedRawWeight h u k := by
  rw [ramifiedRawWeight, ramifiedRawWeight, arithmeticResidueSum_frequency_cube h _ p
    (ramifiedElement_ne_zero u (k + 2)) (ramifiedElement_level u (k + 2) (by omega)) hp
    (ramified_primary_coprime u (k + 2) p hp).of_mul_left_right]

lemma lowRamifiedTransform_cube_comp (F : O → ℂ) (h p : O) (hp : lambda ^ 2 ∣ p - 1) :
    lowRamifiedTransform (fun x => F (x * p ^ 3)) h = lowRamifiedTransform F (h * p ^ 3) := by
  simp only [lowRamifiedTransform, ramifiedRawWeight_frequency_cube h p hp]
  rw [show 9 * h * p ^ 3 = 9 * (h * p ^ 3) by ring]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  ring

theorem lowRamifiedTransform_cube_difference (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (a r : Fin 3) (b : O) (hb : lambda ^ 2 ∣ b - 1) :
    lowRamifiedTransform (fun x => unramifiedGaussResidue (x * p ^ 3) - unramifiedGaussResidue x)
      (lowRamifiedFrequency a r * b) = 0 := by
  rw [lowRamifiedTransform_sub, lowRamifiedTransform_cube_comp _ _ p hprimary]
  have hb3 : lambda ^ 2 ∣ b * p ^ 3 - 1 :=
    primary_mul b (p ^ 3) hb (primary_pow_congruence p hprimary 3)
  rw [mul_assoc, lowRamifiedTransform_actual a r (b * p ^ 3) hb3,
    lowRamifiedTransform_actual a r b hb, ← mul_assoc,
    rationalSourceScatteringResidue_mul_prime_cube p hp hprimary, sub_self]

end

lemma ramifiedFunction_reduce (F : O → ℂ) (hneg : ∀ x, F (-x) = F x)
    (hpow : ∀ x m, F (x * lambda ^ m) = F (x * lambda ^ (m % 3))) (b : O) (u : Oˣ) (m : ℕ) :
    ∃ j k : Fin 3, F (b * ((u : O) * lambda ^ m)) = F (b * omega ^ j.val * lambda ^ k.val) := by
  obtain ⟨j, hj | hj⟩ := unit_eq_sign_omega u
  · refine ⟨j, ⟨m % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    rw [hj, ← mul_assoc, hpow]
  · refine ⟨j, ⟨m % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    rw [hj, neg_mul, mul_neg, hneg, ← mul_assoc, hpow]

lemma lowRamified_inner_family (a r : Fin 3) (b : O) (u : Oˣ) (k : ℕ) :
    9 * (lowRamifiedFrequency a r * b) * ((u : O) * lambda ^ (k + 2)) =
      b * (((cuspOmegaUnit ^ (a.val + 1) * u : Oˣ) : O) * lambda ^ (r.val + k + 8)) := by
  simp only [lowRamifiedFrequency, ramifiedNine_eq, Units.val_mul, Units.val_pow_eq_pow_val, cuspOmegaUnit_val]
  rw [show r.val + k + 8 = 4 + ((r.val + 2) + (k + 2)) by omega]
  simp only [pow_add, pow_one]
  ring

lemma lowRamifiedLeading (F : O → ℂ)
    (hpow : ∀ x m, F (x * lambda ^ m) = F (x * lambda ^ (m % 3))) (b : O) (j k : Fin 3) :
    F (9 * (lowRamifiedFrequency ⟨(j.val + 2) % 3, Nat.mod_lt _ (by norm_num)⟩ k * b)) =
      F (b * omega ^ j.val * lambda ^ k.val) := by
  have ho : omega ^ ((j.val + 2) % 3 + 1) = omega ^ j.val := by
    fin_cases j <;> norm_num [omega_primitive.pow_eq_one]
  have he : 9 * (lowRamifiedFrequency ⟨(j.val + 2) % 3, Nat.mod_lt _ (by norm_num)⟩ k * b) =
      (b * omega ^ j.val) * lambda ^ (k.val + 6) := by
    simp only [lowRamifiedFrequency, ramifiedNine_eq]
    rw [show k.val + 6 = 4 + (k.val + 2) by omega, pow_add, ← ho, pow_succ]
    ring
  rw [he, hpow, show (k.val + 6) % 3 = k.val by omega]

section
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

lemma lowRamified_remainder_bound (F : O → ℂ) (hneg : ∀ x, F (-x) = F x)
    (hpow : ∀ x m, F (x * lambda ^ m) = F (x * lambda ^ (m % 3))) (b : O) (hb : lambda ^ 2 ∣ b - 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ j k : Fin 3, ‖F (b * omega ^ j.val * lambda ^ k.val)‖ ≤ M)
    (a r : Fin 3) :
    ‖∑ u : Oˣ, ∑ k : Fin 5, ramifiedRawWeight (lowRamifiedFrequency a r * b) u k.val *
      F (9 * (lowRamifiedFrequency a r * b) * ((u : O) * lambda ^ (k.val + 2)))‖ ≤ (2671 / 900) * M := by
  have hbound (u : Oˣ) (k : Fin 5) :
      ‖F (9 * (lowRamifiedFrequency a r * b) * ((u : O) * lambda ^ (k.val + 2)))‖ ≤ M := by
    rw [lowRamified_inner_family]
    obtain ⟨j, l, he⟩ := ramifiedFunction_reduce F hneg hpow b (cuspOmegaUnit ^ (a.val + 1) * u) (r.val + k.val + 8)
    rw [he]
    exact hM j l
  calc
    _ ≤ ∑ u : Oˣ, ∑ k : Fin 5, ‖ramifiedRawWeight (lowRamifiedFrequency a r * b) u k.val *
        F (9 * (lowRamifiedFrequency a r * b) * ((u : O) * lambda ^ (k.val + 2)))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ u : Oˣ, ∑ k : Fin 5, ‖ramifiedRawWeight (lowRamifiedFrequency a r * b) u k.val‖ * M := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound u k) (norm_nonneg _)
    _ = (∑ u : Oˣ, ∑ k : Fin 5, ‖ramifiedRawWeight (lowRamifiedFrequency a r * b) u k.val‖) * M := by
      simp only [Finset.sum_mul]
    _ ≤ (2671 / 900) * M := mul_le_mul_of_nonneg_right (lowRamifiedRawWeight_sum a r b hb) hM0

/-- Strict domination by the leading term makes the ramified transform injective on its nine residue classes. -/
theorem lowRamifiedTransform_injective (F : O → ℂ) (hneg : ∀ x, F (-x) = F x)
    (hpow : ∀ x m, F (x * lambda ^ m) = F (x * lambda ^ (m % 3))) (b : O) (hb : lambda ^ 2 ∣ b - 1)
    (hz : ∀ a r : Fin 3, lowRamifiedTransform F (lowRamifiedFrequency a r * b) = 0) :
    ∀ j k : Fin 3, F (b * omega ^ j.val * lambda ^ k.val) = 0 := by
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun i => ‖F (b * omega ^ i.1.val * lambda ^ i.2.val)‖) Finset.univ_nonempty
  let M := ‖F (b * omega ^ i.1.val * lambda ^ i.2.val)‖
  have hM : ∀ j k : Fin 3, ‖F (b * omega ^ j.val * lambda ^ k.val)‖ ≤ M :=
    fun j k => himax (j, k) (Finset.mem_univ _)
  let a : Fin 3 := ⟨(i.1.val + 2) % 3, Nat.mod_lt _ (by norm_num)⟩
  have hbnd := lowRamified_remainder_bound F hneg hpow b hb M (norm_nonneg _) hM a i.2
  have he := hz a i.2
  unfold lowRamifiedTransform at he
  rw [lowRamifiedLeading F hpow b i.1 i.2] at he
  have hnorm : 3 * M ≤ (2671 / 900) * M := by
    have heq : 3 * F (b * omega ^ i.1.val * lambda ^ i.2.val) =
        -(∑ u : Oˣ, ∑ k : Fin 5, ramifiedRawWeight (lowRamifiedFrequency a i.2 * b) u k.val *
          F (9 * (lowRamifiedFrequency a i.2 * b) * ((u : O) * lambda ^ (k.val + 2)))) := by
      linear_combination he
    have hh := congrArg norm heq
    rw [norm_mul, Complex.norm_ofNat, norm_neg] at hh
    exact hh.le.trans hbnd
  have hmzero : M = 0 := by have hM0 : 0 ≤ M := norm_nonneg _; linarith only [hnorm, hM0]
  intro j k
  exact norm_eq_zero.mp (le_antisymm (hmzero ▸ hM j k) (norm_nonneg _))

end

/-- Primary prime cubes leave every unramified Gauss residue unchanged. -/
theorem unramifiedGaussResidue_prime_cube (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) (h : O) :
    unramifiedGaussResidue (h * p ^ 3) = unramifiedGaussResidue h := by
  by_cases hh : h = 0
  · simp only [hh, zero_mul]
  obtain ⟨u, m, I, hI, hfactor⟩ := exists_unit_lambda_primary_factor h hh
  let b := primaryIdealGenerator I
  have hb : lambda ^ 2 ∣ b - 1 := (primaryIdealGenerator_spec I hI).2
  let F : O → ℂ := fun x => unramifiedGaussResidue (x * p ^ 3) - unramifiedGaussResidue x
  have hneg (x : O) : F (-x) = F x := by
    dsimp only [F]
    rw [neg_mul, unramifiedGaussResidue_neg, unramifiedGaussResidue_neg]
  have hpow (x : O) (k : ℕ) : F (x * lambda ^ k) = F (x * lambda ^ (k % 3)) := by
    dsimp only [F]
    rw [show (x * lambda ^ k) * p ^ 3 = (x * p ^ 3) * lambda ^ k by ring,
      show (x * lambda ^ (k % 3)) * p ^ 3 = (x * p ^ 3) * lambda ^ (k % 3) by ring,
      unramifiedGaussResidue_lambda_pow (x * p ^ 3) k, unramifiedGaussResidue_lambda_pow x k]
  have hz : ∀ j k : Fin 3, F (b * omega ^ j.val * lambda ^ k.val) = 0 :=
    lowRamifiedTransform_injective F hneg hpow b hb
      (fun a r => lowRamifiedTransform_cube_difference p hp hprimary a r b hb)
  obtain ⟨j, k, hjk⟩ := ramifiedFunction_reduce F hneg hpow b u m
  have hF : F h = 0 := by
    rw [hfactor, mul_comm ((u : O) * lambda ^ m) b, hjk, hz]
  exact sub_eq_zero.mp hF

lemma unramifiedGaussResidue_prime_pow_mod (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (n : ℕ) :
    unramifiedGaussResidue (h * p ^ n) = unramifiedGaussResidue (h * p ^ (n % 3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 3
    · rw [Nat.mod_eq_of_lt hn]
    have h3 : 3 ≤ n := by omega
    calc
      _ = unramifiedGaussResidue ((h * p ^ (n - 3)) * p ^ 3) := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h3]
      _ = unramifiedGaussResidue (h * p ^ (n - 3)) := unramifiedGaussResidue_prime_cube p hp hprimary _
      _ = unramifiedGaussResidue (h * p ^ ((n - 3) % 3)) := ih (n - 3) (by omega)
      _ = _ := by rw [show (n - 3) % 3 = n % 3 by omega]

lemma unramifiedGaussResidue_prime_square_zero (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    unramifiedGaussResidue (h * p ^ 2) = 0 := by
  have hc := unramifiedGaussResidue_prime_cube p hp hprimary (h * p ^ 2)
  rw [show (h * p ^ 2) * p ^ 3 = h * p ^ 5 by ring,
    unramifiedGaussResidue_square_cube p hp hprimary h hph] at hc
  have hn := principalNorm_complex_ne_zero p hp.ne_zero
  exact (mul_eq_zero.mp (show (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ *
    unramifiedGaussResidue (h * p ^ 2) = 0 by linear_combination hc)).resolve_left (inv_ne_zero hn)

/-- The surviving first-power residue is determined by the second cubic Gauss sum. -/
theorem unramifiedGaussResidue_prime_factor (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    unramifiedGaussResidue (h * p) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ) *
        primeCubicGauss p hp hprimary 2 h * unramifiedGaussResidue h := by
  have hn := principalNorm_complex_ne_zero p hp.ne_zero
  have hgg := primeCubicGauss_one_mul_two p hp hprimary h hph
  have hG : primeCubicGauss p hp hprimary 1 h ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hgg
    exact hn hgg.symm
  have hweight : (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
  have hfactor : (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) *
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ) * (Ideal.absNorm (Ideal.span {p}) : ℂ)) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ := by
    conv_lhs => rhs; rhs; rw [← Complex.cpow_one (Ideal.absNorm (Ideal.span {p}) : ℂ)]
    rw [← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
    convert Complex.cpow_neg_one (Ideal.absNorm (Ideal.span {p}) : ℂ) using 1
    congr 1
    norm_num
  have hrec := unramifiedGaussResidue_prime_recurrence p hp hprimary h hph
  rw [unramifiedGaussResidue_prime_cube p hp hprimary h] at hrec
  have hrel : (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) *
      primeCubicGauss p hp hprimary 1 h * unramifiedGaussResidue (h * p) =
        (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * unramifiedGaussResidue h := by linear_combination hrec
  apply mul_left_cancel₀ (mul_ne_zero hweight hG)
  calc
    _ = (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ * unramifiedGaussResidue h := hrel
    _ = ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-(4 / 3 : ℂ)) *
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ) *
          (primeCubicGauss p hp hprimary 1 h * primeCubicGauss p hp hprimary 2 h))) *
            unramifiedGaussResidue h := by rw [hgg, hfactor]
    _ = _ := by ring

/-- The unramified residue vanishes at exponents two modulo three; all other values are explicit. -/
theorem unramifiedGaussResidue_prime_power_table (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) (n : ℕ) :
    unramifiedGaussResidue (h * p ^ n) =
      if n % 3 = 0 then unramifiedGaussResidue h
      else if n % 3 = 1 then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ) *
        primeCubicGauss p hp hprimary 2 h * unramifiedGaussResidue h
      else 0 := by
  rw [unramifiedGaussResidue_prime_pow_mod p hp hprimary h n]
  by_cases h0 : n % 3 = 0
  · simp only [h0, pow_zero, mul_one, if_true]
  by_cases h1 : n % 3 = 1
  · simp only [h1, pow_one, if_true, Nat.one_ne_zero, if_false]
    exact unramifiedGaussResidue_prime_factor p hp hprimary h hph
  rw [if_neg h0, if_neg h1, show n % 3 = 2 by omega]
  exact unramifiedGaussResidue_prime_square_zero p hp hprimary h hph

theorem unramifiedGaussResidue_primary_cube (b : O) (hb : b ≠ 0)
    (hprimary : lambda ^ 2 ∣ b - 1) (h : O) :
    unramifiedGaussResidue (h * b ^ 3) = unramifiedGaussResidue h := by
  obtain ⟨s, hs, hpr⟩ := exists_primary_prime_factorization b hb hprimary
  rw [← hs]
  clear hs hb hprimary b
  induction s using Multiset.induction_on generalizing h with
  | empty => simp only [Multiset.prod_zero, one_pow, mul_one]
  | @cons p s ih =>
    obtain ⟨hp, hprimary⟩ := hpr p (Multiset.mem_cons_self _ _)
    rw [Multiset.prod_cons, mul_pow, ← mul_assoc,
      ih (h * p ^ 3) (fun q hq => hpr q (Multiset.mem_cons_of_mem hq)),
      unramifiedGaussResidue_prime_cube p hp hprimary h]

/-- Bessel normalization of the unramified Gauss residue. -/
def unramifiedResidualCoefficient (h : O) : ℂ := sourceBesselNormalizer h * unramifiedGaussResidue h

lemma unramifiedResidualCoefficient_prime_factor (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    unramifiedResidualCoefficient (h * p) =
      (primeCubicGauss p hp hprimary 2 h / (‖ringComplex p‖ : ℂ)) * unramifiedResidualCoefficient h := by
  rw [unramifiedResidualCoefficient, sourceBesselNormalizer_mul,
    unramifiedGaussResidue_prime_factor p hp hprimary h hph, unramifiedResidualCoefficient]
  calc
    _ = ((‖ringComplex p‖ : ℂ) ^ (1 / 3 : ℂ) * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-2 / 3 : ℂ)) *
        primeCubicGauss p hp hprimary 2 h * (sourceBesselNormalizer h * unramifiedGaussResidue h) := by ring
    _ = _ := by rw [sourcePrimeNormalizer_powers p hp.ne_zero]; ring

lemma unramifiedResidualCoefficient_prime_norm (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) :
    ‖unramifiedResidualCoefficient (h * p)‖ = ‖unramifiedResidualCoefficient h‖ := by
  rw [unramifiedResidualCoefficient_prime_factor p hp hprimary h hph, norm_mul, norm_div,
    primeCubicGauss_two_eq_star p hp hprimary h hph, norm_star,
    cubicUnitGaussSum_prime_norm p hp hprimary h hph, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (ringComplex_ne_zero hp.ne_zero)), one_mul]

lemma unramifiedResidualCoefficient_primary_cube (b : O) (hb : b ≠ 0)
    (hprimary : lambda ^ 2 ∣ b - 1) (h : O) :
    unramifiedResidualCoefficient (h * b ^ 3) =
      (‖ringComplex b‖ : ℂ) * unramifiedResidualCoefficient h := by
  rw [unramifiedResidualCoefficient, sourceBesselNormalizer_mul_cube h b hb,
    unramifiedGaussResidue_primary_cube b hb hprimary h, unramifiedResidualCoefficient]
  ring

lemma unramifiedResidualCoefficient_prime_power_vanish (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) (k : ℕ) (hk : k % 3 = 2) :
    unramifiedResidualCoefficient (h * p ^ k) = 0 := by
  rw [unramifiedResidualCoefficient, unramifiedGaussResidue_prime_power_table p hp hprimary h hph k, hk]
  norm_num

theorem unramifiedResidualCoefficient_full_squarefree_cube_support
    (h : O) (hh : h ≠ 0) (hF : unramifiedResidualCoefficient h ≠ 0) :
    ∃ (u : Oˣ) (m : ℕ) (I J : Ideal O), Squarefree I ∧
      primaryIdealGenerator I ≠ 0 ∧ primaryIdealGenerator J ≠ 0 ∧
      h = ((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3 :=
  ramifiedFunction_squarefree_cube_support unramifiedResidualCoefficient
    unramifiedResidualCoefficient_prime_power_vanish h hh hF

/-- The squarefree factor preserves norm; the cube factor contributes its complex absolute value. -/
theorem unramifiedResidualCoefficient_squarefree_cube_norm (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I)
    (u : Oˣ) (m : ℕ) :
    ‖unramifiedResidualCoefficient
      (((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)‖ =
      ‖ringComplex (primaryIdealGenerator J)‖ * ‖unramifiedResidualCoefficient ((u : O) * lambda ^ m)‖ := by
  rw [unramifiedResidualCoefficient_primary_cube _ hJ (primaryIdealGenerator_spec J hJ).2,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  congr 1
  rw [primaryIdealGenerator_squarefree_support I hI hsq]
  apply primeProduct_norm_of unramifiedResidualCoefficient unramifiedResidualCoefficient_prime_norm
  · exact fun P hP => primaryIdealPrime_isPrime_of_mem I P hI hP
  · exact fun P hP => (primaryIdealPrime_spec P
      (primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  · exact primaryIdealPrime_support_coprime I hI
  · intro P hP hd
    have hp := primaryIdealPrime_isPrime_of_mem I P hI hP
    have hpp := (primaryIdealPrime_spec P
      (primaryIdealPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
    exact hp.2.1 ((ramified_primary_coprime u m _ hpp).of_mul_left_right.symm.isUnit_of_dvd hd)

/-- A uniform finite geometric bound, using the rational estimate for the ramified decay ratio. -/
lemma ramifiedDecayRatio_sum_le (N : ℕ) :
    (∑ k ∈ Finset.range N, ramifiedDecayRatio ^ k) ≤ 10 / 3 := by
  have hstrong : (∑ k ∈ Finset.range N, ramifiedDecayRatio ^ k) ≤
      10 / 3 - (10 / 3) * ramifiedDecayRatio ^ N := by
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, pow_zero]; norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hp := mul_nonneg (pow_nonneg ramifiedDecayRatio_pos.le N)
        (sub_nonneg.mpr ramifiedDecayRatio_le_seven_tenths)
      nlinarith only [ih, hp]
  exact hstrong.trans (sub_le_self _ (mul_nonneg (by norm_num) (pow_nonneg ramifiedDecayRatio_pos.le N)))

section
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

lemma ramifiedRawWeight_sum_le (h : O) (N : ℕ) :
    (∑ u : Oˣ, ∑ k ∈ Finset.range N, ‖ramifiedRawWeight h u k‖) ≤ 40 / 3 := by
  have hr2 : ramifiedDecayRatio ^ 2 ≤ 1 := by
    have hp := mul_nonneg (sub_nonneg.mpr ramifiedDecayRatio_le_seven_tenths)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 10) ramifiedDecayRatio_pos.le)
    nlinarith only [hp]
  calc
    _ = ∑ k ∈ Finset.range N, ∑ u : Oˣ, ‖ramifiedRawWeight h u k‖ := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range N, 4 * ramifiedDecayRatio ^ (k + 2) :=
      Finset.sum_le_sum (fun k _ => ramifiedRawWeight_unit_sum_le_four h k)
    _ ≤ ∑ k ∈ Finset.range N, 4 * ramifiedDecayRatio ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [pow_add]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hr2 (pow_nonneg ramifiedDecayRatio_pos.le k)).trans_eq (mul_one _))
        (by norm_num)
    _ = 4 * ∑ k ∈ Finset.range N, ramifiedDecayRatio ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ 40 / 3 := by linarith only [ramifiedDecayRatio_sum_le N]

lemma nonzeroScatteringResidue_family_bound (h : O) (hh : h ≠ 0) :
    ‖nonzeroScatteringResidue h‖ ≤
      ((40 / 3) * ramifiedResidueFamilyMass h) / (9 * Real.sqrt 3 / 2) := by
  rw [nonzeroScatteringResidue_eq_finite_gauss h hh (ramifiedFrequencyBound h + 1) le_rfl,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 9 * Real.sqrt 3 / 2)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ u : Oˣ, ∑ k ∈ Finset.range (ramifiedFrequencyBound h + 1),
        ‖ramifiedRawWeight h u k * unramifiedGaussResidue (9 * h * ((u : O) * lambda ^ (k + 2)))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ u : Oˣ, ∑ k ∈ Finset.range (ramifiedFrequencyBound h + 1),
        ‖ramifiedRawWeight h u k‖ * ramifiedResidueFamilyMass h := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (unramifiedGaussResidue_nine_norm_le h u (k + 2)) (norm_nonneg _)
    _ = (∑ u : Oˣ, ∑ k ∈ Finset.range (ramifiedFrequencyBound h + 1),
        ‖ramifiedRawWeight h u k‖) * ramifiedResidueFamilyMass h := by simp only [Finset.sum_mul]
    _ ≤ (40 / 3) * ramifiedResidueFamilyMass h :=
      mul_le_mul_of_nonneg_right (ramifiedRawWeight_sum_le h _) (ramifiedResidueFamilyMass_nonneg h)

/-- A finite unit–ramified family controls the projected arithmetic residue uniformly. -/
theorem rationalSourceScatteringResidue_family_bound (h : O) (hh : h ≠ 0) :
    ‖rationalSourceScatteringResidue h‖ ≤
      (49 / (12 * (9 * Real.sqrt 3 / 2))) * ramifiedResidueFamilyMass h := by
  have hV : 0 < (9 * Real.sqrt 3 / 2 : ℝ) := by positivity
  have h9 : ‖unramifiedGaussResidue (9 * h)‖ ≤ ramifiedResidueFamilyMass h := by
    simpa only [Units.val_one, pow_zero, mul_one] using unramifiedGaussResidue_nine_norm_le h 1 0
  rw [rationalSourceScatteringResidue, if_neg hh, oppositeCuspResidue_eq_unramified, norm_mul,
    norm_inv, Complex.norm_ofNat]
  calc
    _ ≤ (4 : ℝ)⁻¹ * (‖nonzeroScatteringResidue h‖ +
        ‖rationalCuspPhaseSum h * unramifiedGaussResidue (9 * h) / ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (4 : ℝ)⁻¹ * (((40 / 3) * ramifiedResidueFamilyMass h) / (9 * Real.sqrt 3 / 2) +
        (3 * ramifiedResidueFamilyMass h) / (9 * Real.sqrt 3 / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add (nonzeroScatteringResidue_family_bound h hh)
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (rationalCuspPhaseSum_norm_le h) h9 (norm_nonneg _) (by norm_num)) hV.le
    _ = _ := by ring

def sourceArithmeticBaseBound : ℝ :=
  (49 / (12 * (9 * Real.sqrt 3 / 2))) * (Fintype.card (Oˣ × Fin 3) : ℝ) * ramifiedResidueFamilyMass 1

lemma sourceArithmeticBaseBound_nonneg : 0 ≤ sourceArithmeticBaseBound := by
  unfold sourceArithmeticBaseBound
  exact mul_nonneg (by positivity) (ramifiedResidueFamilyMass_nonneg 1)

theorem rationalSourceScatteringResidue_unit_lambda_bound (u : Oˣ) (m : ℕ) :
    ‖rationalSourceScatteringResidue ((u : O) * lambda ^ m)‖ ≤ sourceArithmeticBaseBound := by
  refine (rationalSourceScatteringResidue_family_bound _ (ramifiedElement_ne_zero u m)).trans ?_
  exact (mul_le_mul_of_nonneg_left (ramifiedResidueFamilyMass_unit_lambda_le u m)
    (by positivity)).trans_eq (by unfold sourceArithmeticBaseBound; ring)

end

lemma sourceBesselNormalizer_mul_norm (h b : O) (hb : b ≠ 0) :
    ‖sourceBesselNormalizer (h * b)‖ = ‖sourceBesselNormalizer h‖ * ‖ringComplex b‖ ^ (1 / 3 : ℝ) := by
  rw [sourceBesselNormalizer_mul, norm_mul]
  have he := Complex.norm_cpow_eq_rpow_re_of_pos
    (norm_pos_iff.mpr (ringComplex_ne_zero hb)) (1 / 3 : ℂ)
  rw [show (1 / 3 : ℂ).re = (1 / 3 : ℝ) by norm_num] at he
  rw [he, mul_comm]

def unramifiedCoefficientBaseBound : ℝ := ‖sourceBesselNormalizer 1‖ * ramifiedResidueFamilyMass 1

def sourceCoefficientBaseBound : ℝ := ‖sourceBesselNormalizer 1‖ * sourceArithmeticBaseBound

lemma unramifiedCoefficientBaseBound_nonneg : 0 ≤ unramifiedCoefficientBaseBound :=
  mul_nonneg (norm_nonneg _) (ramifiedResidueFamilyMass_nonneg 1)

lemma sourceCoefficientBaseBound_nonneg : 0 ≤ sourceCoefficientBaseBound :=
  mul_nonneg (norm_nonneg _) sourceArithmeticBaseBound_nonneg

lemma unramifiedResidualCoefficient_ramified_bound (u : Oˣ) (m : ℕ) :
    ‖unramifiedResidualCoefficient ((u : O) * lambda ^ m)‖ ≤
      unramifiedCoefficientBaseBound * ‖ringComplex ((u : O) * lambda ^ m)‖ ^ (1 / 3 : ℝ) := by
  have hn := sourceBesselNormalizer_mul_norm 1 ((u : O) * lambda ^ m) (ramifiedElement_ne_zero u m)
  rw [one_mul] at hn
  rw [unramifiedResidualCoefficient, norm_mul, hn]
  exact (mul_le_mul_of_nonneg_left (unramifiedGaussResidue_unit_lambda_norm_le u m)
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))).trans_eq
      (by unfold unramifiedCoefficientBaseBound; ring)

lemma rationalSourceResidualFourierCoefficient_ramified_bound (u : Oˣ) (m : ℕ) :
    ‖rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m)‖ ≤
      sourceCoefficientBaseBound * ‖ringComplex ((u : O) * lambda ^ m)‖ ^ (1 / 3 : ℝ) := by
  have hn := sourceBesselNormalizer_mul_norm 1 ((u : O) * lambda ^ m) (ramifiedElement_ne_zero u m)
  rw [one_mul] at hn
  rw [rationalSourceResidualFourierCoefficient_eq _ (ramifiedElement_ne_zero u m)]
  change ‖rationalSourceScatteringResidue ((u : O) * lambda ^ m) *
    sourceBesselNormalizer ((u : O) * lambda ^ m)‖ ≤ _
  rw [norm_mul, hn]
  exact (mul_le_mul_of_nonneg_right (rationalSourceScatteringResidue_unit_lambda_bound u m)
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))).trans_eq
      (by unfold sourceCoefficientBaseBound; ring)

def threeRamifiedUnit : Oˣ := -(cuspOmegaUnit ^ 2)

lemma three_eq_ramifiedUnit : (3 : O) = (threeRamifiedUnit : O) * lambda ^ 2 := by
  simp only [threeRamifiedUnit, Units.val_neg, Units.val_pow_eq_pow_val, cuspOmegaUnit_val, lambda_sq_eq]
  calc
    (3 : O) = 3 * omega ^ 3 := by rw [omega_primitive.pow_eq_one]; ring
    _ = _ := by ring

def ramifiedSixUnit (u t : Oˣ) : RamifiedSixBranch → Oˣ
  | .inl _ => threeRamifiedUnit * u
  | .inr (.inl _) => threeRamifiedUnit * (-u)⁻¹ ^ 4 * (-u)
  | .inr (.inr (.inl _)) => threeRamifiedUnit * (-u)⁻¹ ^ 4
  | .inr (.inr (.inr j)) => threeRamifiedUnit * (-u)⁻¹ ^ 4 * t * (-cuspOmegaUnit) * cuspOmegaUnit ^ j.val

def ramifiedSixPower : RamifiedSixBranch → ℕ
  | .inl _ => 2
  | .inr (.inl _) => 2
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

lemma scaledAffineGaussWeight_divides (q : O) (u : Oˣ) (n : ℕ) (h : O) (s : ℂ)
    (hw : scaledAffineGaussWeight q u n h s ≠ 0) : q ∣ h := by
  by_contra hd
  exact hw (by simp only [scaledAffineGaussWeight, dif_neg hd])

lemma scaledAffineGaussIndex_eq_mul (q : O) (u : Oˣ) (n : ℕ) (h b : O)
    (hd : q ∣ h) (hb : 3 * ((u : O) * lambda ^ n) ^ 2 = b * q) :
    scaledAffineGaussIndex q u n h = b * h := by
  rw [scaledAffineGaussIndex, dif_pos hd, hb, mul_assoc, ← Classical.choose_spec hd]

/-- Every branch with nonzero weight multiplies frequency by a unit and a ramified power. -/
theorem ramifiedSixIndex_multiplier (u t : Oˣ) (h : O) (i : RamifiedSixBranch)
    (hw : ramifiedSixWeight u t h i (4 / 3) ≠ 0) :
    ramifiedSixIndex u t h i = ((ramifiedSixUnit u t i : O) * lambda ^ ramifiedSixPower i) * h := by
  rcases i with i | i
  · have hd := scaledAffineGaussWeight_divides (u : O) u 0 h (4 / 3) (mul_ne_zero_iff.mp hw).2
    apply scaledAffineGaussIndex_eq_mul _ _ _ _ _ hd
    simp only [ramifiedSixUnit, ramifiedSixPower, Units.val_mul, pow_zero, mul_one]
    rw [three_eq_ramifiedUnit]
    ring
  rcases i with i | i
  · have hd := scaledAffineGaussWeight_divides (-(u : O)) ((-u)⁻¹ ^ 2 * (-u)) 0 h (4 / 3)
      (mul_ne_zero_iff.mp hw).2
    apply scaledAffineGaussIndex_eq_mul _ _ _ _ _ hd
    simp only [ramifiedSixUnit, ramifiedSixPower, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_neg, pow_zero, mul_one]
    rw [three_eq_ramifiedUnit]
    ring
  rcases i with i | j
  · have hd := scaledAffineGaussWeight_divides 1 ((-u)⁻¹ ^ 2) 0 h (4 / 3) (mul_ne_zero_iff.mp hw).2
    apply scaledAffineGaussIndex_eq_mul _ _ _ _ _ hd
    simp only [ramifiedSixUnit, ramifiedSixPower, Units.val_mul, Units.val_pow_eq_pow_val, pow_zero, mul_one]
    rw [three_eq_ramifiedUnit]
    ring
  · have hd := scaledAffineGaussWeight_divides (onceCuspScale t * omega ^ j.val)
      (onceCuspArithmeticUnit (-u) t j) 1 h (4 / 3) (mul_ne_zero_iff.mp hw).2
    apply scaledAffineGaussIndex_eq_mul _ _ _ _ _ hd
    rw [pow_one, onceCuspArithmeticUnit_spec]
    simp only [ramifiedSixUnit, ramifiedSixPower, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_neg, cuspOmegaUnit_val, onceCuspScale, traceLambda_eq_unit_mul_lambda]
    rw [three_eq_ramifiedUnit]
    ring

lemma ramifiedResidualFourierCoefficient_prime_power_vanish (u t : Oˣ) (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) (hph : ¬ p ∣ h) (k : ℕ) (hk : k % 3 = 2) :
    ramifiedResidualFourierCoefficient u t (h * p ^ k) = 0 := by
  have hz : ramifiedArithmeticResidue u t (h * p ^ k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hw : ramifiedSixWeight u t (h * p ^ k) i (4 / 3) = 0
    · rw [hw, zero_mul]
    rw [ramifiedSixIndex_multiplier u t _ i hw, ← mul_assoc]
    have hnot : ¬ p ∣ ((ramifiedSixUnit u t i : O) * lambda ^ ramifiedSixPower i) * h := by
      intro hd
      rcases hp.dvd_mul.mp hd with hd | hd
      · exact hp.2.1 ((ramified_primary_coprime (ramifiedSixUnit u t i) (ramifiedSixPower i)
          p hprimary).of_mul_left_right.symm.isUnit_of_dvd hd)
      · exact hph hd
    rw [unramifiedGaussResidue_prime_power_table p hp hprimary _ hnot k, hk]
    norm_num
  simp only [ramifiedResidualFourierCoefficient, hz, mul_zero, zero_div, zero_mul]

theorem ramifiedBesselCoefficient_full_squarefree_cube_support (side : Bool)
    (h : O) (hh : h ≠ 0) (hF : ramifiedBesselCoefficient side h ≠ 0) :
    ∃ (u : Oˣ) (m : ℕ) (I J : Ideal O), Squarefree I ∧
      primaryIdealGenerator I ≠ 0 ∧ primaryIdealGenerator J ≠ 0 ∧
      h = ((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3 :=
  ramifiedFunction_squarefree_cube_support (ramifiedBesselCoefficient side)
    (ramifiedResidualFourierCoefficient_prime_power_vanish (ramifiedCuspRoot side)
      (ramifiedCuspScaleUnit side)) h hh hF

theorem unramifiedResidualCoefficient_squarefree_cube_bound (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I)
    (u : Oˣ) (m : ℕ) :
    ‖unramifiedResidualCoefficient
      (((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)‖ ≤
      unramifiedCoefficientBaseBound * ‖ringComplex ((u : O) * lambda ^ m)‖ ^ (1 / 3 : ℝ) *
        ‖ringComplex (primaryIdealGenerator J)‖ := by
  rw [unramifiedResidualCoefficient_squarefree_cube_norm I J hI hJ hsq u m]
  exact (mul_le_mul_of_nonneg_left (unramifiedResidualCoefficient_ramified_bound u m)
    (norm_nonneg _)).trans_eq (by ring)

theorem rationalSourceResidualFourierCoefficient_squarefree_cube_bound (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I)
    (u : Oˣ) (m : ℕ) :
    ‖rationalSourceResidualFourierCoefficient
      (((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)‖ ≤
      sourceCoefficientBaseBound * ‖ringComplex ((u : O) * lambda ^ m)‖ ^ (1 / 3 : ℝ) *
        ‖ringComplex (primaryIdealGenerator J)‖ := by
  rw [rationalSourceResidualFourierCoefficient_full_squarefree_cube_norm I J hI hJ hsq u m]
  exact (mul_le_mul_of_nonneg_left (rationalSourceResidualFourierCoefficient_ramified_bound u m)
    (norm_nonneg _)).trans_eq (by ring)

/-- Removing the finite-character mask leaves a bound independent of frequency. -/
def scaledAffineGaussBound (q : O) : ℝ :=
  ‖(Ideal.absNorm (Ideal.span {3 * q}) : ℂ) *
    ((‖ringComplex (3 * q)‖ ^ 2 : ℝ) : ℂ) ^ (-(4 / 3 : ℂ))‖

lemma scaledAffineGaussWeight_bound (q : O) (u : Oˣ) (n : ℕ) (h : O) :
    ‖scaledAffineGaussWeight q u n h (4 / 3)‖ ≤ scaledAffineGaussBound q := by
  unfold scaledAffineGaussWeight
  split_ifs
  · rw [norm_mul, tracePhase_norm, mul_one]
    exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _
  · rw [norm_zero]
    exact norm_nonneg _

def ramifiedSixWeightBound (u t : Oˣ) : RamifiedSixBranch → ℝ
  | .inl _ => (4 : ℝ)⁻¹ * scaledAffineGaussBound (u : O)
  | .inr (.inl _) => (4 : ℝ)⁻¹ * scaledAffineGaussBound (-(u : O))
  | .inr (.inr (.inl _)) => (4 : ℝ)⁻¹ * scaledAffineGaussBound 1
  | .inr (.inr (.inr j)) => (4 : ℝ)⁻¹ * scaledAffineGaussBound (onceCuspScale t * omega ^ j.val)

lemma ramifiedSixWeightBound_nonneg (u t : Oˣ) (i : RamifiedSixBranch) :
    0 ≤ ramifiedSixWeightBound u t i := by
  rcases i with i | i
  · exact mul_nonneg (by norm_num) (norm_nonneg _)
  rcases i with i | i
  · exact mul_nonneg (by norm_num) (norm_nonneg _)
  rcases i with i | i <;> exact mul_nonneg (by norm_num) (norm_nonneg _)

lemma ramifiedSixWeight_norm_bound (u t : Oˣ) (h : O) (i : RamifiedSixBranch) :
    ‖ramifiedSixWeight u t h i (4 / 3)‖ ≤ ramifiedSixWeightBound u t i := by
  rcases i with i | i
  · simpa only [ramifiedSixWeight, ramifiedSixWeightBound, norm_mul, norm_inv, Complex.norm_ofNat]
      using mul_le_mul_of_nonneg_left (scaledAffineGaussWeight_bound (u : O) u 0 h) (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  rcases i with i | i
  · simpa only [ramifiedSixWeight, ramifiedSixWeightBound, norm_mul, norm_inv, Complex.norm_ofNat,
      tracePhase_norm, mul_one] using mul_le_mul_of_nonneg_left
        (scaledAffineGaussWeight_bound (-(u : O)) ((-u)⁻¹ ^ 2 * (-u)) 0 h) (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  rcases i with i | j
  · simpa only [ramifiedSixWeight, ramifiedSixWeightBound, norm_mul, norm_inv, Complex.norm_ofNat,
      tracePhase_norm, mul_one] using mul_le_mul_of_nonneg_left
        (scaledAffineGaussWeight_bound 1 ((-u)⁻¹ ^ 2) 0 h) (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  · simpa only [ramifiedSixWeight, ramifiedSixWeightBound, norm_mul, norm_inv, Complex.norm_ofNat,
      tracePhase_norm, mul_one] using mul_le_mul_of_nonneg_left
        (scaledAffineGaussWeight_bound (onceCuspScale t * omega ^ j.val)
          (onceCuspArithmeticUnit (-u) t j) 1 h) (by norm_num : (0 : ℝ) ≤ 4⁻¹)

/-- The ramified multiplier cancels exactly against the Bessel normalization. -/
lemma normalizedRamifiedGaussTerm_squarefree_cube_bound (v : Oˣ) (n : ℕ) (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I)
    (u : Oˣ) (m : ℕ) :
    ‖sourceBesselNormalizer (((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3) *
      unramifiedGaussResidue (((v : O) * lambda ^ n) *
        (((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3))‖ ≤
      unramifiedCoefficientBaseBound * ‖ringComplex ((u : O) * lambda ^ m)‖ ^ (1 / 3 : ℝ) *
        ‖ringComplex (primaryIdealGenerator J)‖ := by
  let a := (v : O) * lambda ^ n
  let b := (u : O) * lambda ^ m
  let h := b * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3
  have ha : a ≠ 0 := ramifiedElement_ne_zero v n
  have ht : 0 < ‖ringComplex a‖ ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero ha)) _
  have he : a * b = ((v * u : Oˣ) : O) * lambda ^ (n + m) := by
    simp only [a, b, Units.val_mul, pow_add]
    ring
  have hbnd : ‖unramifiedResidualCoefficient (a * h)‖ ≤
      unramifiedCoefficientBaseBound * ‖ringComplex (a * b)‖ ^ (1 / 3 : ℝ) *
        ‖ringComplex (primaryIdealGenerator J)‖ := by
    change ‖unramifiedResidualCoefficient (a * (b * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3))‖ ≤ _
    rw [← mul_assoc, ← mul_assoc, he]
    exact unramifiedResidualCoefficient_squarefree_cube_bound I J hI hJ hsq (v * u) (n + m)
  have hn : ‖sourceBesselNormalizer h * unramifiedGaussResidue (a * h)‖ *
      ‖ringComplex a‖ ^ (1 / 3 : ℝ) = ‖unramifiedResidualCoefficient (a * h)‖ := by
    rw [unramifiedResidualCoefficient, norm_mul, norm_mul,
      mul_comm a h, sourceBesselNormalizer_mul_norm h a ha]
    ring
  have he : ‖sourceBesselNormalizer h * unramifiedGaussResidue (a * h)‖ *
      ‖ringComplex a‖ ^ (1 / 3 : ℝ) ≤
      (unramifiedCoefficientBaseBound * ‖ringComplex b‖ ^ (1 / 3 : ℝ) *
        ‖ringComplex (primaryIdealGenerator J)‖) * ‖ringComplex a‖ ^ (1 / 3 : ℝ) := by
    rw [hn]
    refine hbnd.trans_eq ?_
    rw [map_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    ring
  change ‖sourceBesselNormalizer h * unramifiedGaussResidue (a * h)‖ ≤ _
  nlinarith only [ht, he]

def ramifiedCoefficientBaseBound (u t : Oˣ) : ℝ :=
  ‖(3 : ℂ) ^ (4 / 3 : ℂ) / ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)‖ *
    (∑ i : RamifiedSixBranch, ramifiedSixWeightBound u t i) * unramifiedCoefficientBaseBound

lemma ramifiedCoefficientBaseBound_nonneg (u t : Oˣ) : 0 ≤ ramifiedCoefficientBaseBound u t :=
  mul_nonneg (mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg (fun i _ => ramifiedSixWeightBound_nonneg u t i))) unramifiedCoefficientBaseBound_nonneg

/-- All six ramified branches obey the same squarefree–cube bound. -/
theorem ramifiedResidualFourierCoefficient_squarefree_cube_bound (v t : Oˣ) (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hJ : primaryIdealGenerator J ≠ 0) (hsq : Squarefree I)
    (u : Oˣ) (m : ℕ) :
    ‖ramifiedResidualFourierCoefficient v t
      (((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)‖ ≤
      ramifiedCoefficientBaseBound v t * ‖ringComplex ((u : O) * lambda ^ m)‖ ^ (1 / 3 : ℝ) *
        ‖ringComplex (primaryIdealGenerator J)‖ := by
  let h := ((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3
  let D := unramifiedCoefficientBaseBound * ‖ringComplex ((u : O) * lambda ^ m)‖ ^ (1 / 3 : ℝ) *
    ‖ringComplex (primaryIdealGenerator J)‖
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg unramifiedCoefficientBaseBound_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg _)
  have hs : ‖sourceBesselNormalizer h * ramifiedArithmeticResidue v t h‖ ≤
      (∑ i : RamifiedSixBranch, ramifiedSixWeightBound v t i) * D := by
    have he : sourceBesselNormalizer h * ramifiedArithmeticResidue v t h =
        ∑ i : RamifiedSixBranch, ramifiedSixWeight v t h i (4 / 3) *
          (sourceBesselNormalizer h * unramifiedGaussResidue (ramifiedSixIndex v t h i)) := by
      rw [ramifiedArithmeticResidue, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro i hi
    by_cases hw : ramifiedSixWeight v t h i (4 / 3) = 0
    · rw [hw, zero_mul, norm_zero]
      exact mul_nonneg (ramifiedSixWeightBound_nonneg v t i) hD
    rw [norm_mul, ramifiedSixIndex_multiplier v t h i hw]
    exact mul_le_mul (ramifiedSixWeight_norm_bound v t h i)
      (normalizedRamifiedGaussTerm_squarefree_cube_bound (ramifiedSixUnit v t i) (ramifiedSixPower i)
        I J hI hJ hsq u m) (norm_nonneg _) (ramifiedSixWeightBound_nonneg v t i)
  have he : ramifiedResidualFourierCoefficient v t h =
      ((3 : ℂ) ^ (4 / 3 : ℂ) / ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) *
        (sourceBesselNormalizer h * ramifiedArithmeticResidue v t h) := by
    unfold ramifiedResidualFourierCoefficient sourceBesselNormalizer
    ring
  change ‖ramifiedResidualFourierCoefficient v t h‖ ≤ _
  rw [he, norm_mul]
  exact (mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans_eq
    (by unfold ramifiedCoefficientBaseBound; dsimp only [D]; ring)

lemma squarefreeCube_scale_le_norm_third (I J : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (u : Oˣ) (m : ℕ) :
    ‖ringComplex ((u : O) * lambda ^ m)‖ ^ (1 / 3 : ℝ) * ‖ringComplex (primaryIdealGenerator J)‖ ≤
      ‖ringComplex (((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)‖ ^ (1 / 3 : ℝ) := by
  have hn : 1 ≤ ‖ringComplex (primaryIdealGenerator I)‖ := by
    have hs := one_le_normSq_embedding (primaryIdealGenerator I) hI
    rw [Complex.normSq_eq_norm_sq] at hs
    have hp := norm_nonneg (ringComplex (primaryIdealGenerator I))
    nlinarith only [hs, hp]
  have hn' := Real.one_le_rpow hn (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hc : (‖ringComplex (primaryIdealGenerator J)‖ ^ 3) ^ (1 / 3 : ℝ) =
      ‖ringComplex (primaryIdealGenerator J)‖ := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    norm_num
  conv_rhs => rw [map_mul, map_mul, map_pow, norm_mul, norm_mul, norm_pow]
  rw [Real.mul_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _),
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _), hc]
  exact mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right (Real.rpow_nonneg (norm_nonneg _) _) hn') (norm_nonneg _)

/-- Squarefree–cube support and its sharp coefficient bound imply cubic-root growth. -/
lemma coefficient_polynomial_of_squarefree_cube_support (F : O → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsupport : ∀ h : O, h ≠ 0 → F h ≠ 0 → ∃ (u : Oˣ) (m : ℕ) (I J : Ideal O),
      Squarefree I ∧ primaryIdealGenerator I ≠ 0 ∧ primaryIdealGenerator J ≠ 0 ∧
      h = ((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)
    (hbound : ∀ (I J : Ideal O), primaryIdealGenerator I ≠ 0 → primaryIdealGenerator J ≠ 0 → Squarefree I →
      ∀ (u : Oˣ) (m : ℕ),
      ‖F (((u : O) * lambda ^ m) * primaryIdealGenerator I * (primaryIdealGenerator J) ^ 3)‖ ≤
        C * ‖ringComplex ((u : O) * lambda ^ m)‖ ^ (1 / 3 : ℝ) * ‖ringComplex (primaryIdealGenerator J)‖)
    (h : O) (hh : h ≠ 0) : ‖F h‖ ≤ C * ‖ringComplex h‖ ^ (1 / 3 : ℝ) := by
  by_cases hz : F h = 0
  · rw [hz, norm_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)
  obtain ⟨u, m, I, J, hsq, hI, hJ, rfl⟩ := hsupport h hh hz
  refine (hbound I J hI hJ hsq u m).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (squarefreeCube_scale_le_norm_third I J hI u m) hC

theorem unramifiedResidualCoefficient_polynomial_bound (h : O) (hh : h ≠ 0) :
    ‖unramifiedResidualCoefficient h‖ ≤ unramifiedCoefficientBaseBound * ‖ringComplex h‖ ^ (1 / 3 : ℝ) :=
  coefficient_polynomial_of_squarefree_cube_support _ _ unramifiedCoefficientBaseBound_nonneg
    unramifiedResidualCoefficient_full_squarefree_cube_support
    unramifiedResidualCoefficient_squarefree_cube_bound h hh

theorem rationalSourceResidualFourierCoefficient_polynomial_bound (h : O) (hh : h ≠ 0) :
    ‖rationalSourceResidualFourierCoefficient h‖ ≤ sourceCoefficientBaseBound * ‖ringComplex h‖ ^ (1 / 3 : ℝ) :=
  coefficient_polynomial_of_squarefree_cube_support _ _ sourceCoefficientBaseBound_nonneg
    rationalSourceResidualFourierCoefficient_full_squarefree_cube_support
    rationalSourceResidualFourierCoefficient_squarefree_cube_bound h hh

theorem ramifiedBesselCoefficient_polynomial_bound (side : Bool) (h : O) (hh : h ≠ 0) :
    ‖ramifiedBesselCoefficient side h‖ ≤
      ramifiedCoefficientBaseBound (ramifiedCuspRoot side) (ramifiedCuspScaleUnit side) * ‖ringComplex h‖ ^ (1 / 3 : ℝ) :=
  coefficient_polynomial_of_squarefree_cube_support _ _ (ramifiedCoefficientBaseBound_nonneg _ _)
    (ramifiedBesselCoefficient_full_squarefree_cube_support side)
    (ramifiedResidualFourierCoefficient_squarefree_cube_bound _ _) h hh

abbrev ThetaPrimaryCubePair :=
  {I : Ideal O // Squarefree I ∧ primaryIdealGenerator I ≠ 0} × GoodIdeal

def thetaPrimaryProduct (p : ThetaPrimaryCubePair) : GoodIdeal :=
  ⟨p.1.val * p.2.val ^ 3, by
    rw [primaryIdealGenerator_mul, primaryIdealGenerator_pow]
    exact mul_ne_zero p.1.property.2 (pow_ne_zero 3 p.2.property)⟩

lemma thetaPrimaryProduct_injective : Function.Injective thetaPrimaryProduct := by
  intro p q he
  have hi : p.1.val * p.2.val ^ 3 = q.1.val * q.2.val ^ 3 := congrArg Subtype.val he
  obtain ⟨hI, hJ⟩ := squarefree_cube_decomposition_unique
    (primaryIdealGenerator_ne_zero_ideal _ p.2.property)
    (primaryIdealGenerator_ne_zero_ideal _ q.2.property) p.1.property.1 q.1.property.1 hi
  exact Prod.ext (Subtype.ext hI) (Subtype.ext hJ)

/-- Unit, ramified exponent, squarefree ideal, and cube ideal index the supported frequencies uniquely. -/
abbrev ThetaFullIndex := Oˣ × ℕ × ThetaPrimaryCubePair

def thetaFullFrequency (p : ThetaFullIndex) : O :=
  ((p.1 : O) * lambda ^ p.2.1) * primaryIdealGenerator p.2.2.1.val *
    (primaryIdealGenerator p.2.2.2.val) ^ 3

lemma thetaFullFrequency_product (p : ThetaFullIndex) :
    thetaFullFrequency p = (p.1 : O) *
      (lambda ^ p.2.1 * primaryIdealGenerator (thetaPrimaryProduct p.2.2).val) := by
  simp only [thetaFullFrequency, thetaPrimaryProduct, primaryIdealGenerator_mul, primaryIdealGenerator_pow]
  ring

lemma thetaFullFrequency_ne_zero (p : ThetaFullIndex) : thetaFullFrequency p ≠ 0 := by
  rw [thetaFullFrequency_product]
  exact mul_ne_zero p.1.ne_zero (mul_ne_zero (pow_ne_zero _ residue_lambda_prime.ne_zero)
    (thetaPrimaryProduct p.2.2).property)

lemma thetaFullFrequency_span (p : ThetaFullIndex) :
    Ideal.span {thetaFullFrequency p} = ramifiedIdeal ^ p.2.1 * (thetaPrimaryProduct p.2.2).val := by
  have hu : Ideal.span {(p.1 : O)} = (1 : Ideal O) := by
    rw [Ideal.one_eq_top]
    exact Ideal.span_singleton_eq_top.mpr p.1.isUnit
  rw [thetaFullFrequency_product, ← Ideal.span_singleton_mul_span_singleton, hu, one_mul,
    lambdaFactor_generator_span]

theorem thetaFullFrequency_injective : Function.Injective thetaFullFrequency := by
  rintro ⟨u, m, p⟩ ⟨v, n, q⟩ he
  have hs := congrArg (fun x : O => Ideal.span {x}) he
  rw [thetaFullFrequency_span, thetaFullFrequency_span] at hs
  have hmap : lambdaFactorMap (m, thetaPrimaryProduct p) = lambdaFactorMap (n, thetaPrimaryProduct q) :=
    Subtype.ext hs
  have hij := lambdaFactorMap_bijective.1 hmap
  have hmn : m = n := congrArg Prod.fst hij
  have hpq : p = q := thetaPrimaryProduct_injective (congrArg Prod.snd hij)
  subst n
  subst q
  have huv : u = v := by
    apply Units.ext
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero m residue_lambda_prime.ne_zero)
      (thetaPrimaryProduct p).property)
    simpa only [thetaFullFrequency_product] using he
  subst v
  rfl

/-- Reindex every supported nonzero Fourier sum without introducing multiplicities. -/
theorem thetaFullFrequency_tsum (c w : O → ℂ)
    (hsupp : ∀ h : O, h ≠ 0 → c h ≠ 0 → ∃ p : ThetaFullIndex, thetaFullFrequency p = h) :
    (∑' h : {h : O // h ≠ 0}, w h.val * c h.val) =
      ∑' p : ThetaFullIndex, w (thetaFullFrequency p) * c (thetaFullFrequency p) := by
  let φ : ThetaFullIndex → {h : O // h ≠ 0} := fun p => ⟨thetaFullFrequency p, thetaFullFrequency_ne_zero p⟩
  let f : {h : O // h ≠ 0} → ℂ := fun h => w h.val * c h.val
  have hinj : Function.Injective φ := fun p q hpq => thetaFullFrequency_injective (congrArg Subtype.val hpq)
  change (∑' h, f h) = ∑' p, f (φ p)
  apply tsum_eq_tsum_of_ne_zero_bij (fun p : Function.support (fun p : ThetaFullIndex => f (φ p)) => φ p.val)
  · exact hinj.comp Subtype.val_injective
  · intro h hh
    have hc : c h.val ≠ 0 := by intro hz; exact hh (by simp only [f, hz, mul_zero])
    obtain ⟨p, hp⟩ := hsupp h.val h.property hc
    have hφ : φ p = h := Subtype.ext hp
    exact ⟨⟨p, by change f (φ p) ≠ 0; rwa [hφ]⟩, hφ⟩
  · intro p
    rfl

theorem sourceFourier_tsum_full_index (w : O → ℂ) :
    (∑' h : {h : O // h ≠ 0}, w h.val * star (rationalSourceResidualFourierCoefficient h.val)) =
      ∑' p : ThetaFullIndex, w (thetaFullFrequency p) *
        star (rationalSourceResidualFourierCoefficient (thetaFullFrequency p)) := by
  apply thetaFullFrequency_tsum (fun h => star (rationalSourceResidualFourierCoefficient h)) w
  intro h hh hc
  have hn : rationalSourceResidualFourierCoefficient h ≠ 0 := by
    intro hz
    exact hc (by rw [hz, star_zero])
  obtain ⟨u, m, I, J, hsq, hI, hJ, he⟩ :=
    rationalSourceResidualFourierCoefficient_full_squarefree_cube_support h hh hn
  exact ⟨(u, m, (⟨I, hsq, hI⟩, ⟨J, hJ⟩)), he.symm⟩

theorem ramifiedFourier_tsum_full_index (side : Bool) (w : O → ℂ) :
    (∑' h : {h : O // h ≠ 0}, w h.val * star (ramifiedBesselCoefficient side h.val)) =
      ∑' p : ThetaFullIndex, w (thetaFullFrequency p) * star (ramifiedBesselCoefficient side (thetaFullFrequency p)) := by
  apply thetaFullFrequency_tsum (fun h => star (ramifiedBesselCoefficient side h)) w
  intro h hh hc
  have hn : ramifiedBesselCoefficient side h ≠ 0 := by
    intro hz
    exact hc (by rw [hz, star_zero])
  obtain ⟨u, m, I, J, hsq, hI, hJ, he⟩ := ramifiedBesselCoefficient_full_squarefree_cube_support side h hh hn
  exact ⟨(u, m, (⟨I, hsq, hI⟩, ⟨J, hJ⟩)), he.symm⟩

/-- Cubic-root coefficient growth gives an absolutely summable fourth-power frequency weight. -/
lemma coefficient_weighted_summable_of_polynomial (F : O → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ h : O, h ≠ 0 → ‖F h‖ ≤ C * ‖ringComplex h‖ ^ (1 / 3 : ℝ)) :
    Summable (fun h : O => if h = 0 then (0 : ℝ) else ‖F h‖ * ‖cuspFrequency h‖ ^ (-4 : ℝ)) := by
  let D : ℝ := ‖(3 : ℂ) * ringComplex traceLambda‖
  have hD : 0 < D := norm_pos_iff.mpr (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero))
  have hp : 0 < D ^ (-4 : ℝ) := Real.rpow_pos_of_pos hD _
  have hs := (summable_embedding_rpow (-11 / 3) (by norm_num)).mul_left (C / D ^ (-4 : ℝ))
  apply Summable.of_nonneg_of_le (fun h => by split_ifs <;> positivity) _ hs
  intro h
  split_ifs with hh
  · exact mul_nonneg (div_nonneg hC hp.le) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hx : 0 < ‖ringComplex h‖ := norm_pos_iff.mpr (ringComplex_ne_zero hh)
    have he : ‖ringComplex h‖ ^ (1 / 3 : ℝ) * ‖ringComplex h‖ ^ (-4 : ℝ) =
        ‖ringComplex h‖ ^ (-11 / 3 : ℝ) := by
      rw [← Real.rpow_add hx]
      congr 1
      norm_num
    calc
      _ ≤ (C * ‖ringComplex h‖ ^ (1 / 3 : ℝ)) * ‖cuspFrequency h‖ ^ (-4 : ℝ) :=
        mul_le_mul_of_nonneg_right (hF h hh) (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (C / D ^ (-4 : ℝ)) * (‖ringComplex h‖ ^ (1 / 3 : ℝ) * ‖ringComplex h‖ ^ (-4 : ℝ)) := by
        rw [cuspFrequency, norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
        change (C * ‖ringComplex h‖ ^ (1 / 3 : ℝ)) * (‖ringComplex h‖ ^ (-4 : ℝ) / D ^ (-4 : ℝ)) = _
        ring
      _ = _ := by rw [he]

theorem sourceCoefficient_weighted_summable :
    Summable (fun h : O => if h = 0 then (0 : ℝ) else
      ‖rationalSourceResidualFourierCoefficient h‖ * ‖cuspFrequency h‖ ^ (-4 : ℝ)) :=
  coefficient_weighted_summable_of_polynomial _ _ sourceCoefficientBaseBound_nonneg
    rationalSourceResidualFourierCoefficient_polynomial_bound

theorem ramifiedCoefficient_weighted_summable (side : Bool) :
    Summable (fun h : O => if h = 0 then (0 : ℝ) else
      ‖ramifiedBesselCoefficient side h‖ * ‖cuspFrequency h‖ ^ (-4 : ℝ)) :=
  coefficient_weighted_summable_of_polynomial _ _ (ramifiedCoefficientBaseBound_nonneg _ _)
    (ramifiedBesselCoefficient_polynomial_bound side)

def sourceCuspCoefficient (j : Fin 3) : O → ℂ :=
  ![rationalSourceResidualFourierCoefficient, ramifiedBesselCoefficient false, ramifiedBesselCoefficient true] j

def sourceCuspScale (j : Fin 3) : ℝ := ![1, 3, 3] j

lemma sourceCuspScale_pos (j : Fin 3) : 0 < sourceCuspScale j := by
  fin_cases j <;> norm_num [sourceCuspScale]

def sourceCuspCoefficientBound (j : Fin 3) : ℝ :=
  ![sourceCoefficientBaseBound,
    ramifiedCoefficientBaseBound (ramifiedCuspRoot false) (ramifiedCuspScaleUnit false),
    ramifiedCoefficientBaseBound (ramifiedCuspRoot true) (ramifiedCuspScaleUnit true)] j

lemma sourceCuspCoefficientBound_nonneg (j : Fin 3) : 0 ≤ sourceCuspCoefficientBound j := by
  fin_cases j
  · exact sourceCoefficientBaseBound_nonneg
  · exact ramifiedCoefficientBaseBound_nonneg _ _
  · exact ramifiedCoefficientBaseBound_nonneg _ _

theorem sourceCuspCoefficient_polynomial_bound (j : Fin 3) (h : O) (hh : h ≠ 0) :
    ‖sourceCuspCoefficient j h‖ ≤ sourceCuspCoefficientBound j * ‖ringComplex h‖ ^ (1 / 3 : ℝ) := by
  fin_cases j
  · exact rationalSourceResidualFourierCoefficient_polynomial_bound h hh
  · exact ramifiedBesselCoefficient_polynomial_bound false h hh
  · exact ramifiedBesselCoefficient_polynomial_bound true h hh

theorem sourceCuspCoefficient_weighted_summable (j : Fin 3) :
    Summable (fun h : O => if h = 0 then (0 : ℝ) else
      ‖sourceCuspCoefficient j h‖ * ‖cuspFrequency h‖ ^ (-4 : ℝ)) :=
  coefficient_weighted_summable_of_polynomial _ _ (sourceCuspCoefficientBound_nonneg j)
    (sourceCuspCoefficient_polynomial_bound j)

theorem sourceCuspCoefficient_tsum_full_index (j : Fin 3) (w : O → ℂ) :
    (∑' h : {h : O // h ≠ 0}, w h.val * star (sourceCuspCoefficient j h.val)) =
      ∑' p : ThetaFullIndex, w (thetaFullFrequency p) * star (sourceCuspCoefficient j (thetaFullFrequency p)) := by
  fin_cases j
  · exact sourceFourier_tsum_full_index w
  · exact ramifiedFourier_tsum_full_index false w
  · exact ramifiedFourier_tsum_full_index true w

def sourceCuspBarCoefficient (j : Fin 3) : O → ℂ :=
  ![sourceBarBesselCoefficient, ramifiedBarBesselCoefficient false, ramifiedBarBesselCoefficient true] j

lemma sourceCuspBarCoefficient_subexponential (j : Fin 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖sourceCuspBarCoefficient j h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) := by
  fin_cases j
  · exact sourceBarBesselCoefficient_subexponential ε hε
  · exact ramifiedBarBesselCoefficient_subexponential false ε hε
  · exact ramifiedBarBesselCoefficient_subexponential true ε hε

def sourceCuspZTerm (j : Fin 3) (z : ℂ) (v : ℝ) (h : O) : ℂ :=
  star (cubicBesselTerm (sourceCuspBarCoefficient j) h (v / sourceCuspScale j, z / (sourceCuspScale j : ℂ)))

theorem sourceCuspZFamily_series (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceCuspZFamily j z v = ∑' h : O, sourceCuspZTerm j z v h := by
  have h0 : cuspZProfile (fun w => star (cubicSourceResidualFunction w)) z v =
      ∑' h : O, star (cubicBesselTerm sourceBarBesselCoefficient h (v, z)) := by
    rw [conjugateSource_zProfile z v hv, cuspBarProfile_positive _ _ _ hv,
      cubicSource_wirtingerBar_bessel v hv z, tsum_star]
  have hr (side : Bool) : cuspZProfile
      (fun w => star (ramifiedSourceFunction (ramifiedCuspRoot side : O) w)) z v =
      ∑' h : O, star (cubicBesselTerm (ramifiedBarBesselCoefficient side) h (v / 3, z / 3)) := by
    rw [conjugateRamifiedSource_zProfile side z v hv, cuspBarProfile_positive _ _ _ hv,
      ramifiedSource_wirtingerBar_bessel side v hv z, tsum_star]
  fin_cases j
  · simpa [sourceCuspZFamily, sourceCuspZTerm, sourceCuspBarCoefficient, sourceCuspScale,
      cuspRepresentative, cuspParameter, lowerCuspMatrix_zero] using h0
  · simpa [sourceCuspZFamily, sourceCuspZTerm, sourceCuspBarCoefficient, sourceCuspScale,
      cuspRepresentative, cuspParameter, ramifiedSourceFunction, ramifiedCuspRoot, cuspOmegaUnit_val] using hr false
  · simpa [sourceCuspZFamily, sourceCuspZTerm, sourceCuspBarCoefficient, sourceCuspScale,
      cuspRepresentative, cuspParameter, ramifiedSourceFunction, ramifiedCuspRoot, cuspOmegaUnit_val] using hr true

theorem sourceCuspZTerm_summable (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    Summable (sourceCuspZTerm j z v) := by
  apply Summable.of_norm
  simpa only [sourceCuspZTerm, norm_star] using
    cubicBesselTerm_summable_norm (sourceCuspBarCoefficient j) (sourceCuspBarCoefficient_subexponential j)
      (v / sourceCuspScale j, z / (sourceCuspScale j : ℂ)) (div_pos hv (sourceCuspScale_pos j))

lemma sourceCuspZTerm_zero (j : Fin 3) (z : ℂ) (v : ℝ) : sourceCuspZTerm j z v 0 = 0 := by
  simp only [sourceCuspZTerm, cubicBesselTerm, cubicBesselAmplitude, if_true, zero_mul, star_zero]

lemma sourceCuspBarCoefficient_eq (j : Fin 3) (h : O) :
    sourceCuspBarCoefficient j h =
      (2 * Real.pi * Complex.I * star (cuspFrequency h) / (sourceCuspScale j : ℂ)) * sourceCuspCoefficient j h := by
  fin_cases j
  · simp [sourceCuspBarCoefficient, sourceCuspScale, sourceCuspCoefficient, sourceBarBesselCoefficient]
  · simp [sourceCuspBarCoefficient, sourceCuspScale, sourceCuspCoefficient,
      ramifiedBarBesselCoefficient, ninthCuspFrequency_eq_third, star_div₀, mul_div_assoc]
  · simp [sourceCuspBarCoefficient, sourceCuspScale, sourceCuspCoefficient,
      ramifiedBarBesselCoefficient, ninthCuspFrequency_eq_third, star_div₀, mul_div_assoc]

lemma sourceCuspZTerm_bessel (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    sourceCuspZTerm j z v h =
      (-2 * Real.pi * Complex.I * cuspFrequency h / (sourceCuspScale j : ℂ)) *
        star (sourceCuspCoefficient j h) * ((v / sourceCuspScale j : ℝ) : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * (v / sourceCuspScale j)) *
          tracePhase (-cuspFrequency h * (z / (sourceCuspScale j : ℂ))) := by
  rw [sourceCuspZTerm, cubicBesselTerm, cubicBesselAmplitude, if_neg hh, sourceCuspBarCoefficient_eq]
  simp only [star_mul, star_div₀, star_star, Complex.star_def, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.star_def, star_schlafliBesselK_cubic _
    (mul_pos (mul_pos (by positivity) (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)))
      (div_pos hv (sourceCuspScale_pos j)))]
  rw [star_tracePhase, star_star, neg_mul]
  ring

def thetaFrequencyScale : ℂ := 1 / ((3 : ℂ) * ringComplex traceLambda)

def thetaBesselScale : ℝ := ‖thetaFrequencyScale‖

lemma thetaBesselScale_pos : 0 < thetaBesselScale :=
  norm_pos_iff.mpr (one_div_ne_zero (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero)))

lemma cuspFrequency_eq_thetaFrequencyScale (h : O) : cuspFrequency h = thetaFrequencyScale * ringComplex h := by
  unfold cuspFrequency thetaFrequencyScale
  ring

def sourceCuspRadialLength (h : O) : ℝ := if h = 0 then 1 else ‖ringComplex h‖ ^ 2

def sourceCuspRadialScale (j : Fin 3) : ℝ := thetaBesselScale / sourceCuspScale j

def sourceCuspRadialBaseCoefficient (j : Fin 3) (h : O) : ℂ :=
  (-2 * Real.pi * Complex.I * cuspFrequency h) * star (sourceCuspCoefficient j h) /
    ((sourceCuspScale j : ℂ) ^ 2 * (sourceCuspRadialLength h : ℂ))

def sourceCuspRadialCoefficient (j : Fin 3) (z : ℂ) (h : O) : ℂ :=
  sourceCuspRadialBaseCoefficient j h * tracePhase (-cuspFrequency h * (z / (sourceCuspScale j : ℂ)))

lemma sourceCuspRadialLength_pos (h : O) : 0 < sourceCuspRadialLength h := by
  by_cases hh : h = 0
  · simp only [sourceCuspRadialLength, if_pos hh, zero_lt_one]
  · rw [sourceCuspRadialLength, if_neg hh]
    exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hh))

lemma sourceCuspRadialScale_pos (j : Fin 3) : 0 < sourceCuspRadialScale j :=
  div_pos thetaBesselScale_pos (sourceCuspScale_pos j)

lemma sourceCuspRadialCoefficient_norm (j : Fin 3) (z : ℂ) (h : O) :
    ‖sourceCuspRadialCoefficient j z h‖ = ‖sourceCuspRadialBaseCoefficient j h‖ := by
  rw [sourceCuspRadialCoefficient, norm_mul, tracePhase_norm, mul_one]

lemma sourceCuspRadialCoefficient_zero (j : Fin 3) (z : ℂ) : sourceCuspRadialCoefficient j z 0 = 0 := by
  simp only [sourceCuspRadialCoefficient, sourceCuspRadialBaseCoefficient, cuspFrequency,
    map_zero, zero_div, mul_zero, zero_mul]

lemma sourceCuspRadialLength_frequency (h : O) (hh : h ≠ 0) :
    ‖cuspFrequency h‖ = thetaBesselScale * Real.sqrt (sourceCuspRadialLength h) := by
  rw [cuspFrequency_eq_thetaFrequencyScale, norm_mul, sourceCuspRadialLength, if_neg hh,
    Real.sqrt_sq (norm_nonneg _)]
  rfl

/-- A radial coefficient is normalized so its Mellin series uses the squared frequency length. -/
def radialBesselProfile {ι : Type*} (length : ι → ℝ) (coefficient : ι → ℂ) (scale : ℝ) (v : ℝ) : ℂ :=
  ∑' h : ι, (coefficient h * (length h : ℂ)) * (v : ℂ) *
    schlafliBesselK (1 / 3) (4 * Real.pi * scale * Real.sqrt (length h) * v)

theorem sourceCuspZTerm_eq_radial (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0 < v) (h : O) :
    sourceCuspZTerm j z v h =
      (sourceCuspRadialCoefficient j z h * (sourceCuspRadialLength h : ℂ)) * (v : ℂ) *
        schlafliBesselK (1 / 3) (4 * Real.pi * sourceCuspRadialScale j *
          Real.sqrt (sourceCuspRadialLength h) * v) := by
  by_cases hh : h = 0
  · subst h
    rw [sourceCuspZTerm_zero, sourceCuspRadialCoefficient_zero]
    ring
  rw [sourceCuspZTerm_bessel j z v hv h hh, sourceCuspRadialLength_frequency h hh]
  rw [show 4 * Real.pi * (thetaBesselScale * Real.sqrt (sourceCuspRadialLength h)) * (v / sourceCuspScale j) =
    4 * Real.pi * sourceCuspRadialScale j * Real.sqrt (sourceCuspRadialLength h) * v by
      unfold sourceCuspRadialScale; ring]
  have hs := Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
  have hl := Complex.ofReal_ne_zero.mpr (sourceCuspRadialLength_pos h).ne'
  simp only [sourceCuspRadialCoefficient, sourceCuspRadialBaseCoefficient, Complex.ofReal_div]
  field_simp [hs, hl]

theorem sourceCuspZFamily_eq_radialBesselProfile (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceCuspZFamily j z v =
      radialBesselProfile sourceCuspRadialLength (sourceCuspRadialCoefficient j z) (sourceCuspRadialScale j) v := by
  rw [sourceCuspZFamily_series j z v hv]
  exact tsum_congr (sourceCuspZTerm_eq_radial j z v hv)

theorem SourceCuspDatum.reflection_radial (d : SourceCuspDatum) (v : ℝ) (hv : 0 < v) :
    cuspBarProfile (fun w => star (cubicSourceResidualFunction w)) d.point v =
      d.multiplier / (v : ℂ) ^ 2 *
        radialBesselProfile sourceCuspRadialLength (sourceCuspRadialCoefficient d.index d.dualPoint)
          (sourceCuspRadialScale d.index) ((d.heightScale * v)⁻¹) := by
  rw [d.reflection v hv, sourceCuspZFamily_eq_radialBesselProfile _ _ _
    (inv_pos.mpr (mul_pos d.heightScale_pos hv))]

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
