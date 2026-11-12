import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubeFrequenciesOfTheThetaSquareFactorOut
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheMellinTransformOfTheThetaSquareReadsItsDirichletSeries

/-!
# The squared theta series splits into nine twists

Every nonzero frequency is uniquely `h = u λ^m gen(I)` (`u` a unit, `I` unramified; `frequencySplit`),
and the coefficients `T = T_s` of the projected cubic theta function are *twisted* multiplicative across
this split (`sourceCoefficient_twisted_mul`): for `h₀` coprime to `gen I`,

`T(h₀ gen I) T(1) = (h₀/gen I)₃ T(h₀) T(gen I)`.

(Squarefree part: the prime-product law `T(h ∏p) = (9h/∏p)₃ \overline{G̃(∏p)} T(h)` at `h = h₀` and `h = 1`;
cube part: `T(h b³) = |b| T(h)`; a prime valuation `≡ 2 mod 3` kills both sides.) Hence, for `Re s > 4`
(`thetaSqDirichlet_eq_twisted`),

`D(s) = Σ_{u, m} (T(uλ^m)/T(1))² (4π|ξ_{uλ^m}|)^{−s} P_{uλ^m}(s/2)`,
`P_{h₀}(w) = Σ_I N(I)^{−w} (h₀/gen I)₃² T(gen I)²`  (unramified ideals),

and every twist carries the cube factor (`twistedPrimarySeries_eq`, `Re w > 1`):

`P_{uλ^m}(w) = \overline{C}² Z₀(3w − 1) S_{uλ^m}(w)`,   `S_{h₀}(w) = Σ_{A squarefree} (h₀/gen A)₃² σ(A) N(A)^{−w}`,

so `D(s) = \overline{C}² Z₀(3s/2 − 1) Σ_{u,m} (T(uλ^m)/T(1))² (4π|ξ_{uλ^m}|)^{−s} S_{uλ^m}(s/2)`
(`thetaSqDirichlet_eq_zeta_mul`). The twist only sees `u` modulo `±1` and `m` modulo `3`
(`twistedSquarefreeSeries_neg`, `twistedSquarefreeSeries_lambda_mod`): nine series. The source mask removes
two layers: `T(uλ) = 0` and `T(u) = 0` unless `u = ±1` (`sourceCoefficient_unit_mul_lambda`,
`sourceCoefficient_unit_eq`).
-/

noncomputable section

open MeasureTheory UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi

/-! ### Twisted multiplicativity -/

/-- Split one prime off a primary generator: `gen I = p^k gen J` with `p ∤ gen J`, `k` the count of `P`. -/
theorem gen_eq_primePow_mul (I P : Ideal O) (hI : primaryIdealGenerator I ≠ 0)
    (hP : P ∈ normalizedFactors I) :
    ∃ J : Ideal O, primaryIdealGenerator J ≠ 0 ∧
      primaryIdealGenerator I =
        primaryIdealPrime P ^ (normalizedFactors I).count P * primaryIdealGenerator J ∧
      ¬ primaryIdealPrime P ∣ primaryIdealGenerator J := by
  have hI0 := primaryIdealGenerator_ne_zero_ideal I hI
  have hprime := prime_of_normalized_factor P hP
  have hp0 : primaryIdealPrime P ≠ 0 := primaryIdealPrime_factor_ne_zero I P hI hP
  have hps := primaryIdealPrime_spec P hp0
  have hPgen : primaryIdealGenerator P = primaryIdealPrime P := by
    have h := primaryIdealGenerator_span _ hp0 hps.2.2.2
    rwa [hps.2.2.1] at h
  obtain ⟨J, hJ, hnot⟩ := (FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hcount := multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  have hgen : primaryIdealGenerator I =
      primaryIdealPrime P ^ (normalizedFactors I).count P * primaryIdealGenerator J := by
    rw [← hcount, ← hPgen, ← primaryIdealGenerator_pow, ← primaryIdealGenerator_mul, ← hJ]
  have hgJ : primaryIdealGenerator J ≠ 0 := fun hz => hI (by rw [hgen, hz, mul_zero])
  refine ⟨J, hgJ, hgen, fun hd => hnot ?_⟩
  rw [Ideal.dvd_iff_le, ← (primaryIdealGenerator_spec J hgJ).1, ← hps.2.2.1,
    Ideal.span_singleton_le_span_singleton]
  exact hd

/-- The cubic symbol does not see cubes coprime to the denominator. -/
theorem symbol_mul_cube (h₀ c a : O) (ha : lambda ^ 2 ∣ a - 1) (hc : IsCoprime c a) :
    symbol (h₀ * c ^ 3) a = symbol h₀ a := by
  rw [symbol_mul_numerator, symbol_pow_numerator c a ha 3, symbol_cube_of_isCoprime c a ha hc, mul_one]

/-- **Twisted multiplicativity.** For `h₀ ≠ 0` coprime to `gen I`:
`T(h₀ gen I) T(1) = (h₀/gen I)₃ T(h₀) T(gen I)`. -/
theorem sourceCoefficient_twisted_mul (h₀ : O) (hh₀ : h₀ ≠ 0) (I : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) (hcop : IsCoprime h₀ (primaryIdealGenerator I)) :
    rationalSourceResidualFourierCoefficient (h₀ * primaryIdealGenerator I) *
        rationalSourceResidualFourierCoefficient 1 =
      ringComplex (symbol h₀ (primaryIdealGenerator I)) * rationalSourceResidualFourierCoefficient h₀ *
        rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) := by
  by_cases hv : ∀ P ∈ normalizedFactors I, (normalizedFactors I).count P % 3 ≠ 2
  · -- `I = A B³` with `A` squarefree
    have he := thetaParts_mul_cube I (primaryIdealGenerator_ne_zero_ideal I hI) hv
    set A := thetaSquarefreePart I with hAdef
    set B := thetaCubePart I with hBdef
    have hgen : primaryIdealGenerator I = primaryIdealGenerator A * primaryIdealGenerator B ^ 3 := by
      rw [← primaryIdealGenerator_pow, ← primaryIdealGenerator_mul, he]
    have hA : primaryIdealGenerator A ≠ 0 := fun hz => hI (by rw [hgen, hz, zero_mul])
    have hB : primaryIdealGenerator B ≠ 0 := fun hz =>
      hI (by rw [hgen, hz, zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero])
    have hsq : Squarefree A := thetaSquarefreePart_squarefree I
    have hBp := (primaryIdealGenerator_spec B hB).2
    have hcopA : IsCoprime h₀ (primaryIdealGenerator A) :=
      hcop.of_isCoprime_of_dvd_right (by rw [hgen]; exact dvd_mul_right _ _)
    have hcopB : IsCoprime h₀ (primaryIdealGenerator B) :=
      hcop.of_isCoprime_of_dvd_right
        (by rw [hgen]; exact (dvd_pow_self _ (by decide : (3 : ℕ) ≠ 0)).mul_left _)
    -- the squarefree part: prime products at `h₀` and at `1`
    have hprod := primaryIdealGenerator_squarefree_support A hA hsq
    have hpr : ∀ P ∈ primeSupport A, Prime (primaryIdealPrime P) :=
      fun P hP => primaryIdealPrime_isPrime_of_mem A P hA hP
    have hprim : ∀ P ∈ primeSupport A, lambda ^ 2 ∣ primaryIdealPrime P - 1 := fun P hP =>
      (primaryIdealPrime_spec P (primaryIdealPrime_factor_ne_zero A P hA (Multiset.mem_toFinset.mp hP))).2.2.2
    have hpair := primaryIdealPrime_support_coprime A hA
    have hnd : ∀ P ∈ primeSupport A, ¬ primaryIdealPrime P ∣ h₀ := by
      intro P hP hd
      have hdA : primaryIdealPrime P ∣ primaryIdealGenerator A := hprod ▸ Finset.dvd_prod_of_mem _ hP
      exact (hpr P hP).not_unit (hcopA.isUnit_of_dvd' hd hdA)
    have h1 := rationalSourceResidualFourierCoefficient_prime_product (primeSupport A) primaryIdealPrime
      hpr hprim hpair h₀ hnd
    have h2 := rationalSourceResidualFourierCoefficient_prime_product (primeSupport A) primaryIdealPrime
      hpr hprim hpair 1 (fun P hP hd => (hpr P hP).not_unit (isUnit_of_dvd_one hd))
    rw [← hprod] at h1 h2
    rw [one_mul, mul_one] at h2
    -- the cube part
    have hs3 : symbol h₀ (primaryIdealGenerator B ^ 3) = 1 := by
      rw [show primaryIdealGenerator B ^ 3 =
          primaryIdealGenerator B * primaryIdealGenerator B * primaryIdealGenerator B by ring,
        symbol_mul_denominator, symbol_mul_denominator, ← symbol_cube_of_isCoprime h₀ _ hBp hcopB]
      ring
    rw [hgen, show h₀ * (primaryIdealGenerator A * primaryIdealGenerator B ^ 3) =
        (h₀ * primaryIdealGenerator A) * primaryIdealGenerator B ^ 3 by ring,
      rationalSourceResidualFourierCoefficient_primary_cube _ hB hBp _ (mul_ne_zero hh₀ hA),
      rationalSourceResidualFourierCoefficient_primary_cube _ hB hBp _ hA,
      symbol_mul_denominator, hs3, mul_one, h1, h2, symbol_mul_numerator, map_mul]
    ring
  · -- a prime valuation `≡ 2 mod 3` kills both sides
    push Not at hv
    obtain ⟨P, hP, hk⟩ := hv
    obtain ⟨J, -, hgen, hnd⟩ := gen_eq_primePow_mul I P hI hP
    have hp := primaryIdealPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
    have hprim := (primaryIdealPrime_spec P (primaryIdealPrime_factor_ne_zero I P hI hP)).2.2.2
    have hk0 : (normalizedFactors I).count P ≠ 0 := by omega
    have hnh : ¬ primaryIdealPrime P ∣ h₀ := fun hd => hp.not_unit (hcop.isUnit_of_dvd' hd
      (by rw [hgen]; exact (dvd_pow_self _ hk0).mul_right _))
    have hz1 : rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) = 0 := by
      rw [hgen, mul_comm]
      exact rationalSourceResidualFourierCoefficient_prime_power_vanish _ hp hprim _ hnd _ hk
    have hz2 : rationalSourceResidualFourierCoefficient (h₀ * primaryIdealGenerator I) = 0 := by
      rw [hgen, show h₀ * (primaryIdealPrime P ^ (normalizedFactors I).count P * primaryIdealGenerator J) =
          (h₀ * primaryIdealGenerator J) * primaryIdealPrime P ^ (normalizedFactors I).count P by ring]
      exact rationalSourceResidualFourierCoefficient_prime_power_vanish _ hp hprim _
        (fun hd => (hp.dvd_or_dvd hd).elim hnh hnd) _ hk
    rw [hz1, hz2]
    ring

/-! ### The split `h = u λ^m gen I` -/

/-- `(u, m, I) ↦ u λ^m gen(I)`. -/
def frequencySplit (p : Oˣ × ℕ × GoodIdeal) : O :=
  ((p.1 : O) * lambda ^ p.2.1) * primaryIdealGenerator p.2.2.1

theorem lambda_ne_zero' : lambda ≠ 0 := residue_lambda_prime.ne_zero

theorem ramified_ne_zero (u : Oˣ) (m : ℕ) : (u : O) * lambda ^ m ≠ 0 :=
  mul_ne_zero u.ne_zero (pow_ne_zero _ lambda_ne_zero')

theorem ramified_isCoprime_gen (u : Oˣ) (m : ℕ) (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) :
    IsCoprime ((u : O) * lambda ^ m) (primaryIdealGenerator I) :=
  (ramified_primary_coprime u m _ (primaryIdealGenerator_spec I hI).2).of_mul_left_right

theorem frequencySplit_ne_zero (p : Oˣ × ℕ × GoodIdeal) : frequencySplit p ≠ 0 :=
  mul_ne_zero (ramified_ne_zero _ _) p.2.2.2

theorem frequencySplit_injective : Function.Injective frequencySplit := by
  rintro ⟨u, m, I⟩ ⟨u', m', I'⟩ he
  simp only [frequencySplit] at he
  have hs : lambdaFactorMap (m, I) = lambdaFactorMap (m', I') := by
    apply Subtype.ext
    change ramifiedIdeal ^ m * I.1 = ramifiedIdeal ^ m' * I'.1
    rw [← lambdaFactor_generator_span, ← lambdaFactor_generator_span]
    have h := congrArg (fun x : O => (Ideal.span {x} : Ideal O)) he
    simp only [mul_assoc] at h
    rwa [Ideal.span_singleton_mul_left_unit u.isUnit,
      Ideal.span_singleton_mul_left_unit u'.isUnit] at h
  have hmI := lambdaFactorMap_bijective.1 hs
  simp only [Prod.mk.injEq] at hmI
  obtain ⟨rfl, rfl⟩ := hmI
  have hne : lambda ^ m * primaryIdealGenerator I.1 ≠ 0 := mul_ne_zero (pow_ne_zero _ lambda_ne_zero') I.2
  have hu : (u : O) = u' := mul_right_cancel₀ hne (by simpa only [mul_assoc] using he)
  rw [Units.ext hu]

theorem frequencySplit_surjective (h : O) (hh : h ≠ 0) : ∃ p, frequencySplit p = h := by
  obtain ⟨u, m, I, hI, he⟩ := exists_unit_lambda_primary_factor h hh
  exact ⟨(u, m, ⟨I, hI⟩), he.symm⟩

/-- `(4π|ξ_{h₀ gen I}|)^{−s} = (4π|ξ_{h₀}|)^{−s} N(I)^{−s/2}`. -/
theorem frequencyWeight_split (s : ℂ) (h₀ : O) (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) :
    ((4 * Real.pi * ‖cuspFrequency (h₀ * primaryIdealGenerator I)‖ : ℝ) : ℂ) ^ (-s) =
      ((4 * Real.pi * ‖cuspFrequency h₀‖ : ℝ) : ℂ) ^ (-s) * unramifiedNormWeight (s / 2) I := by
  set g := ‖ringComplex (primaryIdealGenerator I)‖ with hgdef
  have hg : 0 < g := norm_pos_iff.mpr (ringComplex_ne_zero hI)
  have hN : (Ideal.absNorm I : ℂ) = (g : ℂ) * (g : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, hgdef, primaryIdealGenerator_norm_sq I hI, Complex.ofReal_natCast]
  rw [cuspFrequency_mul_right, norm_mul, ← hgdef, unramifiedNormWeight_of_good _ _ hI, hN,
    Complex.mul_cpow_ofReal_nonneg hg.le hg.le, ← Complex.cpow_add _ _ (by exact_mod_cast hg.ne'),
    show -(s / 2) + -(s / 2) = -s by ring,
    show 4 * Real.pi * (‖cuspFrequency h₀‖ * g) = (4 * Real.pi * ‖cuspFrequency h₀‖) * g by ring,
    Complex.ofReal_mul (4 * Real.pi * ‖cuspFrequency h₀‖) g,
    Complex.mul_cpow_ofReal_nonneg (by positivity) hg.le]

/-! ### The twisted primary and squarefree series -/

/-- `P_{h₀}(w) = Σ_I N(I)^{−w} (h₀/gen I)₃² T(gen I)²` over unramified ideals. -/
def twistedPrimarySeries (h₀ : O) (w : ℂ) : ℂ :=
  ∑' I : Ideal O, unramifiedNormWeight w I *
    (ringComplex (symbol h₀ (primaryIdealGenerator I)) ^ 2 *
      rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2)

/-- `S_{h₀}(w) = Σ_{A squarefree} N(A)^{−w} (h₀/gen A)₃² σ(A)`. -/
def twistedSquarefreeSeries (h₀ : O) (w : ℂ) : ℂ :=
  ∑' A : Ideal O, if Squarefree A then
    unramifiedNormWeight w A * (ringComplex (symbol h₀ (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A)
  else 0

/-- **Every twist carries the cube factor.** For `Re w > 1`,
`P_{uλ^m}(w) = \overline{C}² Z₀(3w − 1) S_{uλ^m}(w)`. -/
theorem twistedPrimarySeries_eq (u : Oˣ) (m : ℕ) (w : ℂ) (hw : 1 < w.re) :
    twistedPrimarySeries ((u : O) * lambda ^ m) w =
      star rationalSourceThetaScalar ^ 2 * unramifiedIdealZeta (3 * w - 1) *
        twistedSquarefreeSeries ((u : O) * lambda ^ m) w := by
  set h₀ := (u : O) * lambda ^ m with hh₀
  set χ : O → ℂ := fun a => ringComplex (symbol h₀ a) with hχ
  set f : Ideal O → ℂ := fun I => unramifiedNormWeight w I *
    (χ (primaryIdealGenerator I) ^ 2 * rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2)
    with hf
  set x : Ideal O → ℂ := fun B => unramifiedNormWeight (3 * w - 1) B with hx
  set y : Ideal O → ℂ := fun A => if Squarefree A then
    unramifiedNormWeight w A * (χ (primaryIdealGenerator A) ^ 2 * thetaSquareWeight A) else 0 with hy
  have hw3 : 1 < (3 * w - 1).re := by
    have : (3 * w - 1).re = 3 * w.re - 1 := by simp
    rw [this]
    linarith
  have hxs : Summable (fun B => ‖x B‖) := unramifiedNormWeight_summable_norm _ hw3
  have hys : Summable (fun A => ‖y A‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun A => ?_)
      (unramifiedNormWeight_summable_norm w hw)
    simp only [hy]
    split_ifs with hsq
    · by_cases hA : primaryIdealGenerator A = 0
      · rw [unramifiedNormWeight_of_bad w A hA, zero_mul, norm_zero]
      · rw [norm_mul, norm_mul, norm_pow, norm_thetaSquareWeight A hA hsq, hχ,
          symbol_norm_one _ _ (primaryIdealGenerator_spec A hA).2 (ramified_isCoprime_gen u m A hA)]
        norm_num
    · rw [norm_zero]
      exact norm_nonneg _
  have hpair : ∀ p : Ideal O × Ideal O, star rationalSourceThetaScalar ^ 2 * (x p.1 * y p.2) =
      admissiblePairs.indicator (fun p => f (p.2 * p.1 ^ 3)) p := by
    rintro ⟨B, A⟩
    by_cases hp : (B, A) ∈ admissiblePairs
    · obtain ⟨hsq, hA, hB⟩ := hp
      rw [Set.indicator_of_mem (show (B, A) ∈ admissiblePairs from ⟨hsq, hA, hB⟩)]
      have hc := symbol_mul_cube h₀ (primaryIdealGenerator A) (primaryIdealGenerator B)
      have hs3 : symbol h₀ (primaryIdealGenerator A * primaryIdealGenerator B ^ 3) =
          symbol h₀ (primaryIdealGenerator A) := by
        rw [symbol_mul_denominator, show primaryIdealGenerator B ^ 3 =
            primaryIdealGenerator B * primaryIdealGenerator B * primaryIdealGenerator B by ring,
          symbol_mul_denominator, symbol_mul_denominator,
          ← pow_three' (symbol h₀ (primaryIdealGenerator B)),
          symbol_cube_of_isCoprime h₀ _ (primaryIdealGenerator_spec B hB).2
            (ramified_isCoprime_gen u m B hB), mul_one]
      simp only [hf, hx, hy, hχ, if_pos hsq]
      rw [map_mul, map_pow, primaryIdealGenerator_mul, primaryIdealGenerator_pow, hs3,
        sourceCoefficient_sq A B hA hB hsq, normWeight_shift w B hB]
      ring
    · rw [Set.indicator_of_notMem hp]
      simp only [admissiblePairs, Set.mem_setOf_eq, not_and_or] at hp
      simp only [hx, hy]
      rcases hp with hsq | hA | hB
      · rw [if_neg hsq, mul_zero, mul_zero]
      · push Not at hA
        by_cases hsq : Squarefree A
        · rw [if_pos hsq, unramifiedNormWeight_of_bad w A hA, zero_mul, mul_zero, mul_zero]
        · rw [if_neg hsq, mul_zero, mul_zero]
      · push Not at hB
        rw [unramifiedNormWeight_of_bad _ B hB, zero_mul, mul_zero]
  have hinj : Function.Injective (fun p : admissiblePairs => p.1.2 * p.1.1 ^ 3) := by
    rintro ⟨⟨B₁, A₁⟩, hsq₁, hA₁, hB₁⟩ ⟨⟨B₂, A₂⟩, hsq₂, hA₂, hB₂⟩ h
    obtain ⟨hA, hB⟩ := mul_cube_injective hsq₁ hsq₂ (primaryIdealGenerator_ne_zero_ideal B₁ hB₁)
      (primaryIdealGenerator_ne_zero_ideal B₂ hB₂) h
    subst hA hB
    rfl
  have hsupp : Function.support f ⊆ Set.range (fun p : admissiblePairs => p.1.2 * p.1.1 ^ 3) := by
    intro I hI
    have hI' : f I ≠ 0 := hI
    simp only [hf] at hI'
    have hg : primaryIdealGenerator I ≠ 0 := by
      intro hz
      exact hI' (by rw [unramifiedNormWeight_of_bad w I hz, zero_mul])
    have hT : rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ≠ 0 := by
      intro hz
      exact hI' (by rw [hz]; ring)
    obtain ⟨A, B, hsq, hA, hB, hAB⟩ := (sourceFourier_squarefree_cube_support_iff I hg).mp hT
    exact ⟨⟨(B, A), hsq, hA, hB⟩, hAB⟩
  calc twistedPrimarySeries h₀ w = ∑' I : Ideal O, f I := rfl
    _ = ∑' p : admissiblePairs, f (p.1.2 * p.1.1 ^ 3) := (hinj.tsum_eq hsupp).symm
    _ = ∑' p : Ideal O × Ideal O, admissiblePairs.indicator (fun p => f (p.2 * p.1 ^ 3)) p :=
        tsum_subtype admissiblePairs (fun p => f (p.2 * p.1 ^ 3))
    _ = ∑' p : Ideal O × Ideal O, star rationalSourceThetaScalar ^ 2 * (x p.1 * y p.2) :=
        tsum_congr fun p => (hpair p).symm
    _ = star rationalSourceThetaScalar ^ 2 * ((∑' B, x B) * ∑' A, y A) := by
        rw [tsum_mul_left, tsum_mul_tsum_of_summable_norm hxs hys]
    _ = _ := by
        simp only [hx, unramifiedIdealZeta, twistedSquarefreeSeries]
        ring

/-- Twists by `h₀` and `h₀ c³` agree when `c` is coprime to every primary generator. -/
theorem twistedSquarefreeSeries_mul_cube (h₀ c : O)
    (hc : ∀ I : Ideal O, primaryIdealGenerator I ≠ 0 → IsCoprime c (primaryIdealGenerator I)) (w : ℂ) :
    twistedSquarefreeSeries (h₀ * c ^ 3) w = twistedSquarefreeSeries h₀ w := by
  unfold twistedSquarefreeSeries
  refine tsum_congr fun A => ?_
  split_ifs
  · by_cases hA : primaryIdealGenerator A = 0
    · rw [unramifiedNormWeight_of_bad _ _ hA, zero_mul, zero_mul]
    · rw [symbol_mul_cube _ _ _ (primaryIdealGenerator_spec A hA).2 (hc A hA)]
  · rfl

theorem twistedSquarefreeSeries_neg (h₀ : O) (w : ℂ) :
    twistedSquarefreeSeries (-h₀) w = twistedSquarefreeSeries h₀ w := by
  have h := twistedSquarefreeSeries_mul_cube h₀ (-1) (fun _ _ => isCoprime_one_left.neg_left) w
  rwa [show h₀ * (-1 : O) ^ 3 = -h₀ by ring] at h

/-- Only `m mod 3` matters. -/
theorem twistedSquarefreeSeries_lambda_mod (u : Oˣ) (m : ℕ) (w : ℂ) :
    twistedSquarefreeSeries ((u : O) * lambda ^ m) w =
      twistedSquarefreeSeries ((u : O) * lambda ^ (m % 3)) w := by
  have h := twistedSquarefreeSeries_mul_cube ((u : O) * lambda ^ (m % 3)) (lambda ^ (m / 3))
    (fun I hI => (coprime_of_dvd_sub_one lambda _
      ((dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans (primaryIdealGenerator_spec I hI).2)).pow_left) w
  rwa [mul_assoc, ← pow_mul, ← pow_add, show m % 3 + m / 3 * 3 = m by omega] at h

/-! ### The split of `D(s)` -/

/-- The terms of `D(s)` are absolutely summable for `Re s > 4`. -/
theorem summable_thetaSqDirichlet_term (s : ℂ) (hs : 4 < s.re) :
    Summable (fun h : O => if h = 0 then (0 : ℂ) else
      rationalSourceResidualFourierCoefficient h ^ 2 *
        ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded
    ((summable_sourceCoefficient_sq_rpow hs).mul_left ((4 * Real.pi) ^ (-s.re))) (fun h => ?_)
  by_cases hh : h = 0
  · simp [hh]
  have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  simp only [hh, if_false, norm_mul, norm_pow]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re,
    Real.mul_rpow (by positivity) hξ.le]
  apply le_of_eq
  ring

/-- **The split of the squared theta series.** For `Re s > 4`,
`D(s) = Σ_{u, m} (T(uλ^m)/T(1))² (4π|ξ_{uλ^m}|)^{−s} P_{uλ^m}(s/2)`. -/
theorem thetaSqDirichlet_eq_twisted (s : ℂ) (hs : 4 < s.re) :
    thetaSqDirichlet s = ∑' u : Oˣ, ∑' m : ℕ,
      (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
          rationalSourceResidualFourierCoefficient 1) ^ 2 *
        ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) *
          twistedPrimarySeries ((u : O) * lambda ^ m) (s / 2) := by
  set F : O → ℂ := fun h => if h = 0 then (0 : ℂ) else
    rationalSourceResidualFourierCoefficient h ^ 2 *
      ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s) with hF
  set c : Oˣ → ℕ → ℂ := fun u m =>
    (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
        rationalSourceResidualFourierCoefficient 1) ^ 2 *
      ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) with hc
  set g : O → Ideal O → ℂ := fun h₀ I => unramifiedNormWeight (s / 2) I *
    (ringComplex (symbol h₀ (primaryIdealGenerator I)) ^ 2 *
      rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2) with hg
  have hT1 : rationalSourceResidualFourierCoefficient 1 ≠ 0 := fun hz =>
    rationalSourceThetaScalar_ne_zero (by rw [rationalSourceThetaScalar, hz, star_zero])
  -- the terms along the split
  have hterm : ∀ p : Oˣ × ℕ × GoodIdeal,
      F (frequencySplit p) = c p.1 p.2.1 * g ((p.1 : O) * lambda ^ p.2.1) p.2.2.1 := by
    rintro ⟨u, m, I, hI⟩
    have hmul := sourceCoefficient_twisted_mul _ (ramified_ne_zero u m) I hI (ramified_isCoprime_gen u m I hI)
    have hT := eq_div_of_mul_eq hT1 hmul
    simp only [hF, hc, hg, frequencySplit]
    rw [if_neg (mul_ne_zero (ramified_ne_zero u m) hI), hT, frequencyWeight_split s _ I hI]
    ring
  have hFs : Summable F := summable_thetaSqDirichlet_term s hs
  have hGs : Summable (fun p : Oˣ × ℕ × GoodIdeal => F (frequencySplit p)) :=
    hFs.comp_injective frequencySplit_injective
  have hsupp : Function.support F ⊆ Set.range frequencySplit := by
    intro h hh
    have hh0 : h ≠ 0 := by
      intro hz
      exact hh (by simp only [hF, hz, if_true])
    exact frequencySplit_surjective h hh0
  -- the inner sums over good ideals
  have hgood : ∀ h₀ : O, ∑' I : GoodIdeal, g h₀ I.1 = twistedPrimarySeries h₀ (s / 2) := by
    intro h₀
    refine tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryIdealGenerator I ≠ 0}) ?_
    intro I hI
    by_contra hb
    exact hI (by simp only [hg]; rw [unramifiedNormWeight_of_bad _ _ (not_not.mp hb), zero_mul])
  calc thetaSqDirichlet s = ∑' h : O, F h := rfl
    _ = ∑' p : Oˣ × ℕ × GoodIdeal, F (frequencySplit p) := (frequencySplit_injective.tsum_eq hsupp).symm
    _ = ∑' u : Oˣ, ∑' q : ℕ × GoodIdeal, F (frequencySplit (u, q)) := hGs.tsum_prod
    _ = ∑' u : Oˣ, ∑' m : ℕ, ∑' I : GoodIdeal, F (frequencySplit (u, m, I)) :=
        tsum_congr fun u => (hGs.prod_factor u).tsum_prod
    _ = _ := by
        refine tsum_congr fun u => tsum_congr fun m => ?_
        simp only [hterm]
        rw [tsum_mul_left, hgood]

/-- **The cube factor of `D(s)`.** For `Re s > 4`,
`D(s) = \overline{C}² Z₀(3s/2 − 1) Σ_{u, m} (T(uλ^m)/T(1))² (4π|ξ_{uλ^m}|)^{−s} S_{uλ^m}(s/2)`. -/
theorem thetaSqDirichlet_eq_zeta_mul (s : ℂ) (hs : 4 < s.re) :
    thetaSqDirichlet s = star rationalSourceThetaScalar ^ 2 * unramifiedIdealZeta (3 * (s / 2) - 1) *
      ∑' u : Oˣ, ∑' m : ℕ,
        (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
            rationalSourceResidualFourierCoefficient 1) ^ 2 *
          ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) *
            twistedSquarefreeSeries ((u : O) * lambda ^ m) (s / 2) := by
  have hw : 1 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  rw [thetaSqDirichlet_eq_twisted s hs, ← tsum_mul_left]
  refine tsum_congr fun u => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [twistedPrimarySeries_eq u m _ hw]
  ring

/-! ### The source mask on the ramified layers -/

theorem lambda_not_isUnit : ¬ IsUnit lambda := residue_lambda_prime.not_unit

/-- `T(uλ) = 0`: no frequency of λ-adic valuation one is seen by the source mask. -/
theorem sourceCoefficient_unit_mul_lambda (u : Oˣ) :
    rationalSourceResidualFourierCoefficient ((u : O) * lambda) = 0 := by
  by_contra hT
  have hne : (u : O) * lambda ≠ 0 := mul_ne_zero u.ne_zero lambda_ne_zero'
  have h3 : ¬ (3 : O) ∣ (u : O) * lambda := by
    intro hd
    rw [three_eq_ramifiedUnit] at hd
    have hd' : lambda * lambda ∣ lambda * (u : O) := by
      rw [← sq, mul_comm lambda]
      exact (dvd_mul_left _ _).trans hd
    exact lambda_not_isUnit (isUnit_of_dvd_unit ((mul_dvd_mul_iff_left lambda_ne_zero').mp hd') u.isUnit)
  have hl : lambda ∣ (u : O) * lambda := dvd_mul_left _ _
  rcases primary_or_negative_primary_of_source_mask _ h3 (sourceFourier_phase_of_ne_zero _ hne hT)
    with hp | hp
  · have h := dvd_sub hl ((dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans hp)
    rw [sub_sub_cancel] at h
    exact lambda_not_isUnit (isUnit_of_dvd_one h)
  · have h := dvd_sub hl.neg_right ((dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans hp)
    rw [sub_sub_cancel] at h
    exact lambda_not_isUnit (isUnit_of_dvd_one h)

/-- `T(u) ≠ 0` forces `u = ±1`. -/
theorem sourceCoefficient_unit_eq (u : Oˣ) (hT : rationalSourceResidualFourierCoefficient u ≠ 0) :
    (u : O) = 1 ∨ (u : O) = -1 := by
  have h3 : ¬ (3 : O) ∣ u := by
    intro hd
    have h3u : IsUnit (3 : O) := isUnit_of_dvd_unit hd u.isUnit
    rw [three_eq_ramifiedUnit] at h3u
    exact lambda_not_isUnit ((isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp (isUnit_of_mul_isUnit_right h3u))
  rcases primary_or_negative_primary_of_source_mask _ h3 (sourceFourier_phase_of_ne_zero _ u.ne_zero hT)
    with hp | hp
  · exact Or.inl (primary_unit_eq_one u hp)
  · right
    have h := primary_unit_eq_one (-u) (by rwa [Units.val_neg])
    rw [Units.val_neg] at h
    linear_combination -h

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
