import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeGrowth
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape
import GaloisForLFunctions.RHTower.ThetaCutoffCommutatorMellin
import GaloisForLFunctions.HTGeometry.WeightedHolder
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusMean
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Canonical finite-prime sources blow up in `L²` below damping `1/2`

For a finite set of primes `S`, the finite-prime power-damped source
`F_{S,ε}(t) = −∑_{d | ∏S} μ(d) d^(−ε) φ_d(t)` has Mellin transform
`(1 − 2^(1−s)) ζ(s)/s · ∏_{p∈S} (1 − p^(−s−ε))` on `0 < Re s < 1`. For damping `ε > 1/2` the
triangle inequality bounds every such source by the absolute budget `∑_d 3 d^(−ε−1/2)`. For the
canonical apertures `S_N = {p ≤ N}` and `0 < ε < 1/2`, the Euler factor tends to `0` at each
real `x` with `0 < x + ε ≤ 1`. The sources agree with the full source `F_ε` for
`t > 1/(N+1)`, and a Cauchy–Schwarz bound for Mellin transforms of functions supported near `0`
shows: if some subsequence of canonical sources were uniformly `L²`-bounded, then
`F_ε ∈ L²(0,∞)`, its Mellin transform would vanish on `(1/2, 1−ε)` and hence, by analytic
continuation, at `s = 1`, contradicting `M F_ε(1) = log 2/ζ(1+ε) ≠ 0`. Therefore the
`L²(0,∞)` norms of the canonical finite-prime sources tend to infinity for every `0 < ε < 1/2`.

## Main results

- `pmFinitePrimePowerDampedFermiSource_norm_le_absolute_budget`: for `ε > 1/2`, `‖F_{S,ε}‖₂ ≤ ∑_d 3 d^(−ε−1/2)` for every finite `S`.
- `mellin_pmFinitePrimePowerDampedFermiSource`: Mellin transform `(1 − 2^(1−s)) ζ(s)/s · ∏_{p∈S}(1 − p^(−(s+ε)))` for `0 < Re s < 1`.
- `pm_mellin_norm_le_of_cutoff`: for `f ∈ L²` vanishing beyond `c ≤ 1` and `Re s > 1/2`, `|M f(s)| ≤ ‖f‖₂ √(c^(2Re s − 1)/(2Re s − 1))`.
- `pm_mellin_tendsto_of_cofinal_prime_budget`: a uniform `L²` bound along a cofinal subsequence of canonical sources forces Mellin convergence to `M F_ε(s)` for `Re s > 1/2`.
- `pmCanonicalPrime_no_bounded_cofinal_subsequence`: for `0 < ε < 1/2`, no cofinal subsequence of canonical sources is uniformly `L²`-bounded.
- `pmCanonicalPrime_eventually_exceeds_every_budget`: for `0 < ε < 1/2` and every real `C`, eventually `‖F_{S_N,ε}‖₂ > C`.
- `tendsto_pmCanonicalPrime_norm_atTop`: for `0 < ε < 1/2`, `‖F_{S_N,ε}‖_{L²(0,∞)} → ∞`.

## Hypotheses

All results are unconditional. The blow-up statements assume `0 < ε < 1/2`; the absolute
budget assumes `1/2 < ε`. Auxiliary lemmas take explicit inputs (sets of primes, `L²`
membership, support in `(0,c]`, uniform norm bounds) that are discharged in the main theorems.
The divergence concerns the canonical finite-prime truncations, not the full source `F_ε`.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
noncomputable section
namespace RHTower

/-- For `d ≥ 1`, each finite-prime damped term has `L²(0,∞)` norm at most `3 d^(−ε−1/2)`. -/
theorem pm_eLpNorm_finite_prime_damped_term_le (S : Finset ℕ) (ε : ℝ) {d : ℕ}
    (hd : 1 ≤ d) :
    eLpNorm (fun t => finitePrimeApertureMobiusCoefficient S d *
        (((d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t)
      2 (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal (3 * (d : ℝ) ^ (-ε - 1 / 2)) := by
  by_cases hc : d.primeFactors ⊆ S
  · simpa only [finitePrimeApertureMobiusCoefficient, if_pos hc, mobiusComplexCoefficient,
      Complex.ofReal_mul, Complex.ofReal_intCast] using pm_eLpNorm_power_damped_term_le ε hd
  · simp [finitePrimeApertureMobiusCoefficient, hc]

/-- The absolute budget `∑'_d 3 d^(−ε−1/2)`, finite for `ε > 1/2`. -/
def pmPrimeApertureAbsoluteBudget (ε : ℝ) : ℝ :=
  ∑' d : ℕ, 3 * (d : ℝ) ^ (-ε - 1 / 2)

theorem pmPrimeApertureAbsoluteBudget_nonneg (ε : ℝ) :
    0 ≤ pmPrimeApertureAbsoluteBudget ε := by
  apply tsum_nonneg
  intro d
  positivity

/-- For `ε > 1/2` and every finite `S`, the finite-prime source has `L²(0,∞)` norm at most the
absolute budget `∑'_d 3 d^(−ε−1/2)`. -/
theorem pmFinitePrimePowerDampedFermiSource_norm_le_absolute_budget (S : Finset ℕ)
    {ε : ℝ} (hε : 1 / 2 < ε) :
    eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal (pmPrimeApertureAbsoluteBudget ε) := by
  let g : ℕ → ℝ → ℂ := fun d t => finitePrimeApertureMobiusCoefficient S d *
    (((d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t
  have he : pmFinitePrimePowerDampedFermiSource S ε = -(∑ d ∈ Finset.Icc 1 (∏ p ∈ S, p), g d) := by
    funext t
    simp only [pmFinitePrimePowerDampedFermiSource, g, Finset.sum_apply, Pi.neg_apply]
  have hg (d : ℕ) : AEStronglyMeasurable (g d) (volume.restrict (Ioi (0 : ℝ))) :=
    (measurable_const.mul (measurable_fermiNymanGen (d : ℝ))).aestronglyMeasurable
  have hs : Summable (fun d : ℕ => 3 * (d : ℝ) ^ (-ε - 1 / 2)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -ε - 1 / 2 < -1)).mul_left 3
  rw [he, eLpNorm_neg]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 (∏ p ∈ S, p), eLpNorm (g d) 2 (volume.restrict (Ioi (0 : ℝ))) :=
      eLpNorm_sum_le (fun d _ => hg d) (by norm_num)
    _ ≤ ∑ d ∈ Finset.Icc 1 (∏ p ∈ S, p), ENNReal.ofReal (3 * (d : ℝ) ^ (-ε - 1 / 2)) :=
      Finset.sum_le_sum (fun d hd => pm_eLpNorm_finite_prime_damped_term_le S ε (Finset.mem_Icc.mp hd).1)
    _ ≤ ∑' d : ℕ, ENNReal.ofReal (3 * (d : ℝ) ^ (-ε - 1 / 2)) := ENNReal.sum_le_tsum _
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun d => by positivity) hs).symm

/-- The canonical apertures `{p ≤ N}` consist of primes and eventually contain every prime. -/
theorem primeExhaustion_mobiusFinitePrimeAperture : PrimeExhaustion mobiusFinitePrimeAperture where
  prime _ _ hp := (Finset.mem_filter.mp hp).2
  eventually_mem p hp := by
    filter_upwards [eventually_ge_atTop p] with N hN
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩

/-- For `0 < u ≤ 1`, `∏_{p≤N} (1 − p^(−u)) → 0` as `N → ∞`. -/
theorem pmCanonicalPrimeEulerProduct_tendsto_zero {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    Tendsto (fun N : ℕ => ∏ p ∈ mobiusFinitePrimeAperture N, (1 - (p : ℝ) ^ (-u)))
      atTop (𝓝 0) := by
  have h := primeExhaustion_mobiusFinitePrimeAperture.tendsto_prod_one_sub_rpow
    (w := u - 1 / 2) (by linarith) (by linarith)
  have he : -(1 / 2 : ℝ) - (u - 1 / 2) = -u := by ring
  simpa only [he] using h

/-- For a finite set of primes `S`, `∑_{T⊆S} (−1)^|T| f(∏T) = ∑'_{d≠0, primes of d in S} μ(d) f(d)`. -/
theorem pm_sum_powerset_eq_tsum_moebius_complex (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (f : ℕ → ℂ) :
    (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * f (∏ p ∈ T, p)) =
      ∑' d : ℕ, if d ≠ 0 ∧ d.primeFactors ⊆ S then (moebius d : ℂ) * f d else 0 := by
  classical
  rw [tsum_eq_sum (s := S.powerset.image fun T => ∏ p ∈ T, p), Finset.sum_image (prod_primes_injOn hS)]
  · refine Finset.sum_congr rfl fun T hT => ?_
    have hT' : ∀ p ∈ T, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp hT hp)
    have hne : (∏ p ∈ T, p) ≠ 0 := (Finset.prod_pos fun p hp => (hT' p hp).pos).ne'
    rw [if_pos ⟨hne, by rw [Nat.primeFactors_prod hT']; exact Finset.mem_powerset.mp hT⟩,
      show (moebius (∏ p ∈ T, p) : ℂ) = (((-1 : ℤ) ^ T.card : ℤ) : ℂ) by
        rw [moebius_prod_distinct_primes hT']]
    push_cast
    ring
  · intro d hd
    split_ifs with h
    · by_cases hsq : Squarefree d
      · exact absurd (Finset.mem_image.2 ⟨d.primeFactors, Finset.mem_powerset.2 h.2,
          Nat.prod_primeFactors_of_squarefree hsq⟩) hd
      · rw [moebius_eq_zero_of_not_squarefree hsq]
        simp
    · rfl

/-- For a finite set of primes `S`, the aperture-weighted sum over `d ≤ ∏S` equals the subset sum
`∑_{T⊆S} (−1)^|T| f(∏T)`. -/
theorem pm_finitePrime_coefficient_sum_eq_powerset (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (f : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 (∏ p ∈ S, p), finitePrimeApertureMobiusCoefficient S d * f d) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * f (∏ p ∈ T, p) := by
  have hfun (d : ℕ) : (if d ≠ 0 ∧ d.primeFactors ⊆ S then (moebius d : ℂ) * f d else 0) =
      finitePrimeApertureMobiusCoefficient S d * f d := by
    by_cases hd : d = 0
    · subst d
      simp [finitePrimeApertureMobiusCoefficient, mobiusComplexCoefficient]
    · by_cases hc : d.primeFactors ⊆ S <;>
        simp [hd, hc, finitePrimeApertureMobiusCoefficient, mobiusComplexCoefficient]
  rw [pm_sum_powerset_eq_tsum_moebius_complex S hS f]
  simp_rw [hfun]
  symm
  apply tsum_eq_sum
  intro d hd
  by_cases hd0 : d = 0
  · subst d
    simp [finitePrimeApertureMobiusCoefficient, mobiusComplexCoefficient]
  · have hgt : (∏ p ∈ S, p) < d := by
      have hh := mt Finset.mem_Icc.mpr hd
      omega
    rw [pm_finitePrime_coefficient_eq_zero_above_product hS hgt, zero_mul]

/-- For a finite set of primes `S`, `∑_{d≤∏S} μ_S(d) d^(−s) = ∏_{p∈S} (1 − p^(−s))`. -/
theorem pm_finitePrime_coefficient_cpow_sum (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (s : ℂ) :
    (∑ d ∈ Finset.Icc 1 (∏ p ∈ S, p), finitePrimeApertureMobiusCoefficient S d * (d : ℂ) ^ (-s)) =
      finitePrimeEulerProduct S s := by
  rw [pm_finitePrime_coefficient_sum_eq_powerset S hS, finiteEulerProduct_eq_sum_powerset]

/-- For `0 < Re s < 1` and `a > 0`, the alternating Nyman generator `φ_a` is Mellin convergent at `s`. -/
theorem pmFinitePrime_fermi_mellinConvergent {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) {a : ℝ} (ha : 0 < a) :
    MellinConvergent (fermiNymanGen a) s := by
  have h1 := GaloisForLFunctions.NymanMellin.mellinConvergent_nymanGen hs0 hs1 ha
  have h2 := GaloisForLFunctions.NymanMellin.mellinConvergent_nymanGen hs0 hs1
    (by positivity : (0 : ℝ) < 2 * a)
  change MellinConvergent (fun t => GaloisForLFunctions.NymanMellin.nymanGen a t -
    2 * GaloisForLFunctions.NymanMellin.nymanGen (2 * a) t) s
  simpa only [smul_eq_mul] using (hasMellin_sub h1 (h2.const_smul (2 : ℂ))).1

/-- For a finite set of primes `S` and `0 < Re s < 1`, the Mellin transform of the finite-prime
source is `(1 − 2^(1−s)) ζ(s)/s · ∏_{p∈S} (1 − p^(−(s+ε)))`. -/
theorem mellin_pmFinitePrimePowerDampedFermiSource (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ε : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (pmFinitePrimePowerDampedFermiSource S ε) s =
      ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s / s) *
        finitePrimeEulerProduct S (s + (ε : ℂ)) := by
  let c : ℕ → ℂ := fun d => finitePrimeApertureMobiusCoefficient S d *
    (((d : ℝ) ^ (-ε) : ℝ) : ℂ)
  have hi (d : ℕ) (hd : d ∈ Finset.Icc 1 (∏ p ∈ S, p)) :
      Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * (c d * fermiNymanGen (d : ℝ) t))
        (volume.restrict (Ioi 0)) := by
    have h := (pmFinitePrime_fermi_mellinConvergent hs0 hs1
      (by exact_mod_cast (Finset.mem_Icc.mp hd).1 : (0 : ℝ) < d)).const_smul (c d)
    simpa only [MellinConvergent, IntegrableOn, smul_eq_mul] using h
  have he : mellin (pmFinitePrimePowerDampedFermiSource S ε) s =
      -(∑ d ∈ Finset.Icc 1 (∏ p ∈ S, p), c d * mellin (fermiNymanGen (d : ℝ)) s) := by
    unfold mellin pmFinitePrimePowerDampedFermiSource
    simp only [smul_eq_mul, mul_neg, Finset.mul_sum]
    rw [integral_neg, integral_finsetSum _ hi]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    have hfun : (fun t : ℝ => (t : ℂ) ^ (s - 1) * (c d * fermiNymanGen (d : ℝ) t)) =
        fun t : ℝ => c d * ((t : ℂ) ^ (s - 1) * fermiNymanGen (d : ℝ) t) := by
      funext t
      ring
    change (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (c d * fermiNymanGen (d : ℝ) t)) = _
    rw [hfun, integral_const_mul]
  rw [he, ← pm_finitePrime_coefficient_cpow_sum S hS (s + (ε : ℂ)),
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hp : (((d : ℝ) ^ (-ε) : ℝ) : ℂ) * (d : ℂ) ^ (-s) =
      (d : ℂ) ^ (-(s + (ε : ℂ))) := by
    rw [Complex.ofReal_cpow hd0.le]
    push_cast
    rw [← Complex.cpow_add _ _ hdC]
    congr 1
    ring
  rw [mellin_fermiNymanGen hs0 hs1 hd0]
  dsimp only [c]
  linear_combination finitePrimeApertureMobiusCoefficient S d *
    ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s / s) * hp

/-- Cauchy–Schwarz for Mellin transforms: if `f ∈ L²(0,∞)` vanishes for `t > c` with
`0 < c ≤ 1`, then for `Re s > 1/2`, `|M f(s)| ≤ ‖f‖₂ √(c^(2Re s − 1)/(2Re s − 1))`. -/
theorem pm_mellin_norm_le_of_cutoff {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hsupp : ∀ t : ℝ, c < t → f t = 0)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖mellin f s‖ ≤ (eLpNorm f 2 (volume.restrict (Ioi (0 : ℝ)))).toReal *
      Real.sqrt (c ^ (2 * s.re - 1) / (2 * s.re - 1)) := by
  have hsub : Ioc (0 : ℝ) c ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hhead := hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hsq := hhead.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hw : IntegrableOn (fun t => ‖powerWitness s t‖ ^ (2 : ℕ)) (Ioc (0 : ℝ) c) :=
    (integrableOn_normSq_powerWitness hs).mono_set (Ioc_subset_Ioc_right hc1)
  have hwm : AEStronglyMeasurable (powerWitness s) (volume.restrict (Ioc (0 : ℝ) c)) :=
    ((continuousOn_powerWitness s).mono (Ioc_subset_Ioc_right hc1)).aestronglyMeasurable measurableSet_Ioc
  have he : mellin f s = ∫ t in Ioc (0 : ℝ) c, powerWitness s t * f t := by
    unfold mellin
    simp only [smul_eq_mul]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
    intro t ht
    have hct : c < t := by
      have h := ht.2
      simp only [mem_Ioc, not_and] at h
      exact lt_of_not_ge (h ht.1)
    rw [hsupp t hct, mul_zero]
  have henergy : (∫ t in Ioc (0 : ℝ) c, ‖f t‖ ^ (2 : ℕ)) ≤
      ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ (2 : ℕ) :=
    setIntegral_mono_set (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      (Eventually.of_forall (fun t => sq_nonneg ‖f t‖))
      (Eventually.of_forall (fun t (ht : t ∈ Ioc (0 : ℝ) c) => hsub ht))
  have hnorm : Real.sqrt (∫ t in Ioc (0 : ℝ) c, ‖f t‖ ^ (2 : ℕ)) ≤
      (eLpNorm f 2 (volume.restrict (Ioi (0 : ℝ)))).toReal := by
    calc
      _ ≤ Real.sqrt (∫ t in Ioi (0 : ℝ), ‖f t‖ ^ (2 : ℕ)) := Real.sqrt_le_sqrt henergy
      _ = _ := by
        rw [pm_integral_norm_sq_toLp hf, Real.sqrt_sq (norm_nonneg _), Lp.norm_toLp]
  rw [he]
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ) c, ‖powerWitness s t * f t‖ := norm_integral_le_integral_norm _
    _ = ∫ t in Ioc (0 : ℝ) c, ‖f t‖ * ‖powerWitness s t‖ := by
      simp only [norm_mul, mul_comm]
    _ ≤ Real.sqrt (∫ t in Ioc (0 : ℝ) c, ‖f t‖ ^ (2 : ℕ)) *
        Real.sqrt (∫ t in Ioc (0 : ℝ) c, ‖powerWitness s t‖ ^ (2 : ℕ)) :=
      GaloisForLFunctions.HTGeometry.integral_mul_le_sqrt_mul_sqrt_measure
        hhead.aestronglyMeasurable hwm hsq hw
    _ ≤ _ := by
      rw [integral_Ioc_normSq_powerWitness hs hc]
      exact mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg _)

/-- For `t > 1/(N+1)`, the canonical source on the primes `≤ N` equals the full source `F_ε(t)`. -/
theorem pmFinitePrimePowerDampedFermiSource_eq_of_inverse_cutoff (ε : ℝ) (N : ℕ)
    {t : ℝ} (ht : 1 / ((N : ℝ) + 1) < t) :
    pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε t =
      pmPowerDampedFermiSource ε t := by
  have ht0 : 0 < t := lt_trans (by positivity) ht
  have hx : 1 / t < ((N + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ ht0]
    have h := (div_lt_iff₀ (by positivity : 0 < (N : ℝ) + 1)).mp ht
    push_cast
    nlinarith
  have hfloor : ⌊1 / t⌋₊ ≤ N := by
    have h := (Nat.floor_lt (by positivity : 0 ≤ 1 / t)).mpr hx
    omega
  apply pmFinitePrimePowerDampedFermiSource_eq_of_covers
    (fun p hp => (Finset.mem_filter.mp hp).2) ε ht0
  intro p hp
  simp only [mobiusFinitePrimeAperture, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- If `f_n ∈ L²` are uniformly bounded by `C ≥ 0` and vanish beyond cutoffs `c_n ∈ (0,1]` with
`c_n → 0`, then `M f_n(s) → 0` for every `Re s > 1/2`. -/
theorem pm_mellin_tendsto_zero_of_cutoffs {f : ℕ → ℝ → ℂ}
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict (Ioi (0 : ℝ))))
    {c : ℕ → ℝ} (hc0 : ∀ n, 0 < c n) (hc1 : ∀ n, c n ≤ 1)
    (hclim : Tendsto c atTop (𝓝 0)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, eLpNorm (f n) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal C)
    (hsupp : ∀ n t, c n < t → f n t = 0) {s : ℂ} (hs : 1 / 2 < s.re) :
    Tendsto (fun n => mellin (f n) s) atTop (𝓝 0) := by
  have hq : 0 < 2 * s.re - 1 := by linarith
  have hpow : Tendsto (fun n => c n ^ (2 * s.re - 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow hq.ne'] using
      ((Real.continuous_rpow_const hq.le).tendsto (0 : ℝ)).comp hclim
  have hdiv : Tendsto (fun n => c n ^ (2 * s.re - 1) / (2 * s.re - 1)) atTop (𝓝 0) := by
    simpa only [zero_div] using hpow.div_const (2 * s.re - 1)
  have ht : Tendsto (fun n => C * Real.sqrt (c n ^ (2 * s.re - 1) / (2 * s.re - 1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      ((Real.continuous_sqrt.tendsto (0 : ℝ)).comp hdiv).const_mul C
  apply squeeze_zero_norm (fun n => ?_) ht
  have hb : (eLpNorm (f n) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal ≤ C := by
    simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound n)
  exact (pm_mellin_norm_le_of_cutoff (hf n) (hc0 n) (hc1 n) (hsupp n) hs).trans
    (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _))

/-- If the canonical sources along `k_n → ∞` all have `L²` norm at most `C`, then
`‖F_ε‖_{L²(0,∞)} ≤ C` (Fatou). -/
theorem pmPowerDampedFermiSource_norm_le_of_cofinal_prime_budget (ε : ℝ) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) {C : ENNReal}
    (hC : ∀ n, eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (k n)) ε)
      2 (volume.restrict (Ioi (0 : ℝ))) ≤ C) :
    eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ)) (Eventually.of_forall hC)
    (fun n => (memLp_pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (k n)) ε).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (tendsto_pmFinitePrimePowerDampedFermiSource ε ht).comp hk

/-- Given `k_n → ∞` and a uniform bound `C ≥ 0` on the canonical sources' `L²` norms, their
Mellin transforms converge to `M F_ε(s)` for every `Re s > 1/2`. -/
theorem pm_mellin_tendsto_of_cofinal_prime_budget (ε : ℝ) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (k n)) ε)
      2 (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal C)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Tendsto (fun n => mellin (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (k n)) ε) s)
      atTop (𝓝 (mellin (pmPowerDampedFermiSource ε) s)) := by
  let A := pmPowerDampedFermiSource ε
  let F := fun n => pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (k n)) ε
  let c := fun n => 1 / ((k n : ℝ) + 1)
  have hA := pmPowerDampedFermiSource_norm_le_of_cofinal_prime_budget ε hk hbound
  have hAm : MemLp A 2 (volume.restrict (Ioi (0 : ℝ))) :=
    ⟨(measurable_pmPowerDampedFermiSource ε).aestronglyMeasurable, hA.trans_lt ENNReal.ofReal_lt_top⟩
  have hFm (n : ℕ) : MemLp (F n) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    memLp_pmFinitePrimePowerDampedFermiSource _ ε
  have hc0 (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  have hc1 (n : ℕ) : c n ≤ 1 := by
    dsimp [c]
    rw [div_le_iff₀ (by positivity : 0 < (k n : ℝ) + 1)]
    nlinarith [show (0 : ℝ) ≤ (k n : ℝ) from Nat.cast_nonneg (k n)]
  have hsupport (n : ℕ) (t : ℝ) (ht : c n < t) : F n t - A t = 0 :=
    sub_eq_zero.mpr (pmFinitePrimePowerDampedFermiSource_eq_of_inverse_cutoff ε (k n) ht)
  have hb (n : ℕ) : eLpNorm (fun t => F n t - A t) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal (2 * C) := by
    calc
      _ ≤ eLpNorm (F n) 2 (volume.restrict (Ioi (0 : ℝ))) +
          eLpNorm A 2 (volume.restrict (Ioi (0 : ℝ))) :=
        eLpNorm_sub_le (hFm n).aestronglyMeasurable hAm.aestronglyMeasurable (by norm_num)
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := add_le_add (hbound n) hA
      _ = _ := by rw [← ENNReal.ofReal_add hC hC]; congr 1; ring
  have hz := pm_mellin_tendsto_zero_of_cutoffs (fun n => (hFm n).sub hAm)
    hc0 hc1 (tendsto_one_div_add_atTop_nhds_zero_nat.comp hk) (by positivity : 0 ≤ 2 * C) hb hsupport hs
  have hsub (n : ℕ) : mellin (fun t => F n t - A t) s = mellin (F n) s - mellin A s := by
    exact (hasMellin_sub
      (pm_mellinConvergent_of_memLp (hFm n) (fun t ht => by
        have he := pmFinitePrimePowerDampedFermiSource_eq_of_inverse_cutoff ε (k n) ((hc1 n).trans_lt ht)
        exact he.trans (pmPowerDampedFermiSource_eq_zero_of_one_lt ε ht)) hs)
      (pm_mellinConvergent_of_memLp hAm (fun t ht => pmPowerDampedFermiSource_eq_zero_of_one_lt ε ht) hs)).2
  change Tendsto (fun n => mellin (fun t => F n t - A t) s) atTop (𝓝 0) at hz
  simp_rw [hsub] at hz
  simpa only [sub_add_cancel, zero_add] using hz.add_const (mellin A s)

/-- Identity theorem: a function analytic on `Re z > 1/2` that vanishes on a real interval
`(a, b)` with `1/2 ≤ a < b` vanishes at `z = 1`. -/
theorem pm_analytic_halfplane_zero_of_real_interval {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 1 / 2 < z.re}) {a b : ℝ}
    (ha : 1 / 2 ≤ a) (hab : a < b)
    (hz : ∀ x : ℝ, a < x → x < b → f (x : ℂ) = 0) : f 1 = 0 := by
  let m := (a + b) / 2
  let q := fun n : ℕ => m + ((b - m) / 2) * (1 / ((n : ℝ) + 1))
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hmq (n : ℕ) : m < q n := by
    dsimp [q]
    have hpos : 0 < ((b - m) / 2) * (1 / ((n : ℝ) + 1)) := by positivity
    linarith
  have hqb (n : ℕ) : q n < b := by
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    have h := mul_le_mul_of_nonneg_left hle (by linarith : 0 ≤ (b - m) / 2)
    dsimp [q]
    nlinarith
  have hlim : Tendsto q atTop (𝓝 m) := by
    have hconst : Tendsto (fun _ : ℕ => m) atTop (𝓝 m) := tendsto_const_nhds
    have h := hconst.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((b - m) / 2))
    simpa only [mul_zero, add_zero] using h
  have hclosure : (m : ℂ) ∈ closure ({z : ℂ | f z = 0} \ {(m : ℂ)}) := by
    apply mem_closure_of_tendsto (Complex.continuous_ofReal.tendsto m |>.comp hlim)
    apply Eventually.of_forall
    intro n
    refine ⟨hz (q n) (ham.trans (hmq n)) (hqb n), ?_⟩
    change (q n : ℂ) ≠ (m : ℂ)
    exact fun h => (hmq n).ne' (Complex.ofReal_injective h)
  have he := hf.eqOn_zero_of_preconnected_of_mem_closure
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    (show (m : ℂ) ∈ {z : ℂ | 1 / 2 < z.re} by simp only [mem_setOf_eq, ofReal_re]; linarith)
    hclosure
  exact he (by norm_num : (1 : ℂ) ∈ {z : ℂ | 1 / 2 < z.re})

/-- At real `u`, the finite Euler product is the real product `∏_{p∈S} (1 − p^(−u))`. -/
theorem pm_finitePrimeEulerProduct_ofReal (S : Finset ℕ) (u : ℝ) :
    finitePrimeEulerProduct S (u : ℂ) =
      ((∏ p ∈ S, (1 - (p : ℝ) ^ (-u)) : ℝ) : ℂ) := by
  rw [finitePrimeEulerProduct, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg p),
    Complex.ofReal_natCast, Complex.ofReal_neg]

/-- For `0 < x < 1` and `0 < x + ε ≤ 1`, the Mellin transforms of the canonical sources at `x`
tend to `0` as `N → ∞`. -/
theorem pmCanonicalPrimeMellin_tendsto_zero {ε x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hu0 : 0 < x + ε) (hu1 : x + ε ≤ 1) :
    Tendsto (fun N : ℕ => mellin
      (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε) (x : ℂ))
      atTop (𝓝 0) := by
  let K : ℂ := (1 - (2 : ℂ) ^ (1 - (x : ℂ))) * riemannZeta (x : ℂ) / (x : ℂ)
  have h := ((Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
    (pmCanonicalPrimeEulerProduct_tendsto_zero hu0 hu1)).const_mul K
  have hz : Tendsto (fun N : ℕ => K *
      ((∏ p ∈ mobiusFinitePrimeAperture N, (1 - (p : ℝ) ^ (-(x + ε))) : ℝ) : ℂ))
      atTop (𝓝 0) := by simpa using h
  apply hz.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [mellin_pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N)
    (fun p hp => (Finset.mem_filter.mp hp).2) ε hx0 hx1]
  change K * _ = K * _
  rw [← Complex.ofReal_add, pm_finitePrimeEulerProduct_ofReal]

/-- For `0 < ε < 1/2`, `k_n → ∞` and any `C ≥ 0`, the canonical sources along `k_n` are not
all bounded by `C` in `L²(0,∞)`. -/
theorem pmCanonicalPrime_no_bounded_cofinal_subsequence {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    {C : ℝ} (hC : 0 ≤ C) :
    ¬ ∀ n, eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (k n)) ε)
      2 (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal C := by
  intro hb
  have hA := pmPowerDampedFermiSource_norm_le_of_cofinal_prime_budget ε hk hb
  have hAm : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    ⟨(measurable_pmPowerDampedFermiSource ε).aestronglyMeasurable,
      hA.trans_lt ENNReal.ofReal_lt_top⟩
  have hzero (x : ℝ) (hx0 : 1 / 2 < x) (hx1 : x < 1 - ε) :
      mellin (pmPowerDampedFermiSource ε) (x : ℂ) = 0 := by
    have hlim := pm_mellin_tendsto_of_cofinal_prime_budget ε hk hC hb (s := (x : ℂ)) hx0
    have hz := (pmCanonicalPrimeMellin_tendsto_zero (ε := ε) (x := x)
      (by linarith) (by linarith) (by linarith) (by linarith)).comp hk
    exact tendsto_nhds_unique hlim hz
  have hmean := pm_analytic_halfplane_zero_of_real_interval
    (analyticOnNhd_mellin_pmPowerDampedFermiSource ε hAm)
    (a := 1 / 2) (b := 1 - ε) le_rfl (by linarith) hzero
  rw [(hasMellin_pmPowerDampedFermiSource_one hε0).2] at hmean
  exact (div_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne')
    (riemannZeta_ne_zero_of_one_lt_re (by simp only [add_re, one_re, ofReal_re]; linarith))) hmean

/-- For `0 < ε < 1/2` and every real `C`, the canonical source on the primes `≤ N` eventually
has `L²` norm exceeding `C`. -/
theorem pmCanonicalPrime_eventually_exceeds_every_budget {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ENNReal.ofReal C <
      eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε)
        2 (volume.restrict (Ioi (0 : ℝ))) := by
  by_contra h
  have hfreq : ∃ᶠ N : ℕ in atTop,
      eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε)
        2 (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal C := by
    simpa only [Filter.Frequently, not_le] using h
  obtain ⟨k, hk, hkb⟩ := Filter.exists_seq_forall_of_frequently hfreq
  apply pmCanonicalPrime_no_bounded_cofinal_subsequence hε0 hε1 hk (C := max C 0) (le_max_right _ _)
  intro n
  exact (hkb n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

/-- For `0 < ε < 1/2`, the `L²(0,∞)` norms of the canonical finite-prime sources tend to `∞`. -/
theorem tendsto_pmCanonicalPrime_norm_atTop {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    Tendsto (fun N : ℕ =>
      (eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε)
        2 (volume.restrict (Ioi (0 : ℝ)))).toReal) atTop atTop := by
  rw [tendsto_atTop]
  intro C
  filter_upwards [pmCanonicalPrime_eventually_exceeds_every_budget hε0 hε1 C] with N hN
  by_contra h
  have hle : eLpNorm (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε)
      2 (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal (memLp_pmFinitePrimePowerDampedFermiSource _ ε).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge h))
  exact (not_lt_of_ge hle) hN

end RHTower
