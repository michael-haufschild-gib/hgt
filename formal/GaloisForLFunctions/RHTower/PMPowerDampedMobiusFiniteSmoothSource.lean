import GaloisForLFunctions.RHTower.PMPowerDampedMobiusFiniteDeletion
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Deleting a finite prime set: smooth Haar sources and Euler-product energy

For a finite set `E`, the `E`-factored numbers (positive integers whose prime factors all lie
in `E`) have convergent Euler product `∑ n^(−σ) = ∏_{p∈E prime} (1 − p^(−σ))⁻¹` for `σ > 0`.
The finite smooth Haar source `∑'_{n E-factored} h(n t)` is therefore in `L²(0,∞)` and
integrable with integral zero, and its energy is the explicit Gram double series. Deleting the
primes of `E` from the Möbius Fermi source produces exactly this smooth Haar source, so the
deleted source has energy at least the Mertens-type product `∏_{p∈E prime} (1 − 1/p)⁻¹`.

## Main results

- `pmFactoredNumbers_tsum_neg_rpow`: for `σ > 0`, `∑'_{n E-factored} n^(−σ) = ∏_{p∈E prime} (1 − p^(−σ))⁻¹`.
- `memLp_pmFiniteSmoothHaarSource`, `pmFiniteSmoothHaarSource_integral`: the finite smooth Haar source is in `L²(0,∞)` and has integral `0`.
- `pmFiniteSmoothHaarSource_energy_eq_tsum_gram`: its energy is `∑'_{m,n} max 0 (2/max m n − 1/min m n)` over `E`-factored `m, n`.
- `pmDeletedMobiusFermiSource_eq_finiteSmoothHaar`: deleting `E` from the Möbius Fermi source gives the finite smooth Haar source on `(0,∞)`.
- `pmDeletedMobiusFermiSource_finite_euler_product_le_energy`: the deleted source has energy `≥ ∏_{p∈E prime} (1 − 1/p)⁻¹`.

## Hypotheses

All results are unconditional; the only numerical hypothesis is `0 < σ` in the Euler-product
summation lemmas.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

/-- The completely multiplicative map `n ↦ n^(−σ)` as a monoid homomorphism `ℕ →* ℝ`. -/
def pmNaturalRpowHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' m n := by
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

theorem pmNaturalRpowHom_prime_norm_lt_one {σ : ℝ} (hσ : 0 < σ)
    {p : ℕ} (hp : p.Prime) : ‖pmNaturalRpowHom σ p‖ < 1 := by
  change ‖(p : ℝ) ^ (-σ)‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- For `σ > 0` and finite `E`, `n ↦ n^(−σ)` is summable over the `E`-factored numbers. -/
theorem summable_pmFactoredNumbers_neg_rpow (E : Finset ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : Nat.factoredNumbers E => (n : ℝ) ^ (-σ)) := by
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := pmNaturalRpowHom σ) (fun {_} hp => pmNaturalRpowHom_prime_norm_lt_one hσ hp) E).1
  simpa only [pmNaturalRpowHom, MonoidHom.coe_mk, OneHom.coe_mk, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using h

/-- Euler product over a finite prime set: for `σ > 0`,
`∑'_{n E-factored} n^(−σ) = ∏_{p∈E prime} (1 − p^(−σ))⁻¹`. -/
theorem pmFactoredNumbers_tsum_neg_rpow (E : Finset ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (∑' n : Nat.factoredNumbers E, (n : ℝ) ^ (-σ)) =
      ∏ p ∈ E with p.Prime, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  exact (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := pmNaturalRpowHom σ) (fun {_} hp => pmNaturalRpowHom_prime_norm_lt_one hσ hp) E).2.tsum_eq

/-- The finite smooth Haar source `∑'_{n E-factored} h(n t)`, with `h` the dyadic Haar function
supported on `(0,1]`. -/
def pmFiniteSmoothHaarSource (E : Finset ℕ) : ℝ → ℂ :=
  pmHaarDilationSeries (fun n : Nat.factoredNumbers E => (n : ℝ))

theorem pm_factored_cast_pos (E : Finset ℕ) (n : Nat.factoredNumbers E) : (0 : ℝ) < (n : ℕ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers n.property)

theorem summable_pmFiniteSmoothHaarSource_term_norm (E : Finset ℕ) :
    Summable (fun n : Nat.factoredNumbers E => Real.sqrt (1 / (n : ℝ))) := by
  have heq (n : Nat.factoredNumbers E) : Real.sqrt (1 / (n : ℝ)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← pmHaarDilationVector_norm _ (pm_factored_cast_pos E n), pmHaarDilationVector_norm_rpow]
  simpa only [heq] using summable_pmFactoredNumbers_neg_rpow E (σ := 1 / 2) (by norm_num)

/-- The finite smooth Haar source lies in `L²(0,∞)`. -/
theorem memLp_pmFiniteSmoothHaarSource (E : Finset ℕ) :
    MemLp (pmFiniteSmoothHaarSource E) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  memLp_pmHaarDilationSeries (pm_factored_cast_pos E) (summable_pmFiniteSmoothHaarSource_term_norm E)

/-- For `t > 0`, the smooth Haar series reduces to the finite sum over `E`-factored `n ≤ 1/t`. -/
theorem pmFiniteSmoothHaarSource_eq_sum (E : Finset ℕ) {t : ℝ} (ht : 0 < t) :
    pmFiniteSmoothHaarSource E t = ∑ n ∈ Finset.Icc 1 ⌊1 / t⌋₊,
      if n ∈ Nat.factoredNumbers E then pmSupportedDyadicHaar ((n : ℝ) * t) else 0 := by
  classical
  unfold pmFiniteSmoothHaarSource pmHaarDilationSeries
  rw [tsum_subtype (Nat.factoredNumbers E) (fun n : ℕ => pmSupportedDyadicHaar ((n : ℝ) * t))]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊1 / t⌋₊) (fun n hn => ?_)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [Set.indicator]
  · by_cases hs : n ∈ Nat.factoredNumbers E
    · rw [Set.indicator_of_mem hs]
      have hn0 := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers hs)
      have hgt : ⌊1 / t⌋₊ < n := by
        have hh := mt Finset.mem_Icc.mpr hn
        omega
      have hnt : 1 / t < (n : ℝ) := (Nat.lt_floor_add_one (1 / t)).trans_le
        (by exact_mod_cast (show ⌊1 / t⌋₊ + 1 ≤ n by omega))
      exact pmSupportedDyadicHaar_eq_zero (by
        have hh := (div_lt_iff₀ ht).mp hnt
        nlinarith)
    · exact Set.indicator_of_notMem hs _

/-- The finite smooth Haar source has integral zero over `(0,∞)`. -/
theorem pmFiniteSmoothHaarSource_integral (E : Finset ℕ) :
    (∫ t in Ioi (0 : ℝ), pmFiniteSmoothHaarSource E t) = 0 := by
  have hs : Summable (fun n : Nat.factoredNumbers E => 1 / (n : ℝ)) := by
    simpa only [neg_one_mul, Real.rpow_neg_one, one_div] using
      summable_pmFactoredNumbers_neg_rpow E (σ := 1) (by norm_num)
  have hnorm : Summable (fun n : Nat.factoredNumbers E =>
      ∫ t in Ioi (0 : ℝ), ‖pmSupportedDyadicHaar ((n : ℝ) * t)‖) := by
    simpa only [pmSupportedDyadicHaar_dilation_integral_norm (pm_factored_cast_pos E _)] using hs
  unfold pmFiniteSmoothHaarSource pmHaarDilationSeries
  rw [← integral_tsum_of_summable_integral_norm
    (fun n => integrable_pmSupportedDyadicHaar_dilation (pm_factored_cast_pos E n)) hnorm]
  simp only [pmSupportedDyadicHaar_dilation_integral (pm_factored_cast_pos E _), tsum_zero]

theorem pmFiniteSmoothHaarSource_eq_zero (E : Finset ℕ) {t : ℝ} (ht : 1 < t) : pmFiniteSmoothHaarSource E t = 0 := by
  have hz (n : Nat.factoredNumbers E) : pmSupportedDyadicHaar ((n : ℝ) * t) = 0 := by
    apply pmSupportedDyadicHaar_eq_zero
    have hn : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers n.property)
    nlinarith
  simp only [pmFiniteSmoothHaarSource, pmHaarDilationSeries, hz, tsum_zero]

/-- The finite smooth Haar source is integrable on `(0,∞)` (it vanishes for `t > 1`). -/
theorem integrable_pmFiniteSmoothHaarSource (E : Finset ℕ) :
    Integrable (pmFiniteSmoothHaarSource E) (volume.restrict (Ioi (0 : ℝ))) := by
  have hi : IntegrableOn (pmFiniteSmoothHaarSource E) (Ioc (0 : ℝ) 1) :=
    ((memLp_pmFiniteSmoothHaarSource E).mono_measure
      (Measure.restrict_mono (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self) le_rfl)).integrable
      (by norm_num)
  have hind := (hi.integrable_indicator measurableSet_Ioc).mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ioi (0 : ℝ)))
  apply (integrable_congr (show (Ioc (0 : ℝ) 1).indicator (pmFiniteSmoothHaarSource E) =ᵐ[volume.restrict (Ioi 0)]
    pmFiniteSmoothHaarSource E from ?_)).mp hind
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases ht1 : t ≤ 1
  · exact Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩) _
  · rw [Set.indicator_of_notMem (by simp [ht1]), pmFiniteSmoothHaarSource_eq_zero E (lt_of_not_ge ht1)]

/-- The energy of the finite smooth Haar source is the Gram double series
`∑'_{m,n E-factored} max 0 (2/max m n − 1/min m n)`. -/
theorem pmFiniteSmoothHaarSource_energy_eq_tsum_gram (E : Finset ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖pmFiniteSmoothHaarSource E t‖ ^ (2 : ℕ)) =
      ∑' m : Nat.factoredNumbers E, ∑' n : Nat.factoredNumbers E,
        max 0 (2 / max (m : ℝ) (n : ℝ) - 1 / min (m : ℝ) (n : ℝ)) := by
  rw [pmFiniteSmoothHaarSource, pmHaarDilationSeries_energy_eq_tsum_gram
    (pm_factored_cast_pos E) (summable_pmFiniteSmoothHaarSource_term_norm E)]
  apply tsum_congr
  intro m
  apply tsum_congr
  intro n
  exact pmHaarDilationGram_eq_max (pm_factored_cast_pos E m) (pm_factored_cast_pos E n)

/-- The finite smooth Haar source has energy at least `∏_{p∈E prime} (1 − 1/p)⁻¹`, the sum of
its diagonal Gram entries `1/n`. -/
theorem pmFiniteSmoothHaarSource_euler_product_le_energy (E : Finset ℕ) :
    (∏ p ∈ E with p.Prime, (1 - 1 / (p : ℝ))⁻¹) ≤
      (∫ t in Ioi (0 : ℝ), ‖pmFiniteSmoothHaarSource E t‖ ^ (2 : ℕ)) := by
  have he := pmFactoredNumbers_tsum_neg_rpow E (σ := 1) (by norm_num)
  simp only [Real.rpow_neg_one] at he
  simp only [one_div]
  rw [← he]
  apply Real.tsum_le_of_sum_le (fun n => inv_nonneg.mpr (Nat.cast_nonneg _))
  intro S
  simpa only [one_div, pmFiniteSmoothHaarSource] using pmHaarDilationSeries_diagonal_le_energy S (pm_factored_cast_pos E)
    (summable_pmFiniteSmoothHaarSource_term_norm E)

theorem pm_smoothAF_factoredNumbers (E : Finset ℕ) (n : ℕ) :
    CoprimeMobius.smoothAF (↑E : Set ℕ) n =
      if n ∈ Nat.factoredNumbers E then (1 : ℤ) else 0 := by
  have he : CoprimeMobius.IsSmooth (↑E : Set ℕ) n ↔ n ∈ Nat.factoredNumbers E := by
    change (n ≠ 0 ∧ n.primeFactors ⊆ E) ↔ n ∈ Nat.factoredNumbers E
    exact Nat.mem_factoredNumbers_iff_primeFactors_subset.symm
  simp only [CoprimeMobius.smoothAF_apply, he]

/-- For `t > 0`, the finite smooth Haar source equals
`#{n ≤ 1/t : E-factored} − 2 #{n ≤ 1/(2t) : E-factored}`. -/
theorem pmFiniteSmoothHaarSource_eq_counts (E : Finset ℕ) {t : ℝ} (ht : 0 < t) :
    pmFiniteSmoothHaarSource E t =
      (∑ n ∈ Finset.Icc 1 ⌊1 / t⌋₊, (CoprimeMobius.smoothAF (↑E : Set ℕ) n : ℂ)) -
      2 * (∑ n ∈ Finset.Icc 1 ⌊1 / (2 * t)⌋₊, (CoprimeMobius.smoothAF (↑E : Set ℕ) n : ℂ)) := by
  classical
  let K := ⌊1 / t⌋₊
  let L := ⌊1 / (2 * t)⌋₊
  let c := fun n => (CoprimeMobius.smoothAF (↑E : Set ℕ) n : ℂ)
  have hLK : L ≤ K := Nat.floor_mono (one_div_le_one_div_of_le ht (by linarith))
  have hcond (n : ℕ) : (n : ℝ) * t ≤ 1 / 2 ↔ n ≤ L := by
    rw [Nat.le_floor_iff (by positivity : 0 ≤ 1 / (2 * t)), le_div_iff₀ (by positivity : 0 < 2 * t)]
    constructor <;> intro h <;> nlinarith
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 K) :
      (if n ∈ Nat.factoredNumbers E then pmSupportedDyadicHaar ((n : ℝ) * t) else 0) =
        c n - 2 * (c n * (if n ≤ L then 1 else 0)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn1 : (n : ℝ) * t ≤ 1 := by
      apply (le_div_iff₀ ht).mp
      exact (Nat.le_floor_iff (by positivity : 0 ≤ 1 / t)).mp (Finset.mem_Icc.mp hn).2
    have hH : pmSupportedDyadicHaar ((n : ℝ) * t) = 1 - 2 * (if n ≤ L then 1 else 0) := by
      rw [pmSupportedDyadicHaar_eq_cutoffs (mul_pos hn0 ht), if_pos hn1]
      simp only [hcond n]
    by_cases hs : n ∈ Nat.factoredNumbers E <;> simp [c, pm_smoothAF_factoredNumbers, hs, hH]
  have hfilter : (Finset.Icc 1 K).filter (fun n => n ≤ L) = Finset.Icc 1 L := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hhalf : (∑ n ∈ Finset.Icc 1 K, c n * (if n ≤ L then 1 else 0)) =
      ∑ n ∈ Finset.Icc 1 L, c n := by
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hfilter]
  rw [pmFiniteSmoothHaarSource_eq_sum E ht]
  change (∑ n ∈ Finset.Icc 1 K, _) = (∑ n ∈ Finset.Icc 1 K, c n) - 2 * (∑ n ∈ Finset.Icc 1 L, c n)
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hhalf]

/-- Deleting the finite prime set `E` from the Möbius Fermi source yields the finite smooth Haar
source at every `t > 0`. -/
theorem pmDeletedMobiusFermiSource_eq_finiteSmoothHaar (E : Finset ℕ) {t : ℝ} (ht : 0 < t) :
    pmDeletedMobiusFermiSource (↑E : Set ℕ) t = pmFiniteSmoothHaarSource E t := by
  rw [pmDeletedMobiusFermiSource_eq_counts _ ht, pmFiniteSmoothHaarSource_eq_counts E ht]

/-- The Möbius Fermi source with a finite prime set deleted lies in `L²(0,∞)`. -/
theorem memLp_pmDeletedMobiusFermiSource_finite (E : Finset ℕ) :
    MemLp (pmDeletedMobiusFermiSource (↑E : Set ℕ)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_congr_ae (show pmDeletedMobiusFermiSource (↑E : Set ℕ) =ᵐ[volume.restrict (Ioi 0)]
    pmFiniteSmoothHaarSource E from ?_)).mpr (memLp_pmFiniteSmoothHaarSource E)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact pmDeletedMobiusFermiSource_eq_finiteSmoothHaar E ht

theorem integrable_pmDeletedMobiusFermiSource_finite (E : Finset ℕ) :
    Integrable (pmDeletedMobiusFermiSource (↑E : Set ℕ)) (volume.restrict (Ioi (0 : ℝ))) := by
  apply (integrable_congr (show pmDeletedMobiusFermiSource (↑E : Set ℕ) =ᵐ[volume.restrict (Ioi 0)]
    pmFiniteSmoothHaarSource E from ?_)).mpr (integrable_pmFiniteSmoothHaarSource E)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact pmDeletedMobiusFermiSource_eq_finiteSmoothHaar E ht

/-- The Möbius Fermi source with a finite prime set deleted has integral zero over `(0,∞)`. -/
theorem pmDeletedMobiusFermiSource_finite_integral (E : Finset ℕ) :
    (∫ t in Ioi (0 : ℝ), pmDeletedMobiusFermiSource (↑E : Set ℕ) t) = 0 := by
  rw [← pmFiniteSmoothHaarSource_integral E]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => pmDeletedMobiusFermiSource_eq_finiteSmoothHaar E ht)

/-- The energy of the `E`-deleted Möbius Fermi source is the Gram double series over the
`E`-factored numbers. -/
theorem pmDeletedMobiusFermiSource_finite_energy_eq_tsum_gram (E : Finset ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖pmDeletedMobiusFermiSource (↑E : Set ℕ) t‖ ^ (2 : ℕ)) =
      ∑' m : Nat.factoredNumbers E, ∑' n : Nat.factoredNumbers E,
        max 0 (2 / max (m : ℝ) (n : ℝ) - 1 / min (m : ℝ) (n : ℝ)) := by
  rw [← pmFiniteSmoothHaarSource_energy_eq_tsum_gram E]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [pmDeletedMobiusFermiSource_eq_finiteSmoothHaar E ht]

/-- The `E`-deleted Möbius Fermi source has energy at least `∏_{p∈E prime} (1 − 1/p)⁻¹`. -/
theorem pmDeletedMobiusFermiSource_finite_euler_product_le_energy (E : Finset ℕ) :
    (∏ p ∈ E with p.Prime, (1 - 1 / (p : ℝ))⁻¹) ≤
      (∫ t in Ioi (0 : ℝ), ‖pmDeletedMobiusFermiSource (↑E : Set ℕ) t‖ ^ (2 : ℕ)) := by
  have he : (∫ t in Ioi (0 : ℝ), ‖pmDeletedMobiusFermiSource (↑E : Set ℕ) t‖ ^ (2 : ℕ)) =
      ∫ t in Ioi (0 : ℝ), ‖pmFiniteSmoothHaarSource E t‖ ^ (2 : ℕ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [pmDeletedMobiusFermiSource_eq_finiteSmoothHaar E ht]
  rw [he]
  exact pmFiniteSmoothHaarSource_euler_product_le_energy E

end RHTower
