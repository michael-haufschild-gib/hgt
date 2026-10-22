import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSmoothHaar
import GaloisForLFunctions.RHTower.CoprimeMobiusSumsZeroFree
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap

/-!
# Prime-deleted Möbius Fermi sources and unbounded finite-prime norms

For a set `E` of primes let `μ_E` be the Möbius function restricted to integers with no
prime factor in `E`. The deleted source `pmDeletedMobiusFermiSource E t = −∑_{d ≤ 1/t} μ_E(d) φ_d(t)`,
with `φ_a(t) = {1/(at)} − 2{1/(2at)}` the alternating Nyman generator, is rewritten through
the divisor identity `∑_{d|n} μ_E(d) = 1_{E-smooth}(n)` as a difference of smooth counts.
For `E` the primes below `N` it coincides on `(0,∞)` with the smooth Haar source
`∑_{n N-smooth} h(n t)`, whose energy tends to infinity. The same smooth Haar source is the
pointwise limit of undamped finite-prime sources whose aperture contains the primes from `N`
to `M`. Consequently no finite `L²` budget bounds the power-damped finite-prime sources
uniformly over small positive dampings and finite prime sets.

## Main results

- `pmDeletedMobiusFermiSource_eq_counts`: the deleted source as `∑_{n≤1/t} 1_{E-smooth}(n) − 2∑_{n≤1/(2t)} 1_{E-smooth}(n)`.
- `pmDeletedMobiusFermiSource_eq_smoothHaar`: for `E = primes < N`, the deleted source equals `pmSmoothHaarSource N` at each `t > 0`.
- `pmDeletedMobiusFermiSource_energy_eq_tsum_gram`: its energy is `∑'_{m,n N-smooth} max 0 (2/max m n − 1/min m n)`.
- `pmFinitePrimePowerDampedFermiSource_deleted_eq_of_covers`: the undamped source on the prime aperture `[N, M]` equals the smooth Haar source once `M ≥ ⌊1/t⌋`.
- `pmSmoothHaarSource_no_uniform_norm_budget`: no finite `C` bounds `‖pmSmoothHaarSource N‖_{L²}` for all `N`.
- `pmFinitePrimePowerDampedFermiSource_all_subset_budget_eq_top`: a common bound over all `ε ∈ (0,δ)` and all finite prime sets must be `⊤`.
- `pmFinitePrimePowerDampedFermiSource_exceeds_every_finite_budget`: for every real `C` and `δ > 0` some `ε ∈ (0,δ)` and finite prime set `S` give an `L²` source of norm `> C`.

## Hypotheses

All results are unconditional. The budget statements take as hypotheses only the bound
being refuted (a uniform norm bound `C`, assumed finite where stated) and `0 < δ`.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

/-- Dirichlet hyperbola swap: `∑_{d≤N} f(d)⌊N/d⌋ = ∑_{n≤N} ∑_{d|n} f(d)`. -/
theorem pm_divisor_floor_sum_nat (f : ℕ → ℂ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, f d * ((N / d : ℕ) : ℂ)) =
      ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), f d := by
      simp [mul_comm]
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal, f x.1 :=
      (Sieve.sum_Icc_divisorsAntidiagonal_swap (fun d _ => f d) N).symm
    _ = _ := by simp_rw [Nat.sum_divisorsAntidiagonal (fun d _ => f d)]

/-- For real `x ≥ 0` and any `N ≥ ⌊x⌋`, `∑_{d≤N} f(d)⌊x/d⌋ = ∑_{n≤x} ∑_{d|n} f(d)`. -/
theorem pm_divisor_floor_sum (f : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x)
    {N : ℕ} (hN : ⌊x⌋₊ ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, f d * (⌊x / (d : ℝ)⌋ : ℂ)) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, f d := by
  have hfloor (d : ℕ) : (⌊x / (d : ℝ)⌋ : ℂ) = ((⌊x⌋₊ / d : ℕ) : ℂ) := by
    rw [← Int.natCast_floor_eq_floor (div_nonneg hx (Nat.cast_nonneg d)),
      Int.cast_natCast, Nat.floor_div_natCast]
  simp_rw [hfloor]
  rw [← pm_divisor_floor_sum_nat f ⌊x⌋₊]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hN)
  intro d hd hnot
  have hgt : ⌊x⌋₊ < d := by
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hh := mt Finset.mem_Icc.mpr hnot
    omega
  rw [Nat.div_eq_of_lt hgt, Nat.cast_zero, mul_zero]

/-- For `x ≥ 0` and `N ≥ ⌊x⌋`, `∑_{d≤N} μ_E(d)⌊x/d⌋` counts the `E`-smooth integers up to `x`. -/
theorem pm_deleted_mobius_floor_sum (E : Set ℕ) {x : ℝ} (hx : 0 ≤ x)
    {N : ℕ} (hN : ⌊x⌋₊ ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, (CoprimeMobius.mobiusAF E d : ℂ) * (⌊x / (d : ℝ)⌋ : ℂ)) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (CoprimeMobius.smoothAF E n : ℂ) := by
  rw [pm_divisor_floor_sum _ hx hN]
  apply Finset.sum_congr rfl
  intro n hn
  exact_mod_cast CoprimeMobius.sum_divisors_mobiusAF E n

/-- The prime-deleted Möbius Fermi source `−∑_{d ≤ 1/t} μ_E(d) φ_d(t)`, where `μ_E` is the
Möbius function supported on integers free of primes in `E`. -/
def pmDeletedMobiusFermiSource (E : Set ℕ) (t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 ⌊1 / t⌋₊, (CoprimeMobius.mobiusAF E d : ℂ) * fermiNymanGen (d : ℝ) t)

/-- For `t > 0`, the deleted source equals `#{n ≤ 1/t : E-smooth} − 2 #{n ≤ 1/(2t) : E-smooth}`. -/
theorem pmDeletedMobiusFermiSource_eq_counts (E : Set ℕ) {t : ℝ} (ht : 0 < t) :
    pmDeletedMobiusFermiSource E t =
      (∑ n ∈ Finset.Icc 1 ⌊1 / t⌋₊, (CoprimeMobius.smoothAF E n : ℂ)) -
      2 * (∑ n ∈ Finset.Icc 1 ⌊1 / (2 * t)⌋₊, (CoprimeMobius.smoothAF E n : ℂ)) := by
  have hhalf : ⌊1 / (2 * t)⌋₊ ≤ ⌊1 / t⌋₊ := by
    apply Nat.floor_mono
    exact one_div_le_one_div_of_le ht (by linarith)
  calc
    _ = (∑ d ∈ Finset.Icc 1 ⌊1 / t⌋₊,
        (CoprimeMobius.mobiusAF E d : ℂ) * (⌊(1 / t) / (d : ℝ)⌋ : ℂ)) -
        2 * (∑ d ∈ Finset.Icc 1 ⌊1 / t⌋₊,
          (CoprimeMobius.mobiusAF E d : ℂ) * (⌊(1 / (2 * t)) / (d : ℝ)⌋ : ℂ)) := by
      unfold pmDeletedMobiusFermiSource
      simp_rw [fermiNymanGen_eq_floor_difference]
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by
      rw [pm_deleted_mobius_floor_sum E (by positivity) le_rfl,
        pm_deleted_mobius_floor_sum E (by positivity) hhalf]

theorem pm_smoothAF_primesBelow (N n : ℕ) :
    CoprimeMobius.smoothAF (↑(Nat.primesBelow N) : Set ℕ) n =
      if n ∈ N.smoothNumbers then (1 : ℤ) else 0 := by
  have he : CoprimeMobius.IsSmooth (↑(Nat.primesBelow N) : Set ℕ) n ↔ n ∈ N.smoothNumbers := by
    change (n ≠ 0 ∧ n.primeFactors ⊆ Nat.primesBelow N) ↔ n ∈ N.smoothNumbers
    exact Nat.mem_smoothNumbers_iff_primeFactors_subset.symm
  simp only [CoprimeMobius.smoothAF_apply, he]

/-- For `t > 0`, the smooth Haar source `∑_{n N-smooth} h(n t)` is the same difference of
smooth counts at `1/t` and `1/(2t)`, with `E` the primes below `N`. -/
theorem pmSmoothHaarSource_eq_counts (N : ℕ) {t : ℝ} (ht : 0 < t) :
    pmSmoothHaarSource N t =
      (∑ n ∈ Finset.Icc 1 ⌊1 / t⌋₊, (CoprimeMobius.smoothAF (↑(Nat.primesBelow N) : Set ℕ) n : ℂ)) -
      2 * (∑ n ∈ Finset.Icc 1 ⌊1 / (2 * t)⌋₊, (CoprimeMobius.smoothAF (↑(Nat.primesBelow N) : Set ℕ) n : ℂ)) := by
  classical
  let K := ⌊1 / t⌋₊
  let L := ⌊1 / (2 * t)⌋₊
  let c := fun n => (CoprimeMobius.smoothAF (↑(Nat.primesBelow N) : Set ℕ) n : ℂ)
  have hLK : L ≤ K := Nat.floor_mono (one_div_le_one_div_of_le ht (by linarith))
  have hcond (n : ℕ) : (n : ℝ) * t ≤ 1 / 2 ↔ n ≤ L := by
    rw [Nat.le_floor_iff (by positivity : 0 ≤ 1 / (2 * t)), le_div_iff₀ (by positivity : 0 < 2 * t)]
    constructor <;> intro h <;> nlinarith
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 K) :
      (if n ∈ N.smoothNumbers then pmSupportedDyadicHaar ((n : ℝ) * t) else 0) =
        c n - 2 * (c n * (if n ≤ L then 1 else 0)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn1 : (n : ℝ) * t ≤ 1 := by
      apply (le_div_iff₀ ht).mp
      exact (Nat.le_floor_iff (by positivity : 0 ≤ 1 / t)).mp (Finset.mem_Icc.mp hn).2
    have hH : pmSupportedDyadicHaar ((n : ℝ) * t) = 1 - 2 * (if n ≤ L then 1 else 0) := by
      rw [pmSupportedDyadicHaar_eq_cutoffs (mul_pos hn0 ht), if_pos hn1]
      simp only [hcond n]
    by_cases hs : n ∈ N.smoothNumbers <;> simp [c, pm_smoothAF_primesBelow, hs, hH]
  have hfilter : (Finset.Icc 1 K).filter (fun n => n ≤ L) = Finset.Icc 1 L := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hhalf : (∑ n ∈ Finset.Icc 1 K, c n * (if n ≤ L then 1 else 0)) =
      ∑ n ∈ Finset.Icc 1 L, c n := by
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hfilter]
  rw [pmSmoothHaarSource_eq_sum N ht]
  change (∑ n ∈ Finset.Icc 1 K, _) = (∑ n ∈ Finset.Icc 1 K, c n) - 2 * (∑ n ∈ Finset.Icc 1 L, c n)
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hhalf]

/-- Deleting the primes below `N` turns the Möbius Fermi source into the smooth Haar source:
equality holds at every `t > 0`. -/
theorem pmDeletedMobiusFermiSource_eq_smoothHaar (N : ℕ) {t : ℝ} (ht : 0 < t) :
    pmDeletedMobiusFermiSource (↑(Nat.primesBelow N) : Set ℕ) t = pmSmoothHaarSource N t := by
  rw [pmDeletedMobiusFermiSource_eq_counts _ ht, pmSmoothHaarSource_eq_counts N ht]

/-- The source with the primes below `N` deleted lies in `L²(0,∞)`. -/
theorem memLp_pmDeletedMobiusFermiSource (N : ℕ) :
    MemLp (pmDeletedMobiusFermiSource (↑(Nat.primesBelow N) : Set ℕ)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_congr_ae (show pmDeletedMobiusFermiSource (↑(Nat.primesBelow N) : Set ℕ) =ᵐ[volume.restrict (Ioi 0)]
    pmSmoothHaarSource N from ?_)).mpr (memLp_pmSmoothHaarSource N)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact pmDeletedMobiusFermiSource_eq_smoothHaar N ht

/-- The finite prime aperture of primes `p` with `N ≤ p ≤ M`. -/
def pmDeletedPrimeAperture (N M : ℕ) : Finset ℕ :=
  mobiusFinitePrimeAperture M \ Nat.primesBelow N

theorem pmDeletedPrimeAperture_prime (N M : ℕ) : ∀ p ∈ pmDeletedPrimeAperture N M, Nat.Prime p := by
  intro p hp
  exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2

/-- For `n ≤ M`, the Möbius coefficient retained by the aperture `[N, M]` equals `μ_E(n)` with
`E` the primes below `N`. -/
theorem pmDeletedPrimeAperture_coefficient (N : ℕ) {M n : ℕ} (hn : n ≤ M) :
    finitePrimeApertureMobiusCoefficient (pmDeletedPrimeAperture N M) n =
      (CoprimeMobius.mobiusAF (↑(Nat.primesBelow N) : Set ℕ) n : ℂ) := by
  by_cases hn0 : n = 0
  · subst n
    simp [finitePrimeApertureMobiusCoefficient, mobiusComplexCoefficient]
  have hc : n.primeFactors ⊆ pmDeletedPrimeAperture N M ↔
      CoprimeMobius.IsFree (↑(Nat.primesBelow N) : Set ℕ) n := by
    constructor
    · intro h
      exact ⟨hn0, fun p hp => (Finset.mem_sdiff.mp (h hp)).2⟩
    · rintro ⟨_, h⟩ p hp
      obtain ⟨hpPrime, hpDvd, _⟩ := Nat.mem_primeFactors.mp hp
      have hpn := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpDvd
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, h p hp⟩
      change p ∈ (Finset.range (M + 1)).filter Nat.Prime
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpPrime⟩
  by_cases he : CoprimeMobius.IsFree (↑(Nat.primesBelow N) : Set ℕ) n
  · simp [finitePrimeApertureMobiusCoefficient, hc.mpr he, mobiusComplexCoefficient,
      CoprimeMobius.mobiusAF, ArithmeticFunction.pmul_apply, CoprimeMobius.freeAF_apply, he]
  · have hnot := mt hc.mp he
    simp [finitePrimeApertureMobiusCoefficient, hnot, CoprimeMobius.mobiusAF,
      ArithmeticFunction.pmul_apply, CoprimeMobius.freeAF_apply, he]

theorem pmDeletedMobiusFermiSource_eq_sum (E : Set ℕ) {t : ℝ} (ht : 0 < t) {K : ℕ}
    (hK : ⌊1 / t⌋₊ ≤ K) :
    pmDeletedMobiusFermiSource E t =
      -(∑ d ∈ Finset.Icc 1 K, (CoprimeMobius.mobiusAF E d : ℂ) * fermiNymanGen (d : ℝ) t) := by
  unfold pmDeletedMobiusFermiSource
  congr 1
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hK)
  intro d hd hnot
  have hfloor : ⌊1 / t⌋₊ < d := by
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hh := mt Finset.mem_Icc.mpr hnot
    omega
  rw [pm_fermiNymanGen_eq_zero_of_floor_lt ht hfloor, mul_zero]

/-- For `t > 0` and `⌊1/t⌋ ≤ M`, the undamped finite-prime source on the aperture `[N, M]`
equals the smooth Haar source `pmSmoothHaarSource N t`. -/
theorem pmFinitePrimePowerDampedFermiSource_deleted_eq_of_covers (N : ℕ) {M : ℕ} {t : ℝ}
    (ht : 0 < t) (hM : ⌊1 / t⌋₊ ≤ M) :
    pmFinitePrimePowerDampedFermiSource (pmDeletedPrimeAperture N M) 0 t = pmSmoothHaarSource N t := by
  let S := pmDeletedPrimeAperture N M
  let K := max (∏ p ∈ S, p) ⌊1 / t⌋₊
  have hext : pmFinitePrimePowerDampedFermiSource S 0 t =
      -(∑ d ∈ Finset.Icc 1 K, finitePrimeApertureMobiusCoefficient S d * fermiNymanGen (d : ℝ) t) := by
    unfold pmFinitePrimePowerDampedFermiSource
    simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
    congr 1
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_left _ _))
    intro d hd hnot
    have hgt : (∏ p ∈ S, p) < d := by
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hh := mt Finset.mem_Icc.mpr hnot
      omega
    rw [pm_finitePrime_coefficient_eq_zero_above_product (pmDeletedPrimeAperture_prime N M) hgt, zero_mul]
  rw [hext, ← pmDeletedMobiusFermiSource_eq_smoothHaar N ht,
    pmDeletedMobiusFermiSource_eq_sum _ ht (show ⌊1 / t⌋₊ ≤ K from le_max_right _ _)]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hsmall : d ≤ ⌊1 / t⌋₊
  · rw [pmDeletedPrimeAperture_coefficient N (hsmall.trans hM)]
  · rw [pm_fermiNymanGen_eq_zero_of_floor_lt ht (lt_of_not_ge hsmall), mul_zero, mul_zero]

/-- At each `t > 0`, the undamped aperture-`[N, M]` sources converge to the smooth Haar source
as `M → ∞` (they are eventually constant). -/
theorem tendsto_pmFinitePrimePowerDampedFermiSource_deleted (N : ℕ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun M : ℕ => pmFinitePrimePowerDampedFermiSource (pmDeletedPrimeAperture N M) 0 t)
      atTop (𝓝 (pmSmoothHaarSource N t)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ⌊1 / t⌋₊] with M hM
  exact (pmFinitePrimePowerDampedFermiSource_deleted_eq_of_covers N ht hM).symm

/-- If every undamped aperture-`[N, M]` source has `L²` norm at most `C`, then so does the
smooth Haar source `pmSmoothHaarSource N` (Fatou for `L²` norms). -/
theorem pmDeletedPrimeFermiSource_norm_budget_transfer (N : ℕ) {C : ENNReal}
    (hC : ∀ M : ℕ, eLpNorm (pmFinitePrimePowerDampedFermiSource (pmDeletedPrimeAperture N M) 0) 2
      (volume.restrict (Ioi (0 : ℝ))) ≤ C) :
    eLpNorm (pmSmoothHaarSource N) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
    (Eventually.of_forall hC)
    (fun M => (memLp_pmFinitePrimePowerDampedFermiSource (pmDeletedPrimeAperture N M) 0).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact tendsto_pmFinitePrimePowerDampedFermiSource_deleted N ht

theorem integrable_pmDeletedMobiusFermiSource (N : ℕ) :
    Integrable (pmDeletedMobiusFermiSource (↑(Nat.primesBelow N) : Set ℕ)) (volume.restrict (Ioi (0 : ℝ))) := by
  apply (integrable_congr (show pmDeletedMobiusFermiSource (↑(Nat.primesBelow N) : Set ℕ) =ᵐ[volume.restrict (Ioi 0)]
    pmSmoothHaarSource N from ?_)).mpr (integrable_pmSmoothHaarSource N)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact pmDeletedMobiusFermiSource_eq_smoothHaar N ht

/-- The source with the primes below `N` deleted has integral zero over `(0,∞)`. -/
theorem pmDeletedMobiusFermiSource_integral (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), pmDeletedMobiusFermiSource (↑(Nat.primesBelow N) : Set ℕ) t) = 0 := by
  rw [← pmSmoothHaarSource_integral N]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => pmDeletedMobiusFermiSource_eq_smoothHaar N ht)

/-- The energy of the source with the primes below `N` deleted is the Gram double series
`∑'_{m,n N-smooth} max 0 (2/max m n − 1/min m n)`. -/
theorem pmDeletedMobiusFermiSource_energy_eq_tsum_gram (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖pmDeletedMobiusFermiSource (↑(Nat.primesBelow N) : Set ℕ) t‖ ^ (2 : ℕ)) =
      ∑' m : N.smoothNumbers, ∑' n : N.smoothNumbers,
        max 0 (2 / max (m : ℝ) (n : ℝ) - 1 / min (m : ℝ) (n : ℝ)) := by
  rw [← pmSmoothHaarSource_energy_eq_tsum_gram N]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [pmDeletedMobiusFermiSource_eq_smoothHaar N ht]

/-- No finite `C` bounds the `L²(0,∞)` norms of all smooth Haar sources `pmSmoothHaarSource N`. -/
theorem pmSmoothHaarSource_no_uniform_norm_budget {C : ENNReal} (hC : C ≠ ⊤) :
    ¬ ∀ N : ℕ, eLpNorm (pmSmoothHaarSource N) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C := by
  intro hbound
  have he (N : ℕ) : (∫ t in Ioi (0 : ℝ), ‖pmSmoothHaarSource N t‖ ^ (2 : ℕ)) ≤ C.toReal ^ (2 : ℕ) := by
    rw [pm_integral_norm_sq_toLp (memLp_pmSmoothHaarSource N), Lp.norm_toLp]
    have h := ENNReal.toReal_mono hC (hbound N)
    have hc := ENNReal.toReal_nonneg (a := C)
    have hn := ENNReal.toReal_nonneg (a := eLpNorm (pmSmoothHaarSource N) 2 (volume.restrict (Ioi (0 : ℝ))))
    nlinarith
  obtain ⟨N, hN⟩ := (tendsto_pmSmoothHaarSource_energy.eventually
    (eventually_gt_atTop (C.toReal ^ (2 : ℕ)))).exists
  exact (not_lt_of_ge (he (N + 1))) hN

/-- Given `δ > 0`, if `C` bounds the `L²` norm of every finite-prime power-damped source for all
`ε ∈ (0,δ)` and all finite prime sets, then `C = ⊤`. -/
theorem pmFinitePrimePowerDampedFermiSource_all_subset_budget_eq_top {C : ENNReal}
    {δ : ℝ} (hδ : 0 < δ)
    (hC : ∀ ε : ℝ, 0 < ε → ε < δ → ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
      eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C) : C = ⊤ := by
  by_contra htop
  apply pmSmoothHaarSource_no_uniform_norm_budget htop
  intro N
  apply pmDeletedPrimeFermiSource_norm_budget_transfer N
  intro M
  apply pmFinitePrimePowerDampedFermiSource_zero_norm_le
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε hεδ
  exact hC ε hε hεδ (pmDeletedPrimeAperture N M) (pmDeletedPrimeAperture_prime N M)

/-- For finite `C` and `δ > 0`, some `ε ∈ (0,δ)` and finite prime set `S` give a finite-prime
power-damped source with `L²` norm exceeding `C`. -/
theorem pmFinitePrimePowerDampedFermiSource_exceeds_finite_ennreal_budget {C : ENNReal}
    (hC : C ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      C < eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  by_contra hn
  apply hC
  apply pmFinitePrimePowerDampedFermiSource_all_subset_budget_eq_top hδ
  intro ε hε hεδ S hS
  exact le_of_not_gt (fun hg => hn ⟨ε, hε, hεδ, S, hS, hg⟩)

/-- For every real `C` and `δ > 0` there are `ε ∈ (0,δ)` and a finite prime set `S` whose
power-damped source lies in `L²(0,∞)` with norm exceeding `C`. -/
theorem pmFinitePrimePowerDampedFermiSource_exceeds_every_finite_budget (C : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      MemLp (pmFinitePrimePowerDampedFermiSource S ε) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      ENNReal.ofReal C < eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  obtain ⟨ε, hε, hεδ, S, hS, hg⟩ :=
    pmFinitePrimePowerDampedFermiSource_exceeds_finite_ennreal_budget (C := ENNReal.ofReal C)
      ENNReal.ofReal_ne_top hδ
  exact ⟨ε, hε, hεδ, S, hS, memLp_pmFinitePrimePowerDampedFermiSource S ε, hg⟩

end RHTower
