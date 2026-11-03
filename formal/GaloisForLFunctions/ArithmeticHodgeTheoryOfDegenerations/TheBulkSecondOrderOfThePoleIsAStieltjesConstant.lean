import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFullPrimeMatrixHasRamanujanSpectralPoints
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanPlacePaysTheArithmeticPoint
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheConductorTwoIsTheFirstExcitation
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates

/-!
# The bulk second order of the pole is a Stieltjes constant

The prime matrix `P(n, j) = Λ(j/n)/√(j/n)` (`n ∣ j`, symmetric) acts on the pole packet
`R(n) = n^{−1/2}`, `n ≤ N`, as a quasimode with adjunction energy `γ`: `P R ≈ (log N − γ) R`
(RAPT). Its second-order term is exact and arithmetic, with no prime left in it:

* **The prime pairing is a logarithmic harmonic sum** (`inner_fullPrimeMatrix_pole`):
  `⟨P R, R⟩ = 2 Σ_{j ≤ N} log j/j`, because `Σ_{d ∣ j} Λ(d) = log j`.
* **The first Stieltjes constant** (`tendsto_logHarmonic_sub`): `Σ_{j ≤ N} log j/j − log²N/2 → γ₁`.
* **The bulk second order of the pole** (`tendsto_poleResidualPairing`):
  `⟨P R, R⟩ − (log N − γ)⟨R, R⟩ → 2γ₁ + γ²`; normalized, the pole entry is
  `⟨P r, r⟩ = (log N − γ)⟨r, r⟩ + (2γ₁ + γ²)/log N + o(1/log N)` (`tendsto_log_mul_poleResidual`).

Since `ζ(s) = 1/(s−1) + γ − γ₁(s−1) + …`, the constant `2γ₁ + γ²` is the coefficient of `s − 1` in
`−ζ'(s)/ζ(s) = 1/(s−1) − γ + (2γ₁ + γ²)(s−1) + …`: the first Laurent coefficients of the
logarithmic derivative give the quasimode energy and the second order of the pole packet.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticFunction (vonMangoldt)
open RenormalizedArithmeticPotentialTheory ArithmeticEffectivityTheory

/-! ### The first Stieltjes constant -/

/-- The logarithmic harmonic sum `Σ_{1 ≤ j ≤ N} log j/j`. -/
def logHarmonic (N : ℕ) : ℝ := ∑ j ∈ Icc 1 N, Real.log j / j

/-- `∫_a^b log t/t dt = (log²b − log²a)/2`. -/
theorem integral_log_div_self {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, Real.log t / t = (Real.log b ^ 2 - Real.log a ^ 2) / 2 := by
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => Real.log t ^ 2 / 2) (Real.log t / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    refine (((Real.hasDerivAt_log ht0).pow 2).div_const 2).congr_deriv ?_
    norm_num
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · ring
  · refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((Real.continuousAt_log ht0).div continuousAt_id ht0).continuousWithinAt

/-- On a unit step beyond `e`: `log(k+1)/(k+1) ≤ ∫_k^{k+1} log t/t ≤ log k/k`. -/
theorem log_div_le_integral_le {k : ℝ} (hk : 3 ≤ k) :
    Real.log (k + 1) / (k + 1) ≤ ∫ t in k..(k + 1), Real.log t / t ∧
      ∫ t in k..(k + 1), Real.log t / t ≤ Real.log k / k := by
  have he : Real.exp 1 ≤ k := by
    have := Real.exp_one_lt_d9; linarith
  have hk0 : 0 < k := by linarith
  have hint : IntervalIntegrable (fun t => Real.log t / t) MeasureTheory.volume k (k + 1) := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((Real.continuousAt_log ht0).div continuousAt_id ht0).continuousWithinAt
  have hanti : ∀ t ∈ Set.Icc k (k + 1), Real.log (k + 1) / (k + 1) ≤ Real.log t / t ∧
      Real.log t / t ≤ Real.log k / k := fun t ht =>
    ⟨Real.log_div_self_antitoneOn (Set.mem_Ici.mpr (he.trans ht.1))
        (Set.mem_Ici.mpr (by linarith [ht.1])) ht.2,
      Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (he.trans ht.1)) ht.1⟩
  constructor
  · have := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hint
      fun t ht => (hanti t ht).1
    simpa using this
  · have := intervalIntegral.integral_mono_on (by linarith) hint intervalIntegrable_const
      fun t ht => (hanti t ht).2
    simpa using this

theorem logHarmonic_succ (N : ℕ) :
    logHarmonic (N + 1) = logHarmonic N + Real.log (N + 1 : ℕ) / (N + 1 : ℕ) := by
  unfold logHarmonic
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- The unit step of `log²/2` between two consecutive values beyond `e`. -/
theorem log_div_le_half_sq_sub {k : ℝ} (hk : 3 ≤ k) :
    Real.log (k + 1) / (k + 1) ≤ (Real.log (k + 1) ^ 2 - Real.log k ^ 2) / 2 ∧
      (Real.log (k + 1) ^ 2 - Real.log k ^ 2) / 2 ≤ Real.log k / k := by
  rw [← integral_log_div_self (by linarith) (by linarith)]
  exact log_div_le_integral_le hk

/-- **The first Stieltjes constant exists**: `Σ_{j ≤ N} log j/j − log²N/2` converges. -/
theorem exists_tendsto_logHarmonic_sub :
    ∃ L : ℝ, Tendsto (fun N : ℕ => logHarmonic N - Real.log N ^ 2 / 2) atTop (𝓝 L) := by
  set a : ℕ → ℝ := fun N => logHarmonic (N + 3) - Real.log ((N + 3 : ℕ) : ℝ) ^ 2 / 2 with ha
  set b : ℕ → ℝ := fun N => logHarmonic (N + 3) - Real.log (((N + 3 : ℕ) : ℝ) + 1) ^ 2 / 2
    with hb
  have hk3 : ∀ N : ℕ, (3 : ℝ) ≤ ((N + 3 : ℕ) : ℝ) := fun N => by push_cast; linarith
  have hcast : ∀ N : ℕ, ((N + 1 + 3 : ℕ) : ℝ) = ((N + 3 : ℕ) : ℝ) + 1 := fun N => by
    push_cast; ring
  have hcast' : ∀ N : ℕ, ((N + 3 + 1 : ℕ) : ℝ) = ((N + 3 : ℕ) : ℝ) + 1 := fun N => by
    push_cast; ring
  have hanti : Antitone a := antitone_nat_of_succ_le fun N => by
    simp only [ha]
    rw [show N + 1 + 3 = N + 3 + 1 by ring, logHarmonic_succ (N + 3), hcast']
    have h := (log_div_le_half_sq_sub (hk3 N)).1
    linarith
  have hmono : Monotone b := monotone_nat_of_le_succ fun N => by
    simp only [hb]
    rw [show N + 1 + 3 = N + 3 + 1 by ring, logHarmonic_succ (N + 3), hcast']
    have h := (log_div_le_half_sq_sub (k := ((N + 3 : ℕ) : ℝ) + 1) (by linarith [hk3 N])).2
    linarith
  have hab : ∀ N, b N ≤ a N := fun N => by
    simp only [ha, hb]
    have h1 : 0 ≤ Real.log ((N + 3 : ℕ) : ℝ) := Real.log_nonneg (by linarith [hk3 N])
    have h2 := Real.log_le_log (by linarith [hk3 N] : (0 : ℝ) < ((N + 3 : ℕ) : ℝ))
      (by linarith : ((N + 3 : ℕ) : ℝ) ≤ ((N + 3 : ℕ) : ℝ) + 1)
    nlinarith
  have hbdd : BddBelow (Set.range a) := ⟨b 0, by
    rintro _ ⟨N, rfl⟩; exact (hmono (Nat.zero_le N)).trans (hab N)⟩
  refine ⟨⨅ N, a N, ?_⟩
  have h := tendsto_atTop_ciInf hanti hbdd
  rw [← tendsto_add_atTop_iff_nat 3]
  exact h

/-- The first Stieltjes constant `γ₁ = lim (Σ_{j ≤ N} log j/j − log²N/2)`. -/
def stieltjesOne : ℝ := Classical.choose exists_tendsto_logHarmonic_sub

theorem tendsto_logHarmonic_sub :
    Tendsto (fun N : ℕ => logHarmonic N - Real.log N ^ 2 / 2) atTop (𝓝 stieltjesOne) :=
  Classical.choose_spec exists_tendsto_logHarmonic_sub

/-! ### The prime pairing of the pole packet -/

/-- `Σ_{n ∣ j, n ≠ j} Λ(j/n) = log j`. -/
theorem sum_divisors_ne_vonMangoldt {j : ℕ} (hj : 0 < j) :
    ∑ n ∈ j.divisors with n ≠ j, vonMangoldt (j / n) = Real.log j := by
  rw [← ArithmeticFunction.vonMangoldt_sum, ← Nat.sum_div_divisors j (fun d => vonMangoldt d)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  split_ifs with h
  · rfl
  · push Not at h; rw [h, Nat.div_self hj, ArithmeticFunction.vonMangoldt_apply_one]

/-- The upper half `U(n, j) = [n ∣ j, n ≠ j] Λ(j/n)/√(j/n)` of the prime kernel. -/
def primeKernelUp (n j : ℕ) : ℝ :=
  if n ∣ j ∧ n ≠ j then vonMangoldt (j / n) / Real.sqrt ((j / n : ℕ) : ℝ) else 0

theorem weilPrimeKernel_eq_up_add (n j : ℕ) :
    weilPrimeKernel n j = primeKernelUp n j + primeKernelUp j n := by
  unfold weilPrimeKernel primeKernelUp
  by_cases h1 : n ∣ j ∧ n ≠ j
  · have h2 : ¬(j ∣ n ∧ j ≠ n) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
    rw [if_pos h1, if_pos h1, if_neg h2, add_zero]
  · rw [if_neg h1, if_neg h1, zero_add]

/-- One half of the pairing: `Σ_{n, j ≤ N} U(n, j)/√(nj) = Σ_{j ≤ N} log j/j`. -/
theorem sum_primeKernelUp_pole (N : ℕ) :
    ∑ j ∈ Icc 1 N, ∑ n ∈ Icc 1 N, primeKernelUp n j * ((Real.sqrt j)⁻¹ * (Real.sqrt n)⁻¹) =
      logHarmonic N := by
  unfold logHarmonic
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjN : j ≤ N := (Finset.mem_Icc.mp hj).2
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  -- restrict to the proper divisors of `j`
  have hsub : ∑ n ∈ Icc 1 N, primeKernelUp n j * ((Real.sqrt j)⁻¹ * (Real.sqrt n)⁻¹) =
      ∑ n ∈ j.divisors with n ≠ j, vonMangoldt (j / n) / j := by
    rw [Finset.sum_filter]
    have hsupp : ∀ n ∈ Icc 1 N, n ∉ j.divisors →
        primeKernelUp n j * ((Real.sqrt j)⁻¹ * (Real.sqrt n)⁻¹) = 0 := fun n _ hn => by
      unfold primeKernelUp
      rw [if_neg fun h => hn (Nat.mem_divisors.mpr ⟨h.1, by omega⟩), zero_mul]
    rw [← Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hn,
      (Nat.divisor_le hn).trans hjN⟩) hsupp]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnj : n ∣ j := Nat.dvd_of_mem_divisors hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_mem_divisors hn
    unfold primeKernelUp
    by_cases hne : n ≠ j
    · rw [if_pos ⟨hnj, hne⟩, if_pos hne]
      have hq : ((j / n : ℕ) : ℝ) = (j : ℝ) / n := by
        rw [Nat.cast_div hnj hn0.ne']
      rw [hq, Real.sqrt_div' _ hn0.le]
      have hs1 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hs2 : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
      field_simp
      rw [Real.sq_sqrt hj0.le]
    · push Not at hne
      rw [if_neg (fun h => h.2 hne), if_neg (not_not.mpr hne), zero_mul]
  rw [hsub, ← Finset.sum_div, sum_divisors_ne_vonMangoldt hj1]

/-- **The prime pairing of the pole packet**: `⟨P R, R⟩ = 2 Σ_{j ≤ N} log j/j`. -/
theorem inner_fullPrimeMatrix_pole (N : ℕ) :
    ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector 1 N),
      ramanujanHorizonVector 1 N⟫ = 2 * logHarmonic N := by
  have hR : ∀ n : ℕ, ramanujanPoleProfile 1 n = (Real.sqrt n)⁻¹ := fun n => by
    simp [ramanujanPoleProfile, normalizedRamanujanMode, ramanujanMode_one]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile 1 n *
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector 1 N)) n = _
  simp only [fullPrimeMatrix_apply_ramanujanHorizonVector]
  rw [Finset.sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile 1 n *
    ∑ j ∈ Icc 1 N, weilPrimeKernel n j * ramanujanPoleProfile 1 j)]
  simp only [hR, weilPrimeKernel_eq_up_add, add_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  have h1 := sum_primeKernelUp_pole N
  have h2 : ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      (Real.sqrt n)⁻¹ * (primeKernelUp n j * (Real.sqrt j)⁻¹) = logHarmonic N := by
    rw [Finset.sum_comm, ← h1]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => by ring
  have h3 : ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      (Real.sqrt n)⁻¹ * (primeKernelUp j n * (Real.sqrt j)⁻¹) = logHarmonic N := by
    rw [← h1]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h2, h3]
  ring

/-- `⟨R, R⟩ = Σ_{n ≤ N} 1/n`. -/
theorem norm_sq_ramanujanHorizonVector_one (N : ℕ) :
    ‖ramanujanHorizonVector 1 N‖ ^ 2 = ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ := by
  rw [ramanujanHorizonVector_norm_sq]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp [ramanujanPoleProfile, normalizedRamanujanMode, ramanujanMode_one, inv_pow,
    Real.sq_sqrt hn0]

/-! ### The second order -/

/-- `0 < Σ_{n ≤ N} 1/n − log N − γ ≤ 1/N`. -/
theorem harmonic_sub_log_sub_gamma_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 < (∑ n ∈ Icc 1 N, (n : ℝ)⁻¹) - Real.log N - Real.eulerMascheroniConstant ∧
      (∑ n ∈ Icc 1 N, (n : ℝ)⁻¹) - Real.log N - Real.eulerMascheroniConstant ≤ 1 / N := by
  have hH : (∑ n ∈ Icc 1 N, (n : ℝ)⁻¹) = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have hlo := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  have hhi := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  have hN0 : N ≠ 0 := by omega
  simp only [Real.eulerMascheroniSeq', Real.eulerMascheroniSeq, hN0, if_false] at hlo hhi
  have hNR : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN0)
  have hlog : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / N := by
    rw [← Real.log_div (by positivity) hNR.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < ((N : ℝ) + 1) / N by positivity)
    rw [show ((N : ℝ) + 1) / N - 1 = 1 / N by field_simp; ring] at this
    exact this
  rw [hH]
  constructor <;> linarith

/-- **The bulk second order of the pole**: `⟨P R, R⟩ − (log N − γ)⟨R, R⟩ → 2γ₁ + γ²`, with the
quasimode energy `R₁ = γ` of the pole conductor. -/
theorem tendsto_poleResidualPairing :
    Tendsto (fun N : ℕ => ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector 1 N),
        ramanujanHorizonVector 1 N⟫ -
      (Real.log N - ramanujanAdjunctionEnergy 1) * ‖ramanujanHorizonVector 1 N‖ ^ 2) atTop
      (𝓝 (2 * stieltjesOne + Real.eulerMascheroniConstant ^ 2)) := by
  set γ := Real.eulerMascheroniConstant with hγ
  set δ : ℕ → ℝ := fun N => (∑ n ∈ Icc 1 N, (n : ℝ)⁻¹) - Real.log N - γ with hδ
  -- `(log N − γ) δ_N → 0`, since `0 < δ_N ≤ 1/N`
  have hδlim : Tendsto (fun N : ℕ => (Real.log N - γ) * δ N) atTop (𝓝 0) := by
    have hlog : Tendsto (fun N : ℕ => (Real.log N - γ) / N) atTop (𝓝 0) := by
      have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
      have h2 := tendsto_const_div_atTop_nhds_zero_nat γ
      have := h1.sub h2
      simp only [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      simp only [Function.comp_apply, pow_one, one_mul, add_zero]
      ring
    refine squeeze_zero_norm' ?_ hlog
    filter_upwards [eventually_ge_atTop 3] with N hN
    obtain ⟨h0, h1⟩ := harmonic_sub_log_sub_gamma_bounds (by omega : 1 ≤ N)
    have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hlogpos : γ ≤ Real.log N := by
      have := Real.eulerMascheroniConstant_lt_two_thirds
      have h3 : (1 : ℝ) ≤ Real.log N := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        have := Real.exp_one_lt_d9; linarith
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.log N - γ),
      abs_of_pos h0]
    calc (Real.log N - γ) * δ N ≤ (Real.log N - γ) * (1 / N) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = (Real.log N - γ) / N := by ring
  have hmain := ((tendsto_logHarmonic_sub.const_mul 2).sub hδlim).add_const (γ ^ 2)
  rw [sub_zero] at hmain
  refine hmain.congr fun N => ?_
  rw [inner_fullPrimeMatrix_pole, norm_sq_ramanujanHorizonVector_one,
    SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_one]
  simp only [hδ]
  ring

/-- **Normalized**: with `r = R/√log N`,
`log N · (⟨P r, r⟩ − (log N − γ)⟨r, r⟩) → 2γ₁ + γ²`. -/
theorem tendsto_log_mul_poleResidual :
    Tendsto (fun N : ℕ => Real.log N *
      (⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector 1 N),
          normalizedRamanujanHorizonVector 1 N⟫ -
        (Real.log N - ramanujanAdjunctionEnergy 1) * ‖normalizedRamanujanHorizonVector 1 N‖ ^ 2))
      atTop (𝓝 (2 * stieltjesOne + Real.eulerMascheroniConstant ^ 2)) := by
  refine tendsto_poleResidualPairing.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ Real.sqrt (Real.log N) = r :=
    ⟨_, Real.sqrt_pos.mpr hlog, rfl⟩
  have hlr : Real.log N = r ^ 2 := by rw [← hr, Real.sq_sqrt hlog.le]
  unfold normalizedRamanujanHorizonVector
  rw [map_smul, inner_smul_left, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_inv, hr, abs_of_pos hr0, hlr]
  simp only [conj_trivial]
  field_simp

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
