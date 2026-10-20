import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrimeBoundaryDissipationAndCofinalDefectSign
import GaloisForLFunctions.BezoutValuationIncidence.PhaseUniformWindowPoincareAndLongWindowDissipation
import GaloisForLFunctions.BezoutValuationIncidence.PrimeTailCalibrationAndMobiusDefect

/-!
# The global sign of the renormalized defect at large horizons

Two regimes control the renormalized prefix defect `D̃_N(M; c)` above the horizon.

* **Polynomial windows.** First-octave Möbius edges (literal Möbius weight) or sub-horizon prime
  boundaries (damping `ε > 0`) give jump energy of size `N` or `N / log N`, which pays every
  endpoint divisor square on `M ≤ N^A`, eventually in `N`.
* **Long windows.** The phase-uniform window Poincaré law gives
  `2 D̃_N(M) ≤ 4 H² - (M - 11 S_N) V` with harmonic sum `H`, window observability constant
  `S_N`, and non-harmonic variance `V`.

Here `S_N ≤ N⁵`, `|H| ≤ N` for weights bounded by one, and a Bertrand prime `p ∈ (N/2, N]`
has the single-multiple Selberg coordinate `c(p)/p`, so `V ≥ (p - 1) c(p)² / p²`. For the literal
Möbius weight this is at least `1/(2N)`; for the damped weight at least `1/(2N^(2⌈ε⌉+1))`.
Hence the long-window regime starts at an explicit polynomial scale at every horizon, where
the polynomial-window regime has not yet ended. No prefix is left uncovered: at every
sufficiently large horizon the renormalized defect is nonpositive at every prefix, for the
literal Möbius weight and for every fixed damping `ε > 0`.

The long-window law is explicit at every horizon `N ≥ 2`: beyond `11 N⁵` the Möbius defect
decreases at least linearly with slope `1/(4N)`. Only the polynomial-window regime is eventual.
-/

open Finset Filter ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty RHTower
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Polynomial size of the long-window constants -/

/-- The window observability constant `S_N = Σ_{q ≤ N} σ(q)² / φ(q)` is at most `N⁵`. -/
theorem sieveWindowObservabilityConstant_le_pow_five (N : ℕ) :
    sieveWindowObservabilityConstant N ≤ (N : ℝ) ^ 5 := by
  unfold sieveWindowObservabilityConstant
  calc
    _ ≤ ∑ _q ∈ Icc 1 N, (N : ℝ) ^ 4 := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hq1, hqN⟩ := mem_Icc.mp hq
      have hσ : ArithmeticFunction.sigma 1 q ≤ q * q := by
        rw [sigma_one_apply]
        calc
          _ ≤ ∑ _d ∈ q.divisors, q := sum_le_sum fun d hd => Nat.divisor_le hd
          _ = q.divisors.card * q := by rw [sum_const, smul_eq_mul]
          _ ≤ q * q := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self q)
      have hσN : ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
        have : ArithmeticFunction.sigma 1 q ≤ N ^ 2 := hσ.trans (by nlinarith)
        exact_mod_cast this
      have hφ : (1 : ℝ) ≤ (q.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
      rw [div_le_iff₀ (by linarith)]
      have h0 : (0 : ℝ) ≤ ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) := Nat.cast_nonneg _
      have hsq : ((ArithmeticFunction.sigma 1 q : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ h0 hσN 2
      nlinarith [pow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) 4]
    _ = (N : ℝ) ^ 5 := by
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast
      ring

/-- A weight bounded by one has harmonic sum at most `N` in absolute value. -/
theorem abs_finiteHarmonicSum_le_of_abs_le_one (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d, |c d| ≤ 1) : |finiteHarmonicSum N c| ≤ N := by
  unfold finiteHarmonicSum
  calc
    _ ≤ ∑ d ∈ Icc 1 N, |c d / (d : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Icc 1 N, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Icc.mp hd).1
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < d), div_le_one (by linarith)]
      linarith [hc d]
    _ = N := by simp

/-- Bertrand's postulate puts a prime in the terminal band `N/2 < p ≤ N`. -/
theorem exists_mem_sievePrimeTail {N : ℕ} (hN : 2 ≤ N) : ∃ p, p ∈ sievePrimeTail N := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) (by omega)
  refine ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le, by omega⟩, hp, by omega⟩⟩

/-- A terminal prime carries its own variance mode `φ(p) (c(p)/p)²`. -/
theorem primeTail_mode_le_sieveVariance {N p : ℕ} (hp : p ∈ sievePrimeTail N) (c : ℕ → ℝ) :
    (p.totient : ℝ) * (c p / (p : ℝ)) ^ 2 ≤ sieveVariance N c := by
  unfold sieveVariance
  rw [← selbergMultiplesCoord_primeTail hp c]
  obtain ⟨hpI, -⟩ := mem_filter.mp hp
  exact single_le_sum (f := fun e => (Nat.totient e : ℝ) * (selbergMultiplesCoord N c e) ^ 2)
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hpI

/-! ### Explicit long-window dissipation at every horizon -/

/-- **Long-window law.** For a weight bounded by one and a terminal prime `p`, every prefix
`M ≥ 11 N⁵` satisfies `2 D̃_N(M) ≤ 4 N² - (M - 11 N⁵) φ(p) (c(p)/p)²`. -/
theorem two_mul_sieveRenormalizedPrefixDefect_le_terminal_mode {N M p : ℕ} (hN : 1 ≤ N)
    {c : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1) (hp : p ∈ sievePrimeTail N)
    (hM : 11 * (N : ℝ) ^ 5 ≤ M) :
    2 * sieveRenormalizedPrefixDefect N M c ≤
      4 * (N : ℝ) ^ 2 - ((M : ℝ) - 11 * (N : ℝ) ^ 5) *
        ((p.totient : ℝ) * (c p / (p : ℝ)) ^ 2) := by
  have hw := two_mul_shortWindowRenormalizedDefect_le hN 0 M c
  have hdef : shortWindowRenormalizedDefect N 0 M c = sieveRenormalizedPrefixDefect N M c := by
    unfold shortWindowRenormalizedDefect
    simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  rw [hdef] at hw
  have hS := sieveWindowObservabilityConstant_le_pow_five N
  have hH : finiteHarmonicSum N c ^ 2 ≤ (N : ℝ) ^ 2 := by
    have h := abs_finiteHarmonicSum_le_of_abs_le_one N hc
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have hV := primeTail_mode_le_sieveVariance hp c
  have hm0 : 0 ≤ (p.totient : ℝ) * (c p / (p : ℝ)) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hgap : (M : ℝ) - 11 * (N : ℝ) ^ 5 ≤
      (M : ℝ) - 11 * sieveWindowObservabilityConstant N := by linarith
  have hgap0 : 0 ≤ (M : ℝ) - 11 * (N : ℝ) ^ 5 := by linarith
  have hprod : ((M : ℝ) - 11 * (N : ℝ) ^ 5) * ((p.totient : ℝ) * (c p / (p : ℝ)) ^ 2) ≤
      ((M : ℝ) - 11 * sieveWindowObservabilityConstant N) * sieveVariance N c :=
    mul_le_mul hgap hV hm0 (by linarith)
  linarith

/-- For the literal Möbius weight the terminal mode is at least `1/(2N)`: beyond `11 N⁵` the
defect decreases at least linearly, `2 D̃_N(M; μ) ≤ 4 N² - (M - 11 N⁵)/(2N)`, at every `N ≥ 2`. -/
theorem two_mul_moebius_defect_le_linear_dissipation {N M : ℕ} (hN : 2 ≤ N)
    (hM : 11 * (N : ℝ) ^ 5 ≤ M) :
    2 * sieveRenormalizedPrefixDefect N M moebiusReal ≤
      4 * (N : ℝ) ^ 2 - ((M : ℝ) - 11 * (N : ℝ) ^ 5) / (2 * N) := by
  obtain ⟨p, hp⟩ := exists_mem_sievePrimeTail hN
  obtain ⟨hpI, hpp, -⟩ := mem_filter.mp hp
  obtain ⟨hp2, hpN⟩ := mem_Icc.mp hpI
  have hc : ∀ d, |moebiusReal d| ≤ 1 := fun d => by
    unfold moebiusReal; exact_mod_cast abs_moebius_le_one
  have h := two_mul_sieveRenormalizedPrefixDefect_le_terminal_mode (by omega) hc hp hM
  have hμ : moebiusReal p = -1 := by
    unfold moebiusReal; rw [moebius_apply_prime hpp]; norm_num
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpNR : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hmode : 1 / (2 * (N : ℝ)) ≤ (p.totient : ℝ) * (moebiusReal p / (p : ℝ)) ^ 2 := by
    rw [Nat.totient_prime hpp, hμ, Nat.cast_sub (by omega), div_pow, neg_one_sq,
      Nat.cast_one]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hgap0 : 0 ≤ (M : ℝ) - 11 * (N : ℝ) ^ 5 := by linarith
  have hcomp : ((M : ℝ) - 11 * (N : ℝ) ^ 5) / (2 * N) ≤
      ((M : ℝ) - 11 * (N : ℝ) ^ 5) * ((p.totient : ℝ) * (moebiusReal p / (p : ℝ)) ^ 2) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hmode hgap0
  linarith

/-- Explicit tail at every horizon `N ≥ 2`: the Möbius defect is nonpositive for
`M ≥ 11 N⁵ + 8 N³`. -/
theorem moebius_defect_nonpos_of_long_window {N M : ℕ} (hN : 2 ≤ N)
    (hM : 11 * (N : ℝ) ^ 5 + 8 * (N : ℝ) ^ 3 ≤ M) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := two_mul_moebius_defect_le_linear_dissipation hN
    (by nlinarith [pow_pos hNpos 3] : 11 * (N : ℝ) ^ 5 ≤ M)
  have hq : 4 * (N : ℝ) ^ 2 ≤ ((M : ℝ) - 11 * (N : ℝ) ^ 5) / (2 * N) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- A natural-number gap: at horizons `N ≥ 19`, `N^(k+6)` exceeds `11 N⁵ + 8 N^(k+3)`. -/
private theorem pow_gap {N : ℕ} (k : ℕ) (hN : 19 ≤ N) :
    11 * (N : ℝ) ^ 5 + 8 * (N : ℝ) ^ (k + 3) ≤ (N : ℝ) ^ (k + 6) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN19 : (19 : ℝ) ≤ N := by exact_mod_cast hN
  have h5 : (N : ℝ) ^ 5 ≤ (N : ℝ) ^ (k + 5) := pow_le_pow_right₀ hN1 (by omega)
  have h3 : (N : ℝ) ^ (k + 3) ≤ (N : ℝ) ^ (k + 5) := pow_le_pow_right₀ hN1 (by omega)
  have h6 : (N : ℝ) ^ (k + 6) = N * (N : ℝ) ^ (k + 5) := by ring
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (k + 5) := by positivity
  nlinarith

/-! ### The global sign -/

/-- **Global sign for the literal Möbius weight.** Eventually in the horizon, the renormalized
defect `D̃_N(M; μ)` is nonpositive at every prefix `M`. -/
theorem eventually_moebius_renormalizedDefect_nonpos_all :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  filter_upwards [eventually_moebiusRenormalizedDefect_polynomial_cofinal_bound 4,
    eventually_ge_atTop 19] with N hpoly hN
  intro M
  by_cases h6 : M + 1 < 6 * (N + 1)
  · exact moebius_prefix_defect_nonpos_of_lt_six_succ h6
  by_cases hw : M ≤ N ^ 6
  · have h := hpoly M (mem_Icc.mpr ⟨by omega, by simpa using hw⟩)
    have : -(N : ℝ) / (2 * Real.pi ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg N)) (by positivity)
    linarith
  · apply moebius_defect_nonpos_of_long_window (by omega)
    have hgap := pow_gap 0 hN
    have hM : (N : ℝ) ^ 6 ≤ M := by exact_mod_cast (show N ^ 6 ≤ M by omega)
    simp only [zero_add] at hgap
    linarith

/-- The damped terminal mode: `φ(p) (c_ε(p)/p)² ≥ 1/(2 N^(2k+1))` whenever `ε ≤ k`. -/
theorem pmPowerDamped_primeTail_mode_ge {ε : ℝ} {k : ℕ} (hk : ε ≤ k)
    {N p : ℕ} (hp : p ∈ sievePrimeTail N) :
    1 / (2 * (N : ℝ) ^ (2 * k + 1)) ≤
      (p.totient : ℝ) * (pmPowerDampedRealWeight ε p / (p : ℝ)) ^ 2 := by
  obtain ⟨hpI, hpp, -⟩ := mem_filter.mp hp
  obtain ⟨hp2, hpN⟩ := mem_Icc.mp hpI
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpNR : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hw : pmPowerDampedRealWeight ε p = -(p : ℝ) ^ (-ε) := by
    unfold pmPowerDampedRealWeight moebiusReal
    rw [moebius_apply_prime hpp]; norm_num
  -- `p^(-ε) ≥ p^(-k) = 1/p^k ≥ 1/N^k`
  have hrpow : 1 / (N : ℝ) ^ k ≤ (p : ℝ) ^ (-ε) := by
    have h1 : (p : ℝ) ^ (-(k : ℝ)) ≤ (p : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast] at h1
    have h2 : 1 / (N : ℝ) ^ k ≤ ((p : ℝ) ^ k)⁻¹ := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hpNR k)
    linarith
  have hsq : 1 / (N : ℝ) ^ (2 * k) ≤ ((p : ℝ) ^ (-ε)) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hrpow 2
    rwa [div_pow, one_pow, ← pow_mul, mul_comm k 2] at this
  rw [Nat.totient_prime hpp, hw, Nat.cast_sub (by omega), div_pow, neg_sq, Nat.cast_one]
  have hNpos : (0 : ℝ) < N := by linarith
  have hhalf : 1 / (2 * (p : ℝ)) ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hhalfN : 1 / (2 * (N : ℝ)) ≤ 1 / (2 * (p : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  calc
    1 / (2 * (N : ℝ) ^ (2 * k + 1)) = 1 / (2 * (N : ℝ)) * (1 / (N : ℝ) ^ (2 * k)) := by
      rw [pow_succ]; field_simp
    _ ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 2 * ((p : ℝ) ^ (-ε)) ^ 2 :=
      mul_le_mul (hhalfN.trans hhalf) hsq (by positivity)
        (div_nonneg (by linarith) (by positivity))
    _ = ((p : ℝ) - 1) * (((p : ℝ) ^ (-ε)) ^ 2 / (p : ℝ) ^ 2) := by ring

/-- Explicit damped tail at every horizon `N ≥ 2`: with `ε ≤ k`, the damped defect is
nonpositive for `M ≥ 11 N⁵ + 8 N^(2k+3)`. -/
theorem pmPowerDamped_defect_nonpos_of_long_window {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ}
    (hk : ε ≤ k) {N M : ℕ} (hN : 2 ≤ N)
    (hM : 11 * (N : ℝ) ^ 5 + 8 * (N : ℝ) ^ (2 * k + 3) ≤ M) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  obtain ⟨p, hp⟩ := exists_mem_sievePrimeTail hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM5 : 11 * (N : ℝ) ^ 5 ≤ M := by nlinarith [pow_pos hNpos (2 * k + 3)]
  have h := two_mul_sieveRenormalizedPrefixDefect_le_terminal_mode (by omega)
    (abs_pmPowerDampedRealWeight_le_one hε) hp hM5
  have hmode := pmPowerDamped_primeTail_mode_ge hk hp
  have hgap0 : 0 ≤ (M : ℝ) - 11 * (N : ℝ) ^ 5 := by linarith
  have hlow : 4 * (N : ℝ) ^ 2 ≤ ((M : ℝ) - 11 * (N : ℝ) ^ 5) *
      (1 / (2 * (N : ℝ) ^ (2 * k + 1))) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    have : 4 * (N : ℝ) ^ 2 * (2 * (N : ℝ) ^ (2 * k + 1)) = 8 * (N : ℝ) ^ (2 * k + 3) := by ring
    linarith
  have := mul_le_mul_of_nonneg_left hmode hgap0
  linarith

/-- **Global sign at fixed damping.** For every `ε > 0`, eventually in the horizon, the damped
renormalized defect is nonpositive at every prefix `M`. -/
theorem eventually_pmPowerDamped_renormalizedDefect_nonpos_all {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  set k : ℕ := ⌈ε⌉₊
  have hk : ε ≤ k := Nat.le_ceil ε
  filter_upwards [eventually_pmPowerDamped_renormalizedDefect_polynomial_cofinal_bound hε
    (2 * k + 4), eventually_ge_atTop 19] with N hpoly hN
  intro M
  by_cases hsub : M + 1 < N
  · by_cases hM0 : M = 0
    · subst hM0
      simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
    · exact (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos hε.le
        (by omega) (by omega)).2
  by_cases hw : M ≤ N ^ (2 * k + 6)
  · have h := hpoly M (by omega) (by rwa [show 2 * k + 4 + 2 = 2 * k + 6 by ring])
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have : 0 ≤ ((2 : ℝ) ^ (-ε) / 2) ^ 2 * N / (16 * Real.log N) := by positivity
    linarith
  · apply pmPowerDamped_defect_nonpos_of_long_window hε.le hk (by omega)
    have hgap := pow_gap (2 * k) hN
    have hM : (N : ℝ) ^ (2 * k + 6) ≤ M := by
      exact_mod_cast (show N ^ (2 * k + 6) ≤ M by omega)
    linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
