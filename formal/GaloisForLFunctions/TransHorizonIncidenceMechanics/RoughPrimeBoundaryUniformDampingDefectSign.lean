import GaloisForLFunctions.TransHorizonIncidenceMechanics.GlobalRenormalizedDefectSignAtLargeHorizons
import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabHorizonFiltrationAndSawtoothEvolution
import GaloisForLFunctions.RHTower.WoldBooleanAcceleratedType

/-!
# Rough-prime boundaries and the defect sign uniformly in the damping

A prime `p ∈ (N, 2N)` is `N`-rough, so the damped response there equals `s(1) = 1` exactly, at
every damping. One of its neighbours `p ± 1` is divisible by four and lies in `[N, 2N]`; there
the response is the complete coefficient `τ_ε(p ± 1) ≤ 1 - 2^(-ε)`, because the only omitted
divisor is the argument itself and it is not squarefree. Each such prime therefore carries a
boundary of jump energy at least `4^(-ε)`, and distinct primes carry distinct boundaries.

This single mechanism covers the literal Möbius weight (`ε = 0`, where it is the first-octave
unit edge) and every positive damping (where the sub-horizon dissipation of the damped
coefficient degenerates as `ε → 0`). With the prime number theorem it gives jump energy at
least `N / (8 log N)` uniformly for `0 ≤ ε ≤ 1`. Together with the unit envelope below
`5(N+1)` and the explicit long-window law beyond `19 N⁵`, the renormalized defect is
nonpositive at every prefix and every damping `0 ≤ ε ≤ 1`, for all sufficiently large horizons,
with a threshold independent of the damping.
-/

open Finset Filter
open GaloisForLFunctions.BezoutValuationIncidence RHTower
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The rough-prime boundary -/

/-- A four-divisible argument in `[1, 2N]` has damped response at most `1 - 2^(-ε)`. -/
theorem sieveSeq_pmPowerDampedRealWeight_le_of_four_dvd {ε : ℝ} (hε : 0 ≤ ε) {N k : ℕ}
    (h4 : 4 ∣ k) (hk : 1 ≤ k) (hk2 : k ≤ 2 * N) :
    sieveSeq N (pmPowerDampedRealWeight ε) k ≤ 1 - (2 : ℝ) ^ (-ε) := by
  have h2 : 2 ∣ k := (Nat.dvd_trans (by norm_num) h4)
  have hτ := pmPowerDampedDivisorCoeff_le_of_two_dvd hε h2 (by omega)
  by_cases hkN : k ≤ N
  · rwa [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hk hkN]
  · have hsq : ¬ Squarefree k := by
      intro hs
      obtain ⟨m, rfl⟩ := h4
      have := hs 2 ⟨m, by ring⟩
      exact absurd this (by decide)
    rw [sieveSeq_pmPowerDampedRealWeight_first_octave_eq ε (by omega) hk2,
      pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε k hsq, sub_zero]
    exact hτ

/-- The boundary carried by a prime: the four-divisible neighbour below or the prime itself. -/
def roughPrimeBoundary (p : ℕ) : ℕ := if 4 ∣ p - 1 then p - 1 else p

/-- Each prime `p ∈ (N, 2N]` pays at least `(2^(-ε))²` across its rough-prime boundary. -/
theorem two_rpow_sq_le_roughPrimeBoundary_jump {ε : ℝ} (hε : 0 ≤ ε) {N p : ℕ} (hN : 2 ≤ N)
    (hp : p.Prime) (hNp : N < p) (hp2 : p ≤ 2 * N) :
    N ≤ roughPrimeBoundary p ∧ roughPrimeBoundary p + 1 ≤ 2 * N ∧
      ((2 : ℝ) ^ (-ε)) ^ 2 ≤
        (sieveSeq N (pmPowerDampedRealWeight ε) (roughPrimeBoundary p + 1) -
          sieveSeq N (pmPowerDampedRealWeight ε) (roughPrimeBoundary p)) ^ 2 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hp2N : p < 2 * N := by
    rcases lt_or_eq_of_le hp2 with h | h
    · exact h
    · exfalso; omega
  have hs1 : sieveSeq N (pmPowerDampedRealWeight ε) p = 1 := by
    rw [sieveSeq_prime_of_gt hp hNp,
      sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff le_rfl (by omega),
      pmPowerDampedDivisorCoeff_one]
  have h2pos : 0 < (2 : ℝ) ^ (-ε) := by positivity
  unfold roughPrimeBoundary
  split_ifs with h4
  · refine ⟨by omega, by omega, ?_⟩
    rw [Nat.sub_add_cancel hp.one_lt.le, hs1]
    have hk := sieveSeq_pmPowerDampedRealWeight_le_of_four_dvd hε h4 (by omega)
      (by omega : p - 1 ≤ 2 * N)
    exact pow_le_pow_left₀ h2pos.le (by linarith) 2
  · have h4' : 4 ∣ p + 1 := by omega
    refine ⟨by omega, by omega, ?_⟩
    rw [hs1]
    have hk := sieveSeq_pmPowerDampedRealWeight_le_of_four_dvd hε h4' (by omega)
      (by omega : p + 1 ≤ 2 * N)
    calc ((2 : ℝ) ^ (-ε)) ^ 2 ≤ (1 - sieveSeq N (pmPowerDampedRealWeight ε) (p + 1)) ^ 2 :=
          pow_le_pow_left₀ h2pos.le (by linarith) 2
      _ = _ := by ring

theorem roughPrimeBoundary_injOn {N : ℕ} :
    Set.InjOn roughPrimeBoundary ((Ioc N (2 * N)).filter Nat.Prime : Finset ℕ) := by
  intro p hp q hq hpq
  have hpp := (mem_filter.mp hp).2
  have hqp := (mem_filter.mp hq).2
  have hpo : p % 2 = 1 ∨ p = 2 := by
    rcases hpp.eq_two_or_odd with h | h <;> [exact Or.inr h; exact Or.inl h]
  have hqo : q % 2 = 1 ∨ q = 2 := by
    rcases hqp.eq_two_or_odd with h | h <;> [exact Or.inr h; exact Or.inl h]
  unfold roughPrimeBoundary at hpq
  have hp1 := hpp.one_lt
  have hq1 := hqp.one_lt
  split_ifs at hpq <;> omega

/-- **Rough-prime boundary dissipation.** For `N ≥ 2`, `ε ≥ 0` and `M ≥ 2N - 1`, the prefix jump
energy is at least `(2^(-ε))²` times the number of primes in `(N, 2N]`. -/
theorem roughPrime_count_le_pmPowerDamped_gradient {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ}
    (hN : 2 ≤ N) (hM : 2 * N ≤ M + 1) :
    ((2 : ℝ) ^ (-ε)) ^ 2 * ((Ioc N (2 * N)).filter Nat.Prime).card ≤
      ∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
        sieveSeq N (pmPowerDampedRealWeight ε) k) ^ 2 := by
  set P := (Ioc N (2 * N)).filter Nat.Prime
  set g : ℕ → ℝ := fun k => (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
    sieveSeq N (pmPowerDampedRealWeight ε) k) ^ 2
  have hmem (p : ℕ) (hp : p ∈ P) := by
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hpI
    exact two_rpow_sq_le_roughPrimeBoundary_jump hε hN hpp h1 h2
  have hsub : P.image roughPrimeBoundary ⊆ Icc 1 M := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    obtain ⟨h1, h2, -⟩ := hmem p hp
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  calc ((2 : ℝ) ^ (-ε)) ^ 2 * P.card = ∑ _p ∈ P, ((2 : ℝ) ^ (-ε)) ^ 2 := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ P, g (roughPrimeBoundary p) := sum_le_sum fun p hp => (hmem p hp).2.2
    _ = ∑ j ∈ P.image roughPrimeBoundary, g j := (sum_image roughPrimeBoundary_injOn).symm
    _ ≤ ∑ k ∈ Icc 1 M, g k := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _

/-! ### Counting the primes of the first octave -/

/-- `π(2N) ≤ π(N) + #{primes in (N, 2N]}`. -/
theorem primeCounting_two_mul_le (N : ℕ) :
    Nat.primeCounting (2 * N) ≤
      Nat.primeCounting N + ((Ioc N (2 * N)).filter Nat.Prime).card := by
  classical
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  calc ((range (2 * N + 1)).filter Nat.Prime).card ≤
        ((range (N + 1)).filter Nat.Prime ∪ (Ioc N (2 * N)).filter Nat.Prime).card := by
        apply card_le_card
        intro x hx
        obtain ⟨hxr, hxp⟩ := mem_filter.mp hx
        have hx2 := mem_range.mp hxr
        by_cases hxN : x ≤ N
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr (by omega), hxp⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hxp⟩)
    _ ≤ _ := card_union_le _ _

/-- By the prime number theorem the first octave eventually holds at least `N / (2 log N)`
primes. -/
theorem eventually_card_primes_first_octave_ge :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (2 * Real.log N) ≤ (((Ioc N (2 * N)).filter Nat.Prime).card : ℝ) := by
  have hratio := tendsto_primeCounting_nat_ratio
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hup : ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log N) ≤ 21 / 20 :=
    hratio.eventually (eventually_le_nhds (by norm_num))
  have hlow : ∀ᶠ N : ℕ in atTop,
      19 / 20 ≤ (Nat.primeCounting (2 * N) : ℝ) / (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) :=
    (hratio.comp h2N).eventually (eventually_ge_nhds (by norm_num))
  filter_upwards [hup, hlow, eventually_ge_atTop 22027] with N hu hl hN
  have hN1 : (22027 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : 10 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    have : Real.exp 10 < 22027 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
        _ < 2.7182818286 ^ 10 := by gcongr
        _ < 22027 := by norm_num
    linarith
  have hlogpos : 0 < Real.log N := by linarith
  have hlog2 : Real.log (2 * N) ≤ 11 / 10 * Real.log N := by
    rw [Real.log_mul (by norm_num) hNpos.ne']
    have := Real.log_two_lt_d9
    linarith
  have hlog2pos : 0 < Real.log (2 * N) := Real.log_pos (by linarith)
  push_cast at hl
  have hπN : (Nat.primeCounting N : ℝ) ≤ 21 / 20 * ((N : ℝ) / Real.log N) := by
    rwa [div_le_iff₀ (by positivity)] at hu
  have hπ2N : 19 / 20 * (2 * (N : ℝ) / Real.log (2 * N)) ≤ (Nat.primeCounting (2 * N) : ℝ) := by
    rwa [le_div_iff₀ (by positivity)] at hl
  have hcmp : 2 * (N : ℝ) / (11 / 10 * Real.log N) ≤ 2 * (N : ℝ) / Real.log (2 * N) :=
    div_le_div_of_nonneg_left (by positivity) hlog2pos hlog2
  have hcount := primeCounting_two_mul_le N
  have hcountR : (Nat.primeCounting (2 * N) : ℝ) ≤
      Nat.primeCounting N + (((Ioc N (2 * N)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast hcount
  have heq : 19 / 20 * (2 * (N : ℝ) / (11 / 10 * Real.log N)) - 21 / 20 * ((N : ℝ) / Real.log N) =
      (N : ℝ) / Real.log N * (19 / 11 - 21 / 20) := by
    field_simp; ring
  have hfin : (N : ℝ) / (2 * Real.log N) ≤ (N : ℝ) / Real.log N * (19 / 11 - 21 / 20) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hlogpos]
    nlinarith
  nlinarith

/-! ### The uniform global sign -/

/-- **Uniform polynomial window.** Eventually in the horizon, uniformly in `0 ≤ ε ≤ 1`, the
damped defect is nonpositive at every prefix `2N - 1 ≤ M ≤ N⁶`. -/
theorem eventually_pmPowerDamped_defect_nonpos_polynomial_window_uniform :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ M : ℕ, 2 * N ≤ M + 1 → M ≤ N ^ 6 →
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_divisor_square_subpower_bound 11
  set a : ℝ := 1 / (((11 : ℕ) : ℝ) + 1)
  have ha : 0 < a := by positivity
  set D : ℝ := C * (2 : ℝ) ^ a
  have hD : 0 < D := by positivity
  have hlog : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ (1 / (8 * D)) * ‖x ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num)).bound (by positivity)
  filter_upwards [eventually_card_primes_first_octave_ge,
    tendsto_natCast_atTop_atTop.eventually hlog, eventually_ge_atTop 2] with N hcard hsmall hN
  intro ε hε0 hε1 M hNM hMN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hn1
  have hsq : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hn]; norm_num
  have hsqpos : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogN, abs_of_pos hsqpos] at hsmall
  have hMN' : (M : ℝ) + 1 ≤ 2 * (N : ℝ) ^ 6 := by
    have hc : (M : ℝ) ≤ (N : ℝ) ^ 6 := by exact_mod_cast hMN
    have : (1 : ℝ) ≤ (N : ℝ) ^ 6 := one_le_pow₀ hn1.le
    linarith
  have hpow : ((M : ℝ) + 1) ^ a ≤ (2 : ℝ) ^ a * (N : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (2 * (N : ℝ) ^ 6) ^ a := Real.rpow_le_rpow (by positivity) hMN' ha.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity),
          ← Real.rpow_natCast (N : ℝ) 6, ← Real.rpow_mul hn.le]
        congr 2
        dsimp [a]
        norm_num
  have hend : ((M + 1).divisors.card : ℝ) ^ 2 - 1 ≤ D * (N : ℝ) ^ (1 / 2 : ℝ) := by
    have h := hbound M
    have : C * ((M : ℝ) + 1) ^ a ≤ C * ((2 : ℝ) ^ a * (N : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow hC.le
    have hass : C * ((2 : ℝ) ^ a * (N : ℝ) ^ (1 / 2 : ℝ)) = D * (N : ℝ) ^ (1 / 2 : ℝ) := by
      dsimp [D]; ring
    have h3 := h.trans (this.trans hass.le)
    linarith
  have hE := roughPrime_count_le_pmPowerDamped_gradient hε0 hN hNM
  have hquarter : (1 / 4 : ℝ) ≤ ((2 : ℝ) ^ (-ε)) ^ 2 := by
    have h1 : (2 : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at h1
    nlinarith
  have hdiss : 1 / 4 * ((N : ℝ) / (2 * Real.log N)) ≤
      ∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
        sieveSeq N (pmPowerDampedRealWeight ε) k) ^ 2 :=
    le_trans (mul_le_mul hquarter hcard (by positivity) (by positivity)) hE
  have hdom : D * (N : ℝ) ^ (1 / 2 : ℝ) ≤ 1 / 4 * ((N : ℝ) / (2 * Real.log N)) := by
    rw [show 1 / 4 * ((N : ℝ) / (2 * Real.log N)) = (N : ℝ) / (8 * Real.log N) by
      field_simp; ring, le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hsmall
      (by positivity : (0 : ℝ) ≤ 8 * D * (N : ℝ) ^ (1 / 2 : ℝ))
    have h2 : 8 * D * (N : ℝ) ^ (1 / 2 : ℝ) * (1 / (8 * D) * (N : ℝ) ^ (1 / 2 : ℝ)) =
        (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by
      field_simp
    rw [hsq] at h2
    nlinarith
  have hid := two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary N M
    (pmPowerDampedRealWeight ε)
  have h1 : sieveSeq N (pmPowerDampedRealWeight ε) 1 = 1 := by
    rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff le_rfl (by omega),
      pmPowerDampedDivisorCoeff_one]
  rw [h1, one_pow] at hid
  have hs : sieveSeq N (pmPowerDampedRealWeight ε) (M + 1) ^ 2 ≤
      ((M + 1).divisors.card : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (abs_sieveSeq_pmPowerDampedRealWeight_le_divisor_card hε0 N M) 2
  linarith

/-- **Uniform global sign.** Eventually in the horizon, for every damping `0 ≤ ε ≤ 1` and every
prefix `M`, the renormalized defect of `c_ε(d) = μ(d) d^(-ε)` is nonpositive. The threshold does
not depend on the damping; `ε = 0` is the literal Möbius weight. -/
theorem eventually_pmPowerDamped_renormalizedDefect_nonpos_uniform :
    ∀ᶠ N : ℕ in atTop, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ M : ℕ,
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  filter_upwards [eventually_pmPowerDamped_defect_nonpos_polynomial_window_uniform,
    eventually_ge_atTop 19] with N hwin hN
  intro ε hε0 hε1 M
  by_cases hM0 : M = 0
  · subst hM0
    simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  by_cases hsub : M + 1 ≤ N
  · exact (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos hε0
      (by omega) hsub).2
  by_cases henv : M + 1 < 5 * (N + 1)
  · have hid := two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary N M
      (pmPowerDampedRealWeight ε)
    have h1 : sieveSeq N (pmPowerDampedRealWeight ε) 1 = 1 := by
      rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff le_rfl (by omega),
        pmPowerDampedDivisorCoeff_one]
    rw [h1, one_pow] at hid
    have hb := abs_sieveSeq_pmPowerDampedRealWeight_le_one_of_lt_five_succ hε0
      (by omega : 2 ≤ M + 1) henv
    have hs : sieveSeq N (pmPowerDampedRealWeight ε) (M + 1) ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hg : 0 ≤ ∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
        sieveSeq N (pmPowerDampedRealWeight ε) k) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    linarith
  by_cases hw : M ≤ N ^ 6
  · exact hwin ε hε0 hε1 M (by omega) hw
  · apply pmPowerDamped_defect_nonpos_of_long_window hε0 (k := 1) (by simpa using hε1)
      (by omega)
    have hgap : 11 * (N : ℝ) ^ 5 + 8 * (N : ℝ) ^ (2 * 1 + 3) ≤ (N : ℝ) ^ 6 := by
      have hN19 : (19 : ℝ) ≤ N := by exact_mod_cast hN
      have h5 : (0 : ℝ) ≤ (N : ℝ) ^ 5 := by positivity
      have : (N : ℝ) ^ 6 = N * (N : ℝ) ^ 5 := by ring
      norm_num
      nlinarith
    have hM : (N : ℝ) ^ 6 ≤ M := by exact_mod_cast (show N ^ 6 ≤ M by omega)
    linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
