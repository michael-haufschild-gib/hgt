import Mathlib.Analysis.PSeries
import GaloisForLFunctions.ArithmeticCountingPositivity.TheFinitePrimeSecularSignsDetermineTheGap
import GaloisForLFunctions.ArithmeticCountingPositivity.SmallPrimeFlipsLieBelowTheMaximalGap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAdjunctionEnergySeparatesValuations

/-!
# Reciprocal conductor counts and collapse of joint prime gaps

An arithmetic progression avoids every prime below a fixed cutoff. Its
reciprocal logarithmic mass diverges by Cauchy condensation. Finite packets
of these conductors test the exact arithmetic secular gap criterion.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- Reciprocal logarithmic mass on the progression M(n+2)+1. -/
def progressionReciprocalLog (M n : ℕ) : ℝ :=
  1 / (((M : ℝ) * ((n : ℝ) + 2) + 1) * Real.log ((M : ℝ) * ((n : ℝ) + 2) + 1))

private theorem progression_point_gt_one {M : ℕ} (hM : 0 < M) (n : ℕ) :
    1 < (M : ℝ) * ((n : ℝ) + 2) + 1 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hp := mul_pos hMR (by positivity : (0 : ℝ) < (n : ℝ) + 2)
  linarith only [hp]

private theorem progressionReciprocalLog_pos {M : ℕ} (hM : 0 < M) (n : ℕ) :
    0 < progressionReciprocalLog M n :=
  div_pos zero_lt_one (mul_pos (zero_lt_one.trans (progression_point_gt_one hM n))
    (Real.log_pos (progression_point_gt_one hM n)))

private theorem progressionReciprocalLog_antitone {M : ℕ} (hM : 0 < M) :
    Antitone (progressionReciprocalLog M) := by
  intro m n hmn
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hxy : (M : ℝ) * ((m : ℝ) + 2) + 1 ≤ (M : ℝ) * ((n : ℝ) + 2) + 1 :=
    add_le_add (mul_le_mul_of_nonneg_left (add_le_add hmnR le_rfl) (Nat.cast_nonneg M)) le_rfl
  have hxm := progression_point_gt_one hM m
  have hxn := progression_point_gt_one hM n
  have hl := Real.log_le_log (zero_lt_one.trans hxm) hxy
  exact div_le_div_of_nonneg_left zero_le_one
    (mul_pos (zero_lt_one.trans hxm) (Real.log_pos hxm))
    (mul_le_mul hxy hl (Real.log_pos hxm).le (zero_lt_one.trans hxn).le)

private theorem condensed_progression_lower_bound {M : ℕ} (hM : 0 < M) (k : ℕ) :
    (1 / ((3 * (M : ℝ) + 1) * (3 * (M : ℝ) + 1 + 1))) * (1 / ((k : ℝ) + 1)) ≤
      (2 : ℝ) ^ k * progressionReciprocalLog M (2 ^ k) := by
  let A : ℝ := 3 * (M : ℝ) + 1
  let q : ℝ := 2 ^ k
  let X : ℝ := (M : ℝ) * (q + 2) + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hq : 1 ≤ q := one_le_pow₀ (by norm_num)
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hX : 1 < X := by
    simpa only [X, q, Nat.cast_pow, Nat.cast_ofNat] using
      progression_point_gt_one hM (2 ^ k)
  have hXle : X ≤ A * q := by
    dsimp only [X, A]
    nlinarith only [mul_nonneg (Nat.cast_nonneg M) (sub_nonneg.mpr hq), hq]
  have hlog : Real.log X ≤ Real.log A + (k : ℝ) * Real.log 2 := by
    have h := Real.log_le_log (zero_lt_one.trans hX) hXle
    rw [Real.log_mul hA.ne' hqpos.ne'] at h
    simpa only [q, Real.log_pow] using h
  have hlogA := Real.log_le_sub_one_of_pos hA
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hterm : (k : ℝ) * Real.log 2 ≤ k := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg k)
  have hlogle : Real.log X ≤ (A + 1) * ((k : ℝ) + 1) := by
    nlinarith only [hlog, hlogA, hterm, mul_nonneg hA.le (Nat.cast_nonneg k)]
  have hprod : X * Real.log X ≤ (A * q) * ((A + 1) * ((k : ℝ) + 1)) :=
    mul_le_mul hXle hlogle (Real.log_pos hX).le (mul_pos hA hqpos).le
  have hA1 : A + 1 ≠ 0 := (by positivity : 0 < A + 1).ne'
  have hk : (k : ℝ) + 1 ≠ 0 := (by positivity : (0 : ℝ) < (k : ℝ) + 1).ne'
  change (1 / (A * (A + 1))) * (1 / ((k : ℝ) + 1)) ≤ _
  calc
    _ = q / ((A * q) * ((A + 1) * ((k : ℝ) + 1))) := by
      field_simp [hA.ne', hA1, hqpos.ne', hk]
    _ ≤ q / (X * Real.log X) := div_le_div_of_nonneg_left hqpos.le
      (mul_pos (zero_lt_one.trans hX) (Real.log_pos hX)) hprod
    _ = _ := by
      simp only [progressionReciprocalLog, Nat.cast_pow, Nat.cast_ofNat]
      dsimp only [q, X]
      ring

/-- Reciprocal logarithmic mass diverges on every progression M(n+2)+1 with
positive integral step. Condensation compares it with the harmonic series. -/
theorem not_summable_progressionReciprocalLog {M : ℕ} (hM : 0 < M) :
    ¬ Summable (progressionReciprocalLog M) := by
  intro hsum
  have hcond := (summable_condensed_iff_of_nonneg
    (fun n => (progressionReciprocalLog_pos hM n).le)
    (fun _ _ _ hmn => progressionReciprocalLog_antitone hM hmn)).mpr hsum
  let A : ℝ := 3 * (M : ℝ) + 1
  let c : ℝ := 1 / (A * (A + 1))
  have hA : 0 < A := by dsimp only [A]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hsmall : Summable (fun k : ℕ => c * (1 / ((k : ℝ) + 1))) :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => condensed_progression_lower_bound hM k) hcond
  have hplain : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
    have h := hsmall.mul_left c⁻¹
    have he : (fun k : ℕ => c⁻¹ * (c * (1 / ((k : ℝ) + 1)))) =
        (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
      funext k
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    rwa [he] at h
  have hshift : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hplain
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hshift)

/-- Finite packets of an arithmetic progression have unbounded reciprocal
logarithmic mass. -/
theorem tendsto_sum_progressionReciprocalLog_atTop {M : ℕ} (hM : 0 < M) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, progressionReciprocalLog M n) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact not_summable_progressionReciprocalLog hM
  · exact fun n => (progressionReciprocalLog_pos hM n).le

local notation "γ" => Real.eulerMascheroniConstant

open private conductor_energy_gap conductor_weight_nonneg from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheFullResolvent

/-- The primes strictly above B and at most Q. -/
def primeTailCutoff (B Q : ℕ) : Finset ℕ :=
  (Nat.primesBelow (Q + 1)).filter (fun p => B < p)

private theorem primeTailCutoff_prime (B Q : ℕ) : ∀ p ∈ primeTailCutoff B Q, p.Prime :=
  fun _ hp => (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2

private theorem primeTailCutoff_mono (B : ℕ) : Monotone (primeTailCutoff B) := by
  intro Q R hQR p hp
  obtain ⟨hpQ, hBp⟩ := mem_filter.mp hp
  obtain ⟨hpQ, hprime⟩ := Nat.mem_primesBelow.mp hpQ
  exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩, hBp⟩

private theorem progression_nat_ge_two {M : ℕ} (hM : 0 < M) (n : ℕ) :
    2 ≤ M * (n + 2) + 1 := by
  have h := Nat.mul_le_mul_left M (by omega : 1 ≤ n + 2)
  omega

private theorem progression_nat_index_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (fun n : ℕ => M * (n + 2) + 1 - 2) := by
  apply StrictMono.injective
  intro m n hmn
  have h := Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hmn 2) hM
  have hm := progression_nat_ge_two hM m
  have hn := progression_nat_ge_two hM n
  change M * (m + 2) + 1 - 2 < M * (n + 2) + 1 - 2
  omega

/-- A factorial-step progression has no prime factor below the fixed cutoff. -/
private theorem progression_conductor_supported (B n Q : ℕ)
    (hQ : B.factorial * (n + 2) + 1 ≤ Q) :
    B.factorial * (n + 2) + 1 ∈ Nat.factoredNumbers (primeTailCutoff B Q) := by
  have hm : 0 < B.factorial * (n + 2) + 1 := by omega
  refine ⟨hm.ne', ?_⟩
  intro p hp
  have hp' := Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp
  obtain ⟨hprime, hpm, _⟩ := Nat.mem_primeFactors.mp hp'
  have hpB : B < p := by
    by_contra hnot
    have hpM : p ∣ B.factorial := Nat.dvd_factorial hprime.pos (le_of_not_gt hnot)
    have hmul : p ∣ B.factorial * (n + 2) := dvd_mul_of_dvd_left hpM _
    have hp1 : p ∣ 1 := (Nat.dvd_add_iff_left hmul).mpr
      (by simpa only [Nat.add_comm] using hpm)
    exact hprime.ne_one (Nat.dvd_one.mp hp1)
  have hpQ : p ≤ Q := (Nat.le_of_dvd hm hpm).trans hQ
  exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩, hpB⟩

private theorem supported_reciprocal_lower_bound {F : Finset ℕ} {m : ℕ}
    (hm2 : 2 ≤ m) (hmF : m ∈ Nat.factoredNumbers F) {t : ℝ}
    (ht : 0 < t) (ht2 : t < 2 * Real.log 2) :
    (1 / ((m : ℝ) * Real.log m)) / 2 ≤ finiteFlipSpectralWeight F m /
      (ramanujanAdjunctionEnergy m - γ - t) := by
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hlog := Real.log_pos hm1
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hφm : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hw : (1 : ℝ) / m ≤ finiteFlipSpectralWeight F m := by
    rw [finiteFlipSpectralWeight_eq, if_pos hmF]
    exact (div_le_div_of_nonneg_left zero_le_one hφ hφm).trans
      (div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)) hφ.le)
  have henergy := (ramanujanAdjunctionEnergy_sub_one_ge hm2).1
  rw [ramanujanAdjunctionEnergy_one] at henergy
  have hden : 0 < ramanujanAdjunctionEnergy m - γ - t :=
    sub_pos.mpr (ht2.trans_le henergy)
  have hupper : ramanujanAdjunctionEnergy m - γ - t ≤ 2 * Real.log m := by
    have hd := tameDifferent_le_log hm
    rw [ramanujanAdjunctionEnergy]
    linarith only [hd, ht]
  calc
    _ = ((1 : ℝ) / m) / (2 * Real.log m) := by
      field_simp [hmR.ne', hlog.ne']
    _ ≤ ((1 : ℝ) / m) / (ramanujanAdjunctionEnergy m - γ - t) :=
      div_le_div_of_nonneg_left (div_nonneg zero_le_one hmR.le) hden hupper
    _ ≤ _ := div_le_div_of_nonneg_right hw hden.le

/-- Above every fixed prime cutoff, some finite joint flip has greatest gap
below any prescribed positive value. -/
theorem exists_primeTailCutoff_gap_lt (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, finiteFlipGreatestGap (primeTailCutoff B Q) < ε := by
  classical
  by_contra hnone
  have hall (Q : ℕ) : ε ≤ finiteFlipGreatestGap (primeTailCutoff B Q) :=
    le_of_not_gt (fun h => hnone ⟨Q, h⟩)
  have hg0 : 0 < 2 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  let t : ℝ := min ε (2 * Real.log 2) / 2
  have hmin : 0 < min ε (2 * Real.log 2) := lt_min hε hg0
  have ht : 0 < t := by dsimp only [t]; linarith only [hmin]
  have htε : t < ε := by
    dsimp only [t]
    linarith only [hmin, min_le_left ε (2 * Real.log 2)]
  have ht2 : t < 2 * Real.log 2 := by
    dsimp only [t]
    linarith only [hmin, min_le_right ε (2 * Real.log 2)]
  have hreading (Q : ℕ) :
      (∑' k : ℕ, finiteFlipSpectralWeight (primeTailCutoff B Q) (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - t)) ≤ 1 / t := by
    have h := ((finiteFlip_hasHyperplaneGap_iff_secular (primeTailCutoff B Q)
      (primeTailCutoff_prime B Q) _).mp
        (isGreatest_finiteFlip_hyperplaneGap (primeTailCutoff B Q)
          (primeTailCutoff_prime B Q)).1).2 t ht (htε.trans_le (hall Q))
    dsimp only [finiteFlipSecular] at h
    linarith only [h]
  let M := B.factorial
  have hM : 0 < M := Nat.factorial_pos B
  obtain ⟨N, hN⟩ := ((tendsto_sum_progressionReciprocalLog_atTop hM).eventually_gt_atTop
    (2 / t)).exists
  let Q := M * (N + 2) + 1
  let F := primeTailCutoff B Q
  let idx : ℕ → ℕ := fun n => M * (n + 2) + 1 - 2
  let T : ℕ → ℝ := fun k => finiteFlipSpectralWeight F (k + 2) /
    (ramanujanAdjunctionEnergy (k + 2) - γ - t)
  have hF : ∀ p ∈ F, p.Prime := primeTailCutoff_prime B Q
  have hinj : Function.Injective idx := progression_nat_index_injective hM
  have hterm (n : ℕ) (hn : n ∈ range N) : progressionReciprocalLog M n / 2 ≤ T (idx n) := by
    have hm2 := progression_nat_ge_two hM n
    have hmQ : M * (n + 2) + 1 ≤ Q :=
      Nat.add_le_add_right (Nat.mul_le_mul_left M
        (Nat.add_le_add_right (Nat.le_of_lt (mem_range.mp hn)) 2)) 1
    have hsupport : M * (n + 2) + 1 ∈ Nat.factoredNumbers F :=
      progression_conductor_supported B n Q hmQ
    have hh := supported_reciprocal_lower_bound hm2 hsupport ht ht2
    dsimp only [T, idx]
    rw [Nat.sub_add_cancel hm2]
    simpa only [progressionReciprocalLog, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] using hh
  have hpacket : (∑ n ∈ range N, progressionReciprocalLog M n / 2) ≤ 1 / t := by
    calc
      _ ≤ ∑ n ∈ range N, T (idx n) := sum_le_sum hterm
      _ = ∑ k ∈ (range N).image idx, T k :=
        (sum_image (fun _ _ _ _ he => hinj he)).symm
      _ ≤ ∑' k : ℕ, T k :=
        (summable_finiteFlipSecularTail F hF ht ht2).sum_le_tsum _
          (fun k _ => div_nonneg (conductor_weight_nonneg F _)
            (sub_pos.mpr (ht2.trans_le (conductor_energy_gap k))).le)
      _ ≤ 1 / t := hreading Q
  rw [← sum_div] at hpacket
  have hbound : (∑ n ∈ range N, progressionReciprocalLog M n) ≤ 2 / t := by
    calc
      _ ≤ (1 / t) * 2 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hpacket
      _ = 2 / t := by ring
  exact not_lt_of_ge hbound hN

/-- The attained greatest gaps of joint flips above a fixed prime cutoff tend
to zero, although every finite stage has a strictly positive gap. -/
theorem tendsto_primeTailGreatestGap_zero (B : ℕ) :
    Tendsto (fun Q : ℕ => finiteFlipGreatestGap (primeTailCutoff B Q)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Q₀, hQ₀⟩ := exists_primeTailCutoff_gap_lt B hε
  refine ⟨Q₀, fun Q hQ => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (finiteFlipGreatestGap_pos (primeTailCutoff B Q) (primeTailCutoff_prime B Q)).le]
  exact (finiteFlipGreatestGap_antitone (primeTailCutoff_mono B hQ)
    (primeTailCutoff_prime B Q)).trans_lt hQ₀

/-- Arbitrarily far out among the primes, individually maximal flips can have
an arbitrarily small positive joint greatest gap. -/
theorem exists_maximal_prime_flips_with_small_joint_gap (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ℕ, F.Nonempty ∧
      (∀ p ∈ F, p.Prime ∧ B < p ∧ 11 ≤ p ∧
        IsGreatest {g : ℝ | HasHyperplaneGap (finiteFlip {p}) g} (2 * Real.log 2)) ∧
      0 < finiteFlipGreatestGap F ∧ finiteFlipGreatestGap F < ε := by
  have hg0 : 0 < 2 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  obtain ⟨Q, hQ⟩ := exists_primeTailCutoff_gap_lt (max B 10) (lt_min hε hg0)
  let F := primeTailCutoff (max B 10) Q
  have hF : ∀ p ∈ F, p.Prime := primeTailCutoff_prime (max B 10) Q
  have hbelow : finiteFlipGreatestGap F < 2 * Real.log 2 :=
    hQ.trans_le (min_le_right ε (2 * Real.log 2))
  have hne : F.Nonempty := by
    by_contra hn
    have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hc : finiteFlipHarmonicDensity F = 1 := by
      simp only [he, finiteFlipHarmonicDensity, prod_empty]
    have hbound := (finiteFlipGreatestGap_bounds F hF).1
    rw [hc, one_pow, mul_one] at hbound
    exact not_lt_of_ge hbound hbelow
  refine ⟨F, hne, ?_, finiteFlipGreatestGap_pos F hF,
    hQ.trans_le (min_le_left ε (2 * Real.log 2))⟩
  intro p hp
  have hcut : max B 10 < p := (mem_filter.mp hp).2
  have hBp : B < p := (le_max_left B 10).trans_lt hcut
  have hp11 : 11 ≤ p := by
    have hh := (le_max_right B 10).trans_lt hcut
    omega
  exact ⟨hF p hp, hBp, hp11, isGreatest_primeFlip_hyperplaneGap (hF p hp) hp11⟩

end GaloisForLFunctions.ArithmeticCountingPositivity
