import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBoundedCompleteWeilSpectrumIsTheCompletedShellSpectrum
import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.PrimeFlipCompleteForm
import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.PrimeFlipTail
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeBecomesVisibleAtTheCriticalExponent
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartSeesEveryFlippedPrime
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapPositivityAtEveryOverlap

/-!
# Every flipped prime is seen by the complete Weil form at large overlap

Flipping the odd powers of one prime `p` changes Weil's form on a test `f` by the `p`-power lags
only. On an atomic test of width `w = c/N` each lag pairs the atoms `a` and `b` with
`|log b − log(p^k a)| ≤ w`. The exact pairs `b = p^k a` give the arithmetic correction of the
separated regime, which on the prime-square trial `F_p(n)/√n` is
`(4 log p/p)(−1 + 2/p²) log N` plus at most `2τ_p(1 − 1/p + 1/p²) log N` from the higher odd powers,
`τ_p = 2 log p/(p(p² − 1))`; the sum is negative for every prime. All other pairs lie in windows of `O(cp^k a/N)` integers
and cost `O(c)` in total, independently of `N` (`abs_flipWindow_le`). Hence, per unit `log N`, the
flipped form on the trial is at most `ζ`'s plus `L_p < 0`. On the Ramanujan span of
conductors `1, p, p²` the energy of `ζ` per unit `log N` is `Σ β_m² E_m(c)` (norm quasimodes), and
every completed energy tends to zero as `c → ∞`. So beyond a finite overlap every flip is seen.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticLorentzianGeometry
open _root_.RHTower (vonMangoldtAtom)

/-! ### The pairing of an atomic test -/

section Pairing

variable {g : ℝ → ℝ}

theorem integrable_atom_mul_atom_shift (hg : Continuous g) (hgc : HasCompactSupport g)
    (a b : ℕ) (s : ℝ) : Integrable fun t => atom g a t * atom g b (t + s) := by
  refine ((hg.comp (continuous_sub_right _)).mul
    (hg.comp ((continuous_add_const s).sub continuous_const))).integrable_of_hasCompactSupport ?_
  exact (hgc.comp_homeomorph (Homeomorph.subRight _)).mul_right

/-- **The pairing of an atomic test** is the double sum of the autocorrelation at the lag
`log k` minus the atom offsets. -/
theorem pairing_atomicTest (hg : Continuous g) (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ)
    (k : ℕ) :
    pairing (atomicTest N x g) k = 2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      x a * x b * bumpCorr g (Real.log k - (Real.log b - Real.log a)) := by
  have hexp : ∀ s : ℝ, (∫ t, atomicTest N x g t * atomicTest N x g (t + s)) =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b * ∫ t, atom g a t * atom g b (t + s) := by
    intro s
    have h : (fun t => atomicTest N x g t * atomicTest N x g (t + s)) =
        fun t => ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b * (atom g a t * atom g b (t + s)) := by
      funext t
      rw [atomicTest_eq_sum_atom, sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [h, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (integrable_atom_mul_atom_shift hg hgc a b s).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (integrable_atom_mul_atom_shift hg hgc a b s).const_mul _]
    exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _
  have h1 := hexp (-Real.log k)
  have h2 := hexp (Real.log k)
  simp only [← sub_eq_add_neg] at h1
  rw [pairing, h1, h2]
  simp_rw [integral_atom_mul_atom_sub_log, integral_atom_mul_atom_add_log]
  rw [Finset.sum_comm (s := Icc 1 N) (t := Icc 1 N)
    (f := fun a b => x a * x b * bumpCorr g (Real.log k - (Real.log a - Real.log b)))]
  rw [two_mul]
  congr 1
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

end Pairing

/-! ### The flip of one prime -/

section Flip

variable {g : ℝ → ℝ} {w : ℝ}

theorem supportedIn_atomicTest (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (N : ℕ)
    (x : ℕ → ℝ) : SupportedIn (Real.log N + w + 1) (atomicTest N x g) := by
  intro u hu
  rw [atomicTest_eq_sum_atom]
  exact Finset.sum_eq_zero fun n hn => by rw [supportedIn_atom hgsupp hw hn u hu, mul_zero]

theorem vonMangoldtAtom_sub_twistCoeff_flip (p k : ℕ) :
    vonMangoldtAtom k - twistCoeff (ArithmeticCountingPositivity.primeFlipWeight p) k =
      (1 - finiteFlip {p} k) * vonMangoldtAtom k := by
  unfold vonMangoldtAtom twistCoeff ArithmeticCountingPositivity.primeFlipWeight
  split_ifs <;> ring

/-- The off-ratio pairs of the flipped lags. -/
def flipWindow (p : ℕ) (g : ℝ → ℝ) (K N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range K, (1 - finiteFlip {p} k) * vonMangoldtAtom k *
    (2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b *
      (if b = k * a then 0 else bumpCorr g (Real.log k - (Real.log b - Real.log a))))

/-- The flipped lags on the exact ratios reproduce the separated arithmetic correction. -/
theorem sum_flip_ratio_eq {p : ℕ} {K N : ℕ} (hKN : N < K) (x : ℕ → ℝ) :
    ∑ k ∈ range K, (1 - finiteFlip {p} k) * vonMangoldtAtom k *
        (2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b * (if b = k * a then 1 else 0)) =
      atomicWeilForm N x - atomicWeilForm N (fun n => finiteFlip {p} n * x n) := by
  have hgauge := finiteFlip_isSignGauge {p}
  rw [atomicWeilForm_eq_edges, atomicWeilForm_eq_edges, ← mul_sub, ← sum_sub_distrib, mul_sum,
    Finset.sum_congr rfl fun k _ => by rw [mul_sum, mul_sum], Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha1 := (mem_Icc.mp ha).1
  -- the inner sum over `b` selects `b = k a`
  have hinner : ∀ k ∈ range K, (1 - finiteFlip {p} k) * vonMangoldtAtom k *
      (2 * ∑ b ∈ Icc 1 N, x a * x b * (if b = k * a then 1 else 0)) =
      if k ∈ Icc 1 (N / a) then
        2 * ((1 - finiteFlip {p} k) * vonMangoldtAtom k * (x a * x (a * k))) else 0 := by
    intro k _
    have hsel : ∑ b ∈ Icc 1 N, x a * x b * (if b = k * a then 1 else 0) =
        if k * a ∈ Icc 1 N then x a * x (k * a) else 0 := by
      simp only [mul_ite, mul_one, mul_zero, sum_ite_eq']
    rw [hsel]
    have hiff : k * a ∈ Icc 1 N ↔ k ∈ Icc 1 (N / a) := by
      simp only [mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨Nat.pos_of_ne_zero fun h0 => by simp [h0] at h1, ?_⟩
        exact (Nat.le_div_iff_mul_le ha1).mpr h2
      · rintro ⟨h1, h2⟩
        exact ⟨Nat.mul_pos h1 ha1, (Nat.le_div_iff_mul_le ha1).mp h2⟩
    by_cases hk : k ∈ Icc 1 (N / a)
    · rw [if_pos (hiff.mpr hk), if_pos hk, Nat.mul_comm k a]
      ring
    · rw [if_neg (fun h => hk (hiff.mp h)), if_neg hk, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  have hfilter : (range K).filter (fun k => k ∈ Icc 1 (N / a)) = Icc 1 (N / a) := by
    ext k
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro ⟨h1, h2⟩
      exact ⟨lt_of_le_of_lt (h2.trans (Nat.div_le_self N a)) hKN, h1, h2⟩
  rw [hfilter, ← sum_sub_distrib, mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht1 := (mem_Icc.mp ht).1
  have hflip : finiteFlip {p} a * finiteFlip {p} (a * t) = finiteFlip {p} t := by
    rw [hgauge.mul (by omega) (by omega), ← mul_assoc, hgauge.mul_self (by omega), one_mul]
  have hcoef : vonMangoldtAtom t = (ArithmeticFunction.vonMangoldt t : ℝ) / Real.sqrt t := by
    unfold vonMangoldtAtom
    split_ifs with h2
    · rfl
    · have ht' : t = 1 := by omega
      subst ht'
      simp
  rw [hcoef]
  linear_combination (2 * ((ArithmeticFunction.vonMangoldt t : ℝ) / Real.sqrt t) * x a *
    x (a * t)) * hflip

/-- **The flip on an atomic test** is the separated arithmetic correction plus the off-ratio
window. -/
theorem weilQuadTw_flip_sub_eq (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (p N : ℕ) (x : ℕ → ℝ) :
    weilQuadTw (ArithmeticCountingPositivity.primeFlipWeight p) (atomicTest N x g) -
        weilQuad (atomicTest N x g) =
      (∫ u, g u ^ 2) * (atomicWeilForm N x - atomicWeilForm N (fun n => finiteFlip {p} n * x n)) +
        flipWindow p g (lagRange (Real.log N + w + 1)) N x := by
  set K := lagRange (Real.log N + w + 1) with hK
  have hKN : N < K := by
    rw [hK, lagRange]
    have hN : (N : ℝ) < Real.exp (2 * (Real.log N + w + 1)) := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0; simp only [Nat.cast_zero]; exact Real.exp_pos _
      · have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
        calc (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hN0).symm
          _ < Real.exp (2 * (Real.log N + w + 1)) := by
            rw [Real.exp_lt_exp]
            have := Real.log_natCast_nonneg N
            linarith
    have := (Nat.lt_ceil.mpr hN)
    omega
  rw [weilQuadTw_eq _ (supportedIn_atomicTest hgsupp hw N x), add_sub_cancel_left,
    ← sum_flip_ratio_eq hKN, mul_sum, flipWindow, ← sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vonMangoldtAtom_sub_twistCoeff_flip, pairing_atomicTest hg.continuous hgc]
  have hsplit : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, x a * x b *
      bumpCorr g (Real.log k - (Real.log b - Real.log a)) =
        (∫ u, g u ^ 2) * (x a * x b * (if b = k * a then 1 else 0)) +
          x a * x b * (if b = k * a then 0 else bumpCorr g (Real.log k - (Real.log b - Real.log a))) := by
    intro a ha b hb
    by_cases hb' : b = k * a
    · have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Icc.mp ha).1
      have hk0 : k ≠ 0 := by
        rintro rfl
        have := (mem_Icc.mp hb).1
        omega
      have hk0' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      rw [if_pos hb', if_pos hb', hb', Nat.cast_mul, Real.log_mul hk0'.ne' ha0.ne',
        show Real.log k - (Real.log k + Real.log a - Real.log a) = 0 by ring, bumpCorr_zero]
      ring
    · rw [if_neg hb', if_neg hb']
      ring
  have hpair : (2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      x a * x b * bumpCorr g (Real.log k - (Real.log b - Real.log a))) =
      (∫ u, g u ^ 2) * (2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b * (if b = k * a then 1 else 0)) +
        2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b *
          (if b = k * a then 0 else bumpCorr g (Real.log k - (Real.log b - Real.log a))) := by
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hsplit a ha b hb]
    simp only [sum_add_distrib, ← mul_sum]
    ring
  rw [hpair]
  ring

/-! ### The off-ratio window costs `O(c)` -/

/-- Only the prime powers of `p` carry a flipped lag, each with weight at most `2 log p/√k`. -/
theorem flip_coeff_cases {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 - finiteFlip {p} k) * vonMangoldtAtom k = 0 ∨
      ∃ j, k = p ^ (j + 1) ∧
        |(1 - finiteFlip {p} k) * vonMangoldtAtom k| ≤ 2 * Real.log p / Real.sqrt k := by
  by_cases hpk : p ∣ k
  · by_cases hΛ : (ArithmeticFunction.vonMangoldt k : ℝ) = 0
    · left
      unfold vonMangoldtAtom
      split_ifs <;> simp [hΛ]
    · right
      obtain ⟨q, m, hq, hm, rfl⟩ :=
        (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpk)
      subst hpq
      refine ⟨m - 1, by rw [Nat.sub_add_cancel hm], ?_⟩
      have h2 : 2 ≤ p ^ m := hp.two_le.trans (Nat.le_self_pow hm.ne' p)
      rw [vonMangoldtAtom, if_pos h2, ArithmeticFunction.vonMangoldt_apply_pow hm.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      have hε : |1 - finiteFlip {p} (p ^ m)| ≤ 2 := by
        have := abs_finiteFlip {p} (p ^ m)
        exact (abs_sub _ _).trans (by rw [abs_one, this]; norm_num)
      have hl : 0 ≤ Real.log p / Real.sqrt (p ^ m : ℕ) :=
        div_nonneg (Real.log_natCast_nonneg p) (Real.sqrt_nonneg _)
      rw [abs_mul, abs_of_nonneg hl, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hε hl
  · left
    rw [finiteFlip_eq_one_of_coprime fun q hq => by
      rw [Finset.mem_singleton] at hq; subst hq; exact hpk]
    ring

open Classical in
/-- The geometric mass of the prime powers of `p` is at most one. -/
theorem sum_primePow_inv_le {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ k ∈ range K, (if ∃ j, k = p ^ (j + 1) then (1 : ℝ) / k else 0) ≤ 1 := by
  have hp2 := hp.two_le
  have hsub : (range K).filter (fun k => ∃ j, k = p ^ (j + 1)) ⊆
      (range K).image (fun j => p ^ (j + 1)) := by
    intro k hk
    obtain ⟨hkK, j, rfl⟩ := mem_filter.mp hk
    refine mem_image.mpr ⟨j, mem_range.mpr ?_, rfl⟩
    have hj : j < p ^ (j + 1) :=
      (Nat.lt_succ_self j).trans (Nat.lt_pow_self (by omega : 1 < p))
    exact hj.trans (mem_range.mp hkK)
  have hinj : Set.InjOn (fun j => p ^ (j + 1)) (range K) := fun i _ j _ hij =>
    by simpa using Nat.pow_right_injective hp2 hij
  rw [← sum_filter]
  calc ∑ k ∈ (range K).filter (fun k => ∃ j, k = p ^ (j + 1)), (1 : ℝ) / k
      ≤ ∑ k ∈ (range K).image (fun j => p ^ (j + 1)), (1 : ℝ) / k :=
        sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity
    _ = ∑ j ∈ range K, (1 : ℝ) / (p ^ (j + 1) : ℕ) := sum_image hinj
    _ ≤ ∑ j ∈ range K, (1 / (2 : ℝ)) ^ (j + 1) := sum_le_sum fun j _ => by
        rw [Nat.cast_pow, one_div_pow]
        exact one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp2) _)
    _ = (1 / 2) * ∑ j ∈ range K, (1 / (2 : ℝ)) ^ j := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    _ ≤ (1 / 2) * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le K) (by norm_num)
    _ = 1 := by norm_num

/-- A product `L = ka` has at most `6wL` integer neighbours at log-distance `w ≤ 1`, all above
`L/3`. -/
theorem sum_near_inv_sqrt_le {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) {N k a : ℕ} (hk : 1 ≤ k)
    (ha : 1 ≤ a) {x : ℕ → ℝ} (hx : ∀ n ∈ Icc 1 N, |x n| ≤ 1 / Real.sqrt n) :
    ∑ b ∈ Icc 1 N, |x b| *
        (if b ≠ k * a ∧ |Real.log k - (Real.log b - Real.log a)| ≤ w then 1 else 0) ≤
      if k * a ≤ 3 * N then 12 * w * Real.sqrt (k * a : ℕ) else 0 := by
  set L := k * a with hL
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
  have hlog : ∀ b : ℕ, 1 ≤ b → Real.log k - (Real.log b - Real.log a) = Real.log L - Real.log b := by
    intro b _
    rw [hL, Nat.cast_mul, Real.log_mul (by exact_mod_cast (by omega : k ≠ 0))
      (by exact_mod_cast (by omega : a ≠ 0))]
    ring
  -- every neighbour lies above `L/3` and within `3wL`
  have hnear : ∀ b ∈ Icc 1 N, b ≠ L → |Real.log k - (Real.log b - Real.log a)| ≤ w →
      (L : ℝ) / 3 ≤ b ∧ |(b : ℝ) - L| ≤ 3 * w * L := by
    intro b hb _ hbw
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (mem_Icc.mp hb).1
    rw [hlog b (mem_Icc.mp hb).1, abs_le] at hbw
    have hup : (b : ℝ) ≤ L * Real.exp w := by
      have := Real.exp_le_exp.mpr (show Real.log b ≤ Real.log L + w by linarith)
      rwa [Real.exp_add, Real.exp_log hb0, Real.exp_log hL0] at this
    have hlo : (L : ℝ) * Real.exp (-w) ≤ b := by
      have := Real.exp_le_exp.mpr (show Real.log L - w ≤ Real.log b by linarith)
      rwa [sub_eq_add_neg, Real.exp_add, Real.exp_log hb0, Real.exp_log hL0] at this
    have he1 : Real.exp w - 1 ≤ 3 * w := by
      have h1 := Real.add_one_le_exp (-w)
      have hmul : (-w + 1) * Real.exp w ≤ Real.exp (-w) * Real.exp w :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos w).le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
      have he : Real.exp w ≤ 3 := (Real.exp_le_exp.mpr hw1).trans
        (Real.exp_one_lt_d9.le.trans (by norm_num))
      nlinarith
    have he2 : 1 - Real.exp (-w) ≤ w := by linarith [Real.add_one_le_exp (-w)]
    have he3 : 1 / 3 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, one_div]
      exact (inv_le_inv₀ (by norm_num) (Real.exp_pos 1)).mpr
        (Real.exp_one_lt_d9.le.trans (by norm_num))
    refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩⟩
    · have : Real.exp (-1) ≤ Real.exp (-w) := Real.exp_le_exp.mpr (by linarith)
      nlinarith
    · nlinarith
    · nlinarith
  split_ifs with h3
  · have hterm : ∀ b ∈ Icc 1 N, |x b| *
        (if b ≠ L ∧ |Real.log k - (Real.log b - Real.log a)| ≤ w then 1 else 0) ≤
        if b ≠ L ∧ |(b : ℝ) - L| ≤ 3 * w * L then 2 / Real.sqrt L else 0 := by
      intro b hb
      by_cases hc : b ≠ L ∧ |Real.log k - (Real.log b - Real.log a)| ≤ w
      · obtain ⟨h13, h2⟩ := hnear b hb hc.1 hc.2
        rw [if_pos hc, if_pos ⟨hc.1, h2⟩, mul_one]
        refine (hx b hb).trans ?_
        rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hb).1))
          (Real.sqrt_pos.mpr hL0), one_mul]
        have : Real.sqrt L ≤ Real.sqrt (4 * b) :=
          Real.sqrt_le_sqrt (by linarith)
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
        exact this
      · rw [if_neg hc, mul_zero]
        split_ifs <;> positivity
    calc _ ≤ ∑ b ∈ Icc 1 N, (if b ≠ L ∧ |(b : ℝ) - L| ≤ 3 * w * L then 2 / Real.sqrt L else 0) :=
          sum_le_sum hterm
      _ = ((Icc 1 N).filter fun b => b ≠ L ∧ |(b : ℝ) - L| ≤ 3 * w * L).card *
            (2 / Real.sqrt L) := by
          rw [← sum_filter, sum_const, nsmul_eq_mul]
      _ ≤ (2 * (3 * w * L)) * (2 / Real.sqrt L) :=
          mul_le_mul_of_nonneg_right (card_near_le _ L (by positivity)) (by positivity)
      _ = 12 * w * Real.sqrt L := by
          have hs : Real.sqrt (L : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hL0).ne'
          field_simp
          rw [Real.sq_sqrt hL0.le]
          ring
  · refine (sum_eq_zero fun b hb => ?_).le
    rw [if_neg, mul_zero]
    rintro ⟨hne, hbw⟩
    obtain ⟨h13, _⟩ := hnear b hb hne hbw
    have hbN : (b : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hb).2
    have : (3 * N : ℝ) < L := by exact_mod_cast (not_le.mp h3)
    linarith

/-- **The window of one flipped lag** costs `72 c ‖g‖²/√k` on the trial, independently of `N`. -/
theorem abs_flipInner_le (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) {N k : ℕ}
    (hk : 1 ≤ k) {x : ℕ → ℝ} (hx : ∀ n ∈ Icc 1 N, |x n| ≤ 1 / Real.sqrt n) :
    |2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b *
        (if b = k * a then 0 else bumpCorr g (Real.log k - (Real.log b - Real.log a)))| ≤
      72 * (w * N) * (∫ u, g u ^ 2) / Real.sqrt k := by
  set G0 := ∫ u, g u ^ 2
  have hG0 : 0 ≤ G0 := integral_nonneg fun u => sq_nonneg _
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  -- each entry is at most `G0` on the window and vanishes elsewhere
  have hentry : ∀ a b : ℕ, |if b = k * a then 0 else bumpCorr g (Real.log k - (Real.log b - Real.log a))|
      ≤ G0 * (if b ≠ k * a ∧ |Real.log k - (Real.log b - Real.log a)| ≤ w then 1 else 0) := by
    intro a b
    by_cases hb : b = k * a
    · rw [if_pos hb, abs_zero]; exact mul_nonneg hG0 (by split_ifs <;> norm_num)
    · rw [if_neg hb]
      by_cases hw' : |Real.log k - (Real.log b - Real.log a)| ≤ w
      · rw [if_pos ⟨hb, hw'⟩, mul_one]; exact abs_bumpCorr_le hg hgc _
      · rw [if_neg (fun h => hw' h.2), mul_zero, bumpCorr_eq_zero hgsupp (not_le.mp hw'), abs_zero]
  have hrow : ∀ a ∈ Icc 1 N, |∑ b ∈ Icc 1 N, x a * x b *
      (if b = k * a then 0 else bumpCorr g (Real.log k - (Real.log b - Real.log a)))| ≤
      G0 * (if k * a ≤ 3 * N then 12 * w * Real.sqrt k else 0) := by
    intro a ha
    have ha1 := (mem_Icc.mp ha).1
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    calc _ ≤ ∑ b ∈ Icc 1 N, |x a| * (|x b| * (G0 *
          (if b ≠ k * a ∧ |Real.log k - (Real.log b - Real.log a)| ≤ w then 1 else 0))) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
          rw [abs_mul, abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hentry a b) (abs_nonneg _))
            (abs_nonneg _)
      _ = |x a| * G0 * ∑ b ∈ Icc 1 N, |x b| *
          (if b ≠ k * a ∧ |Real.log k - (Real.log b - Real.log a)| ≤ w then 1 else 0) := by
          rw [mul_assoc, mul_sum, mul_sum]
          exact sum_congr rfl fun b _ => by ring
      _ ≤ |x a| * G0 * (if k * a ≤ 3 * N then 12 * w * Real.sqrt (k * a : ℕ) else 0) :=
          mul_le_mul_of_nonneg_left (sum_near_inv_sqrt_le hw0 hw1 hk ha1 hx)
            (mul_nonneg (abs_nonneg _) hG0)
      _ ≤ G0 * (if k * a ≤ 3 * N then 12 * w * Real.sqrt k else 0) := by
          split_ifs
          · have hxa := hx a ha
            have hs : Real.sqrt (k * a : ℕ) = Real.sqrt k * Real.sqrt a := by
              rw [Nat.cast_mul, Real.sqrt_mul hk0.le]
            rw [hs]
            have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
            calc |x a| * G0 * (12 * w * (Real.sqrt k * Real.sqrt a))
                ≤ 1 / Real.sqrt a * G0 * (12 * w * (Real.sqrt k * Real.sqrt a)) := by
                  gcongr
              _ = G0 * (12 * w * Real.sqrt k) := by field_simp
          · simp
  have hcount : (((Icc 1 N).filter fun a => k * a ≤ 3 * N).card : ℝ) ≤ 3 * N / k := by
    have hsub : (Icc 1 N).filter (fun a => k * a ≤ 3 * N) ⊆ Icc 1 (3 * N / k) := by
      intro a ha
      obtain ⟨ha1, hka⟩ := mem_filter.mp ha
      refine mem_Icc.mpr ⟨(mem_Icc.mp ha1).1, (Nat.le_div_iff_mul_le hk).mpr ?_⟩
      rw [Nat.mul_comm]; exact hka
    calc (((Icc 1 N).filter fun a => k * a ≤ 3 * N).card : ℝ) ≤ (Icc 1 (3 * N / k)).card := by
          exact_mod_cast card_le_card hsub
      _ = ((3 * N / k : ℕ) : ℝ) := by simp
      _ ≤ (3 * N : ℕ) / (k : ℝ) := Nat.cast_div_le
      _ = 3 * N / k := by push_cast; ring
  calc |2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b *
        (if b = k * a then 0 else bumpCorr g (Real.log k - (Real.log b - Real.log a)))|
      ≤ 2 * ∑ a ∈ Icc 1 N, G0 * (if k * a ≤ 3 * N then 12 * w * Real.sqrt k else 0) := by
        rw [abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hrow))
          (by norm_num)
    _ = 2 * G0 * (12 * w * Real.sqrt k) *
          (((Icc 1 N).filter fun a => k * a ≤ 3 * N).card : ℝ) := by
        rw [← mul_sum, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
        ring
    _ ≤ 2 * G0 * (12 * w * Real.sqrt k) * (3 * N / k) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = 72 * (w * N) * G0 / Real.sqrt k := by
        have hsk : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hk0).ne'
        have hkk : (3 * N / k : ℝ) = 3 * N / (Real.sqrt k * Real.sqrt k) := by
          rw [Real.mul_self_sqrt hk0.le]
        rw [hkk]
        field_simp
        ring

open Classical in
/-- **The whole off-ratio window** of a flipped prime costs at most `144 c log p ‖g‖²`. -/
theorem abs_flipWindow_le (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) {p : ℕ}
    (hp : p.Prime) (K N : ℕ) {x : ℕ → ℝ} (hx : ∀ n ∈ Icc 1 N, |x n| ≤ 1 / Real.sqrt n) :
    |flipWindow p g K N x| ≤ 144 * (w * N) * Real.log p * ∫ u, g u ^ 2 := by
  set G0 := ∫ u, g u ^ 2
  have hG0 : 0 ≤ G0 := integral_nonneg fun u => sq_nonneg _
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hterm : ∀ k ∈ range K, |(1 - finiteFlip {p} k) * vonMangoldtAtom k *
      (2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b *
        (if b = k * a then 0 else bumpCorr g (Real.log k - (Real.log b - Real.log a))))| ≤
      144 * (w * N) * Real.log p * G0 * (if ∃ j, k = p ^ (j + 1) then (1 : ℝ) / k else 0) := by
    intro k _
    rcases flip_coeff_cases hp k with h0 | ⟨j, hkj, hc⟩
    · rw [h0, zero_mul, abs_zero]
      exact mul_nonneg (by positivity) (by split_ifs <;> positivity)
    · have hk : 1 ≤ k := by rw [hkj]; exact Nat.one_le_pow _ _ hp.pos
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      rw [if_pos ⟨j, hkj⟩, abs_mul]
      calc |(1 - finiteFlip {p} k) * vonMangoldtAtom k| * |2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
            x a * x b * (if b = k * a then 0 else bumpCorr g (Real.log k - (Real.log b - Real.log a)))|
          ≤ (2 * Real.log p / Real.sqrt k) * (72 * (w * N) * G0 / Real.sqrt k) :=
            mul_le_mul hc (abs_flipInner_le hg hgc hgsupp hw0 hw1 hk hx) (abs_nonneg _)
              (by positivity)
        _ = 144 * (w * N) * Real.log p * G0 * (1 / k) := by
            have hsk : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hk0).ne'
            have hkk : (1 / k : ℝ) = 1 / (Real.sqrt k * Real.sqrt k) := by
              rw [Real.mul_self_sqrt hk0.le]
            rw [hkk]
            field_simp
            ring
  calc |flipWindow p g K N x| ≤ ∑ k ∈ range K, 144 * (w * N) * Real.log p * G0 *
        (if ∃ j, k = p ^ (j + 1) then (1 : ℝ) / k else 0) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = 144 * (w * N) * Real.log p * G0 *
        ∑ k ∈ range K, (if ∃ j, k = p ^ (j + 1) then (1 : ℝ) / k else 0) := by rw [mul_sum]
    _ ≤ 144 * (w * N) * Real.log p * G0 * 1 :=
        mul_le_mul_of_nonneg_left (sum_primePow_inv_le hp K) (by positivity)
    _ = _ := by ring

end Flip

/-! ### Energies of finite Ramanujan packets -/

/-- Norm quasimodes give the energy of every finite Ramanujan combination in the limit. -/
theorem tendsto_inner_sum_quasimodes {φ : ℝ → ℝ} {c : ℝ} {E : ℕ → ℝ} (S : Finset ℕ)
    (hS : ∀ m ∈ S, 0 < m) (β : ℕ → ℝ)
    (hquasi : ∀ m ∈ S, Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N)
          (∑ m ∈ S, β m • normalizedRamanujanHorizonVector m N),
        ∑ m ∈ S, β m • normalizedRamanujanHorizonVector m N⟫) atTop
      (𝓝 (∑ m ∈ S, β m ^ 2 * E m)) := by
  have hexp : ∀ N : ℕ, ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N)
      (∑ m ∈ S, β m • normalizedRamanujanHorizonVector m N),
        ∑ m ∈ S, β m • normalizedRamanujanHorizonVector m N⟫ =
      ∑ m ∈ S, ∑ l ∈ S, β m * β l *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N),
          normalizedRamanujanHorizonVector l N⟫ := by
    intro N
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun l _ => by ring
  have hterm : ∀ m ∈ S, ∀ l ∈ S, Tendsto (fun N : ℕ => β m * β l *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N),
        normalizedRamanujanHorizonVector l N⟫) atTop
      (𝓝 (β m * β l * (E m * if m = l then 1 else 0))) := by
    intro m hm l hl
    refine Tendsto.const_mul _ ?_
    have hsplit : ∀ N : ℕ, ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N)
        (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫ =
        E m * ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ +
          ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
            E m • normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ := by
      intro N
      rw [inner_sub_left, real_inner_smul_left]
      ring
    have hgram := (tendsto_normalizedRamanujanHorizonVector_gram (hS m hm) (hS l hl)).const_mul (E m)
    have hnorm : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector l N‖) atTop (𝓝 1) := by
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] using
        (tendsto_normalizedRamanujanHorizonVector_norm_sq (hS l hl)).sqrt
    have hres : Tendsto (fun N : ℕ =>
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          E m • normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫)
        atTop (𝓝 0) := by
      have hb := (hquasi m hm).mul hnorm
      rw [zero_mul] at hb
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _)
        (fun N => by rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _) hb
    simpa only [hsplit, add_zero] using hgram.add hres
  have hsum := tendsto_finsetSum S fun m hm => tendsto_finsetSum S fun l hl => hterm m hm l hl
  have hval : ∑ m ∈ S, ∑ l ∈ S, β m * β l * (E m * if m = l then 1 else 0) =
      ∑ m ∈ S, β m ^ 2 * E m := by
    refine sum_congr rfl fun m hm => ?_
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, if_pos hm]
    ring
  rw [← hval]
  exact hsum.congr fun N => (hexp N).symm

/-! ### The prime-square trial at a fixed overlap -/

section Trial

open TransMetzlerWeilPositivity.BoundedOverlap BezoutValuationIncidence CompletedShell
  SelectiveMultiscaleArithmeticPositivity

/-- The conductors of the prime-square trial. -/
def flipTrialConductors (p : ℕ) : Finset ℕ := {1, p, p ^ 2}

/-- Coordinates of the prime-square trial on the normalized Ramanujan vectors. -/
def flipTrialCoeff (p m : ℕ) : ℝ :=
  if m = 1 then 1 - 2 / (p : ℝ) + 2 / (p : ℝ) ^ 2
  else if m = p then (-2 / (p : ℝ) + 2 / (p : ℝ) ^ 2) * Real.sqrt (p.totient : ℝ)
  else (2 / (p : ℝ) ^ 2) * Real.sqrt ((p ^ 2).totient : ℝ)

/-- The completed energy of the prime-square trial per unit `log N`. -/
def flipTrialEnergy (φ : ℝ → ℝ) (c : ℝ) (p : ℕ) : ℝ :=
  ∑ m ∈ flipTrialConductors p, flipTrialCoeff p m ^ 2 * completedConductorEnergy φ c m

open Classical in
/-- The odd prime powers `p^(2j+3)` have harmonic mass at most `1/(p(p² − 1))`. -/
theorem sum_oddPrimePow_inv_le {p : ℕ} (hp : p.Prime) (y : ℕ) :
    ∑ t ∈ Icc 1 y, (if ∃ j, t = p ^ (2 * j + 3) then (1 : ℝ) / t else 0) ≤
      1 / ((p : ℝ) * ((p : ℝ) ^ 2 - 1)) := by
  classical
  have hp2 := hp.two_le
  have hq : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hsub : (Icc 1 y).filter (fun t => ∃ j, t = p ^ (2 * j + 3)) ⊆
      (range y).image (fun j => p ^ (2 * j + 3)) := by
    intro t ht
    obtain ⟨hty, j, rfl⟩ := mem_filter.mp ht
    refine mem_image.mpr ⟨j, mem_range.mpr ?_, rfl⟩
    have hj : j < p ^ (2 * j + 3) :=
      (by omega : j < 2 * j + 3).trans (Nat.lt_pow_self (by omega : 1 < p))
    exact hj.trans_le (mem_Icc.mp hty).2
  have hinj : Set.InjOn (fun j => p ^ (2 * j + 3)) (range y) := fun i _ j _ hij => by
    beta_reduce at hij
    have := Nat.pow_right_injective hp2 hij
    omega
  set r : ℝ := 1 / (p : ℝ) ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by positivity)]; nlinarith
  rw [← sum_filter]
  calc ∑ t ∈ (Icc 1 y).filter (fun t => ∃ j, t = p ^ (2 * j + 3)), (1 : ℝ) / t
      ≤ ∑ t ∈ (range y).image (fun j => p ^ (2 * j + 3)), (1 : ℝ) / t :=
        sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => by positivity
    _ = ∑ j ∈ range y, (1 : ℝ) / ((p ^ (2 * j + 3) : ℕ) : ℝ) := sum_image hinj
    _ = ∑ j ∈ range y, 1 / (p : ℝ) ^ 3 * r ^ j := sum_congr rfl fun j _ => by
        rw [hr, Nat.cast_pow, one_div_pow, ← pow_mul, pow_add, mul_comm (2 : ℕ) j]
        field_simp
    _ = 1 / (p : ℝ) ^ 3 * ∑ j ∈ range y, r ^ j := by rw [mul_sum]
    _ ≤ 1 / (p : ℝ) ^ 3 * (1 / (1 - r)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [geom_sum_eq hr1.ne]
        have h1 : 0 < 1 - r := by linarith
        rw [← neg_div_neg_eq, neg_sub, neg_sub]
        exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 y]) h1.le
    _ = 1 / ((p : ℝ) * ((p : ℝ) ^ 2 - 1)) := by
        rw [hr]
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hp1 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
        field_simp

/-- The cost of the odd prime powers beyond the first, per trial point with value one. -/
def flipTailWeight (p : ℕ) : ℝ := 2 * Real.log p / ((p : ℝ) * ((p : ℝ) ^ 2 - 1))

/-- **Sharp row bound.** The first prime keeps its sign; the higher odd powers `p^(2j+3)` see the
trial value one on `p²`-multiples, so they cost only where the trial equals one. -/
theorem primeSquareFlipRow_le_sharp {p : ℕ} (hp : p.Prime) (n y : ℕ) :
    primeSquareFlipRow p n y ≤
      (if p ≤ y then 2 * Real.log p / p *
        (primeSquareTrial p n * primeSquareTrial p (p * n)) else 0) +
      (if primeSquareTrial p n = 1 then flipTailWeight p else 0) := by
  classical
  have hp2 := hp.two_le
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hterm : ∀ t ∈ Icc 1 y, (1 - finiteFlip {p} t) * ArithmeticFunction.vonMangoldt t / (t : ℝ) *
      (primeSquareTrial p n * primeSquareTrial p (t * n)) ≤
      (if t = p then 2 * Real.log p / p *
        (primeSquareTrial p n * primeSquareTrial p (p * n)) else 0) +
      (if primeSquareTrial p n = 1 then
        (if ∃ j, t = p ^ (2 * j + 3) then 2 * Real.log p * (1 / (t : ℝ)) else 0) else 0) := by
    intro t ht
    have ht1 := (mem_Icc.mp ht).1
    have hrhs2 : 0 ≤ (if primeSquareTrial p n = 1 then
        (if ∃ j, t = p ^ (2 * j + 3) then 2 * Real.log p * (1 / (t : ℝ)) else 0) else 0) := by
      split_ifs <;> positivity
    by_cases htp : t = p
    · subst htp
      rw [if_pos rfl, finiteFlip_prime (fun q hq => by rw [mem_singleton] at hq; rw [hq]; exact hp)
        (mem_singleton_self t), ArithmeticFunction.vonMangoldt_apply_prime hp]
      have : (1 - (-1 : ℝ)) * Real.log t / t = 2 * Real.log t / t := by ring
      rw [this]
      exact le_add_of_nonneg_right hrhs2
    rw [if_neg htp, zero_add]
    by_cases hpt : p ∣ t
    · by_cases hΛ : (ArithmeticFunction.vonMangoldt t : ℝ) = 0
      · rw [hΛ, mul_zero, zero_div, zero_mul]; exact hrhs2
      obtain ⟨q, k, hq, hk, hqk⟩ :=
        (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp
        (hp.dvd_of_dvd_pow (hqk ▸ hpt))
      subst hpq
      subst hqk
      have hk2 : 2 ≤ k := by
        by_contra h
        have : k = 1 := by omega
        subst this
        exact htp (pow_one p)
      have hflip : finiteFlip {p} (p ^ k) = (-1) ^ k := by
        rw [finiteFlip, prod_singleton, Nat.factorization_pow, Finsupp.smul_apply,
          hp.factorization_self, smul_eq_mul, mul_one]
      have htrial : primeSquareTrial p (p ^ k * n) = 1 := by
        have h1 : p ∣ p ^ k * n := Dvd.dvd.mul_right (dvd_pow_self p (by omega)) n
        have h2 : p ^ 2 ∣ p ^ k * n := Dvd.dvd.mul_right (pow_dvd_pow p hk2) n
        simp only [primeSquareTrial, h1, h2, if_true]
        ring
      rw [htrial, mul_one, hflip, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · have heven : ((-1 : ℝ)) ^ k = 1 := by rw [hj, ← two_mul, pow_mul]; norm_num
        rw [heven, sub_self, zero_mul, zero_div, zero_mul]
        exact hrhs2
      · have hj1 : 1 ≤ j := by omega
        have hex : ∃ j', p ^ k = p ^ (2 * j' + 3) := ⟨j - 1, by rw [hj]; congr 1; omega⟩
        have hodd : ((-1 : ℝ)) ^ k = -1 := by rw [hj, pow_succ, pow_mul]; norm_num
        rw [hodd]
        have habs := abs_primeSquareTrial p n
        by_cases hF : primeSquareTrial p n = 1
        · rw [if_pos hF, if_pos hex, hF]
          ring_nf
          exact le_refl _
        · rw [if_neg hF]
          have hFm : primeSquareTrial p n = -1 := by
            rcases abs_eq (zero_le_one) |>.mp habs with h | h
            · exact absurd h hF
            · exact h
          rw [hFm]
          have h0 : (0 : ℝ) ≤ Real.log p / ((p ^ k : ℕ) : ℝ) := by positivity
          have : (1 - -1 : ℝ) * Real.log p / ((p ^ k : ℕ) : ℝ) * -1 =
              -(2 * (Real.log p / ((p ^ k : ℕ) : ℝ))) := by ring
          rw [this]
          linarith
    · rw [finiteFlip_eq_one_of_coprime fun q hq => by
        rw [mem_singleton] at hq; subst hq; exact hpt]
      rw [sub_self, zero_mul, zero_div, zero_mul]
      exact hrhs2
  have h := sum_le_sum hterm
  rw [sum_add_distrib, sum_ite_eq'] at h
  have hpy : (p ∈ Icc 1 y) ↔ p ≤ y := by simp [mem_Icc, hp.one_le]
  unfold primeSquareFlipRow
  refine h.trans (add_le_add (by simp only [hpy]; exact le_rfl) ?_)
  split_ifs with hF
  · have hfac : ∑ t ∈ Icc 1 y, (if ∃ j, t = p ^ (2 * j + 3) then 2 * Real.log p * (1 / (t : ℝ))
        else 0) = 2 * Real.log p * ∑ t ∈ Icc 1 y,
          (if ∃ j, t = p ^ (2 * j + 3) then (1 : ℝ) / t else 0) := by
      rw [mul_sum]
      exact sum_congr rfl fun t _ => by split_ifs <;> ring
    rw [hfac]
    unfold flipTailWeight
    have := sum_oddPrimePow_inv_le hp y
    calc 2 * Real.log p * ∑ t ∈ Icc 1 y, (if ∃ j, t = p ^ (2 * j + 3) then (1 : ℝ) / t else 0)
        ≤ 2 * Real.log p * (1 / ((p : ℝ) * ((p : ℝ) ^ 2 - 1))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  · simp

/-- The arithmetic gain of the flip per unit `log N` on the prime-square trial: the first prime
contributes `(4 log p/p)(−1 + 2/p²)`, the higher odd powers at most
`2 τ_p (1 − 1/p + 1/p²)` with `τ_p = 2 log p/(p(p² − 1))`. -/
def flipGain (p : ℕ) : ℝ :=
  4 * Real.log p / p * (-1 + 2 / (p : ℝ) ^ 2) +
    2 * flipTailWeight p * (1 - 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2)

theorem flipGain_neg {p : ℕ} (hp : p.Prime) : flipGain p < 0 := by
  have hq : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  have hq0 : (0 : ℝ) < p := by linarith
  have hq1 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have heq : flipGain p = 4 * Real.log p *
      ((-(p : ℝ) ^ 4 + 4 * (p : ℝ) ^ 2 - (p : ℝ) - 1) / ((p : ℝ) ^ 3 * ((p : ℝ) ^ 2 - 1))) := by
    unfold flipGain flipTailWeight
    field_simp
    ring
  rw [heq]
  refine mul_neg_of_pos_of_neg (by positivity) (div_neg_of_neg_of_pos ?_ (by positivity))
  have h4 : 0 ≤ (p : ℝ) ^ 2 * ((p : ℝ) ^ 2 - 4) := mul_nonneg (sq_nonneg _) (by nlinarith)
  nlinarith

/-- The sharp finite-horizon bound for the flipped arithmetic correction of the trial. -/
def sharpFlipBound (p N : ℕ) : ℝ :=
  2 * (2 * Real.log p / p) * (-gaugeHarmonicSum (fun _ => 1) (N / p) +
      (2 / (p : ℝ) ^ 2) * gaugeHarmonicSum (fun _ => 1) ((N / p) / p ^ 2)) +
    2 * flipTailWeight p * (gaugeHarmonicSum (fun _ => 1) N -
      (1 / (p : ℝ)) * gaugeHarmonicSum (fun _ => 1) (N / p) +
        (1 / (p : ℝ) ^ 2) * gaugeHarmonicSum (fun _ => 1) (N / p ^ 2))

theorem primeSquareTrial_prime_correction_le_sharp {p : ℕ} (hp : p.Prime) (N : ℕ) :
    atomicWeilForm N (fun n => primeSquareTrial p n / Real.sqrt n) -
      atomicWeilForm N (fun n => finiteFlip {p} n * primeSquareTrial p n / Real.sqrt n) ≤
        sharpFlipBound p N := by
  classical
  rw [primeSquareTrial_prime_correction]
  have h := mul_le_mul_of_nonneg_left (sum_le_sum (s := Icc 1 N) (fun m _ =>
    mul_le_mul_of_nonneg_left (primeSquareFlipRow_le_sharp hp m (N / m))
      (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ)))) (by norm_num : (0 : ℝ) ≤ 2)
  refine h.trans_eq ?_
  simp only [mul_add, sum_add_distrib]
  have hpos := hp.pos
  have hhead : (∑ m ∈ Icc 1 N, (1 / (m : ℝ)) *
      (if p ≤ N / m then 2 * Real.log p / p *
        (primeSquareTrial p m * primeSquareTrial p (p * m)) else 0)) =
      (2 * Real.log p / p) *
        ∑ m ∈ Icc 1 (N / p), primeSquareTrial p m * primeSquareTrial p (p * m) / m := by
    have hfilt : (Icc 1 N).filter (fun m => p ≤ N / m) = Icc 1 (N / p) := by
      ext m
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hm, _⟩, h⟩
        refine ⟨hm, (Nat.le_div_iff_mul_le hpos).mpr ?_⟩
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp h
      · rintro ⟨hm, h⟩
        refine ⟨⟨hm, h.trans (Nat.div_le_self N p)⟩, (Nat.le_div_iff_mul_le hm).mpr ?_⟩
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hpos).mp h
    rw [← hfilt, sum_filter, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  have htail : (∑ m ∈ Icc 1 N, (1 / (m : ℝ)) *
      (if primeSquareTrial p m = 1 then flipTailWeight p else 0)) =
      flipTailWeight p * (gaugeHarmonicSum (fun _ => 1) N -
        (1 / (p : ℝ)) * gaugeHarmonicSum (fun _ => 1) (N / p) +
          (1 / (p : ℝ) ^ 2) * gaugeHarmonicSum (fun _ => 1) (N / p ^ 2)) := by
    have hind : ∀ m : ℕ, (if primeSquareTrial p m = 1 then (1 : ℝ) else 0) =
        1 - (if p ∣ m then 1 else 0) + (if p ^ 2 ∣ m then 1 else 0) := by
      intro m
      by_cases h1 : p ∣ m
      · by_cases h2 : p ^ 2 ∣ m
        · simp only [primeSquareTrial, h1, h2, if_true]; norm_num
        · simp only [primeSquareTrial, h1, h2, if_true, if_false]; norm_num
      · have h2 : ¬ p ^ 2 ∣ m := fun h => h1 ((dvd_pow_self p two_ne_zero).trans h)
        simp only [primeSquareTrial, h1, h2, if_false]; norm_num
    have h1 := harmonic_indicator hpos N
    have h2 := harmonic_indicator (pow_pos hpos 2) N
    calc (∑ m ∈ Icc 1 N, (1 / (m : ℝ)) *
          (if primeSquareTrial p m = 1 then flipTailWeight p else 0))
        = flipTailWeight p * ((∑ m ∈ Icc 1 N, (1 : ℝ) / m) -
            ∑ m ∈ Icc 1 N, (if p ∣ m then (1 : ℝ) else 0) / m +
              ∑ m ∈ Icc 1 N, (if p ^ 2 ∣ m then (1 : ℝ) else 0) / m) := by
          rw [← sum_sub_distrib, ← sum_add_distrib, mul_sum]
          refine sum_congr rfl fun m _ => ?_
          have := hind m
          by_cases hF : primeSquareTrial p m = 1
          · rw [if_pos hF] at this ⊢
            rw [show (1 : ℝ) / m - (if p ∣ m then (1 : ℝ) else 0) / m +
                (if p ^ 2 ∣ m then (1 : ℝ) else 0) / m =
                (1 - (if p ∣ m then (1 : ℝ) else 0) + (if p ^ 2 ∣ m then (1 : ℝ) else 0)) / m by
              ring, ← this]
            ring
          · rw [if_neg hF] at this ⊢
            rw [show (1 : ℝ) / m - (if p ∣ m then (1 : ℝ) else 0) / m +
                (if p ^ 2 ∣ m then (1 : ℝ) else 0) / m =
                (1 - (if p ∣ m then (1 : ℝ) else 0) + (if p ^ 2 ∣ m then (1 : ℝ) else 0)) / m by
              ring, ← this]
            ring
      _ = _ := by
          rw [h1, h2]
          simp only [gaugeHarmonicSum, Nat.cast_pow]
  rw [hhead, htail, primeSquareTrial_harmonic_correlation hpos]
  unfold sharpFlipBound
  ring

theorem tendsto_sharpFlipBound {p : ℕ} (hp : p.Prime) :
    Tendsto (fun N : ℕ => sharpFlipBound p N / Real.log N) atTop (𝓝 (flipGain p)) := by
  have h1 := tendsto_gaugeHarmonicSum_natDiv_div_log hp.pos
  have h3 := tendsto_gaugeHarmonicSum_natDiv_div_log (mul_pos hp.pos (pow_pos hp.pos 2))
  have h2 := tendsto_gaugeHarmonicSum_natDiv_div_log (pow_pos hp.pos 2)
  have h0 : Tendsto (fun N : ℕ => gaugeHarmonicSum (fun _ => 1) N / Real.log N)
      atTop (𝓝 1) := by
    simpa only [Nat.div_one] using
      tendsto_gaugeHarmonicSum_natDiv_div_log (by norm_num : 0 < (1 : ℕ))
  have hA := ((h1.neg.add (h3.const_mul (2 / (p : ℝ) ^ 2))).const_mul (2 * (2 * Real.log p / p)))
  have hB := (((h0.sub (h1.const_mul (1 / (p : ℝ)))).add (h2.const_mul (1 / (p : ℝ) ^ 2))).const_mul
    (2 * flipTailWeight p))
  have hsum := hA.add hB
  convert hsum using 1
  · funext N
    rw [sharpFlipBound, Nat.div_div_eq_div_mul]
    ring
  · unfold flipGain
    ring

theorem flipTrialConductors_pos {p : ℕ} (hp : p.Prime) : ∀ m ∈ flipTrialConductors p, 0 < m := by
  intro m hm
  simp only [flipTrialConductors, mem_insert, mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · exact one_pos
  · exact hp.pos
  · exact pow_pos hp.pos 2

/-- The prime-square trial is `√log N` times a fixed combination of normalized Ramanujan vectors. -/
theorem trial_eq_sqrt_log_smul {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 2 ≤ N) :
    (WithLp.toLp 2 (fun n : PrimeHorizonIndex N => primeSquareTrial p n / Real.sqrt n) :
      EuclideanSpace ℝ (PrimeHorizonIndex N)) =
    Real.sqrt (Real.log N) • ∑ m ∈ flipTrialConductors p,
      flipTrialCoeff p m • normalizedRamanujanHorizonVector m N := by
  have hp2 := hp.two_le
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hsl : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  have h1p : (1 : ℕ) ≠ p := by omega
  have h1q : (1 : ℕ) ≠ p ^ 2 := (Nat.one_lt_pow two_ne_zero (by omega)).ne
  have hpq : p ≠ p ^ 2 := by
    intro e
    have h := Nat.pow_right_injective hp2 (show p ^ 1 = p ^ 2 by rw [pow_one]; exact e)
    omega
  ext n
  have hn := n.property
  have hn0 : 0 < (n : ℕ) := (mem_Icc.mp hn).1
  have ht : ∀ m, 0 < m → (Real.sqrt (m.totient : ℝ)) ≠ 0 := fun m hm =>
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hm)).ne'
  simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    flipTrialConductors]
  rw [sum_insert (by simp [h1p, h1q]), sum_insert (by simp [hpq]), sum_singleton]
  change primeSquareTrial p n / Real.sqrt n = Real.sqrt (Real.log N) *
    (flipTrialCoeff p 1 * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile 1 n) +
      (flipTrialCoeff p p * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile p n) +
        flipTrialCoeff p (p ^ 2) * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile (p ^ 2) n)))
  rw [primeSquareTrial_ramanujan hp hn0]
  simp only [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient one_pos,
    normalizedRamanujanMode_eq_coefficient hp.pos,
    normalizedRamanujanMode_eq_coefficient (pow_pos hp.pos 2), flipTrialCoeff, ite_true,
    if_neg h1p.symm, if_neg (Ne.symm h1q), if_neg hpq.symm, Nat.totient_one,
    Nat.cast_one, Real.sqrt_one]
  have h1 := ht p hp.pos
  have h2 := ht (p ^ 2) (pow_pos hp.pos 2)
  field_simp
  ring

/-- **A fixed overlap sees the flip once the trial energy is below the gain.** -/
theorem eventually_flip_negative_of_energy {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {p : ℕ} (hp : p.Prime)
    {c : ℝ} (hc : 0 < c) (hneg : flipTrialEnergy φ c p + flipGain p < 0) :
    ∀ᶠ N : ℕ in atTop, weilQuadTw (ArithmeticCountingPositivity.primeFlipWeight p)
      (atomicTest N (fun n => primeSquareTrial p n / Real.sqrt n) (atomDilate φ (c / N))) < 0 := by
  set S := flipTrialConductors p
  have hS := flipTrialConductors_pos hp
  set y : ∀ N : ℕ, EuclideanSpace ℝ (PrimeHorizonIndex N) := fun N =>
    ∑ m ∈ S, flipTrialCoeff p m • normalizedRamanujanHorizonVector m N with hy
  have hE := tendsto_inner_sum_quasimodes (φ := φ) (c := c) (E := completedConductorEnergy φ c) S hS
    (flipTrialCoeff p) fun m hm =>
      CriticalArithmeticCorrelationTheory.tendsto_completeWeilMatrix_ramanujan_quasimode_norm
        hφ hsupp hM hc (hS m hm)
  have hB := tendsto_sharpFlipBound hp
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hW : Tendsto (fun N : ℕ => 144 * c * Real.log p / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hQ := (hE.add hB).add hW
  rw [add_zero] at hQ
  have hlt := hQ.eventually (gt_mem_nhds hneg)
  filter_upwards [hlt, eventually_ge_atTop 2, eventually_ge_atTop ⌈c⌉₊] with N hQN hN2 hNc
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN : c ≤ N := (Nat.le_ceil c).trans (by exact_mod_cast hNc)
  have hw0 : 0 < c / N := div_pos hc hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr hcN
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw0
  set g := atomDilate φ (c / N) with hgdef
  set G0 := ∫ u, g u ^ 2 with hG0def
  have hG0 : 0 < G0 := by rw [hG0def, hgdef, integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  set x : ℕ → ℝ := fun n => primeSquareTrial p n / Real.sqrt n with hxdef
  have hx : ∀ n ∈ Icc 1 N, |x n| ≤ 1 / Real.sqrt n := fun n _ => by
    rw [hxdef, abs_div, abs_primeSquareTrial, abs_of_nonneg (Real.sqrt_nonneg _)]
  -- the three pieces of the flipped form
  have heq := weilQuadTw_flip_sub_eq hg hgc hgsupp hw0.le p N x
  have hD : atomicWeilForm N x - atomicWeilForm N (fun n => finiteFlip {p} n * x n) ≤
      sharpFlipBound p N := by
    have h := primeSquareTrial_prime_correction_le_sharp hp N
    have hfun : (fun n => finiteFlip {p} n * x n) =
        fun n => finiteFlip {p} n * primeSquareTrial p n / Real.sqrt n := by
      funext n; rw [hxdef]; ring
    rw [hfun]
    exact h
  have hWin := abs_flipWindow_le hg.continuous hgc hgsupp hw0 hw1 hp
    (lagRange (Real.log N + c / N + 1)) N hx
  have hwN : c / N * N = c := by field_simp
  rw [hwN] at hWin
  -- `ζ`'s energy of the trial
  have hzeta : weilQuad (atomicTest N x g) = G0 * (Real.log N * ⟪Matrix.toEuclideanLin
      (completeWeilMatrix φ c N) (y N), y N⟫) := by
    have h := completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN1
      (WithLp.toLp 2 (fun n : PrimeHorizonIndex N => x n))
    rw [← atomicTest_restrict] at h
    have htrial := trial_eq_sqrt_log_smul hp hN2
    have hsq : Real.sqrt (Real.log N) * Real.sqrt (Real.log N) = Real.log N :=
      Real.mul_self_sqrt hL.le
    have hinner : ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N)
        (WithLp.toLp 2 (fun n : PrimeHorizonIndex N => x n)),
        WithLp.toLp 2 (fun n : PrimeHorizonIndex N => x n)⟫ =
        Real.log N * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (y N), y N⟫ := by
      change ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N)
        (WithLp.toLp 2 (fun n : PrimeHorizonIndex N => primeSquareTrial p n / Real.sqrt n)),
        WithLp.toLp 2 (fun n : PrimeHorizonIndex N => primeSquareTrial p n / Real.sqrt n)⟫ = _
      rw [htrial, map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, hsq]
    rw [hinner] at h
    rw [h, ← hgdef, ← hG0def]
    field_simp
  have hbound : weilQuadTw (ArithmeticCountingPositivity.primeFlipWeight p) (atomicTest N x g) ≤
      G0 * Real.log N * (⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (y N), y N⟫ +
        sharpFlipBound p N / Real.log N + 144 * c * Real.log p / Real.log N) := by
    have h1 := mul_le_mul_of_nonneg_left hD hG0.le
    have h2 := (abs_le.mp hWin).2
    have : G0 * Real.log N * (⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (y N), y N⟫ +
        sharpFlipBound p N / Real.log N + 144 * c * Real.log p / Real.log N) =
        G0 * (Real.log N * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (y N), y N⟫) +
          G0 * sharpFlipBound p N + 144 * c * Real.log p * G0 := by
      field_simp
    rw [this]
    linarith
  exact hbound.trans_lt (mul_neg_of_pos_of_neg (mul_pos hG0 hL) hQN)

/-- **Every flipped prime is seen at a finite overlap.** For every admissible profile and every
prime `p` there is `c₀` such that at every overlap `c ≥ c₀` the flipped Weil form is
eventually negative on the prime-square trial: the completed energies of its conductors vanish
as `c → ∞`, while the flip keeps its arithmetic gain. -/
theorem exists_flip_negative_at_every_large_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {p : ℕ} (hp : p.Prime) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c, c₀ ≤ c → ∀ᶠ N : ℕ in atTop,
      weilQuadTw (ArithmeticCountingPositivity.primeFlipWeight p)
        (atomicTest N (fun n => primeSquareTrial p n / Real.sqrt n) (atomDilate φ (c / N))) < 0 := by
  have hT : Tendsto (fun c => flipTrialEnergy φ c p) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (flipTrialConductors p) fun m _ =>
      (tendsto_completedConductorEnergy_atTop hφ hsupp hM m).const_mul (flipTrialCoeff p m ^ 2)
    simpa only [flipTrialEnergy, mul_zero, sum_const_zero] using h
  have hev := (hT.add_const (flipGain p)).eventually
    (gt_mem_nhds (by rw [zero_add]; exact flipGain_neg hp))
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp hev
  refine ⟨max c₁ 1, by positivity, fun c hc => ?_⟩
  exact eventually_flip_negative_of_energy hφ hsupp hM hp (by linarith [le_max_right c₁ 1])
    (hc₁ c ((le_max_left _ _).trans hc))

/-- **Selectivity at every large overlap.** For the tilted unit spline and every prime `p`,
beyond a finite overlap the complete Weil form of `ζ` is eventually positive definite while the
form of the `p`-flipped twin is eventually negative on the prime-square trial. -/
theorem tiltedUnitSpline_flip_selective {p : ℕ} (hp : p.Prime) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c, c₀ ≤ c →
      (∀ᶠ N : ℕ in atTop, (completeWeilMatrix tiltedUnitSpline c N).PosDef) ∧
      ∀ᶠ N : ℕ in atTop, weilQuadTw (ArithmeticCountingPositivity.primeFlipWeight p)
        (atomicTest N (fun n => primeSquareTrial p n / Real.sqrt n)
          (atomDilate tiltedUnitSpline (c / N))) < 0 := by
  obtain ⟨c₀, hc₀, h⟩ := exists_flip_negative_at_every_large_overlap contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hp
  exact ⟨c₀, hc₀, fun c hc => ⟨CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef
    (hc₀.trans_le hc), h c hc⟩⟩

end Trial

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
