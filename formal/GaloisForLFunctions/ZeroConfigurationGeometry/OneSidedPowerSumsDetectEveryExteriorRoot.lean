import GaloisForLFunctions.ZeroConfigurationGeometry.BoundedImagesCertifyPurity

/-!
# One-sided power sums detect every exterior root

Simultaneous return of all nonzero phases makes every summand have nonnegative
real part. An exterior root then forces arbitrarily large real power sums.
Thus even an eventual upper bound on their real parts forces the unit-disk bound.
-/

noncomputable section
open Complex Filter Topology

namespace GaloisForLFunctions.ZeroConfigurationGeometry

private def unitPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

private theorem norm_unitPhase (z : ℂ) : ‖unitPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp only [unitPhase, if_pos hz, norm_one]
  · rw [unitPhase, if_neg hz, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hz)]

private theorem re_pow_ge_of_phase_return {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hret : ‖unitPhase z ^ n - 1‖ < 1 / 2) : ‖z‖ ^ n / 2 ≤ (z ^ n).re := by
  by_cases hz : z = 0
  · simp only [hz, zero_pow hn, norm_zero, zero_div, Complex.zero_re, le_refl]
  have hnorm : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hid : z ^ n = ((‖z‖ : ℂ) ^ n) * unitPhase z ^ n := by
    rw [unitPhase, if_neg hz, div_pow, mul_div_cancel₀ _ (pow_ne_zero n hnorm)]
  have hre : 1 / 2 ≤ (unitPhase z ^ n).re := by
    have h := Complex.abs_re_le_norm (unitPhase z ^ n - 1)
    rw [Complex.sub_re, Complex.one_re] at h
    linarith only [h, hret, neg_abs_le ((unitPhase z ^ n).re - 1)]
  rw [hid, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith only [mul_le_mul_of_nonneg_left hre (pow_nonneg (norm_nonneg z) n)]

private theorem re_sum_map_nonneg (W : Multiset ℂ) (f : ℂ → ℂ)
    (h : ∀ z ∈ W, 0 ≤ (f z).re) : 0 ≤ (W.map f).sum.re := by
  induction W using Multiset.induction_on with
  | empty => simp
  | cons z W ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_re]
    exact add_nonneg (h z (Multiset.mem_cons_self _ _))
      (ih fun w hw => h w (Multiset.mem_cons_of_mem hw))

/-- Arbitrarily late common phase returns give a real lower bound from any chosen root. -/
theorem exists_large_re_powerSum (W : Multiset ℂ) (m₀ : ℕ) :
    ∃ n, m₀ ≤ n ∧ 0 < n ∧
      ∀ z ∈ W, ‖z‖ ^ n / 2 ≤ (W.map fun w => w ^ n).sum.re := by
  obtain ⟨n, hn, hret⟩ := exists_simultaneous_return (W.map unitPhase)
    (fun u hu => by obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hu; exact norm_unitPhase z)
    (max m₀ 1)
  have hn0 : n ≠ 0 := by omega
  have hw (z : ℂ) (hz : z ∈ W) : ‖z‖ ^ n / 2 ≤ (z ^ n).re :=
    re_pow_ge_of_phase_return hn0 (hret _ (Multiset.mem_map_of_mem unitPhase hz))
  refine ⟨n, (le_max_left _ _).trans hn, Nat.pos_of_ne_zero hn0, fun z hz => ?_⟩
  obtain ⟨V, hV⟩ := Multiset.exists_cons_of_mem hz
  have hVpos : 0 ≤ (V.map fun w => w ^ n).sum.re :=
    re_sum_map_nonneg V _ fun w hmem => (by positivity : 0 ≤ ‖w‖ ^ n / 2).trans
      (hw w (by rw [hV]; exact Multiset.mem_cons_of_mem hmem))
  have hzlow := hw z hz
  rw [hV, Multiset.map_cons, Multiset.sum_cons, Complex.add_re]
  exact hzlow.trans (le_add_of_nonneg_right hVpos)

/-- An exterior root makes the real power sums exceed every bound beyond every cutoff. -/
theorem exists_re_powerSum_gt (W : Multiset ℂ) {z : ℂ} (hz : z ∈ W)
    (hlarge : 1 < ‖z‖) (C : ℝ) (m₀ : ℕ) :
    ∃ n, m₀ ≤ n ∧ 0 < n ∧ C < (W.map fun w => w ^ n).sum.re := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * C) hlarge
  obtain ⟨n, hn, hn0, hsum⟩ := exists_large_re_powerSum W (max m₀ N)
  have hpow := pow_le_pow_right₀ hlarge.le ((le_max_right m₀ N).trans hn)
  refine ⟨n, (le_max_left _ _).trans hn, hn0, ?_⟩
  linarith only [hN, hpow, hsum z hz]

/-- Eventual one-sided boundedness of real power sums is equivalent to the unit-disk bound. -/
theorem roots_norm_le_one_iff_eventually_re_powerSum_bounded (W : Multiset ℂ) :
    (∀ z ∈ W, ‖z‖ ≤ 1) ↔
      ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (W.map fun w => w ^ n).sum.re ≤ C := by
  constructor
  · intro hW
    refine ⟨W.card, Filter.Eventually.of_forall fun n => ?_⟩
    apply (Complex.re_le_norm _).trans
    simpa only [mul_one] using norm_sum_map_le W (fun w => w ^ n)
      (B := 1) (fun w hw => by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hW w hw))
  · rintro ⟨C, hC⟩ z hz
    by_contra h
    obtain ⟨N, hN⟩ := eventually_atTop.mp hC
    obtain ⟨n, hn, _, hsum⟩ := exists_re_powerSum_gt W hz (not_le.mp h) C N
    exact (hN n hn).not_gt hsum

end GaloisForLFunctions.ZeroConfigurationGeometry
