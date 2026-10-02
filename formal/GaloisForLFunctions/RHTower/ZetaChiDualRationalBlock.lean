import GaloisForLFunctions.RHTower.ZetaChiDualRatioAtom
import GaloisForLFunctions.RHTower.ZetaChiRationalSaddleCancellation

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


private theorem continuous_dual_ratio_atom {s : ℂ} (hs : s.re < 1) (n : ℕ) (ξ : ℝ) :
    Continuous (fun t : ℝ => zetaChiDualInteriorAtom s n t *
      bourgainOscillation (t * Real.log ξ)) := by
  have hchi : Continuous (fun t : ℝ => zetaChi (s + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hG : Gammaℝ (1 - (s + (t : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simpa using sub_pos.mpr hs
    have hpath : Continuous (fun u : ℝ => s + (u : ℂ) * I) := by fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => s + (u : ℂ) * I) (x := t)
      (zetaChi_analyticAt hG).continuousAt hpath.continuousAt
  unfold zetaChiDualInteriorAtom bourgainOscillation
  exact ((hchi.mul continuous_const).mul (by fun_prop)).mul (by fun_prop)

private theorem norm_integral_weighted_sum_sub_main
    (S : Finset ℕ) (u a : ℕ → ℂ) (f : ℕ → ℝ → ℂ) (l v e : ℝ)
    (hi : ∀ n ∈ S, IntervalIntegrable (f n) volume l v)
    (hb : ∀ n ∈ S, ‖(∫ t in l..v, f n t) - a n‖ ≤ e) :
    ‖(∫ t in l..v, ∑ n ∈ S, u n * f n t) - ∑ n ∈ S, u n * a n‖ ≤
      e * ∑ n ∈ S, ‖u n‖ := by
  rw [intervalIntegral.integral_finsetSum (fun n hn => (hi n hn).const_mul (u n))]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ S, ‖u n * (∫ t in l..v, f n t) - u n * a n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖u n‖ * e := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (hb n hn) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Actual complete Gaussian-smoothed rational cross blocks cancel off the
divisibility diagonal. The full stationary remainder still pays every term. -/
theorem exists_zetaChi_dual_rational_block_integral_bound
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ a q A K : ℕ, 0 < q → ¬ q ∣ a → 0 < A →
      (∀ n ∈ Finset.range K,
        (m : ℝ) ^ 10 + (m : ℝ) ^ 6 ≤ 2 * Real.pi * (((a : ℝ) / q) * (A + n : ℕ)) ∧
        2 * Real.pi * (((a : ℝ) / q) * (A + n : ℕ)) + (m : ℝ) ^ 6 ≤ 2 * (m : ℝ) ^ 10) →
      ‖∫ t in (m : ℝ) ^ 10..(2 * (m : ℝ) ^ 10),
        ∑ n ∈ Finset.range K, smoothAFECutoff (((A + n : ℕ) : ℝ) / (m : ℝ) ^ 10) *
          zetaChiDualInteriorAtom s (A + n) t * bourgainOscillation (t * Real.log ((a : ℝ) / q))‖ ≤
        ‖(((a : ℝ) / q : ℝ) : ℂ) ^ (1 - s)‖ * (2 * Real.pi * q + (D / m) * K) := by
  obtain ⟨D, hD, hb⟩ := exists_zetaChi_dual_ratio_atom_disc_uniform c hr hc0 hc1
  refine ⟨D, hD, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with m hm hm1
  intro s hs a q A K hq hdiv hA hgeom
  have ha : 0 < a := by
    by_contra h
    have ha0 : a = 0 := by omega
    simp [ha0] at hdiv
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hN : 0 < (m : ℝ) ^ 10 := by positivity
  let ξ : ℝ := (a : ℝ) / q
  let Cξ : ℂ := (ξ : ℂ) ^ (1 - s)
  let u : ℕ → ℂ := fun n => smoothAFECutoff (((A + n : ℕ) : ℝ) / (m : ℝ) ^ 10)
  let phase : ℕ → ℂ := fun n => bourgainOscillation (2 * Real.pi * (a : ℝ) * (A + n : ℕ) / q)
  let f : ℕ → ℝ → ℂ := fun n t => zetaChiDualInteriorAtom s (A + n) t *
    bourgainOscillation (t * Real.log ξ)
  have hξ : 0 < ξ := div_pos haR hqR
  have hnpos (n : ℕ) : 0 < A + n := by omega
  have hpos (n : ℕ) : 0 < ((A + n : ℕ) : ℝ) / (m : ℝ) ^ 10 :=
    div_pos (by exact_mod_cast hnpos n) hN
  have hre : |s.re - c.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c) :
      |s.re - c.re| ≤ dist s c).trans hs
  have hs1 : s.re < 1 := by linarith [(abs_le.mp hre).2]
  have hi : ∀ n ∈ Finset.range K, IntervalIntegrable (f n) volume
      ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10) := fun n _ =>
    (continuous_dual_ratio_atom hs1 (A + n) ξ).intervalIntegrable _ _
  have herr : ∀ n ∈ Finset.range K,
      ‖(∫ t in (m : ℝ) ^ 10..(2 * (m : ℝ) ^ 10), f n t) -
        Cξ * (((2 * Real.pi : ℝ) : ℂ) * phase n)‖ ≤ ‖Cξ‖ * (D / m) := by
    intro n hn
    have hh := hm s hs (A + n) (hnpos n) ξ hξ (hgeom n hn).1 (hgeom n hn).2
    have he : 2 * Real.pi * (ξ * (A + n : ℕ)) =
        2 * Real.pi * (a : ℝ) * (A + n : ℕ) / q := by dsimp [ξ]; ring
    simpa only [he] using hh
  have he := norm_integral_weighted_sum_sub_main (Finset.range K) u
    (fun n => Cξ * (((2 * Real.pi : ℝ) : ℂ) * phase n)) f _ _ _ hi herr
  have hweight (n : ℕ) : ‖u n‖ ≤ 1 := by
    have heq : u n = (((u n).re : ℝ) : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using smoothAFECutoff_im_eq_zero (hpos n)
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (smoothAFECutoff_re_nonneg (hpos n))]
    exact smoothAFECutoff_re_le_one (hpos n)
  have hmass : ∑ n ∈ Finset.range K, ‖u n‖ ≤ (K : ℝ) := by
    simpa using Finset.sum_le_sum (fun n (_ : n ∈ Finset.range K) => hweight n)
  have hphasebound : ‖∑ n ∈ Finset.range K, u n * phase n‖ ≤ (q : ℝ) := by
    have hh := norm_sum_cutoff_bourgainOscillation_rational_saddle_le a q A K hq hdiv hA hN
    have hv : (smoothAFECutoff ((A : ℝ) / (m : ℝ) ^ 10)).re ≤ 1 :=
      smoothAFECutoff_re_le_one (div_pos (by exact_mod_cast hA) hN)
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hv hqR.le])
  have hmainEq : (∑ n ∈ Finset.range K, u n * (Cξ * (((2 * Real.pi : ℝ) : ℂ) * phase n))) =
      Cξ * ((2 * Real.pi : ℝ) : ℂ) * (∑ n ∈ Finset.range K, u n * phase n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hmain : ‖∑ n ∈ Finset.range K, u n * (Cξ * (((2 * Real.pi : ℝ) : ℂ) * phase n))‖ ≤
      ‖Cξ‖ * (2 * Real.pi) * q := by
    rw [hmainEq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left hphasebound (by positivity)
  let Z : ℂ := ∫ t in (m : ℝ) ^ 10..(2 * (m : ℝ) ^ 10), ∑ n ∈ Finset.range K, u n * f n t
  have htri : ‖Z‖ ≤
      ‖Z - ∑ n ∈ Finset.range K, u n * (Cξ * (((2 * Real.pi : ℝ) : ℂ) * phase n))‖ +
      ‖∑ n ∈ Finset.range K, u n * (Cξ * (((2 * Real.pi : ℝ) : ℂ) * phase n))‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (Z - ∑ n ∈ Finset.range K, u n * (Cξ * (((2 * Real.pi : ℝ) : ℂ) * phase n)))
      (∑ n ∈ Finset.range K, u n * (Cξ * (((2 * Real.pi : ℝ) : ℂ) * phase n)))
  have hnorm : ‖Z‖ ≤ ‖Cξ‖ * (2 * Real.pi * q + (D / m) * K) := by
    have hmass' := mul_le_mul_of_nonneg_left hmass (show 0 ≤ ‖Cξ‖ * (D / m) by positivity)
    change ‖Z - _‖ ≤ _ at he
    nlinarith only [htri, he, hmain, hmass']
  have hint : (∫ t in (m : ℝ) ^ 10..(2 * (m : ℝ) ^ 10),
        ∑ n ∈ Finset.range K, smoothAFECutoff (((A + n : ℕ) : ℝ) / (m : ℝ) ^ 10) *
          zetaChiDualInteriorAtom s (A + n) t * bourgainOscillation (t * Real.log ((a : ℝ) / q))) = Z := by
    apply intervalIntegral.integral_congr
    intro t _
    apply Finset.sum_congr rfl
    intro n _
    dsimp [u, f, ξ]
    ring
  rw [hint]
  exact hnorm

end RHTower
