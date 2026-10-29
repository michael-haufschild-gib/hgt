import GaloisForLFunctions.HTGeometry.ExponentialLatticeWeight
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Holomorphic affine degree sums and their leading term

At central level four, degree rotation gives quadratic decay uniformly on a
spectral strip. Exponentially bounded coefficient families therefore have
holomorphic sums. Increasing rotation isolates their index-zero coefficient.
-/

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1

noncomputable section

/-- A strip joining the Godement chamber to the arithmetic pole line at level four. -/
def levelFourStrip : Set ℂ := {s | -1 < s.re ∧ s.re < 2}

lemma isOpen_levelFourStrip : IsOpen levelFourStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma abs_re_le_two_of_mem_levelFourStrip (s : ℂ) (hs : s ∈ levelFourStrip) :
    |s.re| ≤ 2 := by
  rcases hs with ⟨h₁, h₂⟩
  exact abs_le.mpr ⟨by linarith only [h₁], h₂.le⟩

private lemma abs_intCast_le_sq (n : ℤ) : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
  by_cases hn : 0 ≤ n
  · by_cases hz : n = 0
    · subst n; norm_num
    have h₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
    rw [abs_of_nonneg (by linarith only [h₁])]
    have hm := mul_nonneg (show (0 : ℝ) ≤ n by linarith only [h₁]) (sub_nonneg.mpr h₁)
    nlinarith only [hm]
  · have h₁ : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ (-1 : ℤ) by omega)
    rw [abs_of_nonpos (by linarith only [h₁])]
    have hm := mul_nonneg (show (0 : ℝ) ≤ -(n : ℝ) by linarith only [h₁])
      (show (0 : ℝ) ≤ -(n : ℝ) - 1 by linarith only [h₁])
    nlinarith only [hm]

/-- The genuine quadratic affine degree factor on the slice `(4-s,s)`. -/
def degreeFourFactor (R : ℝ) (s : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (-(R : ℂ) * (4 * (n : ℂ) ^ 2 + (n : ℂ) * s))

@[simp] lemma degreeFourFactor_zero (R : ℝ) (s : ℂ) : degreeFourFactor R s 0 = 1 := by
  simp only [degreeFourFactor, Int.cast_zero, pow_two,
    mul_zero, zero_mul, add_zero, Complex.exp_zero]

lemma degreeFourFactor_analytic (R : ℝ) (n : ℤ) (s : ℂ) :
    AnalyticAt ℂ (fun z => degreeFourFactor R z n) s := by
  unfold degreeFourFactor
  fun_prop

lemma norm_degreeFourFactor (R : ℝ) (s : ℂ) (n : ℤ) :
    ‖degreeFourFactor R s n‖ = Real.exp (-R * (4 * (n : ℝ) ^ 2 + (n : ℝ) * s.re)) := by
  rw [degreeFourFactor, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.add_re,
    Complex.intCast_re, Complex.intCast_im,
    pow_two, Complex.mul_im, mul_zero, add_zero]
  norm_num

lemma degreeFour_decay (s : ℂ) (hs : s ∈ levelFourStrip) (n : ℤ) :
    2 * (n : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 + (n : ℝ) * s.re := by
  have hnorm := abs_re_le_two_of_mem_levelFourStrip s hs
  have hprod : -(2 * |(n : ℝ)|) ≤ (n : ℝ) * s.re := by
    calc
      -(2 * |(n : ℝ)|) ≤ -(|(n : ℝ)| * |s.re|) := by
        nlinarith only [hnorm, abs_nonneg (n : ℝ)]
      _ = -|(n : ℝ) * s.re| := by rw [abs_mul]
      _ ≤ (n : ℝ) * s.re := neg_abs_le _
  linarith only [hprod, abs_intCast_le_sq n]

lemma norm_degreeFourFactor_le (R : ℝ) (hR : 0 ≤ R) (s : ℂ)
    (hs : s ∈ levelFourStrip) (n : ℤ) :
    ‖degreeFourFactor R s n‖ ≤ Real.exp (-2 * R * (n : ℝ) ^ 2) := by
  rw [norm_degreeFourFactor]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (degreeFour_decay s hs n) hR
  nlinarith only [h]

/-- Completing the square bounds every exponential-quadratic integer sequence by a geometric one. -/
theorem summable_affineGaussian (a : ℝ) (ha : 0 < a) (b c : ℝ) :
    Summable (fun n : ℤ => Real.exp (c + b * |(n : ℝ)| - a * (n : ℝ) ^ 2)) := by
  have hgeom : Summable (fun n : ℤ => Real.exp (-|(n : ℝ)|)) := by
    simpa only [neg_one_mul] using
      GaloisForLFunctions.HTGeometry.summable_exp_neg_abs_int (c := 1) zero_lt_one
  have hmajor := hgeom.mul_left (Real.exp (c + (b + 1) ^ 2 / (4 * a)))
  apply hmajor.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro n
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq := sq_nonneg (2 * a * |(n : ℝ)| - (b + 1))
  simp only [sub_sq, mul_pow, sq_abs] at hsq
  have hcomplete : (b + 1) * |(n : ℝ)| - a * (n : ℝ) ^ 2 ≤
      (b + 1) ^ 2 / (4 * a) := by
    apply (le_div_iff₀ (show 0 < 4 * a by positivity)).mpr
    nlinarith only [hsq]
  linarith only [hcomplete]

/-- A coefficient family summed against the affine degree factor. -/
def degreeFourSeries (f : ℤ → ℂ → ℂ) (R : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℤ, f n s * degreeFourFactor R s n

lemma degreeFourTerm_bound {f : ℤ → ℂ → ℂ} {A B : ℝ}
    (hf : ∀ n s, s ∈ levelFourStrip → ‖f n s‖ ≤ Real.exp (A + B * |(n : ℝ)|))
    (R : ℝ) (hR : 0 ≤ R) (s : ℂ) (hs : s ∈ levelFourStrip) (n : ℤ) :
    ‖f n s * degreeFourFactor R s n‖ ≤
      Real.exp (A + B * |(n : ℝ)| - 2 * R * (n : ℝ) ^ 2) := by
  rw [norm_mul]
  calc
    _ ≤ Real.exp (A + B * |(n : ℝ)|) * Real.exp (-2 * R * (n : ℝ) ^ 2) :=
      mul_le_mul (hf n s hs) (norm_degreeFourFactor_le R hR s hs n)
        (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma summable_norm_degreeFourSeries {f : ℤ → ℂ → ℂ} {A B : ℝ}
    (hf : ∀ n s, s ∈ levelFourStrip → ‖f n s‖ ≤ Real.exp (A + B * |(n : ℝ)|))
    (R : ℝ) (hR : 0 < R) (s : ℂ) (hs : s ∈ levelFourStrip) :
    Summable (fun n : ℤ => ‖f n s * degreeFourFactor R s n‖) := by
  exact (summable_affineGaussian (2 * R) (by positivity) B A).of_nonneg_of_le
    (fun _ => norm_nonneg _) (degreeFourTerm_bound hf R hR.le s hs)

/-- Uniform quadratic decay makes the complete series holomorphic on the continuation strip. -/
theorem degreeFourSeries_analyticOn {f : ℤ → ℂ → ℂ} {A B : ℝ}
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) levelFourStrip)
    (hb : ∀ n s, s ∈ levelFourStrip → ‖f n s‖ ≤ Real.exp (A + B * |(n : ℝ)|))
    (R : ℝ) (hR : 0 < R) : AnalyticOnNhd ℂ (degreeFourSeries f R) levelFourStrip := by
  have hsum : SummableLocallyUniformlyOn
      (fun n s => f n s * degreeFourFactor R s n) levelFourStrip := by
    apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_levelFourStrip
    intro K hK _
    refine ⟨fun n : ℤ => Real.exp (A + B * |(n : ℝ)| - (2 * R) * (n : ℝ) ^ 2),
      summable_affineGaussian (2 * R) (by positivity) B A, ?_⟩
    intro n s hs
    exact degreeFourTerm_bound hb R hR.le s (hK hs) n
  exact (SummableLocallyUniformlyOn.differentiableOn isOpen_levelFourStrip hsum
    (fun n s hs => ((hf n s hs).mul (degreeFourFactor_analytic R n s)).differentiableAt)).analyticOnNhd
      isOpen_levelFourStrip

lemma degreeFourFactor_tendsto_zero (s : ℂ) (hs : s ∈ levelFourStrip)
    (n : ℤ) (hn : n ≠ 0) :
    Tendsto (fun R : ℝ => degreeFourFactor R s n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_degreeFourFactor]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hc : 0 < 4 * (n : ℝ) ^ 2 + (n : ℝ) * s.re :=
    lt_of_lt_of_le (mul_pos (by norm_num) (sq_pos_of_ne_zero hn')) (degreeFour_decay s hs n)
  have ht : Tendsto (fun R : ℝ => R * (4 * (n : ℝ) ^ 2 + (n : ℝ) * s.re)) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos hc).mpr tendsto_id
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp ht using 1
  funext R
  congr 1
  ring

/-- Strong degree rotation extracts the index-zero coefficient from the infinite series. -/
theorem degreeFourSeries_tendsto {f : ℤ → ℂ → ℂ} {A B : ℝ}
    (hf : ∀ n s, s ∈ levelFourStrip → ‖f n s‖ ≤ Real.exp (A + B * |(n : ℝ)|))
    (s : ℂ) (hs : s ∈ levelFourStrip) :
    Tendsto (fun R : ℝ => degreeFourSeries f R s) atTop (𝓝 (f 0 s)) := by
  have hpoint (n : ℤ) : Tendsto (fun R : ℝ => f n s * degreeFourFactor R s n)
      atTop (𝓝 (if n = 0 then f 0 s else 0)) := by
    by_cases hn : n = 0
    · subst n
      simp only [degreeFourFactor_zero, mul_one, ite_true]
      exact tendsto_const_nhds
    · rw [if_neg hn]
      simpa only [mul_zero] using (degreeFourFactor_tendsto_zero s hs n hn).const_mul (f n s)
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ n : ℤ,
      ‖f n s * degreeFourFactor R s n‖ ≤
        Real.exp (A + B * |(n : ℝ)| - 2 * (n : ℝ) ^ 2) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR n
    apply (degreeFourTerm_bound hf R (by linarith only [hR]) s hs n).trans
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hR (sq_nonneg (n : ℝ))
    nlinarith only [hmul]
  have hlim := tendsto_tsum_of_dominated_convergence
    (summable_affineGaussian 2 (by norm_num) B A) hpoint hbound
  simpa only [degreeFourSeries, tsum_ite_eq] using hlim

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1
