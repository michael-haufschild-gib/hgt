import GaloisForLFunctions.ArithmeticPositiveDuality.TheAbelSpectrumAtUnitDensityIsRigid
import GaloisForLFunctions.ArithmeticPositiveDuality.ApproximateFunctionalEquationNearIntegers

/-!
# Integrable functional-equation defects at unit density are rigid

For a positive discrete spectrum beginning at 1, with each atom of mass at least 1, an
integrable uncompleted Riemann functional-equation defect and pole residue at most 1 force
the positive-integer counting measure. The defect contributes no radial residue to the
Laplace identity. Positivity then saturates every atom's cosine bound.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger
open RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- An integrable defect has no radial residue at any point of the imaginary axis. -/
theorem tendsto_mul_integrable_defectLaplace {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hgi : Integrable g) (y : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + (y : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
  let M : ℝ := ∫ t, ‖g t‖
  have hM : 0 ≤ M := integral_nonneg fun t => norm_nonneg (g t)
  refine squeeze_zero_norm'
    (a := fun ε : ℝ => (3 / (2 * Real.pi) * M) * ε ^ (1 / 2 : ℝ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    let z : ℂ := (ε : ℂ) + (y : ℂ) * I
    have hz : 0 < z.re := by simpa [z] using hε0
    have hnorm : ε ≤ ‖z‖ := by
      have h := Complex.abs_re_le_norm z
      simpa [z, abs_of_pos hε0] using h
    have hδ : 0 < 2 * (z.re / ‖z‖) := mul_pos two_pos (pos_re_div_norm hz)
    have hmass : abelMass g (2 * (z.re / ‖z‖)) ≤ M := by
      apply integral_mono (integrable_abelMass hgm.aestronglyMeasurable hgb hδ) hgi.norm
      intro t
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg hδ.le (abs_nonneg t))))
    have hpow : ‖z‖ ^ (-(1 / 2 : ℝ)) ≤ ε ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hε0 hnorm (by norm_num)
    have hbound : ‖defectLaplace g z‖ ≤
        3 / (2 * Real.pi) * ε ^ (-(1 / 2 : ℝ)) * M :=
      (norm_defectLaplace_le hgm.aestronglyMeasurable hgb hz).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hmass
          (integral_nonneg fun t => by positivity) (by positivity))
    have he : ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' hε0.le (by norm_num)]
      norm_num
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    calc ε * ‖defectLaplace g z‖ ≤ ε * (3 / (2 * Real.pi) * ε ^ (-(1 / 2 : ℝ)) * M) :=
          mul_le_mul_of_nonneg_left hbound hε0.le
      _ = (3 / (2 * Real.pi) * M) * ε ^ (1 / 2 : ℝ) := by rw [← he]; ring
  · have h := (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at h
    simpa using (h.mono_left nhdsWithin_le_nhds).const_mul (3 / (2 * Real.pi) * M)

/-- The defective Laplace identity for arbitrary nonnegative discrete spectra. -/
theorem freqSeries_eq_of_integrable_theta_defect {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℂ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {z : ℂ} (hz : 0 < z.re) :
    freqSeries (fun n => (a n : ℂ)) lam z = freqDual (fun n => (a n : ℂ)) lam z +
      -β / (Real.pi * z) + β + defectLaplace g z := by
  let ν : Measure ℝ := Measure.sum fun n : ℕ => ENNReal.ofReal (a n) • Measure.dirac (lam n)
  have hc : ∀ n, ENNReal.ofReal (a n) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hsupp : ν (Iio 1) = 0 := by
    dsimp only [ν]
    rw [Measure.sum_apply _ measurableSet_Iio]
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_Iio,
      Set.indicator_of_notMem (by simp [hlam n]), mul_zero]
  have hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν := by
    refine integrable_sum_dirac hc (ha.congr fun n => ?_)
    have hl : 0 < lam n := lt_of_lt_of_le zero_lt_one (hlam n)
    rw [ENNReal.toReal_ofReal (ha0 n), Real.norm_eq_abs, abs_of_nonneg (by positivity),
      mul_one_div]
  have htheta : ∀ x, measureTheta ν x = freqTheta (fun n => (a n : ℂ)) lam x := by
    intro x
    unfold measureTheta freqTheta
    dsimp only [ν]
    rw [integral_sum_dirac hc]
    exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (ha0 n), Complex.real_smul]
  have hseries : measureSeries ν z = freqSeries (fun n => (a n : ℂ)) lam z := by
    unfold measureSeries freqSeries
    dsimp only [ν]
    rw [integral_sum_dirac hc]
    exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (ha0 n), Complex.real_smul]; ring
  have hdual : measureDual ν z = freqDual (fun n => (a n : ℂ)) lam z := by
    unfold measureDual freqDual
    dsimp only [ν]
    rw [integral_sum_dirac hc]
    exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (ha0 n), Complex.real_smul]
  rw [← hseries, ← hdual]
  exact measureSeries_eq_of_theta_defect hsupp hmom hgm hgb
    (fun x hx => by rw [htheta x, htheta x⁻¹]; exact hθ x hx) hz

/-- At a positive height the defective Laplace identity has exactly the original atomic residue. -/
private theorem abel_limit_of_defective_series {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℂ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hL : ∀ z : ℂ, 0 < z.re →
      freqSeries (fun n => (a n : ℂ)) lam z = freqDual (fun n => (a n : ℂ)) lam z +
        -β / (Real.pi * z) + β + defectLaplace g z)
    {y : ℝ} (hy : 0 < y) {w : ℂ}
    (hres : Tendsto (fun ε : ℝ => (ε : ℂ) * freqSeries (fun n => (a n : ℂ)) lam
      ((ε : ℂ) + (y : ℂ) * I)) (𝓝[>] 0) (𝓝 w)) :
    Tendsto (abelCos a lam y) (𝓝[>] 0) (𝓝 w.re) := by
  have hy0 : (y : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hy.ne') I_ne_zero
  have hcont : ContinuousAt (fun ε : ℝ => (ε : ℂ) * β /
      (Real.pi * ((ε : ℂ) + (y : ℂ) * I)) - (ε : ℂ) * β) 0 := by
    refine (ContinuousAt.div (by fun_prop) (by fun_prop) ?_).sub (by fun_prop)
    simpa using mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hy0
  have hlin : Tendsto (fun ε : ℝ => (ε : ℂ) * β /
      (Real.pi * ((ε : ℂ) + (y : ℂ) * I)) - (ε : ℂ) * β) (𝓝[>] 0) (𝓝 0) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_abelCos_of_tendsto hlam ha0 ha
  have hh := (hres.add hlin).sub (tendsto_mul_integrable_defectLaplace hgm hgb hgi y)
  simp only [add_zero, sub_zero] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hL _ (by simpa using hε)]
  ring

/-- An integrable defect cannot deform a spectrum whose pole residue is at most one.
Every atom has mass at least one; positivity makes the mass and density inequalities equalities. -/
theorem integer_spectrum_of_integrable_theta_defect {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (ha1 : ∀ n, 1 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ} (hβ : β ≤ 1 / 2)
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    β = 1 / 2 ∧ ∀ n, lam n = n + 1 ∧ a n = 1 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => lt_of_lt_of_le one_pos (hlam n)
  have ha0 : ∀ n, 0 ≤ a n := fun n => le_trans zero_le_one (ha1 n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_integrable_theta_defect ha0 hlam ha hgm hgb hθ
    (z := z) hz
  have hC0 : Tendsto (abelCos a lam 0) (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
    have hres := tendsto_mul_freqSeries_ofReal (a := fun n => (a n : ℂ)) hlam haC
    have hlin : Tendsto (fun ε : ℝ => (β : ℂ) / Real.pi - (ε : ℂ) * β)
        (𝓝[>] 0) (𝓝 ((β : ℂ) / Real.pi)) := by
      simpa using ((by fun_prop : Continuous fun ε : ℝ =>
        (β : ℂ) / Real.pi - (ε : ℂ) * β).tendsto 0).mono_left nhdsWithin_le_nhds
    have hh := (hres.add hlin).sub (tendsto_mul_integrable_defectLaplace hgm hgb hgi 0)
    simp only [zero_add, sub_zero, Complex.ofReal_zero, zero_mul, add_zero] at hh
    have hF : Tendsto (fun ε : ℝ => (ε : ℂ) * freqDual (fun n => (a n : ℂ)) lam
        ((ε : ℂ) + ((0 : ℝ) : ℂ) * I)) (𝓝[>] 0) (𝓝 ((β : ℂ) / Real.pi)) := by
      refine hh.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have he : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      rw [hL _ (by simpa using hε)]
      field_simp
      ring
    have hh := tendsto_abelCos_of_tendsto hlam ha0 ha hF
    simpa only [Complex.div_ofReal_re] using hh
  have hatom : ∀ m, Tendsto (abelCos a lam (lam m)) (𝓝[>] 0)
      (𝓝 (a m / (2 * Real.pi))) := by
    intro m
    obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos m
    have hres := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
      (hpos m) hc hsep
    have hh := abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL (hpos m) hres
    have hre : ((a m : ℂ) / (2 * Real.pi)).re = a m / (2 * Real.pi) := by
      rw [show ((a m : ℂ) / (2 * Real.pi)) = ((a m / (2 * Real.pi) : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_re]
    rwa [hre] at hh
  have hmass : ∀ m, a m ≤ 2 * β := by
    intro m
    have hh : a m / (2 * Real.pi) ≤ β / Real.pi := by
      refine le_of_tendsto_of_tendsto (hatom m) hC0 ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact abelCos_le_of_le hlam ha0 ha hε fun n => by simpa using Real.cos_le_one _
    have hp := Real.pi_pos
    rw [div_le_div_iff₀ (by positivity) hp] at hh
    nlinarith only [hh, hp]
  have hb : β = 1 / 2 := by linarith only [hmass 0, ha1 0, hβ]
  have hunit : ∀ m, a m = 1 := fun m => by linarith only [hmass m, ha1 m, hβ]
  refine ⟨hb, integer_spectrum_of_unit_abel_limits hmono hlam0 hunit ha ?_ hatom ?_⟩
  · convert hC0 using 1 <;> rw [hb] <;> congr 1 <;> ring
  · intro y c hy hc hsep
    have hres := tendsto_mul_freqSeries_gap (a := fun n => (a n : ℂ)) hlam haC hy.le hc hsep
    simpa using abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL hy hres

end GaloisForLFunctions.ArithmeticPositiveDuality
