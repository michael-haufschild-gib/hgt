import GaloisForLFunctions.RHTower.WeilWorkExposingRayCriticalBoundary
import GaloisForLFunctions.RHTower.EvenSectorPolarCompletion

/-!
# Boundary cancellation for actual critical arithmetic separators

The uniform twisted ceiling belongs to one holomorphic Dirichlet series.
Harnack therefore removes its quadratic boundary defect, without a Laurent
expansion or a lower bound. This is the arithmetic input for critical-cost
one-pole recovery, not a positivity or recovery premise.
-/

open Complex Filter Topology Set MeasureTheory
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilOneSided WeilHerglotz OddSector GaloisForLFunctions.HTGeometry

/-- Standard Dirichlet normalization of the raw arithmetic separator. -/
def criticalWeights (b : ℕ → ℝ) (n : ℕ) : ℝ := b n * Real.sqrt n

theorem summable_criticalWeights
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f))
    {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |criticalWeights b n| / (n : ℝ)^σ := by
  refine (summable_critical_separator_coefficients h (p := σ-1/2) (by linarith)).congr ?_
  intro n
  by_cases hn : n=0
  · subst n
    rw [Nat.cast_zero,Real.zero_rpow (by linarith : σ-1/2 ≠ 0)]
    simp [criticalWeights]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [criticalWeights,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_eq_rpow,Real.rpow_sub hn0]
  field_simp

private theorem summable_critical_lamC
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f))
    {z : ℂ} (hz : 1 < z.re) : LSeriesSummable (lamC (criticalWeights b)) z := by
  apply summable_norm_iff.mp
  refine (summable_criticalWeights h hz).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hn : n=0
  · simp only [if_pos hn]
    positivity
  rw [if_neg hn,lamC,Complex.norm_real,Real.norm_eq_abs]
  split_ifs
  · exact le_rfl
  · simp only [abs_zero,zero_div]
    positivity

private theorem re_criticalDirichlet
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f))
    {z : ℂ} (hz : 0 < z.re) :
    (EvenSector.polarDirichlet (criticalWeights b) z).re = criticalCosineSeries b z.re z.im := by
  unfold EvenSector.polarDirichlet LSeries criticalCosineSeries
  have hz1 : 1 < (1+z).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  rw [Complex.re_tsum (summable_critical_lamC h hz1)]
  apply tsum_congr
  intro n
  by_cases hn : 2 ≤ n
  · have hn0 : n ≠ 0 := by omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
    rw [LSeries.term_of_ne_zero hn0,lamC,if_pos hn,if_pos hn,div_eq_mul_inv,
      ← Complex.cpow_neg,Complex.re_ofReal_mul,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn0),
      ← Complex.ofReal_natCast n,← Complex.ofReal_log hnr.le,Complex.exp_re]
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.neg_re,Complex.neg_im,Complex.add_re,Complex.add_im,
      Complex.one_re,Complex.one_im,zero_mul,zero_add,sub_zero,add_zero,
      mul_neg,Real.cos_neg]
    rw [Real.rpow_def_of_pos hnr]
    dsimp [criticalWeights,criticalCosineCoeff]
    rw [mul_comm (Real.log (n:ℝ)) z.im]
    ring_nf
  · simp [LSeries.term_def,lamC,hn]

/-- The actual critical separator has no quadratic Dirichlet boundary defect. -/
theorem tendsto_critical_quadratic_zero
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f)) :
    Tendsto (fun s : ℝ => s^2 * oddDirichlet (criticalWeights b) s) (𝓝[>] 0) (𝓝 0) := by
  have ha : LSeries.abscissaOfAbsConv (lamC (criticalWeights b)) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      summable_critical_lamC h (by simpa using hy)
  have hd : DifferentiableOn ℂ (EvenSector.polarDirichlet (criticalWeights b))
      {z | 0 < z.re} := by
    intro z hz
    change 0 < z.re at hz
    have hr : (1 : ℝ) < (1+z).re := by
      simp only [Complex.add_re,Complex.one_re]
      linarith
    have ha' : LSeries.abscissaOfAbsConv (lamC (criticalWeights b)) < (1+z).re :=
      lt_of_le_of_lt ha (by exact_mod_cast hr)
    exact ((LSeries_hasDerivAt ha').differentiableAt.comp z
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1+w) z)).differentiableWithinAt
  obtain ⟨M,hM,hceil⟩ := critical_uniform_dirichlet_ceiling h
  obtain ⟨r,hr,hi⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hceil
  have ht := tendsto_sq_mul_re_zero_of_uniform_ceiling
    (hd.mono fun _ hz => hz.1) hM hr (fun z hz hzr => by
      rw [re_criticalDirichlet h hz]
      exact hi ⟨hz,hzr⟩ z.im)
  simpa only [EvenSector.polarDirichlet_ofReal,Complex.ofReal_re] using ht

end RHTower.ExposingRayTransfer
