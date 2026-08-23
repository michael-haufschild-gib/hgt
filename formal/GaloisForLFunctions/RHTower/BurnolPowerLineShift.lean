import GaloisForLFunctions.RHTower.BurnolPowerLineIntegral
import GaloisForLFunctions.RHTower.BurnolContourLimits
import GaloisForLFunctions.RHTower.MellinContinuationOrder

/-!
# Shifting the `k^{-s}` line integral across the pole at `s = 1`

The rectangle with vertical sides `Re s = σ` (`1/2 < σ < 1`) and `Re s = 2` contains exactly one
singularity of `M(f)(s)k^{-s}`: the simple pole of the head `d·a^{1−s}/(1−s)` at `s = 1`, whose
residue is `−d/k`.  Quick decrease kills the horizontal sides, so

`(1/2π)∫_{Re s = 2} − (1/2π)∫_{Re s = σ} = −d/k`,

and since the second integral is `d/k` (`BurnolPowerLineIntegral`), the integral on `Re s = 2`
vanishes.  This is the computation behind Burnol's Proposition 5.4.

## Main results

* `burnolPowIntegrand`, `laurentCoeff_burnolPowIntegrand_one`
* `burnolPowLine_two_eq_zero`
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The integrand -/

/-- The integrand of the shifted line integral. -/
def burnolPowIntegrand (G : ℂ → ℂ) (k : ℝ) : ℂ → ℂ :=
  fun s => G s * ((k : ℝ) : ℂ) ^ (-s)

theorem analyticAt_powKernel {k : ℝ} (hk : 0 < k) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => ((k : ℝ) : ℂ) ^ (-z)) s := by
  have hrw : (fun z : ℂ => ((k : ℝ) : ℂ) ^ (-z))
      = fun z : ℂ => Complex.exp ((-z) * (Real.log k : ℂ)) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (ne_of_gt hk)),
      ← Complex.ofReal_log hk.le]
    ring_nf
  rw [hrw]
  exact AnalyticAt.cexp (analyticAt_id.neg.mul analyticAt_const)

theorem powKernel_ne_zero {k : ℝ} (hk : 0 < k) (s : ℂ) : ((k : ℝ) : ℂ) ^ (-s) ≠ 0 :=
  cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 (ne_of_gt hk)))

theorem analyticAt_burnolPowIntegrand {G : ℂ → ℂ} {k : ℝ} (hk : 0 < k) {s : ℂ}
    (hG : AnalyticAt ℂ G s) : AnalyticAt ℂ (burnolPowIntegrand G k) s :=
  hG.mul (analyticAt_powKernel hk s)

theorem meromorphicAt_burnolPowIntegrand {G : ℂ → ℂ} {k : ℝ} (hk : 0 < k) {s : ℂ}
    (hG : MeromorphicAt G s) : MeromorphicAt (burnolPowIntegrand G k) s :=
  hG.mul (analyticAt_powKernel hk s).meromorphicAt

/-! ## The residue at `s = 1` -/

theorem extendedMellinNumerator_one {a : ℝ} (ha : 0 < a) (c d : ℂ) (f : SoninL2) :
    extendedMellinNumerator a c d f 1 = d := by
  rw [extendedMellinNumerator_eq_right a c d f (by simp; norm_num), extendedMellinNumeratorRight]
  simp

/-- **The residue at the pole of the head.** -/
theorem laurentCoeff_burnolPowIntegrand_one {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {k : ℝ} (hk : 0 < k) :
    laurentCoeff (burnolPowIntegrand (extendedMellinContinuation a c d f) k) 1 (-1)
      = -(d * ((k : ℝ) : ℂ) ^ (-(1 : ℂ))) := by
  set A : ℂ → ℂ := fun s : ℂ => extendedMellinNumerator a c d f s * ((k : ℝ) : ℂ) ^ (-s) / s
    with hAdef
  have hnum : AnalyticAt ℂ (extendedMellinNumerator a c d f) 1 :=
    ((differentiable_extendedMellinNumerator ha hev hc hd).1).analyticAt 1
  have hA : AnalyticAt ℂ A 1 := by
    rw [hAdef]
    exact (hnum.mul (analyticAt_powKernel hk 1)).div analyticAt_id one_ne_zero
  have hAval : A 1 = d * ((k : ℝ) : ℂ) ^ (-(1 : ℂ)) := by
    rw [hAdef]
    simp only
    rw [extendedMellinNumerator_one ha c d f]
    field_simp
  have hfun : burnolPowIntegrand (extendedMellinContinuation a c d f) k
      = fun s : ℂ => A s * (1 - s)⁻¹ := by
    funext s
    rw [burnolPowIntegrand, extendedMellinContinuation, hAdef]
    field_simp
  rw [hfun, laurentCoeff_analytic_mul_inv_sub hA, hAval]

/-! ## Quick decrease of the shifted integrand, and integrability on a line -/

theorem hasStripRapidDecrease_burnolPowIntegrand {G : ℂ → ℂ} (hG : HasStripRapidDecrease G)
    {k : ℝ} (hk : 0 < k) : HasStripRapidDecrease (burnolPowIntegrand G k) := by
  intro α β N
  obtain ⟨T, C, hC0, hbound⟩ := hG α β N
  refine ⟨T, C * max (k ^ (-α)) (k ^ (-β)), by positivity, ?_⟩
  intro s hα hβ hT
  have hker : ‖((k : ℝ) : ℂ) ^ (-s)‖ = k ^ (-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hk, Complex.neg_re]
  have hkerle : k ^ (-s.re) ≤ max (k ^ (-α)) (k ^ (-β)) := by
    rcases le_or_gt 1 k with h1 | h1
    · refine le_trans ?_ (le_max_left _ _)
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    · refine le_trans ?_ (le_max_right _ _)
      exact Real.rpow_le_rpow_of_exponent_ge hk (le_of_lt h1) (by linarith)
  rw [burnolPowIntegrand, norm_mul, hker]
  have hMle := hbound s hα hβ hT
  have hbase : (0:ℝ) ≤ (1 + |s.im|) ^ (-(N : ℝ)) := by positivity
  calc ‖G s‖ * k ^ (-s.re)
      ≤ (C * (1 + |s.im|) ^ (-(N : ℝ))) * max (k ^ (-α)) (k ^ (-β)) := by
        refine mul_le_mul hMle hkerle (by positivity) (by positivity)
    _ = C * max (k ^ (-α)) (k ^ (-β)) * (1 + |s.im|) ^ (-(N : ℝ)) := by ring

/-- **Quick decrease on a strip gives integrability on every line of that strip.** -/
theorem integrable_line_of_stripRapidDecrease {F : ℂ → ℂ} (hF : HasStripRapidDecrease F)
    {σ : ℝ} (hcont : Continuous fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * I)) :
    Integrable (fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * I)) volume := by
  obtain ⟨T, C, hC0, hbound⟩ := hF σ σ 2
  set T₀ : ℝ := max T 1 with hT₀def
  have hT₀1 : (1 : ℝ) ≤ T₀ := le_max_right _ _
  have hTT₀ : T ≤ T₀ := le_max_left _ _
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -T₀) (b := T₀)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0 (by
    rw [Set.mem_Icc]; constructor <;> linarith))
  set K : ℝ := C + M₀ * (1 + T₀) ^ ((3 : ℝ) / 2) with hKdef
  refine Integrable.mono'
    ((GaloisForLFunctions.HTGeometry.integrable_one_add_abs_rpow_three_halves).const_mul K)
    hcont.aestronglyMeasurable ?_
  filter_upwards with y
  have hbase : (0 : ℝ) < 1 + |y| := by positivity
  have hone : (1 : ℝ) ≤ 1 + |y| := by simp [abs_nonneg]
  have hpos : (0:ℝ) < (1 + |y|) ^ (-((3 : ℝ) / 2)) := Real.rpow_pos_of_pos hbase _
  rcases le_or_gt |y| T₀ with hy | hy
  · have hval : ‖F ((σ : ℂ) + (y : ℂ) * I)‖ ≤ M₀ := by
      refine hM₀ y ?_
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le y]; linarith [le_abs_self y]]
    have hw : (1:ℝ) ≤ (1 + |y|) ^ (-((3 : ℝ) / 2)) * (1 + T₀) ^ ((3 : ℝ) / 2) := by
      have h1 : (1 + |y|) ^ ((3:ℝ)/2) ≤ (1 + T₀) ^ ((3:ℝ)/2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      have hpos' : (0:ℝ) < (1 + |y|) ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hbase _
      rw [Real.rpow_neg hbase.le, inv_mul_eq_div, le_div_iff₀ hpos']
      linarith
    calc ‖F ((σ : ℂ) + (y : ℂ) * I)‖ ≤ M₀ := hval
      _ = M₀ * 1 := by ring
      _ ≤ M₀ * ((1 + |y|) ^ (-((3 : ℝ) / 2)) * (1 + T₀) ^ ((3 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hw hM₀0
      _ = (M₀ * (1 + T₀) ^ ((3 : ℝ) / 2)) * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by ring
      _ ≤ K * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos.le
          rw [hKdef]; linarith
  · have hyT : T ≤ |y| := le_trans hTT₀ hy.le
    have hre : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
    have him : |((σ : ℂ) + (y : ℂ) * I).im| = |y| := by simp
    have hval := hbound ((σ : ℂ) + (y : ℂ) * I) (by rw [hre]) (by rw [hre])
      (by rw [him]; exact hyT)
    rw [him] at hval
    have hmono : (1 + |y|) ^ (-(2 : ℝ)) ≤ (1 + |y|) ^ (-((3 : ℝ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
    calc ‖F ((σ : ℂ) + (y : ℂ) * I)‖ ≤ C * (1 + |y|) ^ (-((2 : ℕ) : ℝ)) := hval
      _ ≤ C * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          simpa using hmono
      _ ≤ K * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos.le
          rw [hKdef]
          have : (0:ℝ) ≤ M₀ * (1 + T₀) ^ ((3 : ℝ) / 2) := by positivity
          linarith

/-! ## The rectangle -/

theorem continuous_burnolPowIntegrand_line {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {k : ℝ} (hk : 0 < k) {σ : ℝ} (hσ0 : σ ≠ 0) (hσ1 : σ ≠ 1) :
    Continuous fun y : ℝ =>
      burnolPowIntegrand (extendedMellinContinuation a c d f) k ((σ : ℂ) + (y : ℂ) * I) := by
  have h1 := continuous_extendedMellinContinuation_line ha hev hc hd hσ0 hσ1
  have h2 : Continuous fun y : ℝ => ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) := by
    have hpath : Continuous fun y : ℝ => ((σ : ℂ) + (y : ℂ) * I) := by fun_prop
    refine continuous_iff_continuousAt.2 fun y => ?_
    exact ContinuousAt.comp (g := fun z : ℂ => ((k : ℝ) : ℂ) ^ (-z))
      (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (x := y)
      (analyticAt_powKernel hk _).continuousAt hpath.continuousAt
  exact h1.mul h2

/-- **Only the pole at `s = 1` lies in the shift rectangle.** -/
theorem rectangleIntegral'_burnolPowIntegrand {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {k : ℝ} (hk : 0 < k) {σ T : ℝ} (hσ0 : 1 / 2 < σ) (hσ1 : σ < 1) (hT : 0 < T) :
    RectangleIntegral' (burnolPowIntegrand (extendedMellinContinuation a c d f) k)
        ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ((2 : ℂ) + ((T : ℝ) : ℂ) * I)
      = -(d * ((k : ℝ) : ℂ) ^ (-(1 : ℂ))) := by
  classical
  set z : ℂ := (σ : ℂ) + ((-T : ℝ) : ℂ) * I with hzdef
  set w : ℂ := (2 : ℂ) + ((T : ℝ) : ℂ) * I with hwdef
  have hzre : z.re = σ := by rw [hzdef]; simp
  have hzim : z.im = -T := by rw [hzdef]; simp
  have hwre : w.re = 2 := by rw [hwdef]; simp
  have hwim : w.im = T := by rw [hwdef]; simp
  have hle_re : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have hle_im : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  have hmem : ∀ p : ℂ, p ∈ Rectangle z w ↔ σ ≤ p.re ∧ p.re ≤ 2 ∧ -T ≤ p.im ∧ p.im ≤ T := by
    intro p
    rw [mem_Rect hle_re hle_im, hzre, hzim, hwre, hwim]
  have hP : ∀ p ∈ ({1} : Finset ℂ), Rectangle z w ∈ 𝓝 p := by
    intro p hp
    have hp1 : p = 1 := by simpa using hp
    subst hp1
    rw [rectangle_mem_nhds_iff, mem_reProdIm, hzre, hzim, hwre, hwim,
      Set.uIoo_of_le (by linarith : σ ≤ (2:ℝ)), Set.uIoo_of_le (by linarith : -T ≤ T)]
    constructor
    · simp only [Complex.one_re, Set.mem_Ioo]
      constructor <;> linarith
    · simp only [Complex.one_im, Set.mem_Ioo]
      constructor <;> linarith
  have hmero : ∀ p ∈ ({1} : Finset ℂ),
      MeromorphicAt (burnolPowIntegrand (extendedMellinContinuation a c d f) k) p := by
    intro p _
    exact meromorphicAt_burnolPowIntegrand hk
      (meromorphicAt_extendedMellinContinuation ha hev hc hd p)
  have hoff : ∀ s ∈ Rectangle z w, s ∉ ({1} : Finset ℂ) →
      AnalyticAt ℂ (burnolPowIntegrand (extendedMellinContinuation a c d f) k) s := by
    intro s hs hs1
    have hs1' : s ≠ 1 := by simpa using hs1
    rw [hmem] at hs
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      simp at hs
      linarith [hs.1]
    exact analyticAt_burnolPowIntegrand hk
      (analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hs0 hs1')
  rw [rectangleIntegral'_eq_sum_laurentCoeff hle_re hle_im hP hmero hoff]
  rw [Finset.sum_singleton]
  exact laurentCoeff_burnolPowIntegrand_one ha hev hc hd hk

/-! ## The edges in the limit -/

theorem tendsto_hIntegral_of_stripRapidDecrease {F : ℂ → ℂ} (hF : HasStripRapidDecrease F)
    {x₁ x₂ : ℝ} {h : ℕ → ℝ} (hh : Tendsto (fun n : ℕ => |h n|) atTop atTop) :
    Tendsto (fun n : ℕ => HIntegral F x₁ x₂ (h n)) atTop (𝓝 0) := by
  obtain ⟨T, C, hC0, hbound⟩ := hF (min x₁ x₂) (max x₁ x₂) 1
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmaj : Tendsto (fun n : ℕ => C * (1 + |h n|) ^ (-(1 : ℝ)) * |x₂ - x₁|) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (1 + |h n|) ^ (-(1 : ℝ))) atTop (𝓝 0) := by
      have hgo : Tendsto (fun n : ℕ => 1 + |h n|) atTop atTop :=
        Filter.tendsto_atTop_add_const_left _ 1 hh
      have := tendsto_rpow_neg_atTop (y := (1:ℝ)) (by norm_num)
      exact this.comp hgo
    have := (hinv.const_mul C).mul_const |x₂ - x₁|
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Eventually.of_forall fun n => norm_nonneg _) ?_
  filter_upwards [hh.eventually_ge_atTop T] with n hn
  have hpt : ∀ x ∈ Set.uIoc x₁ x₂, ‖F ((x : ℂ) + ((h n : ℝ) : ℂ) * I)‖
      ≤ C * (1 + |h n|) ^ (-(1 : ℝ)) := by
    intro x hx
    rw [Set.mem_uIoc] at hx
    have hx1 : min x₁ x₂ ≤ x := by
      rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact le_trans (min_le_left _ _) h1.le
      · exact le_trans (min_le_right _ _) h1.le
    have hx2 : x ≤ max x₁ x₂ := by
      rcases hx with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact le_trans h2 (le_max_right _ _)
      · exact le_trans h2 (le_max_left _ _)
    have hre : ((x : ℂ) + ((h n : ℝ) : ℂ) * I).re = x := by simp
    have him : |((x : ℂ) + ((h n : ℝ) : ℂ) * I).im| = |h n| := by simp
    have hval := hbound ((x : ℂ) + ((h n : ℝ) : ℂ) * I) (by rw [hre]; exact hx1)
      (by rw [hre]; exact hx2) (by rw [him]; exact hn)
    rw [him] at hval
    simpa using hval
  have hkey := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  exact hkey

theorem tendsto_vIntegral_of_integrable {F : ℂ → ℂ} {σ : ℝ}
    (hint : Integrable (fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * I)) volume)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n : ℕ => VIntegral F σ (-T n) (T n)) atTop
      (𝓝 (I • ∫ y : ℝ, F ((σ : ℂ) + (y : ℂ) * I))) := by
  have hbot : Tendsto (fun n : ℕ => -T n) atTop atBot := tendsto_neg_atTop_atBot.comp hT
  have hlim := intervalIntegral_tendsto_integral (μ := (volume : Measure ℝ)) hint hbot hT
  exact hlim.const_smul I

/-! ## The vanishing of the line integral on `Re s = 2` -/

/-- **Burnol's key computation.**  The `k`-th Möbius line integral on `Re s = 2` vanishes. -/
theorem burnolPowLine_two_eq_zero {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    {k : ℝ} (hk : 0 < k) (hka : 1 / k ≤ a) :
    burnolPowLine (extendedMellinContinuation a c d f) k 2 = 0 := by
  set F : ℂ → ℂ := burnolPowIntegrand (extendedMellinContinuation a c d f) k with hFdef
  have hFrapid : HasStripRapidDecrease F := hasStripRapidDecrease_burnolPowIntegrand hrapid hk
  set σ : ℝ := 3 / 4 with hσdef
  have hσ0 : 1 / 2 < σ := by rw [hσdef]; norm_num
  have hσ1 : σ < 1 := by rw [hσdef]; norm_num
  set T : ℕ → ℝ := fun n => (n : ℝ) + 1 with hTdef
  have hTtop : Tendsto T atTop atTop := by
    rw [hTdef]
    exact tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hTpos : ∀ n : ℕ, 0 < T n := by
    intro n
    rw [hTdef]
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have habs : Tendsto (fun n : ℕ => |T n|) atTop atTop := by
    refine hTtop.congr' ?_
    filter_upwards with n
    exact (abs_of_pos (hTpos n)).symm
  have habsneg : Tendsto (fun n : ℕ => |-T n|) atTop atTop := by
    refine habs.congr' ?_
    filter_upwards with n
    rw [abs_neg]
  -- integrability on the two lines
  have hcont2 : Continuous fun y : ℝ => F ((2 : ℂ) + (y : ℂ) * I) := by
    rw [hFdef]
    have h := continuous_burnolPowIntegrand_line ha hev hc hd hk
      (σ := (2:ℝ)) (by norm_num) (by norm_num)
    simpa using h
  have hcontσ : Continuous fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * I) := by
    rw [hFdef]
    exact continuous_burnolPowIntegrand_line ha hev hc hd hk
      (σ := σ) (by rw [hσdef]; norm_num) (by rw [hσdef]; norm_num)
  have hint2 : Integrable (fun y : ℝ => F ((2 : ℂ) + (y : ℂ) * I)) volume :=
    integrable_line_of_stripRapidDecrease hFrapid hcont2
  have hintσ : Integrable (fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * I)) volume :=
    integrable_line_of_stripRapidDecrease hFrapid hcontσ
  -- the rectangle integrals are constant
  have hrect : ∀ n : ℕ, RectangleIntegral' F ((σ : ℂ) + ((-T n : ℝ) : ℂ) * I)
      ((2 : ℂ) + ((T n : ℝ) : ℂ) * I) = -(d * ((k : ℝ) : ℂ) ^ (-(1 : ℂ))) := by
    intro n
    rw [hFdef]
    exact rectangleIntegral'_burnolPowIntegrand ha hev hc hd hk hσ0 hσ1 (hTpos n)
  -- and they converge to the difference of the line integrals
  have hH1 : Tendsto (fun n : ℕ => HIntegral F σ 2 (-T n)) atTop (𝓝 0) :=
    tendsto_hIntegral_of_stripRapidDecrease hFrapid habsneg
  have hH2 : Tendsto (fun n : ℕ => HIntegral F σ 2 (T n)) atTop (𝓝 0) :=
    tendsto_hIntegral_of_stripRapidDecrease hFrapid habs
  have hV1 := tendsto_vIntegral_of_integrable hint2 hTtop
  have hV2 := tendsto_vIntegral_of_integrable hintσ hTtop
  have hRect : Tendsto (fun n : ℕ => RectangleIntegral F ((σ : ℂ) + ((-T n : ℝ) : ℂ) * I)
      ((2 : ℂ) + ((T n : ℝ) : ℂ) * I)) atTop
      (𝓝 (0 - 0 + I • (∫ y : ℝ, F ((2 : ℂ) + (y : ℂ) * I))
        - I • ∫ y : ℝ, F ((σ : ℂ) + (y : ℂ) * I))) := by
    refine Tendsto.congr (fun n => ?_) (((hH1.sub hH2).add hV1).sub hV2)
    rw [RectangleIntegral]
    congr 1 <;> simp
  have hsmul := hRect.const_smul (1 / (2 * (Real.pi : ℂ) * I))
  have hconst : Tendsto (fun _ : ℕ => -(d * ((k : ℝ) : ℂ) ^ (-(1 : ℂ)))) atTop
      (𝓝 ((1 / (2 * (Real.pi : ℂ) * I)) • ((0 : ℂ) - 0
        + I • (∫ y : ℝ, F ((2 : ℂ) + (y : ℂ) * I))
        - I • ∫ y : ℝ, F ((σ : ℂ) + (y : ℂ) * I)))) := by
    refine hsmul.congr fun n => ?_
    rw [← hrect n]
  have hval := tendsto_nhds_unique tendsto_const_nhds hconst
  -- unwind
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hline2 : (∫ y : ℝ, F ((2 : ℂ) + (y : ℂ) * I))
      = burnolPowLine (extendedMellinContinuation a c d f) k 2 := by
    rw [burnolPowLine, hFdef]
    rfl
  have hlineσ : (∫ y : ℝ, F ((σ : ℂ) + (y : ℂ) * I))
      = burnolPowLine (extendedMellinContinuation a c d f) k σ := by
    rw [burnolPowLine, hFdef]
    rfl
  rw [hline2, hlineσ] at hval
  have hband := burnolPowLine_eq_band_const ha hev hc hd hrapid hσ0 hσ1 hk hka
  have hkne : ((k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hk)
  have hkpow : ((k : ℝ) : ℂ) ^ (-(1 : ℂ)) = (((k : ℝ) : ℂ))⁻¹ := by
    rw [Complex.cpow_neg, Complex.cpow_one]
  rw [hkpow] at hval
  simp only [smul_eq_mul] at hval
  have hIne : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hπ) hI
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hπ
  set P2 : ℂ := burnolPowLine (extendedMellinContinuation a c d f) k 2 with hP2def
  set Pσ : ℂ := burnolPowLine (extendedMellinContinuation a c d f) k σ with hPσdef
  have hmul : (2 * (Real.pi : ℂ) * I) * (-(d * ((k : ℝ) : ℂ)⁻¹))
      = (2 * (Real.pi : ℂ) * I) * ((1 / (2 * (Real.pi : ℂ) * I)) * (0 - 0 + I * P2 - I * Pσ)) := by
    rw [← hval]
  rw [← mul_assoc, mul_one_div, div_self hIne, one_mul] at hmul
  have hcancel : P2 - Pσ = 2 * (Real.pi : ℂ) * (-(d * ((k : ℝ) : ℂ)⁻¹)) := by
    refine mul_left_cancel₀ hI ?_
    linear_combination -hmul
  have hPσ : Pσ = 2 * (Real.pi : ℂ) * (d * ((k : ℝ) : ℂ)⁻¹) := by
    have h : (2 * (Real.pi : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) * Pσ)
        = (2 * (Real.pi : ℂ)) * (d / (k : ℂ)) := by
      rw [hPσdef, hband]
    rw [← mul_assoc, mul_one_div, div_self h2π, one_mul] at h
    rw [h]
    field_simp
  rw [hPσ] at hcancel
  rw [hP2def] at hcancel ⊢
  linear_combination hcancel

end

end RHTower
