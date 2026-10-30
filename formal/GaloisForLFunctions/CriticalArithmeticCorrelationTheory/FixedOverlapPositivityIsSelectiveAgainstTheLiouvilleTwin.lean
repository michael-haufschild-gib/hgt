import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap
import GaloisForLFunctions.TransMetzlerWeilPositivity.LiouvilleTwinSelectivity
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime

/-!
# Fixed-overlap positivity is selective against the Liouville twin

A near-plateau profile `0 ≤ g ≤ B`, supported in `[0, 1]`, at least `m₀` on `[η, 1 − η]` and
`K`-Lipschitz has Robin constant
`β(g) ≤ K B a + (B² − m₀² + 2η m₀²) log(1/a) + m₀² (1 − a)` for every `0 < a ≤ 1`
(`bumpRobin_le_of_nearPlateau`): below `a` the Lipschitz bound, above it the overlap of the plateau
with its shift.

The tilted box plateau `e^{τ(u − 1/2)} ∫_{u−1/2−L}^{u−1/2+L} B_w`, `L = 1/2 − 4w`, `B_w` the
four-fold box of half-width `w`, is such a profile, and its Fourier transform
`2L · sinc-factors` evaluated at `ξ − iτ` has no real zeros. At `w = τ = 1/1000` its Robin–Euler
threshold is below one. Hence at every fixed overlap `c ≥ 1` the complete Weil matrix of `ζ` is
eventually positive definite, while the Liouville twin's complete form is eventually negative
(`tiltedBoxPlateau_liouville_selective`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped Real

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis

/-- **The Robin constant of a near plateau.** -/
theorem bumpRobin_le_of_nearPlateau {g : ℝ → ℝ} (hg : Continuous g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → g u = 0) {B m₀ η K a : ℝ} (hg0 : ∀ u, 0 ≤ g u)
    (hgB : ∀ u, g u ≤ B) (hm : ∀ u ∈ Set.Icc η (1 - η), m₀ ≤ g u) (hm₀ : 0 ≤ m₀)
    (hK : ∀ u v, |g u - g v| ≤ K * |u - v|) (hK0 : 0 ≤ K) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    bumpRobin g 1 ≤
      K * B * a + (B ^ 2 - m₀ ^ 2 + 2 * η * m₀ ^ 2) * Real.log (1 / a) + m₀ ^ 2 * (1 - a) := by
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu
  have hB0 : 0 ≤ B := (hg0 0).trans (hgB 0)
  -- the `L¹` and `L²` masses are at most `B` and `B²`
  have hrest : ∀ F : ℝ → ℝ, F 0 = 0 → ∫ u, F (g u) = ∫ u in Set.Icc 0 1, F (g u) := fun F hF =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by rw [hsupp u hu, hF]).symm
  have hL1 : ∫ u, |g u| ≤ B := by
    rw [hrest (fun z => |z|) (by norm_num)]
    have := setIntegral_mono_on (hg.abs.integrableOn_Icc) (continuous_const.integrableOn_Icc)
      measurableSet_Icc fun u (_ : u ∈ Set.Icc (0 : ℝ) 1) => by
        rw [abs_of_nonneg (hg0 u)]; exact hgB u
    simpa using this
  have hL2 : ∫ u, g u ^ 2 ≤ B ^ 2 := by
    rw [hrest (fun z => z ^ 2) (by norm_num)]
    have := setIntegral_mono_on ((hg.pow 2).integrableOn_Icc) (continuous_const.integrableOn_Icc)
      measurableSet_Icc fun u (_ : u ∈ Set.Icc (0 : ℝ) 1) =>
        pow_le_pow_left₀ (hg0 u) (hgB u) 2
    simpa using this
  -- the overlap of the plateau with its shift
  have hshift : ∀ y, 0 ≤ y → m₀ ^ 2 * (1 - 2 * η - y) ≤ ∫ u, g u * g (u + y) := by
    intro y hy
    have hint : Integrable fun u => g u * g (u + y) := by
      simpa using integrable_comp_sub_mul_comp_add hg hgc 0 y
    have h0 : 0 ≤ ∫ u, g u * g (u + y) := integral_nonneg fun u => mul_nonneg (hg0 u) (hg0 _)
    rcases le_or_gt (1 - η - y) η with h | h
    · nlinarith [sq_nonneg m₀]
    have hset : ∫ u in Set.Icc η (1 - η - y), m₀ ^ 2 = m₀ ^ 2 * (1 - 2 * η - y) := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    have hle : ∫ u in Set.Icc η (1 - η - y), m₀ ^ 2 ≤ ∫ u in Set.Icc η (1 - η - y), g u * g (u + y) :=
      setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc
        fun u hu => by
          have h1 := hm u ⟨hu.1, by linarith [hu.2]⟩
          have h2 := hm (u + y) ⟨by linarith [hu.1], by linarith [hu.2]⟩
          rw [sq]; exact mul_le_mul h1 h2 hm₀ (hg0 u)
    have hsub := setIntegral_le_integral hint (Filter.Eventually.of_forall fun u =>
      mul_nonneg (hg0 u) (hg0 (u + y)))
    linarith
  set Q : ℝ → ℝ := fun y => ∫ u, (g u - g (u + y)) ^ 2 with hQdef
  have hQm : StronglyMeasurable Q := by
    have hc : Continuous fun p : ℝ × ℝ => (g p.2 - g (p.2 + p.1)) ^ 2 := by fun_prop
    exact hc.stronglyMeasurable.integral_prod_right'
  have hQ0 : ∀ y, 0 ≤ Q y := fun y => integral_nonneg fun u => sq_nonneg _
  have hQK : ∀ y, 0 < y → Q y / (2 * y) ≤ K * B := fun y hy => by
    have h1 : Q y ≤ 2 * K * |y| * ∫ u, |g u| := integral_sub_shift_sq_le_lipschitz hg hgc hK y
    rw [abs_of_pos hy] at h1
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hL1 (by positivity : 0 ≤ 2 * K * y)]
  have hQfar : ∀ y, 0 < y → Q y / (2 * y) ≤
      (B ^ 2 - m₀ ^ 2 + 2 * η * m₀ ^ 2) * y⁻¹ + m₀ ^ 2 := fun y hy => by
    have hQ : Q y = 2 * (∫ u, g u ^ 2) - 2 * ∫ u, g u * g (u + y) :=
      integral_sub_shift_sq_eq hg hgc y
    have hs := hshift y hy.le
    rw [div_le_iff₀ (by linarith), hQ]
    have : ((B ^ 2 - m₀ ^ 2 + 2 * η * m₀ ^ 2) * y⁻¹ + m₀ ^ 2) * (2 * y) =
        2 * (B ^ 2 - m₀ ^ 2 + 2 * η * m₀ ^ 2) + 2 * m₀ ^ 2 * y := by
      field_simp
    rw [this]
    nlinarith
  have hint : IntegrableOn (fun y => Q y / (2 * y)) (Set.Ioc 0 1) := by
    refine Measure.integrableOn_of_bounded (M := K * B) (measure_Ioc_lt_top).ne
      ((hQm.measurable.div (measurable_const.mul measurable_id)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hQ0 y) (by linarith [hy.1]))]
    exact hQK y hy.1
  have hsplit : Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 a ∪ Set.Ioc a 1 :=
    (Set.Ioc_union_Ioc_eq_Ioc ha0.le ha1).symm
  unfold bumpRobin
  change ∫ y in Set.Ioc 0 1, Q y / (2 * y) ≤ _
  rw [hsplit, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (hint.mono_set fun y hy => ⟨hy.1, hy.2.trans ha1⟩)
    (hint.mono_set fun y hy => ⟨lt_trans ha0 hy.1, hy.2⟩)]
  have hnear : ∫ y in Set.Ioc 0 a, Q y / (2 * y) ≤ K * B * a := by
    have := setIntegral_mono_on (s := Set.Ioc 0 a)
      (hint.mono_set fun y hy => ⟨hy.1, hy.2.trans ha1⟩) (integrableOn_const (C := K * B) (by simp))
      measurableSet_Ioc fun y hy => hQK y hy.1
    simpa [Real.volume_Ioc, ha0.le, mul_comm] using this
  set D := B ^ 2 - m₀ ^ 2 + 2 * η * m₀ ^ 2 with hD
  have hfarInt : IntegrableOn (fun y : ℝ => D * y⁻¹ + m₀ ^ 2) (Set.Ioc a 1) := by
    have hc : ContinuousOn (fun y : ℝ => D * y⁻¹ + m₀ ^ 2) (Set.Icc a 1) :=
      (continuousOn_const.mul (continuousOn_inv₀.mono fun y hy =>
        ne_of_gt (lt_of_lt_of_le ha0 hy.1))).add continuousOn_const
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hfar : ∫ y in Set.Ioc a 1, Q y / (2 * y) ≤ ∫ y in Set.Ioc a 1, (D * y⁻¹ + m₀ ^ 2) :=
    setIntegral_mono_on (hint.mono_set fun y hy => ⟨lt_trans ha0 hy.1, hy.2⟩) hfarInt
      measurableSet_Ioc fun y hy => hQfar y (lt_trans ha0 hy.1)
  have hfarEq : ∫ y in Set.Ioc a 1, (D * y⁻¹ + m₀ ^ 2) = D * Real.log (1 / a) + m₀ ^ 2 * (1 - a) := by
    have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a 1 :=
      (continuousOn_inv₀.mono fun y hy => by
        rcases Set.mem_uIcc.mp hy with h | h <;> exact ne_of_gt (by linarith [h.1])).intervalIntegrable
    rw [← intervalIntegral.integral_of_le ha1, intervalIntegral.integral_add
      (f := fun x => D * x⁻¹) (g := fun _ => m₀ ^ 2) (hinv.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 one_pos]
    simp only [intervalIntegral.integral_const, smul_eq_mul, one_div]
    ring
  linarith

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
