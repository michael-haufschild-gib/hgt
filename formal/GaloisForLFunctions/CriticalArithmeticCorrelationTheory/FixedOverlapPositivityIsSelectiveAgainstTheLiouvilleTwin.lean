import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap
import GaloisForLFunctions.TransMetzlerWeilPositivity.LiouvilleTwinSelectivity
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime
import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference

/-!
# Fixed-overlap positivity is selective against the Liouville twin

A near-plateau profile `0 ≤ g ≤ B`, supported in `[0, 1]`, at least `m₀` on `[η, 1 − η]` and
`K`-Lipschitz has Robin constant
`β(g) ≤ K B a + (B² − m₀² + 2η m₀²) log(1/a) + m₀² (1 − a)` for every `0 < a ≤ 1`
(`bumpRobin_le_of_nearPlateau`): below `a` the Lipschitz bound, above it the overlap of the plateau
with its shift.

The tilted box plateau `e^{τu} ∫_{u−1/2−L}^{u−1/2+L} B_w`, `L = 1/2 − 4w`, `B_w` the four-fold
box of half-width `w`, is such a profile; its Fourier transform at `ξ` is that of the box plateau,
`2L · Û_L · Û_w⁴`, at `ξ − iτ`, so a nonzero tilt leaves no real Fourier zeros. For the
**Liouville selector** `w = 1/1000`, `e^τ = 1001/1000` the Robin–Euler threshold is below one.
Hence at every fixed overlap `c` above it (in particular every `c ≥ 1`) the complete Weil matrix of
`ζ` is eventually positive definite, while the Liouville twin's complete form is eventually negative
on the same atomic families (`liouvilleSelector_selective`).
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
    have := setIntegral_mono_on (μ := volume) (hg.abs.integrableOn_Icc) (continuous_const.integrableOn_Icc)
      measurableSet_Icc fun u (_ : u ∈ Set.Icc (0 : ℝ) 1) => by
        rw [abs_of_nonneg (hg0 u)]; exact hgB u
    simpa using this
  have hL2 : ∫ u, g u ^ 2 ≤ B ^ 2 := by
    rw [hrest (fun z => z ^ 2) (by norm_num)]
    have := setIntegral_mono_on (μ := volume) ((hg.pow 2).integrableOn_Icc) (continuous_const.integrableOn_Icc)
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
    have hsub : ∫ u in Set.Icc η (1 - η - y), g u * g (u + y) ≤ ∫ u, g u * g (u + y) :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall fun u =>
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

/-! ### The tilted box plateau -/

section BoxPlateau

open RHTower.WeilDeletion (unif upow integrable_upow hasCompactSupport_upow paperFT_upow
  support_upow_subset upow_nonneg integral_upow integrable_unif hasCompactSupport_unif paperFT_conv)
open BiScaleUncertainty.ChebyshevGauge (unif_convolution_eq contDiff_unif_convolution contDiff_upow
  paperFT_unif_ne_zero tiltedSource paperFT_tiltedSource contDiff_tiltedSource)
open ArithmeticCastelnuovoSeveri (cx translate paperFT_translate)
open scoped Convolution

variable {w : ℝ}

/-- The box plateau `∫_{x−L}^{x+L} B_w`, `L = 1/2 − 4w`, `B_w` the four-fold box of half-width `w`. -/
def boxPlateau (w : ℝ) (x : ℝ) : ℝ :=
  ∫ t in (x - (1 / 2 - 4 * w))..(x + (1 / 2 - 4 * w)), upow w 3 t

/-- The tilted box plateau `e^{τu} P_w(u − 1/2)` on `[0, 1]`. -/
def tiltedBoxPlateau (w τ : ℝ) (u : ℝ) : ℝ :=
  Real.exp (τ * u) * boxPlateau w (u - 1 / 2)

theorem boxPlateau_eq_conv (hw8 : w < 1 / 8) (x : ℝ) :
    boxPlateau w x = 2 * (1 / 2 - 4 * w) * (unif (1 / 2 - 4 * w) ⋆ upow w 3) x := by
  have hL : 0 < 1 / 2 - 4 * w := by linarith
  rw [unif_convolution_eq hL (integrable_upow w 3), boxPlateau,
    intervalIntegral.integral_interval_sub_left
      ((integrable_upow w 3).intervalIntegrable) ((integrable_upow w 3).intervalIntegrable),
    ← mul_assoc, mul_one_div_cancel (mul_pos two_pos hL).ne', one_mul]

theorem contDiff_boxPlateau (hw : 0 < w) (hw8 : w < 1 / 8) : ContDiff ℝ 2 (boxPlateau w) := by
  have hL : 0 < 1 / 2 - 4 * w := by linarith
  rw [show boxPlateau w = fun x => 2 * (1 / 2 - 4 * w) * (unif (1 / 2 - 4 * w) ⋆ upow w 3) x from
    funext (boxPlateau_eq_conv hw8)]
  exact contDiff_const.mul ((contDiff_unif_convolution hL (integrable_upow w 3)
    (contDiff_upow hw 2)).of_le (by norm_num))

theorem boxPlateau_nonneg (hw : 0 < w) (hw8 : w < 1 / 8) (x : ℝ) : 0 ≤ boxPlateau w x :=
  intervalIntegral.integral_nonneg (by linarith) fun t _ => upow_nonneg hw 3 t

theorem boxPlateau_le_one (hw : 0 < w) (hw8 : w < 1 / 8) (x : ℝ) : boxPlateau w x ≤ 1 := by
  rw [boxPlateau, intervalIntegral.integral_of_le (by linarith), ← integral_upow hw 3]
  exact setIntegral_le_integral (integrable_upow w 3)
    (Filter.Eventually.of_forall fun t => upow_nonneg hw 3 t)

/-- Outside a window of radius `4w` around the box the four-fold box vanishes. -/
theorem upow_three_eq_zero (hw : 0 < w) {t : ℝ} (ht : t ∉ Set.Icc (-(4 * w)) (4 * w)) :
    upow w 3 t = 0 := by
  by_contra h
  apply ht
  have := support_upow_subset hw 3 h
  norm_num at this ⊢
  exact this

theorem boxPlateau_eq_one (hw : 0 < w) (hw8 : w < 1 / 8) {x : ℝ}
    (hx : |x| < 1 / 2 - 8 * w) : boxPlateau w x = 1 := by
  rw [boxPlateau, intervalIntegral.integral_of_le (by linarith [abs_nonneg x])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => upow_three_eq_zero hw (by
    intro hmem
    apply ht
    obtain ⟨h1, h2⟩ := abs_lt.mp hx
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)]
  exact integral_upow hw 3

theorem boxPlateau_eq_zero (hw : 0 < w) (hw8 : w < 1 / 8) {x : ℝ} (hx : 1 / 2 < |x|) :
    boxPlateau w x = 0 := by
  rw [boxPlateau, intervalIntegral.integral_of_le (by linarith [abs_nonneg x])]
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => upow_three_eq_zero hw ?_
  intro hmem
  rcases lt_abs.mp hx with h | h
  · linarith [ht.1, hmem.2]
  · linarith [ht.2, hmem.1]

/-- The four-fold box is at most `1/(2w)`. -/
theorem upow_three_le (hw : 0 < w) (t : ℝ) : upow w 3 t ≤ 1 / (2 * w) := by
  change (unif w ⋆ upow w 2) t ≤ _
  rw [unif_convolution_eq hw (integrable_upow w 2),
    intervalIntegral.integral_interval_sub_left
      ((integrable_upow w 2).intervalIntegrable) ((integrable_upow w 2).intervalIntegrable)]
  have h1 : (∫ s in (t - w)..(t + w), upow w 2 s) ≤ 1 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_upow hw 2]
    exact setIntegral_le_integral (integrable_upow w 2)
      (Filter.Eventually.of_forall fun s => upow_nonneg hw 2 s)
  have h2 : 0 < 1 / (2 * w) := by positivity
  nlinarith

/-- **The box plateau is `1/w`-Lipschitz.** -/
theorem abs_boxPlateau_sub_le (hw : 0 < w) (x y : ℝ) :
    |boxPlateau w x - boxPlateau w y| ≤ 1 / w * |x - y| := by
  set L := 1 / 2 - 4 * w
  have hi : ∀ a b : ℝ, IntervalIntegrable (upow w 3) volume a b :=
    fun a b => (integrable_upow w 3).intervalIntegrable
  have hbound : ∀ a b : ℝ, |∫ t in a..b, upow w 3 t| ≤ 1 / (2 * w) * |b - a| := fun a b => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := 1 / (2 * w)) (f := upow w 3) fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (upow_nonneg hw 3 t)]; exact upow_three_le hw t
    simpa [Real.norm_eq_abs, mul_comm] using this
  have hsplit : boxPlateau w x - boxPlateau w y =
      (∫ t in (y + L)..(x + L), upow w 3 t) - ∫ t in (y - L)..(x - L), upow w 3 t := by
    simp only [boxPlateau]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi (x - L) (y - L)) (hi (y - L) (x + L)),
      ← intervalIntegral.integral_add_adjacent_intervals (hi (y - L) (x + L)) (hi (x + L) (y + L)),
      intervalIntegral.integral_symm (x + L) (y + L), intervalIntegral.integral_symm (x - L) (y - L)]
    ring
  rw [hsplit]
  calc |(∫ t in (y + L)..(x + L), upow w 3 t) - ∫ t in (y - L)..(x - L), upow w 3 t|
      ≤ |∫ t in (y + L)..(x + L), upow w 3 t| + |∫ t in (y - L)..(x - L), upow w 3 t| :=
        abs_sub _ _
    _ ≤ 1 / (2 * w) * |(x + L) - (y + L)| + 1 / (2 * w) * |(x - L) - (y - L)| :=
        add_le_add (hbound _ _) (hbound _ _)
    _ = 1 / w * |x - y| := by
        rw [show (x + L) - (y + L) = x - y by ring, show (x - L) - (y - L) = x - y by ring]
        field_simp
        ring

/-- The box plateau has no Fourier zeros off the real axis: `P̂_w = 2L · Û_L · Û_w⁴`. -/
theorem paperFT_boxPlateau_ne_zero (hw : 0 < w) (hw8 : w < 1 / 8) {z : ℂ} (hz : z.im ≠ 0) :
    Zeta23.paperFT (fun x => (boxPlateau w x : ℂ)) z ≠ 0 := by
  have hL : 0 < 1 / 2 - 4 * w := by linarith
  set k : ℝ := 2 * (1 / 2 - 4 * w)
  have h : (fun x => (boxPlateau w x : ℂ)) =
      fun x => (k : ℂ) * ((unif (1 / 2 - 4 * w) ⋆ upow w 3) x : ℂ) := by
    funext x; rw [boxPlateau_eq_conv hw8, Complex.ofReal_mul]
  have hk : Zeta23.paperFT (fun x => (k : ℂ) * ((unif (1 / 2 - 4 * w) ⋆ upow w 3) x : ℂ)) z =
      (k : ℂ) * Zeta23.paperFT (fun x => ((unif (1 / 2 - 4 * w) ⋆ upow w 3) x : ℂ)) z := by
    unfold Zeta23.paperFT; simp_rw [mul_assoc]; exact integral_const_mul _ _
  rw [h, hk, paperFT_conv (integrable_unif _) (integrable_upow w 3) (hasCompactSupport_unif _)
    (hasCompactSupport_upow w 3), paperFT_upow]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos two_pos hL).ne')
    (mul_ne_zero (paperFT_unif_ne_zero hL hz) (pow_ne_zero _ (paperFT_unif_ne_zero hw hz)))

/-- **A nonzero tilt removes every real Fourier zero.** -/
theorem paperFT_tiltedBoxPlateau_ne_zero (hw : 0 < w) (hw8 : w < 1 / 8) {τ : ℝ} (hτ : τ ≠ 0)
    (r : ℝ) : Zeta23.paperFT (cx (tiltedBoxPlateau w τ)) (r : ℂ) ≠ 0 := by
  have key : Zeta23.paperFT (cx (tiltedBoxPlateau w τ)) (r : ℂ) =
      Complex.exp (Complex.I * ((r : ℂ) - Complex.I * τ) * ((1 / 2 : ℝ) : ℂ)) *
        Zeta23.paperFT (fun x => (boxPlateau w x : ℂ)) ((r : ℂ) - Complex.I * τ) := by
    change Zeta23.paperFT (fun u => (tiltedSource (fun u => boxPlateau w (u - 1 / 2)) τ u : ℂ)) _ = _
    rw [paperFT_tiltedSource]
    exact paperFT_translate (1 / 2) (fun x => (boxPlateau w x : ℂ)) _
  rw [key]
  refine mul_ne_zero (Complex.exp_ne_zero _) (paperFT_boxPlateau_ne_zero hw hw8 ?_)
  simp [hτ]

theorem half_lt_abs_sub_half {u : ℝ} (hu : u ∉ Set.Icc (0 : ℝ) 1) : 1 / 2 < |u - 1 / 2| := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem tiltedBoxPlateau_eq_zero (hw : 0 < w) (hw8 : w < 1 / 8) (τ : ℝ) {u : ℝ}
    (hu : u ∉ Set.Icc 0 1) : tiltedBoxPlateau w τ u = 0 := by
  rw [tiltedBoxPlateau, boxPlateau_eq_zero hw hw8 (half_lt_abs_sub_half hu), mul_zero]

theorem contDiff_tiltedBoxPlateau (hw : 0 < w) (hw8 : w < 1 / 8) (τ : ℝ) :
    ContDiff ℝ 2 (tiltedBoxPlateau w τ) := by
  have h : ContDiff ℝ 2 (fun u => boxPlateau w (u - 1 / 2)) :=
    (contDiff_boxPlateau hw hw8).comp (contDiff_id.sub contDiff_const)
  exact contDiff_tiltedSource h τ

theorem tiltedBoxPlateau_nonneg (hw : 0 < w) (hw8 : w < 1 / 8) (τ u : ℝ) :
    0 ≤ tiltedBoxPlateau w τ u :=
  mul_nonneg (Real.exp_pos _).le (boxPlateau_nonneg hw hw8 _)

theorem tiltedBoxPlateau_le (hw : 0 < w) (hw8 : w < 1 / 8) {τ : ℝ} (hτ : 0 ≤ τ) (u : ℝ) :
    tiltedBoxPlateau w τ u ≤ Real.exp τ := by
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · calc tiltedBoxPlateau w τ u ≤ Real.exp (τ * u) * 1 :=
          mul_le_mul_of_nonneg_left (boxPlateau_le_one hw hw8 _) (Real.exp_pos _).le
      _ ≤ Real.exp τ := by
          rw [mul_one]; exact Real.exp_le_exp.mpr (mul_le_of_le_one_right hτ hu.2)
  · rw [tiltedBoxPlateau_eq_zero hw hw8 τ hu]; exact (Real.exp_pos _).le

theorem one_le_tiltedBoxPlateau (hw : 0 < w) (hw8 : w < 1 / 8) {τ : ℝ} (hτ : 0 ≤ τ) {u : ℝ}
    (hu : u ∈ Set.Icc (9 * w) (1 - 9 * w)) : 1 ≤ tiltedBoxPlateau w τ u := by
  have hP : boxPlateau w (u - 1 / 2) = 1 :=
    boxPlateau_eq_one hw hw8 (abs_lt.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  rw [tiltedBoxPlateau, hP, mul_one]
  exact Real.one_le_exp (mul_nonneg hτ (by linarith [hu.1]))

theorem abs_tiltedBoxPlateau_sub_le_of_mem (hw : 0 < w) (hw8 : w < 1 / 8) {τ : ℝ} (hτ : 0 ≤ τ)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (v : ℝ) :
    |tiltedBoxPlateau w τ u - tiltedBoxPlateau w τ v| ≤ Real.exp τ * (1 / w + τ) * |u - v| := by
  have hP := abs_boxPlateau_sub_le hw (u - 1 / 2) (v - 1 / 2)
  rw [show u - 1 / 2 - (v - 1 / 2) = u - v by ring] at hP
  have heu : Real.exp (τ * u) ≤ Real.exp τ := Real.exp_le_exp.mpr (mul_le_of_le_one_right hτ hu.2)
  have hsplit : tiltedBoxPlateau w τ u - tiltedBoxPlateau w τ v =
      Real.exp (τ * u) * (boxPlateau w (u - 1 / 2) - boxPlateau w (v - 1 / 2)) +
        (Real.exp (τ * u) - Real.exp (τ * v)) * boxPlateau w (v - 1 / 2) := by
    simp only [tiltedBoxPlateau]; ring
  have h1 : |Real.exp (τ * u) * (boxPlateau w (u - 1 / 2) - boxPlateau w (v - 1 / 2))| ≤
      Real.exp τ * (1 / w * |u - v|) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul heu hP (abs_nonneg _) (Real.exp_pos _).le
  have h2 : |(Real.exp (τ * u) - Real.exp (τ * v)) * boxPlateau w (v - 1 / 2)| ≤
      Real.exp τ * τ * |u - v| := by
    by_cases hv : v ∈ Set.Icc (0 : ℝ) 1
    · have hev : |Real.exp (τ * u) - Real.exp (τ * v)| ≤ Real.exp τ * |τ * u - τ * v| :=
        HTGeometry.abs_exp_sub_exp_le (mul_le_of_le_one_right hτ hu.2)
          (mul_le_of_le_one_right hτ hv.2)
      have hτuv : |τ * u - τ * v| = τ * |u - v| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hτ]
      rw [abs_mul, abs_of_nonneg (boxPlateau_nonneg hw hw8 _)]
      calc |Real.exp (τ * u) - Real.exp (τ * v)| * boxPlateau w (v - 1 / 2)
          ≤ |Real.exp (τ * u) - Real.exp (τ * v)| * 1 :=
            mul_le_mul_of_nonneg_left (boxPlateau_le_one hw hw8 _) (abs_nonneg _)
        _ ≤ Real.exp τ * τ * |u - v| := by rw [mul_one, mul_assoc, ← hτuv]; exact hev
    · rw [boxPlateau_eq_zero hw hw8 (half_lt_abs_sub_half hv), mul_zero, abs_zero]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hτ) (abs_nonneg _)
  rw [hsplit]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ Real.exp τ * (1 / w * |u - v|) + Real.exp τ * τ * |u - v| := add_le_add h1 h2
    _ = Real.exp τ * (1 / w + τ) * |u - v| := by ring

/-- **The tilted box plateau is `e^τ(1/w + τ)`-Lipschitz.** -/
theorem abs_tiltedBoxPlateau_sub_le (hw : 0 < w) (hw8 : w < 1 / 8) {τ : ℝ} (hτ : 0 ≤ τ)
    (u v : ℝ) :
    |tiltedBoxPlateau w τ u - tiltedBoxPlateau w τ v| ≤ Real.exp τ * (1 / w + τ) * |u - v| := by
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · exact abs_tiltedBoxPlateau_sub_le_of_mem hw hw8 hτ hu v
  by_cases hv : v ∈ Set.Icc (0 : ℝ) 1
  · rw [abs_sub_comm, abs_sub_comm u v]; exact abs_tiltedBoxPlateau_sub_le_of_mem hw hw8 hτ hv u
  · rw [tiltedBoxPlateau_eq_zero hw hw8 τ hu, tiltedBoxPlateau_eq_zero hw hw8 τ hv, sub_zero,
      abs_zero]
    have : 0 < 1 / w := one_div_pos.mpr hw
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith)) (abs_nonneg _)

/-- The Robin constant of the tilted box plateau, from the near-plateau bound with `m₀ = 1`,
`B = e^τ`, `η = 9w`. -/
theorem bumpRobin_tiltedBoxPlateau_le (hw : 0 < w) (hw8 : w < 1 / 8) {τ : ℝ} (hτ : 0 ≤ τ)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    bumpRobin (tiltedBoxPlateau w τ) 1 ≤
      Real.exp τ * (1 / w + τ) * Real.exp τ * a +
        (Real.exp τ ^ 2 - 1 ^ 2 + 2 * (9 * w) * 1 ^ 2) * Real.log (1 / a) + 1 ^ 2 * (1 - a) := by
  have : 0 < 1 / w := one_div_pos.mpr hw
  exact bumpRobin_le_of_nearPlateau (contDiff_tiltedBoxPlateau hw hw8 τ).continuous
    (fun _ hu => tiltedBoxPlateau_eq_zero hw hw8 τ hu) (tiltedBoxPlateau_nonneg hw hw8 τ)
    (tiltedBoxPlateau_le hw hw8 hτ) (fun _ hu => one_le_tiltedBoxPlateau hw hw8 hτ hu) zero_le_one
    (abs_tiltedBoxPlateau_sub_le hw hw8 hτ)
    (mul_nonneg (Real.exp_pos _).le (by linarith)) ha0 ha1

/-- The `L²` mass of the tilted box plateau is at least the length `1 − 18w` of its flat top. -/
theorem one_sub_le_integral_tiltedBoxPlateau_sq (hw : 0 < w) (hw18 : w < 1 / 18) {τ : ℝ}
    (hτ : 0 ≤ τ) : 1 - 18 * w ≤ ∫ u, tiltedBoxPlateau w τ u ^ 2 := by
  have hw8 : w < 1 / 8 := by linarith
  have hcs : HasCompactSupport (tiltedBoxPlateau w τ) :=
    HasCompactSupport.intro isCompact_Icc fun _ hu => tiltedBoxPlateau_eq_zero hw hw8 τ hu
  have hint := integrable_sq_of_continuous (contDiff_tiltedBoxPlateau hw hw8 τ).continuous hcs
  have h1 : ∫ _ in Set.Icc (9 * w) (1 - 9 * w), (1 : ℝ) ≤
      ∫ u in Set.Icc (9 * w) (1 - 9 * w), tiltedBoxPlateau w τ u ^ 2 :=
    setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc
      fun u hu => by nlinarith [one_le_tiltedBoxPlateau hw hw8 hτ hu]
  have h2 : ∫ u in Set.Icc (9 * w) (1 - 9 * w), tiltedBoxPlateau w τ u ^ 2 ≤
      ∫ u, tiltedBoxPlateau w τ u ^ 2 :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have h0 : ∫ _ in Set.Icc (9 * w) (1 - 9 * w), (1 : ℝ) = 1 - 18 * w := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  linarith

end BoxPlateau

/-! ### The Liouville selector -/

open TransMetzlerWeilPositivity RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics

/-- The **Liouville selector**: the tilted box plateau with `w = 1/1000` and `e^τ = 1001/1000`. -/
def liouvilleSelector : ℝ → ℝ := tiltedBoxPlateau (1 / 1000) (Real.log (1001 / 1000))

theorem log_selectorTilt_pos : 0 < Real.log (1001 / 1000 : ℝ) := Real.log_pos (by norm_num)

theorem contDiff_liouvilleSelector : ContDiff ℝ 2 liouvilleSelector :=
  contDiff_tiltedBoxPlateau (by norm_num) (by norm_num) _

theorem liouvilleSelector_eq_zero {u : ℝ} (hu : u ∉ Set.Icc 0 1) : liouvilleSelector u = 0 :=
  tiltedBoxPlateau_eq_zero (by norm_num) (by norm_num) _ hu

theorem paperFT_liouvilleSelector_ne_zero (r : ℝ) :
    Zeta23.paperFT (ArithmeticCastelnuovoSeveri.cx liouvilleSelector) (r : ℂ) ≠ 0 :=
  paperFT_tiltedBoxPlateau_ne_zero (by norm_num) (by norm_num) log_selectorTilt_pos.ne' r

theorem integral_liouvilleSelector_sq_ge : 491 / 500 ≤ ∫ u, liouvilleSelector u ^ 2 := by
  have h := one_sub_le_integral_tiltedBoxPlateau_sq (w := 1 / 1000) (by norm_num) (by norm_num)
    log_selectorTilt_pos.le
  unfold liouvilleSelector
  linarith

/-- **The Robin–Euler threshold of the Liouville selector is below one**: `β/‖φ‖² ≤ 3/2`, and
`e^{3/2} < 2π`. -/
theorem robinEulerThreshold_liouvilleSelector_lt_one :
    robinEulerThreshold liouvilleSelector < 1 := by
  have hτ0 := log_selectorTilt_pos
  have hτ1 : Real.log (1001 / 1000 : ℝ) ≤ 1 / 1000 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1001 / 1000 by norm_num); linarith
  have heτ : Real.exp (Real.log (1001 / 1000 : ℝ)) = 1001 / 1000 := Real.exp_log (by norm_num)
  have hβ := bumpRobin_tiltedBoxPlateau_le (w := 1 / 1000) (by norm_num) (by norm_num) hτ0.le
    (a := 1 / 10000) (by norm_num) (by norm_num)
  rw [heτ] at hβ
  have hlog : Real.log (1 / (1 / 10000)) ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc (1 / (1 / 10000) : ℝ) ≤ 2.7 ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h1 10
  have hM := integral_liouvilleSelector_sq_ge
  have hq : bumpRobin liouvilleSelector 1 / ∫ u, liouvilleSelector u ^ 2 ≤ 3 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    unfold liouvilleSelector at hM ⊢
    nlinarith
  have hhalf : Real.exp (1 / 2) < 2 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
    norm_num at this; exact this
  unfold robinEulerThreshold
  rw [div_lt_one (by positivity)]
  calc Real.exp (bumpRobin liouvilleSelector 1 / ∫ u, liouvilleSelector u ^ 2)
      ≤ Real.exp (3 / 2) := Real.exp_le_exp.mpr hq
    _ = Real.exp 1 * Real.exp (1 / 2) := by rw [← Real.exp_add]; norm_num
    _ < 2.7182818286 * 2 :=
        mul_lt_mul'' Real.exp_one_lt_d9 hhalf (Real.exp_pos _).le (Real.exp_pos _).le
    _ < 2 * Real.pi := by linarith [Real.pi_gt_d2]

/-- **Fixed-overlap positivity is selective against the Liouville twin.** For the Liouville
selector and every fixed overlap `c` above its Robin–Euler threshold `< 1`, eventually in `N`: Weil's form of `ζ` is strictly
positive on every nonzero atomic family of width `c/N` (the complete Weil matrix is positive
definite), while the complete form of the Liouville twin `λΛ` is strictly negative on some atomic
family of the same width. -/
theorem liouvilleSelector_selective {c : ℝ} (hc : robinEulerThreshold liouvilleSelector < c) :
    ∀ᶠ N : ℕ in atTop,
      (∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 →
        0 < weilQuad (atomicTest N (primeHorizonExtension x) (atomDilate liouvilleSelector (c / N)))) ∧
      ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        weilQuadTw (fun n => ArithmeticLorentzianGeometry.liouvilleTwin n *
            ArithmeticFunction.vonMangoldt n)
          (atomicTest N (primeHorizonExtension x) (atomDilate liouvilleSelector (c / N))) < 0 := by
  have hc0 : 0 < c := (robinEulerThreshold_pos _).trans hc
  have hM : 0 < ∫ u, liouvilleSelector u ^ 2 := by
    linarith [integral_liouvilleSelector_sq_ge]
  have hpos := eventually_noRealZero_completeWeilMatrix_posDef contDiff_liouvilleSelector
    (fun _ hu => liouvilleSelector_eq_zero hu) paperFT_liouvilleSelector_ne_zero hc0
  have hlim : Tendsto (fun N : ℕ => c / N * (N : ℝ)) atTop (𝓝 c) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have : (N : ℝ) ≠ 0 := by positivity
      field_simp)
  have hneg := eventually_liouville_weilQuadTw_neg_of_gt_robinEuler contDiff_liouvilleSelector
    (fun _ hu => liouvilleSelector_eq_zero hu) hM robinEulerThreshold_liouvilleSelector_lt_one
    hc
    (w := fun N : ℕ => c / N)
    (by filter_upwards [eventually_ge_atTop 1] with N hN; positivity) hlim
  filter_upwards [hpos, hneg, eventually_ge_atTop 1] with N hP hL hN
  obtain ⟨y, hy⟩ := hL
  refine ⟨fun x hx => ?_, ⟨WithLp.toLp 2 (fun n : PrimeHorizonIndex N => y n), ?_⟩⟩
  · have hx' : WithLp.ofLp x ≠ 0 := fun h => hx (by simpa using congrArg (WithLp.toLp 2) h)
    have hin : 0 < inner ℝ (Matrix.toEuclideanLin (completeWeilMatrix liouvilleSelector c N) x) x := by
      have := hP.dotProduct_mulVec_pos hx'
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simpa [Matrix.toLpLin_apply] using this
    rw [completeWeilMatrix_inner_eq_weilQuad contDiff_liouvilleSelector
      (fun _ hu => liouvilleSelector_eq_zero hu) hc0 hN] at hin
    have hG : 0 < ∫ u, atomDilate liouvilleSelector (c / N) u ^ 2 := by
      rw [integral_atomDilate_sq (div_pos hc0 (by exact_mod_cast hN))]
      exact mul_pos (div_pos hc0 (by exact_mod_cast hN)) hM
    exact (div_pos_iff_of_pos_right hG).mp hin
  · rwa [atomicTest_restrict] at hy

/-- Selectivity at every overlap `c ≥ 1`, at and beyond the touching ratio. -/
theorem liouvilleSelector_selective_of_one_le {c : ℝ} (hc : 1 ≤ c) :
    ∀ᶠ N : ℕ in atTop,
      (∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 →
        0 < weilQuad (atomicTest N (primeHorizonExtension x) (atomDilate liouvilleSelector (c / N)))) ∧
      ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        weilQuadTw (fun n => ArithmeticLorentzianGeometry.liouvilleTwin n *
            ArithmeticFunction.vonMangoldt n)
          (atomicTest N (primeHorizonExtension x) (atomDilate liouvilleSelector (c / N))) < 0 :=
  liouvilleSelector_selective (robinEulerThreshold_liouvilleSelector_lt_one.trans_le hc)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
