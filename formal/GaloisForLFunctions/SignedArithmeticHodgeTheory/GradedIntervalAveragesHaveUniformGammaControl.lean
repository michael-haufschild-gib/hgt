import GaloisForLFunctions.SignedArithmeticHodgeTheory.ComparableIntervalsHaveComparableGammaKernels
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaMeanVarianceCapacity

/-!
# Homogeneous Gamma control of graded interval averages

The actual energy of a piecewise constant average splits into its interval
rectangles and exterior rows. Uniform comparison of these kernels with the
far-end conductances lets the original source pay the entire averaged energy.
Adjacent intervals use integrated boundary defects. Nonzero exterior rows
require a width-scale separation, which zero padding supplies on a finite grid.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open ArithmeticCastelnuovoSeveri.MeanZeroIntervals
open ArithmeticCastelnuovoSeveri.IntervalVariance
open ArithmeticCastelnuovoSeveri.LogCells HTGeometry BiarithmeticGaugeGeometry

private theorem lintegral_eq_finite_intervals_and_exterior {ι : Type*} [Fintype ι]
    (I : ι → Set ℝ) (hIm : ∀ i, MeasurableSet (I i))
    (hpd : Pairwise (Function.onFun Disjoint I)) (g : ℝ → ℝ≥0∞) :
    (∫⁻ x, g x) = (∑ i, ∫⁻ x in I i, g x) + ∫⁻ x in (⋃ i, I i)ᶜ, g x := by
  have hU : MeasurableSet (⋃ i, I i) := MeasurableSet.iUnion hIm
  calc
    _ = ∫⁻ x in (⋃ i, I i) ∪ (⋃ i, I i)ᶜ, g x := by
      rw [union_compl_self, Measure.restrict_univ]
    _ = (∫⁻ x in ⋃ i, I i, g x) + ∫⁻ x in (⋃ i, I i)ᶜ, g x :=
      lintegral_union hU.compl disjoint_compl_right
    _ = _ := by rw [lintegral_iUnion hIm hpd, tsum_fintype]

/-- Exact finite interval decomposition of a symmetric kernel with zero exterior square. -/
theorem lintegral_symmetric_eq_interval_blocks {ι : Type*} [Fintype ι]
    (I : ι → Set ℝ) (hIm : ∀ i, MeasurableSet (I i))
    (hpd : Pairwise (Function.onFun Disjoint I))
    {h : ℝ → ℝ → ℝ≥0∞} (hm : Measurable fun p : ℝ × ℝ => h p.1 p.2)
    (hs : ∀ x y, h x y = h y x)
    (hz : (∫⁻ x in (⋃ i, I i)ᶜ, ∫⁻ y in (⋃ i, I i)ᶜ, h x y) = 0) :
    (∫⁻ x, ∫⁻ y, h x y) =
      (∑ i, ∑ j, ∫⁻ x in I i, ∫⁻ y in I j, h x y) +
        2 * ∑ i, ∫⁻ x in I i, ∫⁻ y in (⋃ j, I j)ᶜ, h x y := by
  let F := (⋃ j, I j)ᶜ
  have hGm : ∀ A : Set ℝ, Measurable fun x => ∫⁻ y in A, h x y :=
    fun _ => hm.lintegral_prod_right'
  have hinner (x : ℝ) : (∫⁻ y, h x y) = (∑ j, ∫⁻ y in I j, h x y) + ∫⁻ y in F, h x y :=
    lintegral_eq_finite_intervals_and_exterior I hIm hpd (h x)
  have hsrc (i : ι) : (∫⁻ x in I i, ∫⁻ y, h x y) =
      (∑ j, ∫⁻ x in I i, ∫⁻ y in I j, h x y) + ∫⁻ x in I i, ∫⁻ y in F, h x y := by
    rw [lintegral_congr fun x => hinner x,
      lintegral_add_left (Finset.measurable_sum _ fun j _ => hGm (I j)),
      lintegral_finsetSum _ fun j _ => hGm (I j)]
  have hfree : (∫⁻ x in F, ∫⁻ y, h x y) = ∑ i, ∫⁻ x in I i, ∫⁻ y in F, h x y := by
    rw [lintegral_congr fun x => hinner x,
      lintegral_add_left (Finset.measurable_sum _ fun j _ => hGm (I j)),
      lintegral_finsetSum _ fun j _ => hGm (I j), hz, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_lintegral_swap hm.aemeasurable]
    exact lintegral_congr fun y => lintegral_congr fun x => hs x y
  calc
    _ = (∑ i, ∫⁻ x in I i, ∫⁻ y, h x y) + ∫⁻ x in F, ∫⁻ y, h x y :=
      lintegral_eq_finite_intervals_and_exterior I hIm hpd _
    _ = (∑ i, ((∑ j, ∫⁻ x in I i, ∫⁻ y in I j, h x y) +
        ∫⁻ x in I i, ∫⁻ y in F, h x y)) + ∑ i, ∫⁻ x in I i, ∫⁻ y in F, h x y := by
      rw [Finset.sum_congr rfl fun i _ => hsrc i, hfree]
    _ = _ := by rw [Finset.sum_add_distrib, two_mul, add_assoc]

private theorem gamma_pair_of_constants (g : ℝ → ℝ) (a b c d u v : ℝ)
    (hu : ∀ x ∈ Ioo a b, g x = u) (hv : ∀ y ∈ Ioo c d, g y = v) :
    (∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, gammaDifference g x y) =
      ENNReal.ofReal ((u - v) ^ 2) * gammaIntervalKernel a b c d := by
  calc
    _ = ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d,
        ENNReal.ofReal ((u - v) ^ 2) * ENNReal.ofReal (archLevyDensity |y - x|) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
      rw [gammaDifference, hu x hx, hv y hy, ENNReal.ofReal_mul (sq_nonneg _)]
    _ = _ := by
      simp only [gammaIntervalKernel, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem gamma_exterior_of_constant (g : ℝ → ℝ) (a b u : ℝ) (F : Set ℝ)
    (hu : ∀ x ∈ Ioo a b, g x = u) (hz : ∀ᵐ y ∂volume.restrict F, g y = 0) :
    (∫⁻ x in Ioo a b, ∫⁻ y in F, gammaDifference g x y) =
      ENNReal.ofReal (u ^ 2) *
        (∫⁻ x in Ioo a b, ∫⁻ y in F, ENNReal.ofReal (archLevyDensity |y - x|)) := by
  calc
    _ = ∫⁻ x in Ioo a b, ∫⁻ y in F,
        ENNReal.ofReal (u ^ 2) * ENNReal.ofReal (archLevyDensity |y - x|) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      apply lintegral_congr_ae
      filter_upwards [hz] with y hy
      rw [gammaDifference, hu x hx, hy, sub_zero, ENNReal.ofReal_mul (sq_nonneg _)]
    _ = _ := by simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem comparable_gamma_rectangle {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hu : b - a ≤ 1) (hv : d - c ≤ 1)
    (hsep : b ≤ c ∨ d ≤ a)
    (htouch : (b = c → b - a ≤ 3 * (d - c) ∧ d - c ≤ 3 * (b - a)) ∧
      (d = a → d - c ≤ 3 * (b - a) ∧ b - a ≤ 3 * (d - c)))
    (hgap : (b < c → b - a ≤ 3 * (c - b) ∧ d - c ≤ 3 * (c - b)) ∧
      (d < a → d - c ≤ 3 * (a - d) ∧ b - a ≤ 3 * (a - d))) :
    gammaIntervalKernel a b c d ≤ ENNReal.ofReal
      (stoppingGammaKernelConstant * ((b - a) * (d - c) *
        archLevyDensity (max (d - a) (b - c)))) := by
  rcases hsep with hr | hl
  · rw [max_eq_left (by linarith only [hab, hcd, hr])]
    rcases eq_or_lt_of_le hr with he | he
    · subst c
      exact gammaIntervalKernel_le_stopping_of_touching hab hcd hu hv
        (htouch.1 rfl).1 (htouch.1 rfl).2
    · exact gammaIntervalKernel_le_stopping_of_gap hab he hcd hu hv
        (hgap.1 he).1 (hgap.1 he).2
  · rw [gammaIntervalKernel_comm, max_eq_right (by linarith only [hab, hcd, hl])]
    have h : gammaIntervalKernel c d a b ≤ ENNReal.ofReal
        (stoppingGammaKernelConstant * ((d - c) * (b - a) * archLevyDensity (b - c))) := by
      rcases eq_or_lt_of_le hl with he | he
      · subst a
        exact gammaIntervalKernel_le_stopping_of_touching hcd hab hv hu
          (htouch.2 rfl).1 (htouch.2 rfl).2
      · exact gammaIntervalKernel_le_stopping_of_gap hcd he hab hv hu
          (hgap.2 he).1 (hgap.2 he).2
    convert h using 1 <;> congr 1 <;> ring

/-- Short graded interval averages have a homogeneous Gamma bound with one universal constant.
The geometric assumptions control touching pairs, separated pairs and the nonzero exterior rows. -/
theorem levyEnergy_interval_average_le {ι : Type*} [Fintype ι]
    (L U : ι → ℝ) (f g : ℝ → ℝ)
    (hab : ∀ i, L i < U i) (hw : ∀ i, U i - L i ≤ 1)
    (hsep : ∀ i j, i ≠ j → U i ≤ L j ∨ U j ≤ L i)
    (htouch : ∀ i j, U i = L j →
      U i - L i ≤ 3 * (U j - L j) ∧ U j - L j ≤ 3 * (U i - L i))
    (hgap : ∀ i j, U i < L j →
      U i - L i ≤ 3 * (L j - U i) ∧ U j - L j ≤ 3 * (L j - U i))
    (hfv : BoundedVariationOn f univ) (hfc : HasCompactSupport f)
    (hgv : BoundedVariationOn g univ) (hgc : HasCompactSupport g)
    (hg : ∀ i x, x ∈ Ioo (L i) (U i) → g x = intervalMean (L i) (U i) f)
    (hfz : ∀ᵐ y ∂volume.restrict (⋃ i, Ioo (L i) (U i))ᶜ, f y = 0)
    (hgz : ∀ᵐ y ∂volume.restrict (⋃ i, Ioo (L i) (U i))ᶜ, g y = 0)
    (hext : ∀ i, intervalMean (L i) (U i) f ≠ 0 →
      ∀ᵐ y ∂volume.restrict (⋃ i, Ioo (L i) (U i))ᶜ,
        U i + (U i - L i) / 3 ≤ y ∨ y + (U i - L i) / 3 ≤ L i) :
    levyEnergy g ≤ stoppingGammaKernelConstant * levyEnergy f := by
  let I : ι → Set ℝ := fun i => Ioo (L i) (U i)
  let F := (⋃ i, I i)ᶜ
  let q : ι → ℝ := fun i => intervalMean (L i) (U i) f
  let C : ℝ≥0∞ := ENNReal.ofReal stoppingGammaKernelConstant
  let G : ℝ≥0∞ := ∑ i, ∑ j, gammaMeanPairCharge (L i) (U i) (L j) (U j) f
  let E : ℝ≥0∞ := ∑ i, gammaExteriorMeanCharge (L i) (U i) F f
  have hIm (i : ι) : MeasurableSet (I i) := measurableSet_Ioo
  have hpd : Pairwise (Function.onFun Disjoint I) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hi hj
    rcases hsep i j hij with h | h <;> dsimp only [I] at hi hj <;>
      linarith only [h, hi.1, hi.2, hj.1, hj.2]
  have hpair (i j : ι) : (∫⁻ x in I i, ∫⁻ y in I j, gammaDifference g x y) ≤
      C * gammaMeanPairCharge (L i) (U i) (L j) (U j) f := by
    rw [gamma_pair_of_constants g (L i) (U i) (L j) (U j) (q i) (q j) (hg i) (hg j)]
    by_cases hij : i = j
    · subst j
      simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), ENNReal.ofReal_zero,
        zero_mul, gammaMeanPairCharge_self, mul_zero, le_refl]
    · have hk := comparable_gamma_rectangle (hab i) (hab j) (hw i) (hw j)
        (hsep i j hij) ⟨htouch i j, htouch j i⟩ ⟨hgap i j, hgap j i⟩
      refine (mul_le_mul_left hk (ENNReal.ofReal ((q i - q j) ^ 2))).trans_eq ?_
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      dsimp only [C, gammaMeanPairCharge, gammaMeanPairEnergy, q]
      rw [← ENNReal.ofReal_mul stoppingGammaKernelConstant_pos.le]
      congr 1
      ring
  have houter (i : ι) : (∫⁻ x in I i, ∫⁻ y in F, gammaDifference g x y) ≤
      C * gammaExteriorMeanCharge (L i) (U i) F f := by
    rw [gamma_exterior_of_constant g (L i) (U i) (q i) F (hg i) hgz]
    by_cases hq : q i = 0
    · simp only [hq, zero_pow (by norm_num : 2 ≠ 0), ENNReal.ofReal_zero, zero_mul]
      exact bot_le
    · have hrow : (∫⁻ x in I i, ∫⁻ y in F, ENNReal.ofReal (archLevyDensity |y - x|)) ≤
          C * (ENNReal.ofReal (U i - L i) * ∫⁻ y in F, gammaFarCharge (L i) (U i) y) := by
        calc
          _ ≤ ∫⁻ _x in I i, ∫⁻ y in F, C * gammaFarCharge (L i) (U i) y := by
            refine setLIntegral_mono' measurableSet_Ioo fun x hx => ?_
            apply lintegral_mono_ae
            filter_upwards [hext i hq] with y hy
            exact gammaKernel_le_stopping_far_of_gap hx (hw i) hy
          _ = _ := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const,
              Measure.restrict_apply_univ, Real.volume_Ioo]
            ring
      have he : gammaExteriorMeanCharge (L i) (U i) F f =
          ENNReal.ofReal ((U i - L i) * (q i) ^ 2) *
            ∫⁻ y in F, gammaFarCharge (L i) (U i) y := by
        unfold gammaExteriorMeanCharge
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr_ae
        filter_upwards [hfz] with y hy
        rw [hy, sub_zero]
      refine (mul_le_mul_left hrow (ENNReal.ofReal ((q i) ^ 2))).trans_eq ?_
      rw [he, ENNReal.ofReal_mul (sub_pos.mpr (hab i)).le]
      ring
  have hzero : (∫⁻ x in F, ∫⁻ y in F, gammaDifference g x y) = 0 := by
    calc
      _ = ∫⁻ _x in F, ∫⁻ _y in F, (0 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [hgz] with x hx
        apply lintegral_congr_ae
        filter_upwards [hgz] with y hy
        simp only [gammaDifference, hx, hy, sub_self, zero_pow (by norm_num : 2 ≠ 0),
          zero_mul, ENNReal.ofReal_zero]
      _ = 0 := by simp only [lintegral_zero]
  have hupper : 2 * ENNReal.ofReal (levyEnergy g) ≤ C * (G + 2 * E) := by
    rw [← gammaDifference_eq_two_levyEnergy hgv hgc,
      lintegral_symmetric_eq_interval_blocks I hIm hpd
        (measurable_gammaDifference (measurable_of_boundedVariation_univ hgv))
        (gammaDifference_comm g) hzero]
    calc
      _ ≤ (∑ i, ∑ j, C * gammaMeanPairCharge (L i) (U i) (L j) (U j) f) +
          2 * ∑ i, C * gammaExteriorMeanCharge (L i) (U i) F f :=
        add_le_add (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j)
          (mul_le_mul_right (Finset.sum_le_sum fun i _ => houter i) 2)
      _ = _ := by simp only [G, E, Finset.mul_sum, mul_add]; ring
  have hcapacity := gamma_coherent_mean_variance_farCharge L U hab hsep
    (measurable_of_boundedVariation_univ hfv) (memLp_compact_bv hfv hfc)
  have hlower : G + 2 * E ≤ 2 * ENNReal.ofReal (levyEnergy f) := by
    rw [← gammaDifference_eq_two_levyEnergy hfv hfc]
    refine le_trans ?_ hcapacity
    change G + 2 * E ≤ _ + G + 2 * E
    exact add_le_add (le_add_self) le_rfl
  have hbound := hupper.trans (mul_le_mul_left hlower C)
  have hΓ : 0 ≤ levyEnergy f := by
    rw [← norm_levyVector_sq f hfv hfc]
    exact sq_nonneg _
  have hleft : ENNReal.ofReal (2 * levyEnergy g) = 2 * ENNReal.ofReal (levyEnergy g) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat]
  have hright : ENNReal.ofReal (2 * (stoppingGammaKernelConstant * levyEnergy f)) =
      C * (2 * ENNReal.ofReal (levyEnergy f)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul stoppingGammaKernelConstant_pos.le]
    norm_num only [ENNReal.ofReal_ofNat]
    dsimp only [C]
    ring
  rw [← hleft, ← hright] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (mul_nonneg stoppingGammaKernelConstant_pos.le hΓ))).mp hbound
  linarith only [hreal]

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.levyEnergy_interval_average_le
