import GaloisForLFunctions.RHTower.HedenmalmThetaSeriesExpansion

/-!
# The Hilbert--Schmidt energy of the source inverse

In the intrinsic quantile coordinate the source inverse is `i M_q C`, whose integral kernel against
Lebesgue measure on `(0,1)` is

`K(t,u) = i q(t) (1_{u ≤ t} - t)`.

Its Hilbert--Schmidt energy is computed here in closed form: the inner slice integrates to
`t(1-t)`, so

`∬ |K|² = ∫₀¹ q(t)² t(1-t) dt = M ∫_ℝ p(x)(1-p(x)) / k(x) dx`,

the exact theta-tail expression of the source card.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmHilbertSchmidt

open HedenmalmQuantile

/-- The pinned kernel slice `u ↦ 1_{u ≤ t} - t`. -/
def pinnedKernelSlice (t u : ℝ) : ℝ := (if u ≤ t then (1 : ℝ) else 0) - t

/-- **The inner slice energy.**  The pinned kernel slice has energy `t(1-t)` on the unit
interval. -/
theorem integral_pinnedKernelSlice_sq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫ u in Ioo (0 : ℝ) 1, pinnedKernelSlice t u ^ 2 = t * (1 - t) := by
  have hsplit : Ioo (0 : ℝ) 1 = Ioc 0 t ∪ Ioo t 1 := by
    ext u
    simp only [mem_Ioo, mem_union, mem_Ioc]
    constructor
    · rintro ⟨h0, h1⟩
      rcases le_or_gt u t with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h0, h⟩ | ⟨h, h1⟩)
      · exact ⟨h0, lt_of_le_of_lt h ht.2⟩
      · exact ⟨lt_trans ht.1 h, h1⟩
  have hdisj : Disjoint (Ioc (0 : ℝ) t) (Ioo t 1) := by
    rw [Set.disjoint_left]
    rintro u ⟨_, hu⟩ ⟨hu', _⟩
    exact absurd hu (not_le.mpr hu')
  have hbdd : ∀ u : ℝ, ‖pinnedKernelSlice t u ^ 2‖ ≤ 1 := by
    intro u
    rw [pinnedKernelSlice]
    by_cases h : u ≤ t <;> simp only [h, if_true, if_false] <;>
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] <;> nlinarith [ht.1, ht.2]
  have hmeas : AEStronglyMeasurable (fun u => pinnedKernelSlice t u ^ 2) volume := by
    refine (Measurable.aestronglyMeasurable ?_)
    refine Measurable.pow_const ?_ 2
    refine Measurable.sub ?_ measurable_const
    exact (measurable_const.ite (measurableSet_le measurable_id measurable_const)
      measurable_const)
  have hint : ∀ s : Set ℝ, MeasurableSet s → volume s ≠ ⊤ →
      IntegrableOn (fun u => pinnedKernelSlice t u ^ 2) s volume := by
    intro s hs hfin
    refine Measure.integrableOn_of_bounded hfin hmeas ?_
    filter_upwards with u
    exact hbdd u
  have h1 : IntegrableOn (fun u => pinnedKernelSlice t u ^ 2) (Ioc 0 t) volume :=
    hint _ measurableSet_Ioc (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have h2 : IntegrableOn (fun u => pinnedKernelSlice t u ^ 2) (Ioo t 1) volume :=
    hint _ measurableSet_Ioo (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioo h1 h2]
  have hleft : ∫ u in Ioc (0 : ℝ) t, pinnedKernelSlice t u ^ 2 = t * (1 - t) ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (1 - t) ^ 2) fun u hu => ?_]
    · rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero, smul_eq_mul,
        ENNReal.toReal_ofReal ht.1.le]
    · rw [pinnedKernelSlice, if_pos hu.2]
  have hright : ∫ u in Ioo t (1 : ℝ), pinnedKernelSlice t u ^ 2 = (1 - t) * t ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => t ^ 2) fun u hu => ?_]
    · rw [setIntegral_const, Measure.real, Real.volume_Ioo, smul_eq_mul,
        ENNReal.toReal_ofReal (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)]
    · rw [pinnedKernelSlice, if_neg (not_le.mpr hu.1), zero_sub, neg_pow]
      ring
  rw [hleft, hright]
  ring

/-! ### The Hilbert--Schmidt energy in source coordinates -/

variable (S : PositiveDensitySource)

/-- The reciprocal-tail density `p(1-p)/k` of the source card. -/
def tailEnergyDensity (x : ℝ) : ℝ := S.cdfFun x * (1 - S.cdfFun x) / S.k x

/-- **The Hilbert--Schmidt energy of the source inverse.**  The quantile-coordinate energy of the
pinned kernel is the theta-tail integral `M ∫ p(1-p)/k`. -/
theorem integral_quantileSpeed_sq_slice :
    (∫ t in Ioo (0 : ℝ) 1, quantileSpeed S t ^ 2 * (t * (1 - t)))
      = S.mass * ∫ x, tailEnergyDensity S x := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (S.mass / S.k x) ^ 2 * (S.cdfFun x * (1 - S.cdfFun x)))
      (volume : Measure ℝ) := by
    refine ((continuous_const.div S.continuous_k fun x => (S.pos_k x).ne').pow 2).mul ?_
      |>.aestronglyMeasurable
    exact S.continuous_cdfFun.mul (continuous_const.sub S.continuous_cdfFun)
  have hmain := integral_comp_quantile S
    (fun x => (S.mass / S.k x) ^ 2 * (S.cdfFun x * (1 - S.cdfFun x))) hmeas
  have hleft : (∫ t in Ioo (0 : ℝ) 1,
      (S.mass / S.k (S.quantileFun t)) ^ 2
        * (S.cdfFun (S.quantileFun t) * (1 - S.cdfFun (S.quantileFun t))))
      = ∫ t in Ioo (0 : ℝ) 1, quantileSpeed S t ^ 2 * (t * (1 - t)) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [S.cdfFun_quantile ht, quantileSpeed]
  have hright : (∫ x, S.normalized x •
      ((S.mass / S.k x) ^ 2 * (S.cdfFun x * (1 - S.cdfFun x))))
      = S.mass * ∫ x, tailEnergyDensity S x := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hk : S.k x ≠ 0 := (S.pos_k x).ne'
    have hM : S.mass ≠ 0 := S.mass_ne_zero
    show S.normalized x * ((S.mass / S.k x) ^ 2 * (S.cdfFun x * (1 - S.cdfFun x)))
      = S.mass * tailEnergyDensity S x
    rw [show S.normalized x = S.k x / S.mass from rfl, tailEnergyDensity]
    field_simp
    ring
  rw [← hleft, hmain, hright]

end HedenmalmHilbertSchmidt

end

end RHTower
