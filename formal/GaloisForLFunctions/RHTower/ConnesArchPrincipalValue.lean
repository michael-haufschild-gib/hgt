import Mathlib

/-!
# Connes' archimedean principal values

Formalization of §V (35) and Appendix II (35) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Theorem V.3 produces a canonical principal value `∫'` attached to a basic character; comparing it
with Weil's `Pfw` at the real place goes through two regularizations of the divergent integral
`∫ f d^*x` near the origin, with the multiplicative Haar measure normalized as
`∫_{|λ| ∈ [1,Λ]} d^*λ ~ log Λ`, i.e. `d^*x = dx/(2|x|)`:

  `A_ε(f) = ∫_{|x| ≥ ε} f d^*x + f(0) log ε`     (logarithmic cut-off, §V (35))
  `B_ε(f) = ∫ f |x|^ε d^*x - f(0)/ε`             (power regularization, App. II (35))

* `connesRealLogPV_scale` - §V (35): the exact scaling law `P(f_a) = P(f) - log|a| f(0)`, holding
  at *every* cut-off `ε`, with `f_a(x) = f(ax)`.  This is the identity that shows the Fourier
  transform of `-log|u|` is `ρ^{-1}/|a|` up to a Dirac mass.
* `connesRealLogPV_unitBox`, `connesRealPowerPV_unitBox` - Appendix II (35): both regularizations
  annihilate Connes' reference test function `1_{[-1,1]}`, which is exactly the computation the
  paper offers as justification of (35): the two regularizations can only differ by a multiple of
  `f(0)`, and that multiple vanishes.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Set

/-- The multiplicative Haar measure of `ℝ^*` in Connes' normalization
`∫_{|λ| ∈ [1,Λ]} d^*λ ~ log Λ`, i.e. `d^*x = dx / (2|x|)`. -/
def connesRealMultHaarDensity (x : ℝ) : ℝ := (2 * |x|)⁻¹

/-- The logarithmically regularized principal value of §V (35) at cut-off `ε`. -/
def connesRealLogPV (f : ℝ → ℂ) (ε : ℝ) : ℂ :=
  (∫ x in {x : ℝ | ε ≤ |x|}, f x * (connesRealMultHaarDensity x : ℂ))
    + f 0 * (Real.log ε : ℂ)

theorem measurableSet_connesTail (ε : ℝ) : MeasurableSet {x : ℝ | ε ≤ |x|} :=
  measurableSet_le measurable_const measurable_norm

/-- **§V (35).**  Exact scaling law of the regularized principal value:
`P(f_a) = P(f) - log|a| · f(0)`, where `f_a(x) = f(a x)`.  Stated at each cut-off, so it holds
with no convergence hypothesis. -/
theorem connesRealLogPV_scale (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    connesRealLogPV (fun x => f (a * x)) ε
      = connesRealLogPV f (|a| * ε) - f 0 * (Real.log |a| : ℂ) := by
  have haabs : 0 < |a| := abs_pos.mpr ha
  set H : ℝ → ℂ :=
    Set.indicator {y : ℝ | |a| * ε ≤ |y|} (fun y => f y * (connesRealMultHaarDensity y : ℂ)) with hH
  have hmemiff : ∀ x : ℝ, (a * x ∈ {y : ℝ | |a| * ε ≤ |y|}) ↔ (x ∈ {x : ℝ | ε ≤ |x|}) := by
    intro x
    simp only [mem_setOf_eq, abs_mul]
    constructor
    · intro h; exact le_of_mul_le_mul_left h haabs
    · intro h; exact mul_le_mul_of_nonneg_left h haabs.le
  have hdens : ∀ x : ℝ, x ≠ 0 →
      |a| * connesRealMultHaarDensity (a * x) = connesRealMultHaarDensity x := by
    intro x hx
    have hxa : |x| ≠ 0 := abs_ne_zero.mpr hx
    simp only [connesRealMultHaarDensity, abs_mul]
    field_simp
  have hpt : ∀ x : ℝ,
      Set.indicator {x : ℝ | ε ≤ |x|}
          (fun x => f (a * x) * ((connesRealMultHaarDensity x : ℝ) : ℂ)) x
        = ((|a| : ℝ) : ℂ) * H (a * x) := by
    intro x
    by_cases hx : x ∈ {x : ℝ | ε ≤ |x|}
    · have hxne : x ≠ 0 := by
        intro h
        rw [mem_setOf_eq, h, abs_zero] at hx
        linarith
      rw [Set.indicator_of_mem hx, hH, Set.indicator_of_mem ((hmemiff x).mpr hx)]
      calc f (a * x) * ((connesRealMultHaarDensity x : ℝ) : ℂ)
          = f (a * x) * (((|a| * connesRealMultHaarDensity (a * x)) : ℝ) : ℂ) := by
            rw [hdens x hxne]
        _ = ((|a| : ℝ) : ℂ) * (f (a * x) * ((connesRealMultHaarDensity (a * x) : ℝ) : ℂ)) := by
            rw [Complex.ofReal_mul]; ring
    · rw [Set.indicator_of_notMem hx, hH,
        Set.indicator_of_notMem (fun hc => hx ((hmemiff x).mp hc)), mul_zero]
  have hne : ((|a| : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt haabs
  have hint : ∫ x in {x : ℝ | ε ≤ |x|}, f (a * x) * ((connesRealMultHaarDensity x : ℝ) : ℂ)
      = ∫ y in {y : ℝ | |a| * ε ≤ |y|}, f y * ((connesRealMultHaarDensity y : ℝ) : ℂ) := by
    rw [← integral_indicator (measurableSet_connesTail ε),
      ← integral_indicator (measurableSet_connesTail (|a| * ε))]
    simp only [hpt]
    rw [integral_const_mul, Measure.integral_comp_mul_left H a, Complex.real_smul,
      abs_inv, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  simp only [connesRealLogPV, mul_zero]
  rw [hint, Real.log_mul (ne_of_gt haabs) (ne_of_gt hε), Complex.ofReal_add]
  ring

/-- The power-regularized principal value of Appendix II (35) at exponent `ε`. -/
def connesRealPowerPV (f : ℝ → ℂ) (ε : ℝ) : ℂ :=
  (∫ x : ℝ, f x * (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ)) - f 0 / (ε : ℂ)

/-- Connes' reference test function `1_{[-1,1]}`. -/
def connesUnitBox : ℝ → ℂ := Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => (1 : ℂ))

theorem connesUnitBox_zero : connesUnitBox 0 = 1 := by
  rw [connesUnitBox, Set.indicator_of_mem (by norm_num)]

theorem connesTail_inter_box {ε : ℝ} (hε : 0 < ε) :
    {x : ℝ | ε ≤ |x|} ∩ Set.Icc (-1 : ℝ) 1
      = Set.Icc (-1 : ℝ) (-ε) ∪ Set.Icc ε 1 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_union]
  constructor
  · rintro ⟨habs, h1, h2⟩
    rcases le_or_gt x 0 with hx | hx
    · left
      refine ⟨h1, ?_⟩
      rw [abs_of_nonpos hx] at habs
      linarith
    · right
      refine ⟨?_, h2⟩
      rw [abs_of_pos hx] at habs
      exact habs
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨?_, h1, by linarith⟩
      rw [abs_of_nonpos (by linarith)]
      linarith
    · exact ⟨by rw [abs_of_nonneg (by linarith)]; exact h1, by linarith, h2⟩

/-- **Appendix II (35), left-hand side.**  The logarithmic regularization annihilates Connes'
reference test function `1_{[-1,1]}` at every cut-off. -/
theorem connesRealLogPV_unitBox {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    connesRealLogPV connesUnitBox ε = 0 := by
  have hmeasBox : MeasurableSet (Set.Icc (-1 : ℝ) 1) := measurableSet_Icc
  have hdisj : Disjoint (Set.Icc (-1 : ℝ) (-ε)) (Set.Icc ε 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ ⟨hx3, -⟩
    linarith
  have hcont : ContinuousOn (fun x : ℝ => ((connesRealMultHaarDensity x : ℝ) : ℂ))
      (Set.Icc (-1 : ℝ) (-ε) ∪ Set.Icc ε 1) := by
    have hofReal : Continuous (fun r : ℝ => (r : ℂ)) := Complex.continuous_ofReal
    refine hofReal.comp_continuousOn ?_
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    rintro x (⟨-, hx2⟩ | ⟨hx1, -⟩)
    · have : x < 0 := lt_of_le_of_lt hx2 (by linarith)
      have : |x| > 0 := abs_pos.mpr (ne_of_lt this)
      positivity
    · have : (0:ℝ) < x := lt_of_lt_of_le hε hx1
      have : |x| > 0 := abs_pos.mpr (ne_of_gt this)
      positivity
  have hint1 : IntegrableOn (fun x : ℝ => ((connesRealMultHaarDensity x : ℝ) : ℂ))
      (Set.Icc (-1 : ℝ) (-ε)) :=
    (hcont.mono Set.subset_union_left).integrableOn_compact isCompact_Icc
  have hint2 : IntegrableOn (fun x : ℝ => ((connesRealMultHaarDensity x : ℝ) : ℂ))
      (Set.Icc ε 1) :=
    (hcont.mono Set.subset_union_right).integrableOn_compact isCompact_Icc
  have hbox : ∀ x : ℝ, connesUnitBox x * ((connesRealMultHaarDensity x : ℝ) : ℂ)
      = Set.indicator (Set.Icc (-1:ℝ) 1)
          (fun x => ((connesRealMultHaarDensity x : ℝ) : ℂ)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-1:ℝ) 1
    · rw [connesUnitBox, Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [connesUnitBox, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hsplit : ∫ x in {x : ℝ | ε ≤ |x|}, connesUnitBox x * ((connesRealMultHaarDensity x : ℝ) : ℂ)
      = (∫ x in Set.Icc (-1:ℝ) (-ε), ((connesRealMultHaarDensity x : ℝ) : ℂ))
        + ∫ x in Set.Icc ε 1, ((connesRealMultHaarDensity x : ℝ) : ℂ) := by
    simp only [hbox]
    rw [setIntegral_indicator hmeasBox, connesTail_inter_box hε,
      setIntegral_union hdisj measurableSet_Icc hint1 hint2]
  have hpos : ∫ x in Set.Icc ε 1, ((connesRealMultHaarDensity x : ℝ) : ℂ)
      = ((-(Real.log ε) / 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : ε ≤ (1:ℝ))]
    have hcongr : ∀ x ∈ Set.uIoc ε (1:ℝ),
        ((connesRealMultHaarDensity x : ℝ) : ℂ) = ((2:ℂ))⁻¹ * ((x⁻¹ : ℝ) : ℂ) := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith : ε ≤ (1:ℝ))] at hx
      have hx0 : (0:ℝ) < x := lt_trans hε hx.1
      simp only [connesRealMultHaarDensity, abs_of_pos hx0]
      rw [mul_inv]
      push_cast
      ring
    rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hcongr),
      intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_ofReal, integral_inv (by
      rw [Set.uIcc_of_le (by linarith : ε ≤ (1:ℝ))]
      simp only [Set.mem_Icc, not_and, not_le]
      intro h
      linarith)]
    rw [one_div, Real.log_inv]
    push_cast
    ring
  have hneg : ∫ x in Set.Icc (-1:ℝ) (-ε), ((connesRealMultHaarDensity x : ℝ) : ℂ)
      = ((-(Real.log ε) / 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (-1:ℝ) ≤ -ε)]
    have hcongr : ∀ x ∈ Set.uIoc (-1:ℝ) (-ε),
        ((connesRealMultHaarDensity x : ℝ) : ℂ) = (-((2:ℂ))⁻¹) * ((x⁻¹ : ℝ) : ℂ) := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith : (-1:ℝ) ≤ -ε)] at hx
      have hx0 : x < 0 := lt_of_le_of_lt hx.2 (by linarith)
      simp only [connesRealMultHaarDensity, abs_of_neg hx0]
      rw [mul_inv]
      push_cast
      field_simp
    rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hcongr),
      intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_ofReal, integral_inv (by
      rw [Set.uIcc_of_le (by linarith : (-1:ℝ) ≤ -ε)]
      simp only [Set.mem_Icc, not_and, not_le]
      intro h
      linarith)]
    have : (-ε) / (-1 : ℝ) = ε := by field_simp
    rw [this]
    push_cast
    ring
  rw [connesRealLogPV, hsplit, hpos, hneg, connesUnitBox_zero]
  push_cast
  ring

/-- **Appendix II (35), right-hand side.**  The power regularization also annihilates
`1_{[-1,1]}`, at every exponent.  Together with `connesRealLogPV_unitBox` this is exactly Connes'
justification of (35): the two regularizations differ by a multiple of `f(0)`, and that multiple is
computed on `1_{[-1,1]}`, where both vanish. -/
theorem connesRealPowerPV_unitBox {ε : ℝ} (hε : 0 < ε) :
    connesRealPowerPV connesUnitBox ε = 0 := by
  set g : ℝ → ℂ := fun x => (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ) with hg
  have heven : ∀ x : ℝ, g (-x) = g x := by
    intro x; simp [hg, connesRealMultHaarDensity]
  have hbox : ∀ x : ℝ, connesUnitBox x * (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ)
      = Set.indicator (Set.Icc (-1:ℝ) 1) g x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-1:ℝ) 1
    · rw [connesUnitBox, Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [connesUnitBox, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hrpow : ∀ x : ℝ, 0 < x → g x = ((2:ℂ))⁻¹ * ((x ^ (ε - 1) : ℝ) : ℂ) := by
    intro x hx
    simp only [hg, connesRealMultHaarDensity, abs_of_pos hx]
    rw [Real.rpow_sub hx, Real.rpow_one]
    push_cast
    field_simp
  have hiiR : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => ((2:ℂ))⁻¹ * ((x ^ (ε - 1) : ℝ) : ℂ))
      volume a b := by
    intro a b
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ (ε - 1)) volume a b :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    exact IntervalIntegrable.const_mul (⟨h0.1.ofReal, h0.2.ofReal⟩) _
  have hii : IntervalIntegrable (fun x : ℝ => ((2:ℂ))⁻¹ * ((x ^ (ε - 1) : ℝ) : ℂ)) volume 0 1 :=
    hiiR 0 1
  have hposhalf : ∫ x in (0:ℝ)..1, g x = ((2:ℂ))⁻¹ * ((1 / ε : ℝ) : ℂ) := by
    have hcongr : ∫ x in (0:ℝ)..1, g x
        = ∫ x in (0:ℝ)..1, ((2:ℂ))⁻¹ * ((x ^ (ε - 1) : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro x hx
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      exact hrpow x hx.1
    rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_rpow (Or.inl (by linarith))]
    have h1 : (1:ℝ) ^ (ε - 1 + 1) = 1 := Real.one_rpow _
    have h0 : (0:ℝ) ^ (ε - 1 + 1) = 0 := Real.zero_rpow (by linarith)
    rw [h1, h0]
    push_cast
    ring_nf
  have hneghalf : ∫ x in (-1:ℝ)..0, g x = ((2:ℂ))⁻¹ * ((1 / ε : ℝ) : ℂ) := by
    have hflip : ∫ x in (-1:ℝ)..0, g x = ∫ x in (0:ℝ)..1, g x := by
      have := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := (0:ℝ)) g
      simp only [heven] at this
      simpa using this
    rw [hflip, hposhalf]
  have hiig : IntervalIntegrable g volume 0 1 := by
    refine IntervalIntegrable.congr ?_ hii
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    exact (hrpow x hx.1).symm
  have hiig' : IntervalIntegrable g volume (-1) 0 := by
    have hneg : IntervalIntegrable
        (fun x : ℝ => ((2:ℂ))⁻¹ * (((-x) ^ (ε - 1) : ℝ) : ℂ)) volume (-1) 0 := by
      have h := (IntervalIntegrable.iff_comp_neg
        (f := fun x : ℝ => ((2:ℂ))⁻¹ * ((x ^ (ε - 1) : ℝ) : ℂ)) (a := (1:ℝ)) (b := (0:ℝ))
        (by finiteness)).mp (hiiR 1 0)
      simpa using h
    have hae : (fun x : ℝ => ((2:ℂ))⁻¹ * (((-x) ^ (ε - 1) : ℝ) : ℂ))
        =ᵐ[volume.restrict (Set.Ioc (-1:ℝ) 0)] g := by
      have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
        have h0 : (volume : Measure ℝ) {(0:ℝ)} = 0 := Real.volume_singleton
        have := compl_mem_ae_iff.2 h0
        filter_upwards [this] with x hx
        simpa using hx
      filter_upwards [MeasureTheory.ae_restrict_of_ae hne,
        MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx0 hxmem
      have hxlt : x < 0 := lt_of_le_of_ne hxmem.2 hx0
      have hxneg : 0 < -x := by linarith
      rw [← heven x]
      exact (hrpow (-x) hxneg).symm
    refine ⟨(hneg.1).congr hae, ?_⟩
    rw [Set.Ioc_eq_empty (by norm_num : ¬ (0:ℝ) < -1)]
    exact integrableOn_empty
  have hfull : ∫ x : ℝ, connesUnitBox x * (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ)
      = ((1 / ε : ℝ) : ℂ) := by
    simp only [hbox]
    rw [integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
      ← intervalIntegral.integral_add_adjacent_intervals hiig' hiig, hneghalf, hposhalf]
    push_cast
    ring
  rw [connesRealPowerPV, hfull, connesUnitBox_zero]
  push_cast
  simp

end

end GaloisForLFunctions.RHTower
