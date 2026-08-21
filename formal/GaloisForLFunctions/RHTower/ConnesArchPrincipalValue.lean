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
* `connesRealLogPV_tendsto_of_zero`, `connesRealPowerPV_tendsto_of_zero` - both regularizations
  converge to `∫ f d^*x` for a test function vanishing at the origin (dominated convergence).
* `connes_logPV_sub_powerPV_tendsto` - **Appendix II (35) in full**: for any measurable `f` whose
  origin-corrected part `f - f(0) 1_{[-1,1]}` is dominated by an integrable `‖·‖(1+|x|) d^*x`,
  `A_ε(f) - B_ε(f) → 0` as `ε → 0⁺`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Set

/-- The multiplicative Haar measure of `ℝ^*` in Connes' normalization
`∫_{|λ| ∈ [1,Λ]} d^*λ ~ log Λ`, i.e. `d^*x = dx / (2|x|)`. -/
def connesRealMultHaarDensity (x : ℝ) : ℝ := (2 * |x|)⁻¹

theorem measurable_connesRealMultHaarDensity : Measurable connesRealMultHaarDensity := by
  unfold connesRealMultHaarDensity
  fun_prop

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

/-! ### Integrability of the reference test function -/

theorem connesUnitBox_mul_eq_indicator (g : ℝ → ℂ) (x : ℝ) :
    connesUnitBox x * g x = Set.indicator (Set.Icc (-1:ℝ) 1) g x := by
  by_cases hx : x ∈ Set.Icc (-1:ℝ) 1
  · rw [connesUnitBox, Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
  · rw [connesUnitBox, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

theorem connesUnitBox_integrableOn_tail {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => connesUnitBox x * ((connesRealMultHaarDensity x : ℝ) : ℂ))
      {x : ℝ | ε ≤ |x|} := by
  have hfun : (fun x : ℝ => connesUnitBox x * ((connesRealMultHaarDensity x : ℝ) : ℂ))
      = Set.indicator (Set.Icc (-1:ℝ) 1)
        (fun x : ℝ => ((connesRealMultHaarDensity x : ℝ) : ℂ)) :=
    funext (connesUnitBox_mul_eq_indicator _)
  rw [hfun, integrableOn_indicator_iff measurableSet_Icc]
  have hinter : Set.Icc (-1:ℝ) 1 ∩ {x : ℝ | ε ≤ |x|}
      = Set.Icc (-1:ℝ) (-ε) ∪ Set.Icc ε 1 := by
    rw [Set.inter_comm, connesTail_inter_box hε]
  rw [hinter]
  have hcont : ContinuousOn (fun x : ℝ => ((connesRealMultHaarDensity x : ℝ) : ℂ))
      (Set.Icc (-1:ℝ) (-ε) ∪ Set.Icc ε 1) := by
    have hofReal : Continuous (fun r : ℝ => (r : ℂ)) := Complex.continuous_ofReal
    refine hofReal.comp_continuousOn ?_
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    rintro x (⟨-, hx2⟩ | ⟨hx1, -⟩)
    · have hxneg : x < 0 := lt_of_le_of_lt hx2 (by linarith)
      have : |x| > 0 := abs_pos.mpr (ne_of_lt hxneg)
      positivity
    · have hxpos : (0:ℝ) < x := lt_of_lt_of_le hε hx1
      have : |x| > 0 := abs_pos.mpr (ne_of_gt hxpos)
      positivity
  exact ((hcont.mono Set.subset_union_left).integrableOn_compact isCompact_Icc).union
    ((hcont.mono Set.subset_union_right).integrableOn_compact isCompact_Icc)

theorem connesUnitBox_integrable_power {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ =>
      connesUnitBox x * (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ)) := by
  set g : ℝ → ℂ := fun x => (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ) with hg
  have hfun : (fun x : ℝ => connesUnitBox x * g x)
      = Set.indicator (Set.Icc (-1:ℝ) 1) g := funext (connesUnitBox_mul_eq_indicator _)
  have heven : ∀ x : ℝ, g (-x) = g x := by
    intro x; simp [hg, connesRealMultHaarDensity]
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
  have hiig : IntervalIntegrable g volume 0 1 := by
    refine IntervalIntegrable.congr ?_ (hiiR 0 1)
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
  have hIcc : IntegrableOn g (Set.Icc (-1:ℝ) 1) := by
    have hunion : Set.Icc (-1:ℝ) 1 = Set.Icc (-1:ℝ) 0 ∪ Set.Icc (0:ℝ) 1 := by
      rw [Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
    rw [hunion]
    have h1 : IntegrableOn g (Set.Icc (-1:ℝ) 0) := by
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1:ℝ) ≤ 0)]
      exact hiig'
    have h2 : IntegrableOn g (Set.Icc (0:ℝ) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact hiig
    exact h1.union h2
  rw [hfun]
  rw [← integrableOn_univ, integrableOn_indicator_iff measurableSet_Icc]
  simpa using hIcc

/-! ### The limit form of Appendix II (35) -/

open Filter Topology

/-- The tail cut-off converges: if `f` vanishes at the origin, the logarithmically regularized
principal value is just the tail integral and converges to the full integral. -/
theorem connesRealLogPV_tendsto_of_zero {f : ℝ → ℂ} (hf0 : f 0 = 0)
    (hint : Integrable (fun x : ℝ => f x * ((connesRealMultHaarDensity x : ℝ) : ℂ))) :
    Tendsto (fun ε : ℝ => connesRealLogPV f ε) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ, f x * ((connesRealMultHaarDensity x : ℝ) : ℂ))) := by
  set F : ℝ → ℂ := fun x => f x * ((connesRealMultHaarDensity x : ℝ) : ℂ) with hF
  have hpv : ∀ ε : ℝ, connesRealLogPV f ε = ∫ x : ℝ, Set.indicator {x : ℝ | ε ≤ |x|} F x := by
    intro ε
    rw [connesRealLogPV, hf0, zero_mul, add_zero,
      integral_indicator (measurableSet_connesTail ε)]
  simp only [hpv]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖) ?_ ?_ hint.norm ?_
  · filter_upwards with ε
    exact (hint.aestronglyMeasurable).indicator (measurableSet_connesTail ε)
  · filter_upwards with ε
    filter_upwards with x
    by_cases hx : x ∈ {x : ℝ | ε ≤ |x|}
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact norm_nonneg _
  · have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
      have h0 : (volume : Measure ℝ) {(0:ℝ)} = 0 := Real.volume_singleton
      have := compl_mem_ae_iff.2 h0
      filter_upwards [this] with x hx
      simpa using hx
    filter_upwards [hne] with x hx
    have hxpos : (0:ℝ) < |x| := abs_pos.mpr hx
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := F x))
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hxpos)] with ε hε
    have hε' : ε < |x| := hε
    have hmem : x ∈ {y : ℝ | ε ≤ |y|} := le_of_lt hε'
    exact (Set.indicator_of_mem hmem F).symm

/-- The power regularization converges: if `f` vanishes at the origin and is dominated by an
integrable weight `‖f‖ (1+|x|) d^*x`, the power-regularized principal value converges to the same
integral. -/
theorem connesRealPowerPV_tendsto_of_zero {f : ℝ → ℂ} (hf0 : f 0 = 0)
    (hmeas : AEStronglyMeasurable f volume)
    (hdom : Integrable (fun x : ℝ =>
      ‖f x‖ * ((1 + |x|) * connesRealMultHaarDensity x))) :
    Tendsto (fun ε : ℝ => connesRealPowerPV f ε) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ, f x * ((connesRealMultHaarDensity x : ℝ) : ℂ))) := by
  have hpv : ∀ ε : ℝ, connesRealPowerPV f ε
      = ∫ x : ℝ, f x * (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ) := by
    intro ε
    rw [connesRealPowerPV, hf0, zero_div, sub_zero]
  simp only [hpv]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖f x‖ * ((1 + |x|) * connesRealMultHaarDensity x)) ?_ ?_ hdom ?_
  · filter_upwards with ε
    refine hmeas.mul ?_
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((((measurable_norm : Measurable fun x : ℝ => |x|).pow_const ε).mul
        measurable_connesRealMultHaarDensity).aestronglyMeasurable))
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with ε hε0 hε1
    have hε0' : (0:ℝ) < ε := hε0
    have hε1' : ε < 1 := hε1
    filter_upwards with x
    have hd : 0 ≤ connesRealMultHaarDensity x := by
      rw [connesRealMultHaarDensity]; positivity
    have hpow : |x| ^ ε ≤ 1 + |x| := by
      rcases le_or_gt |x| 1 with hx | hx
      · rcases eq_or_lt_of_le (abs_nonneg x) with hx0 | hx0
        · rw [← hx0, Real.zero_rpow (ne_of_gt hε0')]
          have : (0:ℝ) ≤ |x| := abs_nonneg x
          linarith
        · calc |x| ^ ε ≤ (1:ℝ) ^ ε := Real.rpow_le_rpow (abs_nonneg x) hx hε0'.le
            _ = 1 := Real.one_rpow ε
            _ ≤ 1 + |x| := by linarith [abs_nonneg x]
      · calc |x| ^ ε ≤ |x| ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (le_of_lt hx) (le_of_lt hε1')
          _ = |x| := Real.rpow_one _
          _ ≤ 1 + |x| := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hd) (norm_nonneg _)
  · have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
      have h0 : (volume : Measure ℝ) {(0:ℝ)} = 0 := Real.volume_singleton
      have := compl_mem_ae_iff.2 h0
      filter_upwards [this] with x hx
      simpa using hx
    filter_upwards [hne] with x hx
    have hxpos : (0:ℝ) < |x| := abs_pos.mpr hx
    have hrpow : Tendsto (fun ε : ℝ => |x| ^ ε) (𝓝[>] 0) (𝓝 1) := by
      have h : Tendsto (fun ε : ℝ => |x| ^ ε) (𝓝 0) (𝓝 (|x| ^ (0:ℝ))) :=
        (Real.continuousAt_const_rpow (ne_of_gt hxpos)).tendsto
      rw [Real.rpow_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hmul : Tendsto (fun ε : ℝ => (|x| ^ ε) * connesRealMultHaarDensity x) (𝓝[>] 0)
        (𝓝 (1 * connesRealMultHaarDensity x)) := hrpow.mul tendsto_const_nhds
    rw [one_mul] at hmul
    have hc : Tendsto (fun ε : ℝ => (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 ((connesRealMultHaarDensity x : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hmul
    exact tendsto_const_nhds.mul hc


theorem aestronglyMeasurable_connesUnitBox : AEStronglyMeasurable connesUnitBox volume := by
  refine (aestronglyMeasurable_const (b := (1:ℂ))).indicator measurableSet_Icc

theorem connes_integrable_of_dom {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    (hdom : Integrable (fun x : ℝ => ‖g x‖ * ((1 + |x|) * connesRealMultHaarDensity x))) :
    Integrable (fun x : ℝ => g x * ((connesRealMultHaarDensity x : ℝ) : ℂ)) := by
  refine Integrable.mono' hdom
    (hmeas.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
      measurable_connesRealMultHaarDensity.aestronglyMeasurable)) ?_
  filter_upwards with x
  have hd : 0 ≤ connesRealMultHaarDensity x := by
    rw [connesRealMultHaarDensity]; positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
  have h1 : connesRealMultHaarDensity x ≤ (1 + |x|) * connesRealMultHaarDensity x := by
    nlinarith [abs_nonneg x, hd]
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

/-- **Appendix II (35).**  The logarithmic and the power regularization of the divergent principal
value `∫ f d^*x` have the same limit.  Connes' proof is exactly the argument formalized here: the
difference of the two regularizations is a multiple of `f(0)`, computed on the reference test
function `1_{[-1,1]}`, where both regularizations vanish. -/
theorem connes_logPV_sub_powerPV_tendsto {f : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable f volume)
    (hdom : Integrable (fun x : ℝ =>
      ‖f x - f 0 * connesUnitBox x‖ * ((1 + |x|) * connesRealMultHaarDensity x))) :
    Tendsto (fun ε : ℝ => connesRealLogPV f ε - connesRealPowerPV f ε) (𝓝[>] 0) (𝓝 0) := by
  set h : ℝ → ℂ := fun x => f x - f 0 * connesUnitBox x with hh
  have hh0 : h 0 = 0 := by
    simp only [hh, connesUnitBox_zero, mul_one, sub_self]
  have hmeash : AEStronglyMeasurable h volume :=
    hmeas.sub (aestronglyMeasurable_connesUnitBox.const_mul _)
  have hinth : Integrable (fun x : ℝ => h x * ((connesRealMultHaarDensity x : ℝ) : ℂ)) :=
    connes_integrable_of_dom hmeash hdom
  have hL := connesRealLogPV_tendsto_of_zero hh0 hinth
  have hP := connesRealPowerPV_tendsto_of_zero hh0 hmeash hdom
  have hdiff : Tendsto (fun ε : ℝ => connesRealLogPV h ε - connesRealPowerPV h ε)
      (𝓝[>] 0) (𝓝 0) := by
    have hsub := hL.sub hP
    rwa [sub_self] at hsub
  refine hdiff.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with ε hε0 hε1
  have hε0' : (0:ℝ) < ε := hε0
  have hε1' : ε < 1 := hε1
  -- integrability of the power integrand for `h`
  have hpowh : Integrable (fun x : ℝ =>
      h x * (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ)) := by
    refine Integrable.mono' hdom
      (hmeash.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
        ((((measurable_norm : Measurable fun x : ℝ => |x|).pow_const ε).mul
          measurable_connesRealMultHaarDensity).aestronglyMeasurable))) ?_
    filter_upwards with x
    have hd : 0 ≤ connesRealMultHaarDensity x := by
      rw [connesRealMultHaarDensity]; positivity
    have hpow : |x| ^ ε ≤ 1 + |x| := by
      rcases le_or_gt |x| 1 with hx | hx
      · rcases eq_or_lt_of_le (abs_nonneg x) with hx0 | hx0
        · rw [← hx0, Real.zero_rpow (ne_of_gt hε0')]
          linarith [abs_nonneg x]
        · calc |x| ^ ε ≤ (1:ℝ) ^ ε := Real.rpow_le_rpow (abs_nonneg x) hx hε0'.le
            _ = 1 := Real.one_rpow ε
            _ ≤ 1 + |x| := by linarith [abs_nonneg x]
      · calc |x| ^ ε ≤ |x| ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (le_of_lt hx) (le_of_lt hε1')
          _ = |x| := Real.rpow_one _
          _ ≤ 1 + |x| := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hd) (norm_nonneg _)
  -- split the logarithmic regularization
  have hsplitLog : connesRealLogPV f ε
      = connesRealLogPV h ε + f 0 * connesRealLogPV connesUnitBox ε := by
    have hptf : ∀ x : ℝ, f x * ((connesRealMultHaarDensity x : ℝ) : ℂ)
        = h x * ((connesRealMultHaarDensity x : ℝ) : ℂ)
          + f 0 * (connesUnitBox x * ((connesRealMultHaarDensity x : ℝ) : ℂ)) := by
      intro x; simp only [hh]; ring
    have hbox := connesUnitBox_integrableOn_tail hε0'
    simp only [connesRealLogPV, hptf]
    rw [MeasureTheory.integral_add (hinth.integrableOn) ((hbox.const_mul (f 0)))]
    rw [MeasureTheory.integral_const_mul]
    simp only [hh, connesUnitBox_zero, mul_one, sub_self, zero_mul, add_zero]
    ring
  have hsplitPow : connesRealPowerPV f ε
      = connesRealPowerPV h ε + f 0 * connesRealPowerPV connesUnitBox ε := by
    have hptf : ∀ x : ℝ, f x * (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ)
        = h x * (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ)
          + f 0 * (connesUnitBox x * (((|x| ^ ε) * connesRealMultHaarDensity x : ℝ) : ℂ)) := by
      intro x; simp only [hh]; ring
    have hbox := connesUnitBox_integrable_power hε0'
    simp only [connesRealPowerPV, hptf]
    rw [MeasureTheory.integral_add hpowh (hbox.const_mul (f 0))]
    rw [MeasureTheory.integral_const_mul]
    simp only [hh, connesUnitBox_zero, mul_one, sub_self, zero_div, sub_zero]
    ring
  rw [hsplitLog, hsplitPow, connesRealLogPV_unitBox hε0' (le_of_lt hε1'),
    connesRealPowerPV_unitBox hε0']
  ring

end

end GaloisForLFunctions.RHTower
