import GaloisForLFunctions.RHTower.DigammaQuarter
import GaloisForLFunctions.RHTower.DigammaVerticalLogGrowth
import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# The prime-free CCM aperture already has a real characteristic pair

At an aperture below `(log 2)/2` the finite prime-power sum of the corrected CCM symbol is empty, so
the symbol is the archimedean part plus the exact polar multiplier.  Its value at the origin is
`ψ(1/4) − log π + 8 sinh a`, which is negative for `a` below `arsinh((log π − ψ(1/4))/8)`, while the
archimedean part grows logarithmically and the polar multiplier decays, so the symbol is eventually
positive.  Continuity and evenness then produce a symmetric pair of real characteristic points.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology

noncomputable section

/-- The archimedean part of the corrected CCM symbol, `m(ξ) = Re ψ(1/4 + iξ/2) − log π`. -/
def ccmArchSymbol (ξ : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + ((ξ / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi

/-- The exact polar multiplier of the corrected CCM symbol. -/
def ccmPolarMultiplier (a ξ : ℝ) : ℝ :=
  (2 * Real.sinh a * Real.cos (2 * a * ξ) + 4 * ξ * Real.cosh a * Real.sin (2 * a * ξ))
    / (ξ ^ 2 + 1 / 4)

/-- The finite prime-power sum of the corrected CCM symbol, cut off at `exp (2a)`. -/
def ccmPrimeCutoffSum (a ξ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ) / 2) * Real.cos (ξ * Real.log n)

/-- The corrected CCM symbol at aperture `a`. -/
def ccmCorrectedSymbol (a ξ : ℝ) : ℝ :=
  ccmArchSymbol ξ - 2 * ccmPrimeCutoffSum a ξ + ccmPolarMultiplier a ξ

/-- **Equation (2).**  The explicit prime-free aperture. -/
def ccmPrimeFreeAperture : ℝ := min (Real.log 2 / 2) (Real.arsinh (archRatioCharge / 8))

/-! ## The value at the origin -/

/-- **Equation (5).**  The zero-frequency archimedean value is `ψ(1/4) − log π < 0`. -/
theorem ccmArchSymbol_zero : ccmArchSymbol 0 = -archRatioCharge := by
  unfold ccmArchSymbol
  have hz : ((1 / 4 : ℂ) + (((0 : ℝ) / 2 : ℝ) : ℂ) * Complex.I) = (1 / 4 : ℂ) := by
    norm_num
  rw [hz, digamma_quarter, archRatioCharge]
  simp only [Complex.neg_re, Complex.ofReal_re]
  ring

theorem ccmArchSymbol_zero_neg : ccmArchSymbol 0 < 0 := by
  rw [ccmArchSymbol_zero]
  have := archRatioCharge_pos
  linarith

/-- **Equation (6).**  The exact polar value at the origin. -/
theorem ccmPolarMultiplier_zero (a : ℝ) : ccmPolarMultiplier a 0 = 8 * Real.sinh a := by
  have h1 : (2 : ℝ) * a * 0 = 0 := by ring
  unfold ccmPolarMultiplier
  rw [h1, Real.cos_zero, Real.sin_zero]
  field_simp
  ring

/-- Below `(log 2)/2` the prime-power cutoff admits no index. -/
theorem ccmPrimeCutoffSum_eq_zero {a : ℝ} (ha : a < Real.log 2 / 2) (ξ : ℝ) :
    ccmPrimeCutoffSum a ξ = 0 := by
  have hexp : Real.exp (2 * a) < 2 := by
    have h2a : 2 * a < Real.log 2 := by linarith
    calc Real.exp (2 * a) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr h2a
      _ = 2 := Real.exp_log (by norm_num)
  have hfloor : ⌊Real.exp (2 * a)⌋₊ < 2 := by
    rw [Nat.floor_lt (le_of_lt (Real.exp_pos _))]
    simpa using hexp
  have hempty : Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊ = ∅ :=
    Finset.Icc_eq_empty (by omega)
  unfold ccmPrimeCutoffSum
  rw [hempty, Finset.sum_empty]

theorem arsinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.arsinh x := by
  have h : Real.sinh 0 < Real.sinh (Real.arsinh x) := by
    rw [Real.sinh_zero, Real.sinh_arsinh]
    exact hx
  exact Real.sinh_lt_sinh.mp h

/-- **Equation (2), positivity.**  The prime-free aperture is positive. -/
theorem ccmPrimeFreeAperture_pos : 0 < ccmPrimeFreeAperture := by
  refine lt_min ?_ ?_
  · have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  · exact arsinh_pos_of_pos (by linarith [archRatioCharge_pos])

/-- **Equation (7).**  The corrected symbol is negative at the origin throughout the prime-free
aperture range. -/
theorem ccmCorrectedSymbol_zero_neg {a : ℝ} (ha : a < ccmPrimeFreeAperture) :
    ccmCorrectedSymbol a 0 < 0 := by
  have haprime : a < Real.log 2 / 2 := lt_of_lt_of_le ha (min_le_left _ _)
  have hasinh : a < Real.arsinh (archRatioCharge / 8) := lt_of_lt_of_le ha (min_le_right _ _)
  have hsinh : Real.sinh a < archRatioCharge / 8 := by
    have := Real.sinh_lt_sinh.mpr hasinh
    rwa [Real.sinh_arsinh] at this
  unfold ccmCorrectedSymbol
  rw [ccmPrimeCutoffSum_eq_zero haprime, ccmArchSymbol_zero, ccmPolarMultiplier_zero]
  linarith

/-! ## Evenness -/

theorem conj_quarterLine (ξ : ℝ) :
    ((1 / 4 : ℂ) + ((-ξ / 2 : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) ((1 / 4 : ℂ) + ((ξ / 2 : ℝ) : ℂ) * Complex.I) := by
  have hre : ((1 / 4 : ℂ) + ((ξ / 2 : ℝ) : ℂ) * Complex.I).re = 1 / 4 := by simp
  have him : ((1 / 4 : ℂ) + ((ξ / 2 : ℝ) : ℂ) * Complex.I).im = ξ / 2 := by simp
  apply Complex.ext
  · rw [Complex.conj_re, hre]
    simp
  · rw [Complex.conj_im, him]
    simp
    ring

theorem ccmArchSymbol_even (ξ : ℝ) : ccmArchSymbol (-ξ) = ccmArchSymbol ξ := by
  unfold ccmArchSymbol
  congr 1
  rw [conj_quarterLine ξ, ReflectedDigammaAnomaly.digamma_conj]
  simp

theorem ccmPolarMultiplier_even (a ξ : ℝ) : ccmPolarMultiplier a (-ξ) = ccmPolarMultiplier a ξ := by
  unfold ccmPolarMultiplier
  rw [show 2 * a * -ξ = -(2 * a * ξ) from by ring, Real.cos_neg, Real.sin_neg]
  ring_nf

theorem ccmPrimeCutoffSum_even (a ξ : ℝ) : ccmPrimeCutoffSum a (-ξ) = ccmPrimeCutoffSum a ξ := by
  unfold ccmPrimeCutoffSum
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show -ξ * Real.log n = -(ξ * Real.log n) from by ring, Real.cos_neg]

theorem ccmCorrectedSymbol_even (a ξ : ℝ) :
    ccmCorrectedSymbol a (-ξ) = ccmCorrectedSymbol a ξ := by
  unfold ccmCorrectedSymbol
  rw [ccmArchSymbol_even, ccmPolarMultiplier_even, ccmPrimeCutoffSum_even]

/-! ## Continuity -/

theorem continuous_ccmArchSymbol : Continuous ccmArchSymbol := by
  have hnode : Continuous fun ξ : ℝ => (1 / 4 : ℂ) + ((ξ / 2 : ℝ) : ℂ) * Complex.I := by
    fun_prop
  have hdig : ContinuousOn Complex.digamma {z : ℂ | 0 < z.re} :=
    _root_.RHTower.digamma_continuousOn_re_pos
  have hmem : ∀ ξ : ℝ, ((1 / 4 : ℂ) + ((ξ / 2 : ℝ) : ℂ) * Complex.I) ∈ {z : ℂ | 0 < z.re} := by
    intro ξ
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
  have hcomp : Continuous fun ξ : ℝ =>
      Complex.digamma ((1 / 4 : ℂ) + ((ξ / 2 : ℝ) : ℂ) * Complex.I) :=
    hdig.comp_continuous hnode hmem
  unfold ccmArchSymbol
  exact (Complex.continuous_re.comp hcomp).sub continuous_const

theorem continuous_ccmPolarMultiplier (a : ℝ) : Continuous (ccmPolarMultiplier a) := by
  unfold ccmPolarMultiplier
  have hden : ∀ ξ : ℝ, ξ ^ 2 + 1 / 4 ≠ 0 := fun ξ => by positivity
  fun_prop (disch := intro ξ; exact hden ξ)

theorem continuous_ccmPrimeCutoffSum (a : ℝ) : Continuous (ccmPrimeCutoffSum a) := by
  unfold ccmPrimeCutoffSum
  exact continuous_finsetSum _ fun n _ => by fun_prop

theorem continuous_ccmCorrectedSymbol (a : ℝ) : Continuous (ccmCorrectedSymbol a) := by
  unfold ccmCorrectedSymbol
  exact (continuous_ccmArchSymbol.sub
    (continuous_const.mul (continuous_ccmPrimeCutoffSum a))).add
      (continuous_ccmPolarMultiplier a)

/-! ## Growth of the archimedean part and a uniform polar bound -/

/-- **Equation (8), lower bound.**  The archimedean part grows at least logarithmically. -/
theorem ccmArchSymbol_ge (ξ : ℝ) :
    Real.log (2 + |ξ / 2|) - _root_.RHTower.digammaVerticalCoercivityConst (1 / 4)
        - Real.log Real.pi
      ≤ ccmArchSymbol ξ := by
  have h := _root_.RHTower.re_digamma_vertical_ge (a := 1 / 4) (by norm_num) (by norm_num) (ξ / 2)
  have hcast : (((1 / 4 : ℝ)) : ℂ) = (1 / 4 : ℂ) := by norm_num
  rw [hcast] at h
  unfold ccmArchSymbol
  linarith

/-- **Equation (8).**  The archimedean part tends to `+∞`. -/
theorem tendsto_ccmArchSymbol_atTop : Tendsto ccmArchSymbol atTop atTop := by
  have hhalf : Tendsto (fun ξ : ℝ => ξ / 2) atTop atTop := by
    simpa using tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have habs : Tendsto (fun ξ : ℝ => |ξ / 2|) atTop atTop := tendsto_abs_atTop_atTop.comp hhalf
  have hinner : Tendsto (fun ξ : ℝ => 2 + |ξ / 2|) atTop atTop :=
    tendsto_atTop_add_const_left _ 2 habs
  have hlog : Tendsto (fun ξ : ℝ => Real.log (2 + |ξ / 2|)) atTop atTop :=
    Real.tendsto_log_atTop.comp hinner
  have hshift := tendsto_atTop_add_const_right atTop
    (-(_root_.RHTower.digammaVerticalCoercivityConst (1 / 4)) - Real.log Real.pi) hlog
  refine tendsto_atTop_mono (fun ξ => ?_) hshift
  have := ccmArchSymbol_ge ξ
  linarith

/-- The polar multiplier is bounded uniformly in the frequency. -/
theorem abs_ccmPolarMultiplier_le (a ξ : ℝ) :
    |ccmPolarMultiplier a ξ| ≤ 8 * |Real.sinh a| + 4 * Real.cosh a := by
  have hden : (0 : ℝ) < ξ ^ 2 + 1 / 4 := by positivity
  have hcosh : 0 < Real.cosh a := Real.cosh_pos a
  have hnum : |2 * Real.sinh a * Real.cos (2 * a * ξ) + 4 * ξ * Real.cosh a * Real.sin (2 * a * ξ)|
      ≤ 2 * |Real.sinh a| + 4 * |ξ| * Real.cosh a := by
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |2 * Real.sinh a * Real.cos (2 * a * ξ)| ≤ 2 * |Real.sinh a| := by
      rw [abs_mul, abs_mul]
      have hc := Real.abs_cos_le_one (2 * a * ξ)
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]
      calc 2 * |Real.sinh a| * |Real.cos (2 * a * ξ)|
          ≤ 2 * |Real.sinh a| * 1 := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = 2 * |Real.sinh a| := by ring
    have h2 : |4 * ξ * Real.cosh a * Real.sin (2 * a * ξ)| ≤ 4 * |ξ| * Real.cosh a := by
      rw [abs_mul, abs_mul, abs_mul]
      have hs := Real.abs_sin_le_one (2 * a * ξ)
      have h4 : |(4 : ℝ)| = 4 := by norm_num
      have hch : |Real.cosh a| = Real.cosh a := abs_of_pos hcosh
      rw [h4, hch]
      calc 4 * |ξ| * Real.cosh a * |Real.sin (2 * a * ξ)|
          ≤ 4 * |ξ| * Real.cosh a * 1 :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 4 * |ξ| * Real.cosh a := by ring
    linarith
  have hsplit : (2 * |Real.sinh a| + 4 * |ξ| * Real.cosh a) / (ξ ^ 2 + 1 / 4)
      ≤ 8 * |Real.sinh a| + 4 * Real.cosh a := by
    rw [div_le_iff₀ hden]
    have hxi : |ξ| ≤ ξ ^ 2 + 1 / 4 := by
      have habs : |ξ| ^ 2 = ξ ^ 2 := sq_abs ξ
      nlinarith [sq_nonneg (|ξ| - 1 / 2), abs_nonneg ξ]
    have hone : (1 : ℝ) ≤ 4 * (ξ ^ 2 + 1 / 4) := by nlinarith [sq_nonneg ξ]
    nlinarith [abs_nonneg (Real.sinh a), abs_nonneg ξ, hcosh.le, hden]
  unfold ccmPolarMultiplier
  rw [abs_div, abs_of_pos hden]
  refine le_trans ?_ hsplit
  exact div_le_div_of_nonneg_right hnum hden.le

/-- **Equation (8), consequence.**  Above the prime-free aperture cutoff the corrected symbol is
positive at some frequency. -/
theorem exists_pos_ccmCorrectedSymbol {a : ℝ} (ha : a < Real.log 2 / 2) :
    ∃ R : ℝ, 0 < R ∧ 0 < ccmCorrectedSymbol a R := by
  obtain ⟨R, hR1, hR2⟩ := ((tendsto_atTop.mp tendsto_ccmArchSymbol_atTop
      (8 * |Real.sinh a| + 4 * Real.cosh a + 1)).and (eventually_gt_atTop (0 : ℝ))).exists
  refine ⟨R, hR2, ?_⟩
  have hpolar := abs_ccmPolarMultiplier_le a R
  have hpolar' : -(8 * |Real.sinh a| + 4 * Real.cosh a) ≤ ccmPolarMultiplier a R :=
    neg_le_of_abs_le hpolar
  unfold ccmCorrectedSymbol
  rw [ccmPrimeCutoffSum_eq_zero ha]
  linarith

/-! ## The symmetric characteristic pair -/

/-- **Equation (3).**  Inside the prime-free aperture the corrected symbol has a nonzero symmetric
pair of real characteristic points. -/
theorem exists_characteristic_pair {a : ℝ} (ha : a < ccmPrimeFreeAperture) :
    ∃ τ : ℝ, 0 < τ ∧ ccmCorrectedSymbol a τ = 0 ∧ ccmCorrectedSymbol a (-τ) = 0 := by
  have haprime : a < Real.log 2 / 2 := lt_of_lt_of_le ha (min_le_left _ _)
  obtain ⟨R, hRpos, hRval⟩ := exists_pos_ccmCorrectedSymbol haprime
  have hneg := ccmCorrectedSymbol_zero_neg ha
  have hmem : (0 : ℝ) ∈ Set.Ioo (ccmCorrectedSymbol a 0) (ccmCorrectedSymbol a R) := ⟨hneg, hRval⟩
  have hsub := intermediate_value_Ioo (le_of_lt hRpos)
    (continuous_ccmCorrectedSymbol a).continuousOn
  obtain ⟨τ, hτmem, hτ⟩ := hsub hmem
  exact ⟨τ, hτmem.1, hτ, by rw [ccmCorrectedSymbol_even]; exact hτ⟩

end

end GaloisForLFunctions.RHTower
