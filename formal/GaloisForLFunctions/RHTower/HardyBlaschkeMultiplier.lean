import GaloisForLFunctions.RHTower.SuzukiModelKernel

noncomputable section

/-!
# Blaschke multipliers on the Hardy space

For a point `w` above the axis the two unimodular symbols

```text
b_w(x) = (x - conj w)/(x - w),      β_w(x) = (x - w)/(x - conj w) = conj (b_w(x))
```

are inverse to one another and act isometrically on `L²(ℝ)`.

The inner factor `β_w` carries the Hardy space into itself unconditionally: pairing against a
Cauchy kernel below the axis and splitting into partial fractions leaves two Cauchy transforms of a
Hardy function at points below the axis, both zero.  At the single test point `conj w` the partial
fraction degenerates, and there the totality criterion with one point removed is used.

The Blaschke symbol `b_w` has a pole above the axis, so it preserves the Hardy space only on
functions whose Cauchy transform at `w` vanishes; the same partial fraction then leaves exactly that
transform and one below the axis.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The Blaschke symbol `(x - conj w)/(x - w)` of a point off the axis. -/
def blaschkeSymbol (w : ℂ) (x : ℝ) : ℂ :=
  (((x : ℝ) : ℂ) - (starRingEnd ℂ) w) / (((x : ℝ) : ℂ) - w)

/-- The inner factor `(x - w)/(x - conj w)`, inverse to the Blaschke symbol. -/
def blaschkeSymbolInv (w : ℂ) (x : ℝ) : ℂ :=
  (((x : ℝ) : ℂ) - w) / (((x : ℝ) : ℂ) - (starRingEnd ℂ) w)

theorem ofReal_sub_ne_zero {w : ℂ} (hw : w.im ≠ 0) (x : ℝ) : ((x : ℝ) : ℂ) - w ≠ 0 := by
  intro h
  apply hw
  have : w = ((x : ℝ) : ℂ) := by linear_combination -h
  rw [this]
  simp

theorem norm_ofReal_sub_conj (w : ℂ) (x : ℝ) :
    ‖((x : ℝ) : ℂ) - (starRingEnd ℂ) w‖ = ‖((x : ℝ) : ℂ) - w‖ := by
  have h : ((x : ℝ) : ℂ) - (starRingEnd ℂ) w = (starRingEnd ℂ) (((x : ℝ) : ℂ) - w) := by
    rw [map_sub, Complex.conj_ofReal]
  rw [h, RCLike.norm_conj]

theorem norm_blaschkeSymbol {w : ℂ} (hw : w.im ≠ 0) (x : ℝ) : ‖blaschkeSymbol w x‖ = 1 := by
  rw [blaschkeSymbol, norm_div, norm_ofReal_sub_conj]
  exact div_self (norm_ne_zero_iff.mpr (ofReal_sub_ne_zero hw x))

theorem norm_blaschkeSymbolInv {w : ℂ} (hw : w.im ≠ 0) (x : ℝ) :
    ‖blaschkeSymbolInv w x‖ = 1 := by
  have hc : ((starRingEnd ℂ) w).im ≠ 0 := by simpa using hw
  rw [blaschkeSymbolInv, norm_div]
  have h : ‖((x : ℝ) : ℂ) - w‖ = ‖((x : ℝ) : ℂ) - (starRingEnd ℂ) w‖ :=
    (norm_ofReal_sub_conj w x).symm
  rw [h]
  exact div_self (norm_ne_zero_iff.mpr (ofReal_sub_ne_zero hc x))

theorem norm_blaschkeSymbol_le (w : ℂ) (x : ℝ) : ‖blaschkeSymbol w x‖ ≤ 1 := by
  by_cases hx : ((x : ℝ) : ℂ) - w = 0
  · rw [blaschkeSymbol, hx, div_zero, norm_zero]
    norm_num
  · rw [blaschkeSymbol, norm_div, norm_ofReal_sub_conj]
    rw [div_self (norm_ne_zero_iff.mpr hx)]

theorem norm_blaschkeSymbolInv_le (w : ℂ) (x : ℝ) : ‖blaschkeSymbolInv w x‖ ≤ 1 := by
  by_cases hx : ((x : ℝ) : ℂ) - (starRingEnd ℂ) w = 0
  · rw [blaschkeSymbolInv, hx, div_zero, norm_zero]
    norm_num
  · rw [blaschkeSymbolInv, norm_div, ← norm_ofReal_sub_conj w x]
    rw [div_self (norm_ne_zero_iff.mpr hx)]

theorem measurable_blaschkeSymbol (w : ℂ) : Measurable (blaschkeSymbol w) := by
  unfold blaschkeSymbol
  fun_prop

theorem measurable_blaschkeSymbolInv (w : ℂ) : Measurable (blaschkeSymbolInv w) := by
  unfold blaschkeSymbolInv
  fun_prop

theorem conj_blaschkeSymbol (w : ℂ) (x : ℝ) :
    (starRingEnd ℂ) (blaschkeSymbol w x) = blaschkeSymbolInv w x := by
  rw [blaschkeSymbol, blaschkeSymbolInv, map_div₀, map_sub, map_sub, Complex.conj_ofReal,
    Complex.conj_conj]

/-- Multiplication by the Blaschke symbol on `L²(ℝ)`. -/
def blaschkeMul (w : ℂ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) (measurable_blaschkeSymbol w)
    (by norm_num : (0:ℝ) ≤ 1) (norm_blaschkeSymbol_le w)

/-- Multiplication by the inner factor on `L²(ℝ)`. -/
def blaschkeMulInv (w : ℂ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) (measurable_blaschkeSymbolInv w)
    (by norm_num : (0:ℝ) ≤ 1) (norm_blaschkeSymbolInv_le w)

theorem coeFn_blaschkeMul (w : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (blaschkeMul w f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => blaschkeSymbol w x * (f : ℝ → ℂ) x :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) (measurable_blaschkeSymbol w)
    (by norm_num) (norm_blaschkeSymbol_le w) f

theorem coeFn_blaschkeMulInv (w : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (blaschkeMulInv w f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => blaschkeSymbolInv w x * (f : ℝ → ℂ) x :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) (measurable_blaschkeSymbolInv w)
    (by norm_num) (norm_blaschkeSymbolInv_le w) f

theorem norm_blaschkeMul {w : ℂ} (hw : w.im ≠ 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖blaschkeMul w f‖ = ‖f‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [coeFn_blaschkeMul w f] with x h
  rw [h, norm_mul, norm_blaschkeSymbol hw x, one_mul]

theorem norm_blaschkeMulInv {w : ℂ} (hw : w.im ≠ 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖blaschkeMulInv w f‖ = ‖f‖ := by
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [coeFn_blaschkeMulInv w f] with x h
  rw [h, norm_mul, norm_blaschkeSymbolInv hw x, one_mul]

/-! ## Partial fractions -/

theorem blaschke_partialFraction {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) (hwv : w - v ≠ 0)
    (x : ℝ) :
    blaschkeSymbol w x / (((x : ℝ) : ℂ) - v)
      = ((w - (starRingEnd ℂ) w) / (w - v)) * (((x : ℝ) : ℂ) - w)⁻¹
        + ((v - (starRingEnd ℂ) w) / (v - w)) * (((x : ℝ) : ℂ) - v)⁻¹ := by
  have h1 := ofReal_sub_ne_zero hw x
  have h2 := ofReal_sub_ne_zero hv x
  have h3 : v - w ≠ 0 := fun h => hwv (by linear_combination -h)
  rw [blaschkeSymbol]
  field_simp
  ring

theorem blaschkeInv_partialFraction {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0)
    (hwv : (starRingEnd ℂ) w - v ≠ 0) (x : ℝ) :
    blaschkeSymbolInv w x / (((x : ℝ) : ℂ) - v)
      = (((starRingEnd ℂ) w - w) / ((starRingEnd ℂ) w - v))
          * (((x : ℝ) : ℂ) - (starRingEnd ℂ) w)⁻¹
        + ((v - w) / (v - (starRingEnd ℂ) w)) * (((x : ℝ) : ℂ) - v)⁻¹ := by
  have hc : ((starRingEnd ℂ) w).im ≠ 0 := by simpa using hw
  have h1 := ofReal_sub_ne_zero hc x
  have h2 := ofReal_sub_ne_zero hv x
  have h3 : v - (starRingEnd ℂ) w ≠ 0 := fun h => hwv (by linear_combination -h)
  rw [blaschkeSymbolInv]
  field_simp
  ring

/-! ## The Hardy space is stable under the inner factor -/

/-- **The inner factor preserves the Hardy space.**  At the exceptional test point `conj w` the
partial fraction degenerates, but a single point may be dropped from the totality criterion. -/
theorem blaschkeMulInv_mem_hardyL2 {w : ℂ} (hw : 0 < w.im)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ hardyL2) : blaschkeMulInv w F ∈ hardyL2 := by
  have hwne : w.im ≠ 0 := ne_of_gt hw
  have hc : ((starRingEnd ℂ) w).im < 0 := by simpa using hw
  refine mem_hardyL2_of_cauchyTransform_eq_zero_of_ne ((starRingEnd ℂ) w) ?_
  intro v hv hwv'
  have hvne : v.im ≠ 0 := ne_of_lt hv
  have hwv : (starRingEnd ℂ) w - v ≠ 0 := fun h => hwv' (by linear_combination -h)
  have hint1 := integrable_lp_div_sub (ne_of_lt hc) F
  have hint2 := integrable_lp_div_sub hvne F
  have hae : (fun x : ℝ => (blaschkeMulInv w F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - v))
      =ᵐ[volume] fun x : ℝ =>
        (((starRingEnd ℂ) w - w) / ((starRingEnd ℂ) w - v))
            * ((F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - (starRingEnd ℂ) w))
          + ((v - w) / (v - (starRingEnd ℂ) w))
            * ((F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - v)) := by
    filter_upwards [coeFn_blaschkeMulInv w F] with x h
    rw [h, mul_comm (blaschkeSymbolInv w x), mul_div_assoc,
      blaschkeInv_partialFraction hwne hvne hwv x]
    ring
  rw [MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_add (hint1.const_mul _) (hint2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_cauchyTransform_eq_zero hF hc, integral_cauchyTransform_eq_zero hF hv]
  ring

/-- **Dividing out a zero.**  If a Hardy function has a vanishing Cauchy transform at a point of
the upper half-plane, the Blaschke symbol at that point still carries it into the Hardy space. -/
theorem blaschkeMul_mem_hardyL2 {w : ℂ} (hw : 0 < w.im)
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hF : F ∈ hardyL2)
    (hzero : (∫ x : ℝ, (F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) = 0) :
    blaschkeMul w F ∈ hardyL2 := by
  have hwne : w.im ≠ 0 := ne_of_gt hw
  refine mem_hardyL2_of_cauchyTransform_eq_zero ?_
  intro v hv
  have hvne : v.im ≠ 0 := ne_of_lt hv
  have hwv : w - v ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    linarith
  have hint1 := integrable_lp_div_sub hwne F
  have hint2 := integrable_lp_div_sub hvne F
  have hae : (fun x : ℝ => (blaschkeMul w F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - v))
      =ᵐ[volume] fun x : ℝ =>
        ((w - (starRingEnd ℂ) w) / (w - v)) * ((F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w))
          + ((v - (starRingEnd ℂ) w) / (v - w)) * ((F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - v)) := by
    filter_upwards [coeFn_blaschkeMul w F] with x h
    rw [h, mul_comm (blaschkeSymbol w x), mul_div_assoc,
      blaschke_partialFraction hwne hvne hwv x]
    ring
  rw [MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_add (hint1.const_mul _) (hint2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    hzero, integral_cauchyTransform_eq_zero hF hv]
  ring

/-! ## Interaction with conjugation and the inner symbol -/

theorem star_blaschkeMul (w : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    star (blaschkeMul w f) = blaschkeMulInv w (star f) := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star (blaschkeMul w f), coeFn_blaschkeMul w f,
    coeFn_blaschkeMulInv w (star f), MeasureTheory.Lp.coeFn_star f] with x h1 h2 h3 h4
  rw [h1, Pi.star_apply, h2, h3, h4, Pi.star_apply]
  show (starRingEnd ℂ) (blaschkeSymbol w x * (f : ℝ → ℂ) x)
    = blaschkeSymbolInv w x * (starRingEnd ℂ) ((f : ℝ → ℂ) x)
  rw [map_mul, conj_blaschkeSymbol]

theorem thetaMul_blaschkeMulInv (w : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    thetaMul (blaschkeMulInv w f) = blaschkeMulInv w (thetaMul f) := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [thetaMul_coeFn (blaschkeMulInv w f), coeFn_blaschkeMulInv w f,
    coeFn_blaschkeMulInv w (thetaMul f), thetaMul_coeFn f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

/-- The involution `κ f = Θ conj f` exchanges the Blaschke symbol for its inner factor. -/
theorem thetaMul_star_blaschkeMul (w : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    thetaMul (star (blaschkeMul w f)) = blaschkeMulInv w (thetaMul (star f)) := by
  rw [star_blaschkeMul, thetaMul_blaschkeMulInv]


end RHTower
