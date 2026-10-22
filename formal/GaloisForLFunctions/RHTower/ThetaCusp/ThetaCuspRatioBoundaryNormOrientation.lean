import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.RealCore
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.SplitRe
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.SplitIm
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Quadratic norm orientation of the boundary reduced slope

On the nonlinear boundary `t = b(h) s`, `r = s (1 - h² b(h) s)`, write `A`, `B` for the real
compact coefficients of the reduced source slope (`A = h²² W.re`, `B = h²¹ W.im`), `G` for the
regular core, `Z = (1 - h b(h) s)/3`, `y = h Z`, `β = (2h-1)/3`, `α = y² - β y`.  The C76
regularization is `A + y B = h⁶ G`.  This file proves:

* the exact factorizations `N = A² + β A B - α B² = h⁶ G J` with `J = h⁶ G + (β - 2y) B` the
  conjugate value `A + (β - y) B`, `A = h Â` with `Â = h⁵ G - Z B`, and `2A + β B = 2h⁶G + (β-2y)B`;
* the clock-zero values `A(0,s) = 0`, `B(0,s) = B₀ = 268435456/2187`,
  `G(0,s) = 155520 - (567/64) s²`;
* `boundaryNorm78_uniform_strip`: one `ε > 0` such that on `[0, ε) × [0, S]` simultaneously
  `G > 0`, `B > 0`, `J < 0`, `Â < 0`, `G J < 0` and `2A + βB < 0`;
* consequently `A < 0`, `A + y B > 0`, `A + (β - y) B < 0` and `N < 0` for `0 < h < ε`;
* exact orders: `N` has no continuous factor `h⁷ D`, `A` none of the form `h² D`;
* the source identification `h⁴⁴ · norm W = N`, `h²² (2 W.re + b W.im) = 2A + βB` in the boundary
  quadratic algebra, so the norm and trace of `W` are negative on the strip;
* the pole orders `h³⁸ norm W → -B₀ g(s)/3` and `h²¹ W.re → -B₀/3` as `h → 0⁺`.
-/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology

/-- The admissible boundary parameter range `0 ≤ s ≤ S`, `S = (6/5)(361/25)`. -/
def boundaryNormS78 : ℝ := (6/5)*(361/25)

/-! ### Real low parts and the real-cast bridge -/

/-- The low-clock part of the compact first coefficient, as a real polynomial. -/
def boundaryReLow77 (h r : ℝ) : ℝ :=
  h^5*(1490519130112/531441)+h^4*(68961173504/177147)+
    h^3*(-11127488512/59049+(r*h^2)*(175354806272/531441))+
    h^2*(3489660928/19683+(r*h^2)*(-1414529024/6561))+
    h*(-268435456/6561+(r*h^2)*(721420288/19683)+(r*h^2)^2*(-1636827136/177147))+
    ((r*h^2)*(67108864/19683)+(r*h^2)^2*(-255852544/59049))

/-- The low-clock part of the compact second coefficient, as a real polynomial. -/
def boundaryImLow77 (h r : ℝ) : ℝ :=
  h^4*(-1490519130112/177147)+h^3*(-68961173504/59049)+
    h^2*(11127488512/19683+(r*h^2)*(-67443884032/59049))+
    h*(-3489660928/6561+(r*h^2)*(14675869696/19683))+
    (268435456/2187+(r*h^2)*(-1090519040/6561)+(r*h^2)^2*(5924454400/59049))

theorem boundaryReLow77_ofReal (h r : ℝ) :
    ((boundaryReLow77 h r : ℝ) : ℂ)=boundaryReLow76 (h:ℂ) (r:ℂ) := by
  norm_num [boundaryReLow77,boundaryReLow76,boundaryReLowColumn76_0,boundaryReLowColumn76_1,
    boundaryReLowColumn76_2,boundaryReLowColumn76_3,boundaryReLowColumn76_4,
    boundaryReLowColumn76_5,boundaryReLowColumn76_6,boundaryReLowColumn76_7,
    boundaryReLowColumn76_8,boundaryReLowColumn76_9,boundaryReLowColumn76_10,
    boundaryReLowColumn76_11,boundaryReLowColumn76_12,boundaryReLowColumn76_13,
    boundaryReLowColumn76_14,boundaryReLowColumn76_15,boundaryReLowColumn76_16,
    boundaryReLowColumn76_17,boundaryReLowColumn76_18,boundaryReLowColumn76_19,
    boundaryReLowColumn76_20,boundaryReLowColumn76_21,boundaryReLowColumn76_22]
  ring

theorem boundaryImLow77_ofReal (h r : ℝ) :
    ((boundaryImLow77 h r : ℝ) : ℂ)=boundaryImLow76 (h:ℂ) (r:ℂ) := by
  norm_num [boundaryImLow77,boundaryImLow76,boundaryImLowColumn76_0,boundaryImLowColumn76_1,
    boundaryImLowColumn76_2,boundaryImLowColumn76_3,boundaryImLowColumn76_4,
    boundaryImLowColumn76_5,boundaryImLowColumn76_6,boundaryImLowColumn76_7,
    boundaryImLowColumn76_8,boundaryImLowColumn76_9,boundaryImLowColumn76_10,
    boundaryImLowColumn76_11,boundaryImLowColumn76_12,boundaryImLowColumn76_13,
    boundaryImLowColumn76_14,boundaryImLowColumn76_15,boundaryImLowColumn76_16,
    boundaryImLowColumn76_17,boundaryImLowColumn76_18,boundaryImLowColumn76_19,
    boundaryImLowColumn76_20,boundaryImLowColumn76_21]
  ring

/-- The compact first coefficient as a real polynomial. -/
def boundaryCompactA77 (h r : ℝ) : ℝ := boundaryReLow77 h r+h^6*boundaryReHigh77 h r

/-- The compact second coefficient as a real polynomial. -/
def boundaryCompactB77 (h r : ℝ) : ℝ := boundaryImLow77 h r+h^5*boundaryImHigh77 h r

theorem boundaryCompactA77_ofReal (h r : ℝ) :
    ((boundaryCompactA77 h r : ℝ) : ℂ)=boundaryCompactA75 (h:ℂ) (r:ℂ) := by
  rw [boundaryReCompleteSplit76,boundaryCompactA77]
  push_cast
  rw [boundaryReLow77_ofReal,boundaryReHigh77_ofReal]

theorem boundaryCompactB77_ofReal (h r : ℝ) :
    ((boundaryCompactB77 h r : ℝ) : ℂ)=boundaryCompactB75 (h:ℂ) (r:ℂ) := by
  rw [boundaryImCompleteSplit76,boundaryCompactB77]
  push_cast
  rw [boundaryImLow77_ofReal,boundaryImHigh77_ofReal]

/-! ### The boundary quadratic data -/

/-- `A(h,s)`: the real compact first coefficient on the nonlinear boundary. -/
def boundaryNormA78 (h s : ℝ) : ℝ := boundaryCompactA77 h (boundaryR77 h s)

/-- `B(h,s)`: the real compact second coefficient on the nonlinear boundary. -/
def boundaryNormB78 (h s : ℝ) : ℝ := boundaryCompactB77 h (boundaryR77 h s)

/-- `y = h Z`, the boundary root in compact scale. -/
def boundaryNormY78 (h s : ℝ) : ℝ := h*boundaryZ77 h s

/-- `β = (2h-1)/3 = h · boundaryB (1/h)`. -/
def boundaryNormBeta78 (h : ℝ) : ℝ := (2*h-1)/3

/-- `α = y² - β y = h² · boundaryA (V, 1/h)`. -/
def boundaryNormAlpha78 (h s : ℝ) : ℝ :=
  boundaryNormY78 h s^2-boundaryNormBeta78 h*boundaryNormY78 h s

/-- `Δ = β - 2y`. -/
def boundaryNormDelta78 (h s : ℝ) : ℝ := boundaryNormBeta78 h-2*boundaryNormY78 h s

/-- `J = h⁶ G + Δ B`, the conjugate value `A + (β - y) B`. -/
def boundaryNormJ78 (h s : ℝ) : ℝ :=
  h^6*boundaryRegularCore77 h s+boundaryNormDelta78 h s*boundaryNormB78 h s

/-- The compact quadratic norm `N = A² + β A B - α B²`. -/
def boundaryNorm78 (h s : ℝ) : ℝ :=
  boundaryNormA78 h s^2+boundaryNormBeta78 h*boundaryNormA78 h s*boundaryNormB78 h s-
    boundaryNormAlpha78 h s*boundaryNormB78 h s^2

/-- `N̂ = G J`. -/
def boundaryNormHat78 (h s : ℝ) : ℝ := boundaryRegularCore77 h s*boundaryNormJ78 h s

/-- `Â = h⁵ G - Z B`. -/
def boundaryNormAHat78 (h s : ℝ) : ℝ :=
  h^5*boundaryRegularCore77 h s-boundaryZ77 h s*boundaryNormB78 h s

/-- The compact trace `2A + β B`. -/
def boundaryNormTrace78 (h s : ℝ) : ℝ :=
  2*boundaryNormA78 h s+boundaryNormBeta78 h*boundaryNormB78 h s

/-- The C76 regularization in real form: `A + y B = h⁶ G`. -/
theorem boundaryNormA78_add_y_mul (h s : ℝ) :
    boundaryNormA78 h s+boundaryNormY78 h s*boundaryNormB78 h s=
      h^6*boundaryRegularCore77 h s := by
  have hc := boundaryCompact_regularization76 (h:ℂ) (s:ℂ)
  rw [←boundaryR77_ofReal,←boundaryZ77_ofReal,←boundaryCompactA77_ofReal,
    ←boundaryCompactB77_ofReal,←boundaryRegularCore77_ofReal] at hc
  apply Complex.ofReal_injective
  unfold boundaryNormA78 boundaryNormB78 boundaryNormY78
  push_cast
  linear_combination hc

theorem boundaryNormA78_eq (h s : ℝ) :
    boundaryNormA78 h s=h^6*boundaryRegularCore77 h s-boundaryNormY78 h s*boundaryNormB78 h s := by
  linarith [boundaryNormA78_add_y_mul h s]

/-- `N = (A + y B)(A + (β - y) B) = h⁶ · G J`. -/
theorem boundaryNorm78_factor (h s : ℝ) : boundaryNorm78 h s=h^6*boundaryNormHat78 h s := by
  unfold boundaryNorm78 boundaryNormHat78 boundaryNormJ78 boundaryNormAlpha78 boundaryNormDelta78
  rw [boundaryNormA78_eq]
  ring

/-- The second factor is the actual conjugate value `A + (β - y) B`. -/
theorem boundaryNormJ78_eq_conjugate (h s : ℝ) :
    boundaryNormA78 h s+(boundaryNormBeta78 h-boundaryNormY78 h s)*boundaryNormB78 h s=
      boundaryNormJ78 h s := by
  unfold boundaryNormJ78 boundaryNormDelta78
  rw [boundaryNormA78_eq]
  ring

theorem boundaryNormA78_eq_mul_hat (h s : ℝ) : boundaryNormA78 h s=h*boundaryNormAHat78 h s := by
  unfold boundaryNormAHat78
  rw [boundaryNormA78_eq]
  unfold boundaryNormY78
  ring

theorem boundaryNormTrace78_eq (h s : ℝ) :
    boundaryNormTrace78 h s=2*h^6*boundaryRegularCore77 h s+
      boundaryNormDelta78 h s*boundaryNormB78 h s := by
  unfold boundaryNormTrace78 boundaryNormDelta78
  rw [boundaryNormA78_eq]
  ring

/-! ### Clock-zero values -/

/-- The clock-zero second coefficient `B₀`. -/
def boundaryNormB0 : ℝ := 268435456/2187

theorem boundaryNormB0_pos : 0<boundaryNormB0 := by norm_num [boundaryNormB0]

theorem boundaryNormA78_zero (s : ℝ) : boundaryNormA78 0 s=0 := by
  simp [boundaryNormA78,boundaryCompactA77,boundaryReLow77]

theorem boundaryNormB78_zero (s : ℝ) : boundaryNormB78 0 s=boundaryNormB0 := by
  simp [boundaryNormB78,boundaryCompactB77,boundaryImLow77,boundaryNormB0]

theorem boundaryZ77_zero (s : ℝ) : boundaryZ77 0 s=1/3 := by simp [boundaryZ77]

theorem boundaryNormJ78_zero (s : ℝ) : boundaryNormJ78 0 s=-boundaryNormB0/3 := by
  simp only [boundaryNormJ78,boundaryNormDelta78,boundaryNormBeta78,boundaryNormY78,
    boundaryNormB78_zero]
  ring

theorem boundaryNormAHat78_zero (s : ℝ) : boundaryNormAHat78 0 s=-boundaryNormB0/3 := by
  simp only [boundaryNormAHat78,boundaryZ77_zero,boundaryNormB78_zero]
  ring

theorem boundaryNormTrace78_zero (s : ℝ) : boundaryNormTrace78 0 s=-boundaryNormB0/3 := by
  simp only [boundaryNormTrace78,boundaryNormA78_zero,boundaryNormBeta78,boundaryNormB78_zero]
  ring

/-- The clock-zero regular core is `g(s) = 155520 - (567/64) s²`. -/
theorem boundaryRegularCore77_zero (s : ℝ) :
    boundaryRegularCore77 0 s=155520-567/64*s^2 := by
  norm_num [boundaryRegularCore77,boundaryLowCore77,boundaryR77,boundaryZ77,boundaryReHigh77,
    boundaryImHigh77,boundaryReHighColumn77_0,boundaryReHighColumn77_1,boundaryReHighColumn77_2,
    boundaryReHighColumn77_3,boundaryReHighColumn77_4,boundaryReHighColumn77_5,
    boundaryReHighColumn77_6,boundaryReHighColumn77_7,boundaryReHighColumn77_8,
    boundaryReHighColumn77_9,boundaryReHighColumn77_10,boundaryReHighColumn77_11,
    boundaryReHighColumn77_12,boundaryReHighColumn77_13,boundaryReHighColumn77_14,
    boundaryReHighColumn77_15,boundaryReHighColumn77_16,boundaryReHighColumn77_17,
    boundaryReHighColumn77_18,boundaryReHighColumn77_19,boundaryReHighColumn77_20,
    boundaryReHighColumn77_21,boundaryReHighColumn77_22,boundaryImHighColumn77_0,
    boundaryImHighColumn77_1,boundaryImHighColumn77_2,boundaryImHighColumn77_3,
    boundaryImHighColumn77_4,boundaryImHighColumn77_5,boundaryImHighColumn77_6,
    boundaryImHighColumn77_7,boundaryImHighColumn77_8,boundaryImHighColumn77_9,
    boundaryImHighColumn77_10,boundaryImHighColumn77_11,boundaryImHighColumn77_12,
    boundaryImHighColumn77_13,boundaryImHighColumn77_14,boundaryImHighColumn77_15,
    boundaryImHighColumn77_16,boundaryImHighColumn77_17,boundaryImHighColumn77_18,
    boundaryImHighColumn77_19,boundaryImHighColumn77_20,boundaryImHighColumn77_21]
  ring

theorem boundaryRegularCore77_zero_pos {s : ℝ} (hs0 : 0≤s) (hs1 : s≤boundaryNormS78) :
    0<boundaryRegularCore77 0 s := by
  rw [boundaryRegularCore77_zero]
  have hS : s^2≤boundaryNormS78^2 := pow_le_pow_left₀ hs0 hs1 2
  norm_num [boundaryNormS78] at hS ⊢
  nlinarith

theorem boundaryNormHat78_zero (s : ℝ) :
    boundaryNormHat78 0 s=-boundaryNormB0*boundaryRegularCore77 0 s/3 := by
  rw [boundaryNormHat78,boundaryNormJ78_zero]
  ring

theorem boundaryNormHat78_zero_neg {s : ℝ} (hs0 : 0≤s) (hs1 : s≤boundaryNormS78) :
    boundaryNormHat78 0 s<0 := by
  rw [boundaryNormHat78_zero]
  have := mul_pos boundaryNormB0_pos (boundaryRegularCore77_zero_pos hs0 hs1)
  linarith

/-! ### Continuity -/

theorem continuous_boundaryReHigh77 : Continuous (fun p : ℝ×ℝ => boundaryReHigh77 p.1 p.2) := by
  unfold boundaryReHigh77 boundaryReHighColumn77_0 boundaryReHighColumn77_1
    boundaryReHighColumn77_2 boundaryReHighColumn77_3 boundaryReHighColumn77_4
    boundaryReHighColumn77_5 boundaryReHighColumn77_6 boundaryReHighColumn77_7
    boundaryReHighColumn77_8 boundaryReHighColumn77_9 boundaryReHighColumn77_10
    boundaryReHighColumn77_11 boundaryReHighColumn77_12 boundaryReHighColumn77_13
    boundaryReHighColumn77_14 boundaryReHighColumn77_15 boundaryReHighColumn77_16
    boundaryReHighColumn77_17 boundaryReHighColumn77_18 boundaryReHighColumn77_19
    boundaryReHighColumn77_20 boundaryReHighColumn77_21 boundaryReHighColumn77_22
  fun_prop

theorem continuous_boundaryImHigh77 : Continuous (fun p : ℝ×ℝ => boundaryImHigh77 p.1 p.2) := by
  unfold boundaryImHigh77 boundaryImHighColumn77_0 boundaryImHighColumn77_1
    boundaryImHighColumn77_2 boundaryImHighColumn77_3 boundaryImHighColumn77_4
    boundaryImHighColumn77_5 boundaryImHighColumn77_6 boundaryImHighColumn77_7
    boundaryImHighColumn77_8 boundaryImHighColumn77_9 boundaryImHighColumn77_10
    boundaryImHighColumn77_11 boundaryImHighColumn77_12 boundaryImHighColumn77_13
    boundaryImHighColumn77_14 boundaryImHighColumn77_15 boundaryImHighColumn77_16
    boundaryImHighColumn77_17 boundaryImHighColumn77_18 boundaryImHighColumn77_19
    boundaryImHighColumn77_20 boundaryImHighColumn77_21
  fun_prop

theorem continuous_boundaryR77 : Continuous (fun p : ℝ×ℝ => boundaryR77 p.1 p.2) := by
  unfold boundaryR77; fun_prop

theorem continuous_boundaryZ77 : Continuous (fun p : ℝ×ℝ => boundaryZ77 p.1 p.2) := by
  unfold boundaryZ77; fun_prop

theorem continuous_boundaryRegularCore77 :
    Continuous (fun p : ℝ×ℝ => boundaryRegularCore77 p.1 p.2) := by
  have hR := continuous_boundaryR77
  have hZ := continuous_boundaryZ77
  have hRe := continuous_boundaryReHigh77.comp (continuous_fst.prodMk hR)
  have hIm := continuous_boundaryImHigh77.comp (continuous_fst.prodMk hR)
  have hL : Continuous (fun p : ℝ×ℝ => boundaryLowCore77 p.1 p.2) := by
    unfold boundaryLowCore77; fun_prop
  exact (hL.add hRe).add (hZ.mul hIm)

theorem continuous_boundaryNormA78 : Continuous (fun p : ℝ×ℝ => boundaryNormA78 p.1 p.2) := by
  have hR := continuous_boundaryR77
  have hRe := continuous_boundaryReHigh77.comp (continuous_fst.prodMk hR)
  have hL : Continuous (fun p : ℝ×ℝ => boundaryReLow77 p.1 (boundaryR77 p.1 p.2)) := by
    unfold boundaryReLow77; fun_prop
  exact hL.add ((continuous_fst.pow 6).mul hRe)

theorem continuous_boundaryNormB78 : Continuous (fun p : ℝ×ℝ => boundaryNormB78 p.1 p.2) := by
  have hR := continuous_boundaryR77
  have hIm := continuous_boundaryImHigh77.comp (continuous_fst.prodMk hR)
  have hL : Continuous (fun p : ℝ×ℝ => boundaryImLow77 p.1 (boundaryR77 p.1 p.2)) := by
    unfold boundaryImLow77; fun_prop
  exact hL.add ((continuous_fst.pow 5).mul hIm)

theorem continuous_boundaryNormJ78 : Continuous (fun p : ℝ×ℝ => boundaryNormJ78 p.1 p.2) := by
  have hG := continuous_boundaryRegularCore77
  have hB := continuous_boundaryNormB78
  have hZ := continuous_boundaryZ77
  unfold boundaryNormJ78 boundaryNormDelta78 boundaryNormBeta78 boundaryNormY78
  fun_prop

theorem continuous_boundaryNormAHat78 :
    Continuous (fun p : ℝ×ℝ => boundaryNormAHat78 p.1 p.2) := by
  have hG := continuous_boundaryRegularCore77
  have hB := continuous_boundaryNormB78
  have hZ := continuous_boundaryZ77
  unfold boundaryNormAHat78
  fun_prop

theorem continuous_boundaryNormHat78 : Continuous (fun p : ℝ×ℝ => boundaryNormHat78 p.1 p.2) :=
  continuous_boundaryRegularCore77.mul continuous_boundaryNormJ78

theorem continuous_boundaryNormTrace78 :
    Continuous (fun p : ℝ×ℝ => boundaryNormTrace78 p.1 p.2) := by
  have hA := continuous_boundaryNormA78
  have hB := continuous_boundaryNormB78
  unfold boundaryNormTrace78 boundaryNormBeta78
  fun_prop

theorem continuous_boundaryNormHat78_clock (s : ℝ) :
    Continuous (fun h : ℝ => boundaryNormHat78 h s) := by
  have hc := continuous_boundaryNormHat78.comp (continuous_id.prodMk (continuous_const (y := s)))
  exact hc

theorem continuous_boundaryNormAHat78_clock (s : ℝ) :
    Continuous (fun h : ℝ => boundaryNormAHat78 h s) := by
  have hc := continuous_boundaryNormAHat78.comp
    (continuous_id.prodMk (continuous_const (y := s)))
  exact hc

/-! ### Uniform orientation on a clock strip -/

/-- A continuous function negative on the compact face `{0} × [a, b]` stays negative on a whole
strip `(-ε, ε) × [a, b]`. -/
theorem exists_strip_neg_of_continuous {f : ℝ×ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hneg : ∀ s ∈ Set.Icc a b, f (0, s)<0) :
    ∃ ε>0, ∀ h s, |h|<ε → s ∈ Set.Icc a b → f (h, s)<0 := by
  have hK : IsCompact ({(0:ℝ)} ×ˢ Set.Icc a b) := isCompact_singleton.prod isCompact_Icc
  have hU : IsOpen (f ⁻¹' Set.Iio 0) := isOpen_Iio.preimage hf
  have hsub : {(0:ℝ)} ×ˢ Set.Icc a b ⊆ f ⁻¹' Set.Iio 0 := by
    rintro ⟨x, s⟩ ⟨hx, hs⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hneg s hs
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open hU hsub
  refine ⟨δ, hδ, fun h s hh hs => hth ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨(0, s), ⟨rfl, hs⟩, ?_⟩
  rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, max_eq_left (abs_nonneg h)]
  exact hh

/-- **Uniform orientation.**  There is one `ε > 0` such that, simultaneously for all
`s ∈ [0, S]` and `0 ≤ h < ε`: `G > 0`, `B > 0`, `J < 0`, `Â < 0`, `G J < 0`, `2A + βB < 0`. -/
theorem boundaryNorm78_uniform_strip :
    ∃ ε>0, ε≤4/5 ∧ ∀ h s, 0≤h → h<ε → 0≤s → s≤boundaryNormS78 →
      0<boundaryRegularCore77 h s ∧ 0<boundaryNormB78 h s ∧ boundaryNormJ78 h s<0 ∧
        boundaryNormAHat78 h s<0 ∧ boundaryNormHat78 h s<0 ∧ boundaryNormTrace78 h s<0 := by
  have hB0 := boundaryNormB0_pos
  obtain ⟨e0, he0, h0⟩ := exists_strip_neg_of_continuous continuous_boundaryRegularCore77.neg
    (a := 0) (b := boundaryNormS78) (fun s hs => by
      have := boundaryRegularCore77_zero_pos hs.1 hs.2
      simp only [Pi.neg_apply, neg_lt_zero]; exact this)
  obtain ⟨e1, he1, h1⟩ := exists_strip_neg_of_continuous continuous_boundaryNormB78.neg
    (a := 0) (b := boundaryNormS78) (fun s _ => by
      simp only [Pi.neg_apply, boundaryNormB78_zero]; linarith)
  obtain ⟨e2, he2, h2⟩ := exists_strip_neg_of_continuous continuous_boundaryNormJ78
    (a := 0) (b := boundaryNormS78) (fun s _ => by
      simp only [boundaryNormJ78_zero]; linarith)
  obtain ⟨e3, he3, h3⟩ := exists_strip_neg_of_continuous continuous_boundaryNormAHat78
    (a := 0) (b := boundaryNormS78) (fun s _ => by
      simp only [boundaryNormAHat78_zero]; linarith)
  obtain ⟨e4, he4, h4⟩ := exists_strip_neg_of_continuous continuous_boundaryNormHat78
    (a := 0) (b := boundaryNormS78) (fun s hs => boundaryNormHat78_zero_neg hs.1 hs.2)
  obtain ⟨e5, he5, h5⟩ := exists_strip_neg_of_continuous continuous_boundaryNormTrace78
    (a := 0) (b := boundaryNormS78) (fun s _ => by
      simp only [boundaryNormTrace78_zero]; linarith)
  have hH : (0:ℝ)<4/5 := by norm_num
  refine ⟨min (min (min e1 e2) (min e3 e4)) (min e5 (min e0 (4/5))), ?_, ?_, ?_⟩
  · exact lt_min (lt_min (lt_min he1 he2) (lt_min he3 he4)) (lt_min he5 (lt_min he0 hH))
  · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  · intro h s hh0 hhe hs0 hs1
    have hs : s ∈ Set.Icc 0 boundaryNormS78 := ⟨hs0, hs1⟩
    have habs : |h|=h := abs_of_nonneg hh0
    have hlt (e : ℝ)
        (he : min (min (min e1 e2) (min e3 e4)) (min e5 (min e0 (4/5)))≤e) : |h|<e := by
      rw [habs]; linarith
    refine ⟨?_, ?_, h2 h s (hlt e2 ?_) hs,
      h3 h s (hlt e3 ?_) hs, h4 h s (hlt e4 ?_) hs, h5 h s (hlt e5 ?_) hs⟩
    · have := h0 h s (hlt e0 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_left _ _)))) hs
      simp only [Pi.neg_apply, neg_lt_zero] at this
      exact this
    · have := h1 h s (hlt e1 (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
        (min_le_left _ _)))) hs
      simp only [Pi.neg_apply, neg_lt_zero] at this
      exact this
    · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    · exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    · exact le_trans (min_le_right _ _) (min_le_left _ _)

/-- **Orientation of the physical and conjugate values.**  On the strip `0 < h < ε`: the first
coefficient is negative, the physical value `A + y B = h⁶ G` positive, the conjugate value
`A + (β - y) B` negative, and the norm `N` negative. -/
theorem boundaryNorm78_orientation :
    ∃ ε>0, ε≤4/5 ∧ ∀ h s, 0<h → h<ε → 0≤s → s≤boundaryNormS78 →
      boundaryNormA78 h s<0 ∧
      0<boundaryNormA78 h s+boundaryNormY78 h s*boundaryNormB78 h s ∧
      boundaryNormA78 h s+(boundaryNormBeta78 h-boundaryNormY78 h s)*boundaryNormB78 h s<0 ∧
      boundaryNorm78 h s<0 ∧ boundaryNormTrace78 h s<0 := by
  obtain ⟨ε, hε, hεH, hstrip⟩ := boundaryNorm78_uniform_strip
  refine ⟨ε, hε, hεH, fun h s hh0 hhe hs0 hs1 => ?_⟩
  obtain ⟨hG, -, hJ, hAh, hN, hT⟩ := hstrip h s hh0.le hhe hs0 hs1
  refine ⟨?_, ?_, ?_, ?_, hT⟩
  · rw [boundaryNormA78_eq_mul_hat]; exact mul_neg_of_pos_of_neg hh0 hAh
  · rw [boundaryNormA78_add_y_mul]; exact mul_pos (pow_pos hh0 6) hG
  · rw [boundaryNormJ78_eq_conjugate]; exact hJ
  · rw [boundaryNorm78_factor]; exact mul_neg_of_pos_of_neg (pow_pos hh0 6) hN

/-! ### Exact vanishing orders -/

/-- `N` has exact order six at zero clock: no factorization `N = h⁷ D` with `D` continuous at
zero holds on any punctured right neighbourhood. -/
theorem boundaryNorm78_not_seventh_order {s : ℝ} (hs0 : 0≤s) (hs1 : s≤boundaryNormS78) :
    ¬ ∃ D : ℝ → ℝ, ContinuousAt D 0 ∧
      ∀ᶠ h in 𝓝[>] (0:ℝ), boundaryNorm78 h s=h^7*D h := by
  rintro ⟨D, hD, hev⟩
  have hc := continuous_boundaryNormHat78_clock s
  have hlim1 : Tendsto (fun h : ℝ => boundaryNormHat78 h s) (𝓝[>] 0)
      (𝓝 (boundaryNormHat78 0 s)) := (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun h : ℝ => h*D h) (𝓝[>] 0) (𝓝 (0*D 0)) :=
    ((continuousAt_id.mul hD).tendsto).mono_left nhdsWithin_le_nhds
  have heq : (fun h : ℝ => h*D h) =ᶠ[𝓝[>] 0] (fun h : ℝ => boundaryNormHat78 h s) := by
    filter_upwards [hev, self_mem_nhdsWithin] with h hh hpos
    rw [boundaryNorm78_factor] at hh
    have hp : (h:ℝ)^6≠0 := pow_ne_zero 6 (ne_of_gt hpos)
    have : h^6*boundaryNormHat78 h s=h^6*(h*D h) := by rw [hh]; ring
    exact (mul_left_cancel₀ hp this).symm
  have hu := tendsto_nhds_unique (hlim2.congr' heq) hlim1
  rw [zero_mul] at hu
  exact (boundaryNormHat78_zero_neg hs0 hs1).ne hu.symm

/-- `A` has exact order one at zero clock: no factorization `A = h² D` with `D` continuous at
zero. -/
theorem boundaryNormA78_not_second_order (s : ℝ) :
    ¬ ∃ D : ℝ → ℝ, ContinuousAt D 0 ∧
      ∀ᶠ h in 𝓝[>] (0:ℝ), boundaryNormA78 h s=h^2*D h := by
  rintro ⟨D, hD, hev⟩
  have hc := continuous_boundaryNormAHat78_clock s
  have hlim1 : Tendsto (fun h : ℝ => boundaryNormAHat78 h s) (𝓝[>] 0)
      (𝓝 (boundaryNormAHat78 0 s)) := (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun h : ℝ => h*D h) (𝓝[>] 0) (𝓝 (0*D 0)) :=
    ((continuousAt_id.mul hD).tendsto).mono_left nhdsWithin_le_nhds
  have heq : (fun h : ℝ => h*D h) =ᶠ[𝓝[>] 0] (fun h : ℝ => boundaryNormAHat78 h s) := by
    filter_upwards [hev, self_mem_nhdsWithin] with h hh hpos
    rw [boundaryNormA78_eq_mul_hat] at hh
    have hp : h≠0 := ne_of_gt hpos
    have : h*boundaryNormAHat78 h s=h*(h*D h) := by rw [hh]; ring
    exact (mul_left_cancel₀ hp this).symm
  have hu := tendsto_nhds_unique (hlim2.congr' heq) hlim1
  rw [zero_mul, boundaryNormAHat78_zero] at hu
  have := boundaryNormB0_pos
  linarith

/-! ### Identification with the source quadratic algebra -/

/-- The boundary reduced slope `W ∈ BoundaryAlg (V, 1/h)` at real `h, s`. -/
def boundaryNormSlope78 (h s : ℝ) :
    BoundaryAlg (9-nonlinearBoundaryR (h:ℂ) (s:ℂ)*(h:ℂ)^2) (h:ℂ)⁻¹ :=
  boundaryReducedSlope75 (9-nonlinearBoundaryR (h:ℂ) (s:ℂ)*(h:ℂ)^2) (h:ℂ)⁻¹

/-- **Source identification.**  For `h ≠ 0`: `h²² W.re = A`, `h²¹ W.im = B`,
`h² a = α`, `h b = β` for the boundary quadratic `ω² = a + b ω`, hence
`h⁴⁴ norm W = N` and `h²² (2 W.re + b W.im) = 2A + βB`. -/
theorem boundaryNormSlope78_source {h : ℝ} (hh : h≠0) (s : ℝ) :
    (h:ℂ)^22*(boundaryNormSlope78 h s).re=boundaryNormA78 h s ∧
    (h:ℂ)^21*(boundaryNormSlope78 h s).im=boundaryNormB78 h s ∧
    (h:ℂ)^2*boundaryA (9-nonlinearBoundaryR (h:ℂ) (s:ℂ)*(h:ℂ)^2) (h:ℂ)⁻¹=
      boundaryNormAlpha78 h s ∧
    (h:ℂ)*boundaryB (h:ℂ)⁻¹=boundaryNormBeta78 h ∧
    (h:ℂ)^44*QuadraticAlgebra.norm (boundaryNormSlope78 h s)=boundaryNorm78 h s ∧
    (h:ℂ)^22*(2*(boundaryNormSlope78 h s).re+
      boundaryB (h:ℂ)⁻¹*(boundaryNormSlope78 h s).im)=boundaryNormTrace78 h s := by
  have hhC : (h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hh
  have hR : nonlinearBoundaryR (h:ℂ) (s:ℂ)=((boundaryR77 h s : ℝ) : ℂ) :=
    (boundaryR77_ofReal h s).symm
  have hA : (h:ℂ)^22*(boundaryNormSlope78 h s).re=boundaryNormA78 h s := by
    rw [boundaryNormSlope78, boundaryCompactA75_eq hhC, hR, boundaryNormA78,
      boundaryCompactA77_ofReal]
  have hB : (h:ℂ)^21*(boundaryNormSlope78 h s).im=boundaryNormB78 h s := by
    rw [boundaryNormSlope78, boundaryCompactB75_eq hhC, hR, boundaryNormB78,
      boundaryCompactB77_ofReal]
  have hbeta : (h:ℂ)*boundaryB (h:ℂ)⁻¹=boundaryNormBeta78 h := by
    unfold boundaryB boundaryNormBeta78
    push_cast
    field_simp
  have hroot := nonlinearBoundary_root76 hhC (s:ℂ)
  have hZ : nonlinearBoundaryZ (h:ℂ) (s:ℂ)=((boundaryZ77 h s : ℝ) : ℂ) :=
    (boundaryZ77_ofReal h s).symm
  have halpha : (h:ℂ)^2*boundaryA (9-nonlinearBoundaryR (h:ℂ) (s:ℂ)*(h:ℂ)^2) (h:ℂ)⁻¹=
      boundaryNormAlpha78 h s := by
    have hV : nonlinearBoundaryV (h:ℂ) (s:ℂ)=9-nonlinearBoundaryR (h:ℂ) (s:ℂ)*(h:ℂ)^2 := rfl
    rw [hV, hZ] at hroot
    unfold boundaryNormAlpha78 boundaryNormY78
    push_cast
    rw [←hbeta]
    linear_combination -(h:ℂ)^2*hroot
  refine ⟨hA, hB, halpha, hbeta, ?_, ?_⟩
  · rw [QuadraticAlgebra.norm_def]
    unfold boundaryNorm78
    push_cast
    rw [←hA, ←hB, ←halpha, ←hbeta]
    ring
  · unfold boundaryNormTrace78
    push_cast
    rw [←hA, ←hB, ←hbeta]
    ring

/-- **Negative source norm and trace.**  On the strip `0 < h < ε`, the norm of the boundary
reduced slope is the negative real `N / h⁴⁴`, and `2 W.re + b W.im` and `W.re` are negative reals. -/
theorem boundaryNormSlope78_norm_trace_neg :
    ∃ ε>0, ε≤4/5 ∧ ∀ h s, 0<h → h<ε → 0≤s → s≤boundaryNormS78 →
      QuadraticAlgebra.norm (boundaryNormSlope78 h s)=((boundaryNorm78 h s/h^44 : ℝ) : ℂ) ∧
      boundaryNorm78 h s/h^44<0 ∧
      2*(boundaryNormSlope78 h s).re+boundaryB (h:ℂ)⁻¹*(boundaryNormSlope78 h s).im=
        ((boundaryNormTrace78 h s/h^22 : ℝ) : ℂ) ∧ boundaryNormTrace78 h s/h^22<0 ∧
      (boundaryNormSlope78 h s).re=((boundaryNormA78 h s/h^22 : ℝ) : ℂ) ∧
      boundaryNormA78 h s/h^22<0 := by
  obtain ⟨ε, hε, hεH, hor⟩ := boundaryNorm78_orientation
  refine ⟨ε, hε, hεH, fun h s hh0 hhe hs0 hs1 => ?_⟩
  obtain ⟨hA, -, -, hN, hT⟩ := hor h s hh0 hhe hs0 hs1
  obtain ⟨eA, -, -, -, eN, eT⟩ := boundaryNormSlope78_source hh0.ne' s
  have hhC : (h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hh0.ne'
  refine ⟨?_, div_neg_of_neg_of_pos hN (pow_pos hh0 44), ?_,
    div_neg_of_neg_of_pos hT (pow_pos hh0 22), ?_, div_neg_of_neg_of_pos hA (pow_pos hh0 22)⟩
  · push_cast
    rw [←eN]
    field_simp
  · push_cast
    rw [←eT]
    field_simp
  · push_cast
    rw [←eA]
    field_simp

/-! ### Pole orders -/

theorem boundaryNormSlope78_pole_identities {h : ℝ} (hh : h≠0) (s : ℝ) :
    (h:ℂ)^38*QuadraticAlgebra.norm (boundaryNormSlope78 h s)=boundaryNormHat78 h s ∧
      (h:ℂ)^21*(boundaryNormSlope78 h s).re=boundaryNormAHat78 h s := by
  obtain ⟨eA, -, -, -, eN, -⟩ := boundaryNormSlope78_source hh s
  have hhC : (h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hh
  constructor
  · apply mul_left_cancel₀ (pow_ne_zero 6 hhC)
    rw [←mul_assoc, ←pow_add, eN, boundaryNorm78_factor]
    push_cast
    ring
  · apply mul_left_cancel₀ hhC
    rw [←mul_assoc, ←pow_succ', eA, boundaryNormA78_eq_mul_hat]
    push_cast
    ring

/-- **Exact pole orders.**  As `h → 0⁺`, `h³⁸ norm W → -B₀ g(s)/3` and `h²¹ W.re → -B₀/3`,
both nonzero on `[0, S]`: the norm has a pole of exact order `38` and the first source coefficient
a pole of exact order `21`. -/
theorem boundaryNormSlope78_pole_limits (s : ℝ) :
    Tendsto (fun h : ℝ => (h:ℂ)^38*QuadraticAlgebra.norm (boundaryNormSlope78 h s)) (𝓝[>] 0)
        (𝓝 ((-boundaryNormB0*(155520-567/64*s^2)/3 : ℝ) : ℂ)) ∧
      Tendsto (fun h : ℝ => (h:ℂ)^21*(boundaryNormSlope78 h s).re) (𝓝[>] 0)
        (𝓝 ((-boundaryNormB0/3 : ℝ) : ℂ)) := by
  have hcN : Continuous (fun h : ℝ => ((boundaryNormHat78 h s : ℝ) : ℂ)) := by
    have hc := Complex.continuous_ofReal.comp (continuous_boundaryNormHat78_clock s)
    exact hc
  have hcA : Continuous (fun h : ℝ => ((boundaryNormAHat78 h s : ℝ) : ℂ)) := by
    have hc := Complex.continuous_ofReal.comp (continuous_boundaryNormAHat78_clock s)
    exact hc
  constructor
  · have hlim : Tendsto (fun h : ℝ => ((boundaryNormHat78 h s : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 ((-boundaryNormB0*(155520-567/64*s^2)/3 : ℝ) : ℂ)) := by
      refine (hcN.tendsto' 0 _ ?_).mono_left nhdsWithin_le_nhds
      simp only [boundaryNormHat78_zero, boundaryRegularCore77_zero]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hpos
    exact ((boundaryNormSlope78_pole_identities (ne_of_gt hpos) s).1).symm
  · have hlim : Tendsto (fun h : ℝ => ((boundaryNormAHat78 h s : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 ((-boundaryNormB0/3 : ℝ) : ℂ)) := by
      refine (hcA.tendsto' 0 _ ?_).mono_left nhdsWithin_le_nhds
      simp only [boundaryNormAHat78_zero]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hpos
    exact ((boundaryNormSlope78_pole_identities (ne_of_gt hpos) s).2).symm

theorem boundaryNorm78_clock_zero_value_pos {s : ℝ} (hs0 : 0≤s) (hs1 : s≤boundaryNormS78) :
    0<155520-567/64*s^2 := by
  rw [←boundaryRegularCore77_zero]
  exact boundaryRegularCore77_zero_pos hs0 hs1

end
end HTGeometry.ThetaRatioInfinity
