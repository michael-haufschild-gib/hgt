import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioSourceSlopeReal
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioNonlinearConeTailIncidence

/-!
# Negative quadratic source norm and trace at strict interior points of the C78 cone

Fix `0 < s < 361/25`.  For a small clock `h > 0` the exact nonlinear boundary point
`r = s (1 - h² b(h) s)`, `t₀ = b(h) s` satisfies every strict non-error constraint of the
coarse source cone, and the boundary reduced slope has negative norm and trace
(`ThetaCuspRatioBoundaryNormOrientation`).  Keep `h`, `r`, `V = 9 - r h²` fixed and move along
`t_e = t₀ + 3 (1 - e) Z / h`, so that the source coordinate is `J = (1 - t_e h)/3 = e Z`.
Evaluating the full source slope in the same boundary quadratic algebra with `J ↦ e ω` gives an
element `W_e` with `W_1 = W`.  Its norm and trace are real (`sourcePolyConj_slope`) and continuous
in `e`, the error has the exact factorization `E(t_e) = (t_e - t₀)(1 - h² (t_e + t₀)) > 0`, and the
speed constraint persists.  Hence (`boundaryNorm78_interior_negative`) there are physical interior
points with `E > 0` at which the quadratic source norm and trace are negative.
-/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology ComplexConjugate

/-! ### The interior path -/

/-- The boundary clock time `t₀ = b(h) s`. -/
def boundaryT77 (h s : ℝ) : ℝ := (1/12-7*h/72)*s

/-- The clock time at which the source coordinate equals `e Z`. -/
def interiorT78 (h s e : ℝ) : ℝ := boundaryT77 h s+3*(1-e)*boundaryZ77 h s/h

/-- The drift coordinate `V = 9 - r h²` of the boundary point. -/
def interiorV78 (h s : ℝ) : ℝ := 9-boundaryR77 h s*h^2

theorem interiorT78_source {h : ℝ} (hh : h≠0) (s e : ℝ) :
    (1-interiorT78 h s e*h)/3=e*boundaryZ77 h s := by
  unfold interiorT78 boundaryT77 boundaryZ77
  field_simp
  ring

theorem boundaryT77_error (h s : ℝ) :
    boundaryT77 h s-h^2*boundaryT77 h s^2=boundaryR77 h s*(1/12-7*h/72) := by
  unfold boundaryT77 boundaryR77
  ring

/-- Exact error factorization `E(t) = (t - t₀)(1 - h² (t + t₀))`. -/
theorem interior_error_factor (h s t : ℝ) :
    t-h^2*t^2-boundaryR77 h s*(1/12-7*h/72)=
      (t-boundaryT77 h s)*(1-h^2*(t+boundaryT77 h s)) := by
  rw [←boundaryT77_error]
  ring

theorem strictCoarseCone_speed_eq {h : ℝ} (hh : h≠0) (r t : ℝ) :
    h⁻¹^2*(9-(9-r*h^2))-6*h⁻¹-4+2*(9-r*h^2)*(h⁻¹+2/3)*((1-t*h)/3)=compactSpeed h r t := by
  unfold compactSpeed
  field_simp
  ring

/-! ### The interior source element -/

/-- `W_e = (c V)⁻¹ · interiorHom(slope)` in the boundary quadratic algebra, `c = 6²⁴·24⁹`. -/
def interiorSlope78 (h s e : ℝ) :
    BoundaryAlg ((interiorV78 h s : ℝ) : ℂ) ((h⁻¹ : ℝ) : ℂ) :=
  algebraMap ℂ _ (((6:ℂ)^24*24^9*((interiorV78 h s : ℝ) : ℂ))⁻¹)*
    interiorHom ((interiorV78 h s : ℝ) : ℂ) ((h⁻¹ : ℝ) : ℂ) (e:ℂ) ThetaRatioSquare.slope

theorem algebraMap_mul_re {a b : ℂ} (c : ℂ) (z : QuadraticAlgebra ℂ a b) :
    (algebraMap ℂ (QuadraticAlgebra ℂ a b) c*z).re=c*z.re := by
  simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]

theorem algebraMap_mul_im {a b : ℂ} (c : ℂ) (z : QuadraticAlgebra ℂ a b) :
    (algebraMap ℂ (QuadraticAlgebra ℂ a b) c*z).im=c*z.im := by
  simp [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]

theorem interiorScale_conj (h s : ℝ) :
    conj (((6:ℂ)^24*24^9*((interiorV78 h s : ℝ) : ℂ))⁻¹)=
      ((6:ℂ)^24*24^9*((interiorV78 h s : ℝ) : ℂ))⁻¹ := by
  simp [map_inv₀, map_mul, map_pow, map_ofNat]

theorem interiorSlope78_conj (h s e : ℝ) :
    conj (interiorSlope78 h s e).re=(interiorSlope78 h s e).re ∧
      conj (interiorSlope78 h s e).im=(interiorSlope78 h s e).im := by
  obtain ⟨hre, him⟩ := interiorHom_slope_conj (interiorV78 h s) h⁻¹ e
  unfold interiorSlope78
  rw [algebraMap_mul_re, algebraMap_mul_im, map_mul, map_mul, interiorScale_conj, hre, him]
  exact ⟨rfl, rfl⟩

/-- The quadratic source norm of `W_e` (a real number). -/
def interiorNorm78 (h s e : ℝ) : ℝ := (QuadraticAlgebra.norm (interiorSlope78 h s e)).re

/-- The quadratic source trace `2 W_e.re + b W_e.im` (a real number). -/
def interiorTrace78 (h s e : ℝ) : ℝ :=
  (2*(interiorSlope78 h s e).re+boundaryB ((h⁻¹ : ℝ) : ℂ)*(interiorSlope78 h s e).im).re

theorem interiorNorm78_ofReal (h s e : ℝ) :
    ((interiorNorm78 h s e : ℝ) : ℂ)=QuadraticAlgebra.norm (interiorSlope78 h s e) := by
  apply Complex.conj_eq_iff_re.mp
  obtain ⟨hre, him⟩ := interiorSlope78_conj h s e
  rw [QuadraticAlgebra.norm_def]
  simp only [map_sub, map_add, map_mul, hre, him, boundaryA_conj_ofReal, boundaryB_conj_ofReal]

theorem interiorTrace78_ofReal (h s e : ℝ) :
    ((interiorTrace78 h s e : ℝ) : ℂ)=
      2*(interiorSlope78 h s e).re+boundaryB ((h⁻¹ : ℝ) : ℂ)*(interiorSlope78 h s e).im := by
  apply Complex.conj_eq_iff_re.mp
  obtain ⟨hre, him⟩ := interiorSlope78_conj h s e
  simp only [map_add, map_mul, hre, him, boundaryB_conj_ofReal, map_ofNat]

theorem continuous_interiorSlope78 (h s : ℝ) :
    Continuous (fun e : ℝ => (interiorSlope78 h s e).re) ∧
      Continuous (fun e : ℝ => (interiorSlope78 h s e).im) := by
  obtain ⟨hre, him⟩ := continuous_interiorHom ((interiorV78 h s : ℝ) : ℂ) ((h⁻¹ : ℝ) : ℂ)
    ThetaRatioSquare.slope
  unfold interiorSlope78
  simp only [algebraMap_mul_re, algebraMap_mul_im]
  exact ⟨continuous_const.mul hre, continuous_const.mul him⟩

theorem continuous_interiorNorm78 (h s : ℝ) : Continuous (fun e : ℝ => interiorNorm78 h s e) := by
  obtain ⟨hre, him⟩ := continuous_interiorSlope78 h s
  unfold interiorNorm78
  simp only [QuadraticAlgebra.norm_def]
  exact Complex.continuous_re.comp ((hre.mul hre).add ((continuous_const.mul hre).mul him) |>.sub
    ((continuous_const.mul him).mul him))

theorem continuous_interiorTrace78 (h s : ℝ) :
    Continuous (fun e : ℝ => interiorTrace78 h s e) := by
  obtain ⟨hre, him⟩ := continuous_interiorSlope78 h s
  unfold interiorTrace78
  exact Complex.continuous_re.comp ((continuous_const.mul hre).add (continuous_const.mul him))

/-! ### The boundary value `e = 1` -/

theorem interiorV78_ofReal (h s : ℝ) :
    ((interiorV78 h s : ℝ) : ℂ)=9-nonlinearBoundaryR (h:ℂ) (s:ℂ)*(h:ℂ)^2 := by
  rw [interiorV78, ←boundaryR77_ofReal]
  push_cast
  rfl

theorem interiorSlope78_one {h s : ℝ} (hv : interiorV78 h s≠0) :
    interiorSlope78 h s 1=boundaryReducedSlope75 ((interiorV78 h s : ℝ) : ℂ) ((h⁻¹ : ℝ) : ℂ) := by
  have hvC : ((interiorV78 h s : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv
  have hs := boundarySlope_source75 ((interiorV78 h s : ℝ) : ℂ) ((h⁻¹ : ℝ) : ℂ)
  rw [boundarySlope_factor75] at hs
  unfold interiorSlope78
  rw [Complex.ofReal_one, interiorHom_one]
  have hsplit : (((6:ℂ)^24*24^9*((interiorV78 h s : ℝ) : ℂ))⁻¹)=
      ((interiorV78 h s : ℝ) : ℂ)⁻¹*((6:ℂ)^24*24^9)⁻¹ := by
    rw [mul_inv, mul_comm]
  rw [hsplit, map_mul, mul_assoc, hs, ←mul_assoc, ←map_mul, inv_mul_cancel₀ hvC, map_one, one_mul]

theorem boundaryReducedSlope_source_of_eq {h : ℝ} (hh : h≠0) (s : ℝ) {v k : ℂ}
    (hv : v=9-nonlinearBoundaryR (h:ℂ) (s:ℂ)*(h:ℂ)^2) (hk : k=(h:ℂ)⁻¹) :
    (h:ℂ)^44*QuadraticAlgebra.norm (boundaryReducedSlope75 v k)=boundaryNorm78 h s ∧
      (h:ℂ)^22*(2*(boundaryReducedSlope75 v k).re+boundaryB k*(boundaryReducedSlope75 v k).im)=
        boundaryNormTrace78 h s := by
  subst hv hk
  obtain ⟨-, -, -, -, h1, h2⟩ := boundaryNormSlope78_source hh s
  exact ⟨h1, h2⟩

theorem interiorNorm78_one {h s : ℝ} (hh : h≠0) (hv : interiorV78 h s≠0) :
    interiorNorm78 h s 1=boundaryNorm78 h s/h^44 ∧
      interiorTrace78 h s 1=boundaryNormTrace78 h s/h^22 := by
  have hk : ((h⁻¹ : ℝ) : ℂ)=(h:ℂ)⁻¹ := Complex.ofReal_inv h
  obtain ⟨hN, hT⟩ := boundaryReducedSlope_source_of_eq hh s (interiorV78_ofReal h s) hk
  have hhC : (h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hh
  constructor
  · apply Complex.ofReal_injective
    rw [interiorNorm78_ofReal, interiorSlope78_one hv, Complex.ofReal_div, Complex.ofReal_pow, ←hN,
      mul_div_cancel_left₀ _ (pow_ne_zero 44 hhC)]
  · apply Complex.ofReal_injective
    rw [interiorTrace78_ofReal, interiorSlope78_one hv, Complex.ofReal_div, Complex.ofReal_pow,
      ←hT, mul_div_cancel_left₀ _ (pow_ne_zero 22 hhC)]

/-- The interior element evaluates, at the physical root `Z`, to the actual source slope at the
interior state `(h, r, t_e)`. -/
theorem interiorSlope78_physical {h : ℝ} (hh : h≠0) (s e : ℝ) :
    (((6:ℂ)^24*24^9*((interiorV78 h s : ℝ) : ℂ))⁻¹)*
        eval (sourcePoint (h:ℂ) (boundaryR77 h s : ℂ) (interiorT78 h s e : ℂ)) ThetaRatioSquare.slope=
      (interiorSlope78 h s e).re+(boundaryZ77 h s : ℂ)*(interiorSlope78 h s e).im := by
  have hhC : (h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hh
  have hroot : ((boundaryZ77 h s : ℝ) : ℂ)^2=
      boundaryA ((interiorV78 h s : ℝ) : ℂ) ((h⁻¹ : ℝ) : ℂ)+
        boundaryB ((h⁻¹ : ℝ) : ℂ)*((boundaryZ77 h s : ℝ) : ℂ) := by
    have hr := nonlinearBoundary_root76 hhC (s:ℂ)
    rw [(boundaryZ77_ofReal h s).symm,
      show nonlinearBoundaryV (h:ℂ) (s:ℂ)=((interiorV78 h s : ℝ) : ℂ) from
        (interiorV78_ofReal h s).symm, (Complex.ofReal_inv h).symm] at hr
    exact hr
  have he := boundaryEval_interiorHom ((interiorV78 h s : ℝ) : ℂ) ((h⁻¹ : ℝ) : ℂ) (e:ℂ)
    ((boundaryZ77 h s : ℝ) : ℂ) hroot ThetaRatioSquare.slope
  have hpt : basePoint ((interiorV78 h s : ℝ) : ℂ) ((h⁻¹ : ℝ) : ℂ) ((e:ℂ)*((boundaryZ77 h s : ℝ) : ℂ))=
      sourcePoint (h:ℂ) (boundaryR77 h s : ℂ) (interiorT78 h s e : ℂ) := by
    funext i
    cases i
    · simp only [basePoint, sourcePoint, interiorV78]
      push_cast
      ring
    · simp [basePoint, sourcePoint]
    · simp only [basePoint, sourcePoint]
      have hJ := interiorT78_source hh s e
      have hJC : ((1-interiorT78 h s e*h)/3 : ℝ)=((e*boundaryZ77 h s : ℝ)) := hJ
      have := congrArg (fun x : ℝ => (x:ℂ)) hJC
      push_cast at this
      exact this.symm
  rw [hpt] at he
  unfold interiorSlope78
  rw [algebraMap_mul_re, algebraMap_mul_im, ←he]
  ring

/-! ### Interior points with negative norm and trace -/

private theorem eventually_pos_of_continuousAt {f : ℝ → ℝ} {a : ℝ} (hf : ContinuousAt f a)
    (ha : 0<f a) : ∀ᶠ x in 𝓝 a, 0<f x :=
  continuousAt_const.eventually_lt hf ha

/-- **Strict-interior orientation.**  For every `0 < s < 361/25` there are a clock `h > 0` and an
`e₀ < 1` such that for all `e ∈ (e₀, 1)` the state `(h, r, t_e)` with `r = s (1 - h² b(h) s)`
lies in the strict coarse source cone, has positive error `t - h² t² - r b(h) > 0`, source
coordinate `J = e Z`, and its quadratic source norm and trace are negative.  The physical value of
`W_e` at `Z` is the normalized actual source slope at that state. -/
theorem boundaryNorm78_interior_negative {s : ℝ} (hs0 : 0<s) (hs1 : s<361/25) :
    ∃ h : ℝ, 0<h ∧ ∃ e₀<1, ∀ e ∈ Set.Ioo e₀ 1,
      StrictCoarseCone (9-boundaryR77 h s*h^2) h⁻¹ ((1-interiorT78 h s e*h)/3) ∧
      boundaryR77 h s*(1/12-7*h/72)< interiorT78 h s e-h^2*interiorT78 h s e^2 ∧
      (1-interiorT78 h s e*h)/3=e*boundaryZ77 h s ∧
      interiorNorm78 h s e<0 ∧ interiorTrace78 h s e<0 ∧
      (((6:ℂ)^24*24^9*((interiorV78 h s : ℝ) : ℂ))⁻¹)*
          eval (sourcePoint (h:ℂ) (boundaryR77 h s : ℂ) (interiorT78 h s e : ℂ))
            ThetaRatioSquare.slope=
        (interiorSlope78 h s e).re+(boundaryZ77 h s : ℂ)*(interiorSlope78 h s e).im := by
  obtain ⟨ε, hε, -, hor⟩ := boundaryNorm78_orientation
  have hsS : s≤boundaryNormS78 := by norm_num [boundaryNormS78]; linarith
  -- small-clock conditions at the boundary point
  have hc1 : ∀ᶠ h in 𝓝 (0:ℝ), 0<1-h^2*(1/12-7*h/72)*s :=
    eventually_pos_of_continuousAt (by fun_prop) (by norm_num)
  have hc2 : ∀ᶠ h in 𝓝 (0:ℝ), 0<1-h*(1/12-7*h/72)*s :=
    eventually_pos_of_continuousAt (by fun_prop) (by norm_num)
  have hc3 : ∀ᶠ h in 𝓝 (0:ℝ), 0<1/12-7*h/72 :=
    eventually_pos_of_continuousAt (by fun_prop) (by norm_num)
  have hc4 : ∀ᶠ h in 𝓝 (0:ℝ), 0<9-boundaryR77 h s*h^2 :=
    eventually_pos_of_continuousAt (by unfold boundaryR77; fun_prop) (by simp [boundaryR77])
  have hc5 : ∀ᶠ h in 𝓝 (0:ℝ), 0<compactSpeed h (boundaryR77 h s) (boundaryT77 h s) :=
    eventually_pos_of_continuousAt (by unfold compactSpeed boundaryR77 boundaryT77; fun_prop)
      (by simp [compactSpeed, boundaryR77, boundaryT77]; nlinarith)
  have hc6 : ∀ᶠ h in 𝓝 (0:ℝ), 0<1-h^2*(2*boundaryT77 h s) :=
    eventually_pos_of_continuousAt (by unfold boundaryT77; fun_prop) (by norm_num)
  have hc7 : ∀ᶠ h in 𝓝 (0:ℝ), h<min ε (4/5) :=
    continuousAt_id.eventually_lt continuousAt_const (lt_min hε (by norm_num))
  have hall := ((((((hc1.and hc2).and hc3).and hc4).and hc5).and hc6).and hc7)
  obtain ⟨h, ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hpos⟩ :=
    ((eventually_nhdsWithin_of_eventually_nhds hall).and
      (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ 𝓝[>] (0:ℝ))).exists
  have hh0 : 0<h := hpos
  have hhne : h≠0 := hh0.ne'
  have hhε : h<ε := lt_of_lt_of_le h7 (min_le_left _ _)
  have hh45 : h<4/5 := lt_of_lt_of_le h7 (min_le_right _ _)
  set r := boundaryR77 h s with hrdef
  set Z := boundaryZ77 h s with hZdef
  set t0 := boundaryT77 h s with ht0def
  have hr0 : 0<r := by simp only [hrdef, boundaryR77]; exact mul_pos hs0 (by linarith)
  have hZ0 : 0<Z := by simp only [hZdef, boundaryZ77]; linarith
  have hZ3 : Z<1/3 := by
    simp only [hZdef, boundaryZ77]
    have : 0<h*(1/12-7*h/72)*s := mul_pos (mul_pos hh0 h3) hs0
    linarith
  have hrS : r<361/25 := by
    have : 0≤h^2*(1/12-7*h/72)*s*s := by positivity
    simp only [hrdef, boundaryR77]
    nlinarith
  have hv0 : 0< interiorV78 h s := h4
  -- boundary norm and trace at e = 1
  obtain ⟨-, -, -, hN, hT⟩ := hor h s hh0 hhε hs0.le hsS
  obtain ⟨hN1, hT1⟩ := interiorNorm78_one hhne hv0.ne'
  have hNe : interiorNorm78 h s 1<0 := by
    rw [hN1]; exact div_neg_of_neg_of_pos hN (pow_pos hh0 44)
  have hTe : interiorTrace78 h s 1<0 := by
    rw [hT1]; exact div_neg_of_neg_of_pos hT (pow_pos hh0 22)
  -- conditions near e = 1
  have he1 : ∀ᶠ e in 𝓝 (1:ℝ), interiorNorm78 h s e<0 :=
    (continuous_interiorNorm78 h s).continuousAt.eventually_lt continuousAt_const hNe
  have he2 : ∀ᶠ e in 𝓝 (1:ℝ), interiorTrace78 h s e<0 :=
    (continuous_interiorTrace78 h s).continuousAt.eventually_lt continuousAt_const hTe
  have hspeedcont : Continuous (fun e : ℝ => compactSpeed h r (interiorT78 h s e)) := by
    unfold compactSpeed interiorT78
    fun_prop
  have he3 : ∀ᶠ e in 𝓝 (1:ℝ), 0<compactSpeed h r (interiorT78 h s e) :=
    eventually_pos_of_continuousAt hspeedcont.continuousAt (by
      simpa [interiorT78] using h5)
  have hfac : Continuous (fun e : ℝ => 1-h^2*(interiorT78 h s e+t0)) := by
    unfold interiorT78
    fun_prop
  have he4 : ∀ᶠ e in 𝓝 (1:ℝ), 0<1-h^2*(interiorT78 h s e+t0) :=
    eventually_pos_of_continuousAt hfac.continuousAt (by
      simp only [interiorT78, sub_self, mul_zero, zero_mul, zero_div, add_zero]
      linarith)
  have he5 : ∀ᶠ e in 𝓝 (1:ℝ), 0<e :=
    eventually_pos_of_continuousAt continuousAt_id (by norm_num)
  have hev := (((he1.and he2).and he3).and he4).and he5
  obtain ⟨e₀, he₀, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (eventually_nhdsWithin_of_eventually_nhds (s := Set.Iio (1:ℝ)) hev)
  refine ⟨h, hh0, e₀, he₀, fun e he => ?_⟩
  obtain ⟨⟨⟨⟨hNe', hTe'⟩, hsp⟩, hf⟩, hepos⟩ := hsub he
  have hJ := interiorT78_source hhne s e
  have he_lt : e<1 := he.2
  have htt : 0< interiorT78 h s e-t0 := by
    simp only [interiorT78, ←ht0def, add_sub_cancel_left]
    have : 0<3*(1-e)*Z := by
      have : 0<1-e := by linarith
      positivity
    exact div_pos this hh0
  refine ⟨?_, ?_, hJ, hNe', hTe', interiorSlope78_physical hhne s e⟩
  · rw [hJ]
    have hk : (5:ℝ)/4<h⁻¹ := by
      rw [lt_inv_comm₀ (by norm_num) hh0]
      linarith
    have heZ0 : 0<e*Z := mul_pos hepos hZ0
    have heZ3 : e*Z<1/3 := by
      have : e*Z<Z := by nlinarith
      linarith
    have hr2 : h⁻¹^2*(9-(9-r*h^2))=r := by field_simp; ring
    refine ⟨by simpa [interiorV78] using hv0, ?_, hk, heZ0, heZ3, by rw [hr2]; exact hrS, ?_⟩
    · have : 0<r*h^2 := mul_pos hr0 (pow_pos hh0 2)
      linarith
    · rw [←hJ, strictCoarseCone_speed_eq hhne r]
      exact hsp
  · have hE := interior_error_factor h s (interiorT78 h s e)
    rw [←ht0def] at hE
    have : 0<(interiorT78 h s e-t0)*(1-h^2*(interiorT78 h s e+t0)) := mul_pos htt hf
    linarith

end
end HTGeometry.ThetaRatioInfinity
