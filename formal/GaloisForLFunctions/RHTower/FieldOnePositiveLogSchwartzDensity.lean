import GaloisForLFunctions.RHTower.FieldOnePositiveUnitsLogHaar
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Positive real Schwartz lifts of compact-smooth logarithmic functions

For a compactly supported smooth function `h` on the logarithmic line, the formula

`f(x) = x⁻¹ᐟ² h(log x)` for `x > 0`, and `f(x) = 0` for `x ≤ 0`,

is a Schwartz function on the real additive factor.  Compact support of `h` makes the extension
identically zero near the origin, so this is a genuine global smooth function, not a one-sided
regularity assertion.  Its Connes--Marcolli half-density is exactly `h` in logarithmic coordinates.
-/

open scoped ContDiff ENNReal Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function MeasureTheory Set TopologicalSpace

/-- Compactly supported smooth complex functions on the full logarithmic real line. -/
abbrev FieldOneCompactSmoothLog :=
  TestFunction (⊤ : Opens ℝ) ℂ ⊤

/-- Positive-half-line additive function corresponding to a logarithmic test function after
removing the module half-density. -/
def fieldOnePositiveLogSchwartzRaw
    (h : FieldOneCompactSmoothLog) (x : ℝ) : ℂ :=
  if 0 < x then
    (Real.exp (-Real.log x / 2) : ℂ) * h (Real.log x)
  else 0

theorem fieldOnePositiveLogSchwartzRaw_contDiff
    (h : FieldOneCompactSmoothLog) :
    ContDiff ℝ ∞ (fieldOnePositiveLogSchwartzRaw h) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.2 hx.ne'
    have hformula : ContDiffAt ℝ ∞
        (fun y : ℝ =>
          (Real.exp (-Real.log y / 2) : ℂ) * h (Real.log y)) x := by
      have hweight : ContDiffAt ℝ ∞
          (fun y : ℝ => (Real.exp (-Real.log y / 2) : ℂ)) x := by
        have hreal : ContDiffAt ℝ ∞
            (fun y : ℝ => Real.exp (-Real.log y / 2)) x :=
          (hlog.neg.div_const 2).exp
        exact Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
      exact hweight.mul (h.contDiff.contDiffAt.comp x hlog)
    apply hformula.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    change 0 < y at hy
    simp only [fieldOnePositiveLogSchwartzRaw, if_pos hy]
  · rcases h.hasCompactSupport.bddBelow with ⟨L, hL⟩
    have hxexp : x < Real.exp L :=
      lt_of_le_of_lt (le_of_not_gt hx) (Real.exp_pos L)
    have hconst : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) x :=
      contDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxexp] with y hy
    by_cases hypos : 0 < y
    · have hloglt : Real.log y < L := by
        have := Real.strictMonoOn_log hypos (Real.exp_pos L) hy
        simpa using this
      have hzero : h (Real.log y) = 0 := by
        rw [← notMem_support]
        intro hsupp
        exact (not_lt_of_ge
          (hL ((subset_tsupport (h : ℝ → ℂ)) hsupp))) hloglt
      simp [fieldOnePositiveLogSchwartzRaw, hypos, hzero]
    · simp [fieldOnePositiveLogSchwartzRaw, hypos]

theorem fieldOnePositiveLogSchwartzRaw_hasCompactSupport
    (h : FieldOneCompactSmoothLog) :
    HasCompactSupport (fieldOnePositiveLogSchwartzRaw h) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (h.hasCompactSupport.image Real.continuous_exp)
  intro x hx
  have hxpos : 0 < x := by
    by_contra hnot
    exact hx (by simp [fieldOnePositiveLogSchwartzRaw, hnot])
  have hproduct :
      (Real.exp (-Real.log x / 2) : ℂ) * h (Real.log x) ≠ 0 := by
    simpa [fieldOnePositiveLogSchwartzRaw, hxpos] using hx
  refine ⟨Real.log x,
    (subset_tsupport (h : ℝ → ℂ)) (mul_ne_zero_iff.mp hproduct).2, ?_⟩
  exact Real.exp_log hxpos

/-- The exact positive real Schwartz lift of a logarithmic test function. -/
def fieldOnePositiveLogTestToSchwartz :
    FieldOneCompactSmoothLog →ₗ[ℂ] SchwartzMap ℝ ℂ where
  toFun h := HasCompactSupport.toSchwartzMap
    (fieldOnePositiveLogSchwartzRaw_hasCompactSupport h)
    (fieldOnePositiveLogSchwartzRaw_contDiff h)
  map_add' h g := by
    ext x
    by_cases hx : 0 < x <;>
      simp [fieldOnePositiveLogSchwartzRaw, hx]
    ring
  map_smul' c h := by
    ext x
    by_cases hx : 0 < x <;>
      simp [fieldOnePositiveLogSchwartzRaw, hx]
    ring

@[simp]
theorem fieldOnePositiveLogTestToSchwartz_apply
    (h : FieldOneCompactSmoothLog) (x : ℝ) :
    fieldOnePositiveLogTestToSchwartz h x =
      fieldOnePositiveLogSchwartzRaw h x :=
  rfl

/-- Exact half-density cancellation in logarithmic coordinates. -/
theorem fieldOnePositiveLogTestToSchwartz_halfDensity_exp
    (h : FieldOneCompactSmoothLog) (t : ℝ) :
    (Real.exp (t / 2) : ℂ) *
        fieldOnePositiveLogTestToSchwartz h (Real.exp t) = h t := by
  rw [fieldOnePositiveLogTestToSchwartz_apply]
  simp only [fieldOnePositiveLogSchwartzRaw, Real.exp_pos, ↓reduceIte,
    Real.log_exp]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  ring_nf
  simp

/-- Logarithmic test functions as a linear subspace of Lebesgue `L²`. -/
def fieldOneCompactSmoothLogToL2 :
    FieldOneCompactSmoothLog →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) where
  toFun h :=
    (h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport).toLp h
  map_add' h g := by
    apply Lp.ext
    filter_upwards [
      (h + g).continuous.memLp_of_hasCompactSupport
        (h + g).hasCompactSupport |>.coeFn_toLp,
      h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport |>.coeFn_toLp,
      g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport |>.coeFn_toLp,
      Lp.coeFn_add
        ((h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport).toLp h)
        ((g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport).toLp g)]
      with x hsum hh hg hadd
    rw [hsum, hadd]
    change h x + g x =
      ((h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport).toLp h) x +
        ((g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport).toLp g) x
    rw [hh, hg]
  map_smul' c h := by
    apply Lp.ext
    filter_upwards [
      (c • h).continuous.memLp_of_hasCompactSupport
        (c • h).hasCompactSupport |>.coeFn_toLp,
      h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport |>.coeFn_toLp,
      Lp.coeFn_smul c
        ((h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport).toLp h)]
      with x hsmul hh hLp
    rw [hsmul]
    change c • h x =
      (c • ((h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport).toLp h)) x
    rw [hLp]
    change c • h x = c •
      ((h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport).toLp h) x
    rw [hh]

theorem fieldOneCompactSmoothLogToL2_ae
    (h : FieldOneCompactSmoothLog) :
    fieldOneCompactSmoothLogToL2 h =ᵐ[(volume : Measure ℝ)] h :=
  (h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport).coeFn_toLp

/-- Compact-smooth logarithmic functions are dense in Lebesgue `L²`. -/
theorem fieldOneCompactSmoothLogToL2_denseRange :
    DenseRange fieldOneCompactSmoothLogToL2 := by
  have hdense := Lp.dense_hasCompactSupport_contDiff
    (F := ℂ) (μ := (volume : Measure ℝ)) (p := 2) (by norm_num)
  apply hdense.mono
  intro f hf
  rcases hf with ⟨g, hfg, hgcompact, hgsmooth⟩
  let h : FieldOneCompactSmoothLog :=
    ⟨g, hgsmooth, hgcompact, subset_univ _⟩
  refine ⟨h, ?_⟩
  apply Lp.ext
  filter_upwards [fieldOneCompactSmoothLogToL2_ae h, hfg] with x hh hfx
  exact hh.trans hfx.symm

end

end GaloisForLFunctions.RHTower
