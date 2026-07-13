import GaloisForLFunctions.HTGeometry.SchwartzCompactDiagonalFunctional
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Positivity of the compact diagonal functional on smooth tests

Every nonnegative compactly supported real smooth test is a Schwartz-topology limit of explicit
smooth modulus squares, after adding a vanishing canonical-cutoff error.  Consequently positivity
of a momentum-symmetric Schwartz form makes its stabilized local diagonal functional positive on
the full cone of nonnegative compactly supported smooth tests.
-/

open Complex Function Filter Set
open scoped SchwartzMap FourierTransform Topology Polynomial ContDiff

noncomputable section

namespace SchwartzMap

/-- Complexification of a real Schwartz function. -/
def realToComplexSchwartz (h : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℂ :=
  h.postcompCLM Complex.ofRealCLM

@[simp] theorem realToComplexSchwartz_apply (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    realToComplexSchwartz h t = (h t : ℂ) := rfl

/-- Compactly supported smooth square-root regularization of a nonnegative real Schwartz map. -/
def nonnegativeSquareRootRegularization
    (h : SchwartzMap ℝ ℝ) (hnonneg : ∀ t, 0 ≤ h t)
    (R ε : ℝ) (hε : 0 < ε) : SchwartzMap ℝ ℂ := by
  let χ : SchwartzMap ℝ ℂ := compactIntervalCutoff R
  let F : ℝ → ℂ := fun t => χ t * (Real.sqrt (h t + ε) : ℂ)
  have hcompact : HasCompactSupport F := by
    exact (compactIntervalCutoff_hasCompactSupport R).mul_right
  have hsqrt : ContDiff ℝ ∞ (fun t => Real.sqrt (h t + ε)) := by
    apply ((h.smooth ⊤).add contDiff_const).sqrt
    intro t
    linarith [hnonneg t]
  have hsmooth : ContDiff ℝ ∞ F := by
    exact (χ.smooth ⊤).mul (Complex.ofRealCLM.contDiff.comp hsqrt)
  exact hcompact.toSchwartzMap hsmooth

@[simp] theorem nonnegativeSquareRootRegularization_apply
    (h : SchwartzMap ℝ ℝ) (hnonneg : ∀ t, 0 ≤ h t)
    (R ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    nonnegativeSquareRootRegularization h hnonneg R ε hε t =
      compactIntervalCutoff R t * (Real.sqrt (h t + ε) : ℂ) := rfl

/-- The regularized square is the original nonnegative test plus an explicit vanishing cutoff
error. -/
theorem pointwiseMulConj_nonnegativeSquareRootRegularization_self
    (h : SchwartzMap ℝ ℝ) (hnonneg : ∀ t, 0 ≤ h t)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hh : tsupport h ⊆ {t : ℝ | |t| ≤ R}) :
    pointwiseMulConj
        (nonnegativeSquareRootRegularization h hnonneg R ε hε)
        (nonnegativeSquareRootRegularization h hnonneg R ε hε) =
      realToComplexSchwartz h +
        ε • pointwiseMulConj (compactIntervalCutoff R) (compactIntervalCutoff R) := by
  ext t
  rw [pointwiseMulConj_apply, nonnegativeSquareRootRegularization_apply]
  change compactIntervalCutoff R t * (Real.sqrt (h t + ε) : ℂ) *
      (starRingEnd ℂ)
        (compactIntervalCutoff R t * (Real.sqrt (h t + ε) : ℂ)) =
    (h t : ℂ) + (ε : ℂ) *
      (compactIntervalCutoff R t *
        (starRingEnd ℂ) (compactIntervalCutoff R t))
  by_cases ht : t ∈ tsupport h
  · have hχ : compactIntervalCutoff R t = 1 := by
      apply compactIntervalCutoff_apply_of_abs_le
      simpa [abs_of_nonneg hR] using hh ht
    rw [hχ]
    have hsqrt : Real.sqrt (h t + ε) ^ 2 = h t + ε :=
      Real.sq_sqrt (by linarith [hnonneg t])
    simp only [one_mul, Complex.conj_ofReal, map_one]
    norm_cast
    simpa [pow_two] using hsqrt
  · have hzero : h t = 0 := image_eq_zero_of_notMem_tsupport ht
    rw [hzero]
    have hsqrt : Real.sqrt (0 + ε) ^ 2 = 0 + ε :=
      Real.sq_sqrt (by linarith)
    simp only [zero_add] at hsqrt ⊢
    simp only [map_mul, Complex.conj_ofReal, ofReal_zero]
    have hsqrtC : (Real.sqrt ε : ℂ) ^ 2 = (ε : ℂ) := by
      exact_mod_cast (by simpa using hsqrt)
    calc
      compactIntervalCutoff R t * (Real.sqrt ε : ℂ) *
          ((starRingEnd ℂ) (compactIntervalCutoff R t) * (Real.sqrt ε : ℂ)) =
          (Real.sqrt ε : ℂ) ^ 2 *
            (compactIntervalCutoff R t *
              (starRingEnd ℂ) (compactIntervalCutoff R t)) := by ring
      _ = _ := by rw [hsqrtC]; simp

/-- Every square-root regularization is supported inside the canonical cutoff. -/
theorem nonnegativeSquareRootRegularization_tsupport_subset
    (h : SchwartzMap ℝ ℝ) (hnonneg : ∀ t, 0 ≤ h t)
    (R ε : ℝ) (hε : 0 < ε) :
    tsupport (nonnegativeSquareRootRegularization h hnonneg R ε hε) ⊆
      {t : ℝ | |t| ≤ |R| + 2} := by
  rw [← compactIntervalCutoff_tsupport R]
  exact tsupport_mul_subset_left (f := compactIntervalCutoff R)
    (g := fun t : ℝ => (Real.sqrt (h t + ε) : ℂ))

/-- The canonical local diagonal functional is positive on every nonnegative compactly supported
real smooth test, not only on explicit modulus squares. -/
theorem ContinuousSchwartzSesquilinearForm.compactIntervalDiagonalFunctional_nonnegative_real
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (h : SchwartzMap ℝ ℝ)
    (hnonneg : ∀ t, 0 ≤ h t) {R : ℝ} (hR : 0 ≤ R)
    (hh : tsupport h ⊆ {t : ℝ | |t| ≤ R}) :
    0 ≤ (Q.compactIntervalDiagonalFunctional (R + 2) (realToComplexSchwartz h)).re ∧
      (Q.compactIntervalDiagonalFunctional (R + 2) (realToComplexSchwartz h)).im = 0 := by
  let χ2 : SchwartzMap ℝ ℂ :=
    pointwiseMulConj (compactIntervalCutoff R) (compactIntervalCutoff R)
  let A : ℂ := Q.compactIntervalDiagonalFunctional (R + 2) (realToComplexSchwartz h)
  let B : ℂ := Q.compactIntervalDiagonalFunctional (R + 2) χ2
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hsquare (n : ℕ) :
      pointwiseMulConj
          (nonnegativeSquareRootRegularization h hnonneg R (ε n) (hεpos n))
          (nonnegativeSquareRootRegularization h hnonneg R (ε n) (hεpos n)) =
        realToComplexSchwartz h + (ε n) • χ2 := by
    simpa only [χ2] using
      pointwiseMulConj_nonnegativeSquareRootRegularization_self
        h hnonneg hR (hεpos n) hh
  have hfsupp (n : ℕ) :
      tsupport (nonnegativeSquareRootRegularization h hnonneg R (ε n) (hεpos n)) ⊆
        {t : ℝ | |t| ≤ R + 2} := by
    have hs := nonnegativeSquareRootRegularization_tsupport_subset
      h hnonneg R (ε n) (hεpos n)
    simpa [abs_of_nonneg hR] using hs
  have hpositive (n : ℕ) :
      0 ≤ (A + (ε n : ℂ) * B).re ∧ (A + (ε n : ℂ) * B).im = 0 := by
    have hs := Q.compactIntervalDiagonalFunctional_square_nonnegative hQ hQnonneg
      (nonnegativeSquareRootRegularization h hnonneg R (ε n) (hεpos n))
      (show 0 ≤ R + 2 by linarith) (hfsupp n)
    rw [hsquare n, map_add] at hs
    have hsmul :
        Q.compactIntervalDiagonalFunctional (R + 2) ((ε n) • χ2) =
          (ε n : ℂ) * Q.compactIntervalDiagonalFunctional (R + 2) χ2 := by
      change Q.compactIntervalDiagonalFunctional (R + 2) ((ε n : ℂ) • χ2) = _
      rw [map_smul]
      rfl
    rw [hsmul] at hs
    simpa only [A, B, χ2] using hs
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have hεcomplex : Tendsto (fun n => (ε n : ℂ)) atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hεzero
  have hcomplex : Tendsto (fun n => A + (ε n : ℂ) * B) atTop (𝓝 A) := by
    simpa using tendsto_const_nhds.add (hεcomplex.mul tendsto_const_nhds)
  constructor
  · exact ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp hcomplex)
      (fun n => (hpositive n).1)
  · have him := Complex.continuous_im.continuousAt.tendsto.comp hcomplex
    have him' : Tendsto (fun n => (A + (ε n : ℂ) * B).im) atTop (𝓝 A.im) := by
      simpa only [Function.comp_apply] using him
    have hzero : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have heq : (fun n => (A + (ε n : ℂ) * B).im) = fun _n : ℕ => (0 : ℝ) := by
      funext n
      exact (hpositive n).2
    rw [heq] at him'
    change A.im = 0
    exact tendsto_nhds_unique him' hzero

end SchwartzMap

