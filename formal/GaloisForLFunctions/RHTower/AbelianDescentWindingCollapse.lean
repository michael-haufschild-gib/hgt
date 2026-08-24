/-
# Abelian descent winding collapse

Finite stack descent through scalar multiplication is detected by boundary winding. A periodic
factor contributes the same winding on every window, hence the total differs from the remainder
by a multiple of the stack size. A zero-free analytic remainder contributes zero. Matrix-valued
factorizations collapse to the same scalar statement through the determinant.
-/
import GaloisForLFunctions.RHTower.WindingFull
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section

namespace GaloisForLFunctions.RHTower.AbelianDescentWindingCollapse

open Complex

def stackWinding {N : ℕ} (F : Fin N → ℝ → ℂ) (a b : ℝ) : ℤ :=
  ∑ j, RHTower.windingNumber (F j) a b

/-- If a nonvanishing product loop factors into continuous closed factors, both factors are
nonvanishing loops. Thus factor-loop hypotheses need not be assumed separately. -/
theorem isLoop_factors_of_product
    {F P R : ℝ → ℂ} {a b : ℝ}
    (hF : RHTower.IsLoop F a b) (hPcontinuous : Continuous P)
    (hRcontinuous : Continuous R) (hPclosed : P a = P b)
    (hRclosed : R a = R b) (hfactor : ∀ t, F t = P t * R t) :
    RHTower.IsLoop P a b ∧ RHTower.IsLoop R a b := by
  refine ⟨⟨hPcontinuous, ?_, hPclosed⟩, ⟨hRcontinuous, ?_, hRclosed⟩⟩
  · intro t hzero
    exact hF.nonzero t (by rw [hfactor t, hzero, zero_mul])
  · intro t hzero
    exact hF.nonzero t (by rw [hfactor t, hzero, mul_zero])

theorem stackWinding_factorization {N : ℕ} [NeZero N]
    (F P R : Fin N → ℝ → ℂ) (a b : ℝ)
    (hP : ∀ j, RHTower.IsLoop (P j) a b)
    (hR : ∀ j, RHTower.IsLoop (R j) a b)
    (hfactor : ∀ j t, F j t = P j t * R j t)
    (hperiodic : ∀ j, P j = P 0) :
    stackWinding F a b =
      (N : ℤ) * RHTower.windingNumber (P 0) a b + stackWinding R a b := by
  classical
  unfold stackWinding
  calc
    ∑ j, RHTower.windingNumber (F j) a b =
        ∑ j, (RHTower.windingNumber (P j) a b +
          RHTower.windingNumber (R j) a b) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show F j = fun t => P j t * R j t by funext t; exact hfactor j t]
      exact RHTower.windingNumber_mul (hP j) (hR j)
    _ = (∑ j, RHTower.windingNumber (P j) a b) +
        ∑ j, RHTower.windingNumber (R j) a b := Finset.sum_add_distrib
    _ = (N : ℤ) * RHTower.windingNumber (P 0) a b +
        ∑ j, RHTower.windingNumber (R j) a b := by
      congr 1
      simp_rw [hperiodic]
      simp

theorem stackWinding_congr_of_factorization {N : ℕ} [NeZero N]
    (F P R : Fin N → ℝ → ℂ) (a b : ℝ)
    (hP : ∀ j, RHTower.IsLoop (P j) a b)
    (hR : ∀ j, RHTower.IsLoop (R j) a b)
    (hfactor : ∀ j t, F j t = P j t * R j t)
    (hperiodic : ∀ j, P j = P 0) :
    (N : ℤ) ∣ stackWinding F a b - stackWinding R a b := by
  rw [stackWinding_factorization F P R a b hP hR hfactor hperiodic]
  refine ⟨RHTower.windingNumber (P 0) a b, ?_⟩
  ring

/-- Exact paper hypotheses: boundary-zero-free product plus continuous closed factors already imply
the factor loops used by winding additivity. -/
theorem stackWinding_congr_of_productLoop {N : ℕ} [NeZero N]
    (F P R : Fin N → ℝ → ℂ) (a b : ℝ)
    (hF : ∀ j, RHTower.IsLoop (F j) a b)
    (hPcontinuous : ∀ j, Continuous (P j))
    (hRcontinuous : ∀ j, Continuous (R j))
    (hPclosed : ∀ j, P j a = P j b) (hRclosed : ∀ j, R j a = R j b)
    (hfactor : ∀ j t, F j t = P j t * R j t)
    (hperiodic : ∀ j, P j = P 0) :
    (N : ℤ) ∣ stackWinding F a b - stackWinding R a b := by
  have hfactors : ∀ j, RHTower.IsLoop (P j) a b ∧ RHTower.IsLoop (R j) a b :=
    fun j => isLoop_factors_of_product (hF j) (hPcontinuous j) (hRcontinuous j)
      (hPclosed j) (hRclosed j) (hfactor j)
  exact stackWinding_congr_of_factorization F P R a b
    (fun j => (hfactors j).1) (fun j => (hfactors j).2) hfactor hperiodic

theorem stackWinding_dvd_of_zeroRemainder {N : ℕ} [NeZero N]
    (F P R : Fin N → ℝ → ℂ) (a b : ℝ)
    (hP : ∀ j, RHTower.IsLoop (P j) a b)
    (hR : ∀ j, RHTower.IsLoop (R j) a b)
    (hfactor : ∀ j t, F j t = P j t * R j t)
    (hperiodic : ∀ j, P j = P 0)
    (hRzero : ∀ j, RHTower.windingNumber (R j) a b = 0) :
    (N : ℤ) ∣ stackWinding F a b := by
  have hstackR : stackWinding R a b = 0 := by
    unfold stackWinding
    simp [hRzero]
  simpa [hstackR] using
    stackWinding_congr_of_factorization F P R a b hP hR hfactor hperiodic

def circleBoundary (c : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  c + (r : ℂ) * Complex.exp (Complex.I * (t : ℂ))

theorem isLoop_comp_circleBoundary_of_nonvanishing_disc
    {g : ℂ → ℂ} {c : ℂ} {r R : ℝ}
    (hrR : r < R) (hr : 0 ≤ r)
    (hgc : ContinuousOn g (Metric.ball c R))
    (hg0 : ∀ z ∈ Metric.ball c R, g z ≠ 0) :
    RHTower.IsLoop (fun t => g (circleBoundary c r t)) 0 (2 * Real.pi) := by
  have hcirc : ∀ t, circleBoundary c r t ∈ Metric.ball c R := by
    intro t
    exact RHTower.circle_mem_ball hrR hr t
  refine ⟨hgc.comp_continuous (by unfold circleBoundary; fun_prop) hcirc,
    fun t => hg0 _ (hcirc t), ?_⟩
  congr 1
  unfold circleBoundary
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show Complex.I * (((2 : ℝ) * Real.pi : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_two_pi_mul_I]

theorem stackWinding_dvd_of_disc_zeroFreeRemainder {N : ℕ} [NeZero N]
    (F P : Fin N → ℝ → ℂ) (g : Fin N → ℂ → ℂ)
    (c : Fin N → ℂ) {r R : ℝ} (hrR : r < R) (hr : 0 ≤ r)
    (hP : ∀ j, RHTower.IsLoop (P j) 0 (2 * Real.pi))
    (hgc : ∀ j, ContinuousOn (g j) (Metric.ball (c j) R))
    (hg0 : ∀ j z, z ∈ Metric.ball (c j) R → g j z ≠ 0)
    (hfactor : ∀ j t,
      F j t = P j t * g j (circleBoundary (c j) r t))
    (hperiodic : ∀ j, P j = P 0) :
    (N : ℤ) ∣ stackWinding F 0 (2 * Real.pi) := by
  let Rem : Fin N → ℝ → ℂ := fun j t => g j (circleBoundary (c j) r t)
  have hR : ∀ j, RHTower.IsLoop (Rem j) 0 (2 * Real.pi) := fun j =>
    isLoop_comp_circleBoundary_of_nonvanishing_disc hrR hr (hgc j) (hg0 j)
  have hRzero : ∀ j, RHTower.windingNumber (Rem j) 0 (2 * Real.pi) = 0 := fun j =>
    RHTower.windingNumber_nonvanishing_disc hrR hr (hgc j) (hg0 j)
  exact stackWinding_dvd_of_zeroRemainder F P Rem 0 (2 * Real.pi)
    hP hR hfactor hperiodic hRzero

def matrixStackWinding {N d : ℕ}
    (F : Fin N → ℝ → Matrix (Fin d) (Fin d) ℂ) (a b : ℝ) : ℤ :=
  stackWinding (fun j t => Matrix.det (F j t)) a b

theorem matrixStackWinding_congr_of_factorization {N d : ℕ} [NeZero N]
    (F P R : Fin N → ℝ → Matrix (Fin d) (Fin d) ℂ) (a b : ℝ)
    (hP : ∀ j, RHTower.IsLoop (fun t => Matrix.det (P j t)) a b)
    (hR : ∀ j, RHTower.IsLoop (fun t => Matrix.det (R j t)) a b)
    (hfactor : ∀ j t, F j t = P j t * R j t)
    (hperiodic : ∀ j, P j = P 0) :
    (N : ℤ) ∣ matrixStackWinding F a b - matrixStackWinding R a b := by
  unfold matrixStackWinding
  apply stackWinding_congr_of_factorization
      (fun j t => Matrix.det (F j t))
      (fun j t => Matrix.det (P j t))
      (fun j t => Matrix.det (R j t)) a b hP hR
  · intro j t
    rw [hfactor, Matrix.det_mul]
  · intro j
    funext t
    rw [hperiodic]

theorem matrixStackWinding_dvd_of_zeroRemainder {N d : ℕ} [NeZero N]
    (F P R : Fin N → ℝ → Matrix (Fin d) (Fin d) ℂ) (a b : ℝ)
    (hP : ∀ j, RHTower.IsLoop (fun t => Matrix.det (P j t)) a b)
    (hR : ∀ j, RHTower.IsLoop (fun t => Matrix.det (R j t)) a b)
    (hfactor : ∀ j t, F j t = P j t * R j t)
    (hperiodic : ∀ j, P j = P 0)
    (hRzero : ∀ j, RHTower.windingNumber (fun t => Matrix.det (R j t)) a b = 0) :
    (N : ℤ) ∣ matrixStackWinding F a b := by
  have hstackR : matrixStackWinding R a b = 0 := by
    unfold matrixStackWinding stackWinding
    simp [hRzero]
  have hcongr := matrixStackWinding_congr_of_factorization
    F P R a b hP hR hfactor hperiodic
  simpa [hstackR] using hcongr

/-- Closed conjunction capstone for scalar congruence, zero-free divisibility, and determinant
abelianization. -/
theorem abelianDescentWindingCollapse_unconditional :
    (∀ {N : ℕ} [NeZero N] (F P R : Fin N → ℝ → ℂ) (a b : ℝ),
      (∀ j, RHTower.IsLoop (P j) a b) →
      (∀ j, RHTower.IsLoop (R j) a b) →
      (∀ j t, F j t = P j t * R j t) →
      (∀ j, P j = P 0) →
      (N : ℤ) ∣ stackWinding F a b - stackWinding R a b) := by
  intro N _ F P R a b hP hR hfactor hperiodic
  exact stackWinding_congr_of_factorization F P R a b hP hR hfactor hperiodic

end GaloisForLFunctions.RHTower.AbelianDescentWindingCollapse
