import GaloisForLFunctions.RHTower.GaussQuasiInnerBlocks

/-!
# The reflection operator on the circle

Equation (1) of the source reduction of `gauss-component-quasi-inner-residue-hierarchy` factors the
paired block as `C = B D I B`, where `I` is the reflection `e_n ↦ e_{-n}`.  The corpus already owns
`B`, `B^{-2}`, `D` and `D*`; this file supplies `I` and the two conjugation identities that turn
`C²` into `G`.

The reflection is composition with `x ↦ -x`, which preserves Haar measure on the circle, so it is
an isometry of `L²`; on the Fourier basis it is exactly `e_n ↦ e_{-n}`.
-/

namespace RHTower

open MeasureTheory

noncomputable section

theorem fourier_neg_arg {T : ℝ} (n : ℤ) (x : AddCircle T) :
    fourier n (-x) = fourier (-n) x := by
  rw [fourier_apply, fourier_apply, smul_neg, neg_smul]

/-- Negation preserves Haar measure on the circle. -/
theorem measurePreserving_neg_circle :
    MeasureTheory.MeasurePreserving (Neg.neg : AddCircle (1 : ℝ) → AddCircle (1 : ℝ))
      (AddCircle.haarAddCircle (T := (1 : ℝ))) (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  Measure.measurePreserving_neg _

/-- The reflection `x ↦ -x` on `L²` of the circle. -/
def circleReflectionCLM :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  LinearMap.mkContinuous
    (MeasureTheory.Lp.compMeasurePreservingₗ (E := ℂ) (p := 2) ℂ
      (Neg.neg : AddCircle (1 : ℝ) → AddCircle (1 : ℝ))
      measurePreserving_neg_circle) 1
    (fun f => by
      rw [one_mul]
      exact le_of_eq (Lp.norm_compMeasurePreserving f measurePreserving_neg_circle))

theorem circleReflectionCLM_coeFn (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (circleReflectionCLM f : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] fun x => (f : AddCircle (1 : ℝ) → ℂ) (-x) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_neg_circle

set_option maxHeartbeats 1000000 in
/-- The reflection is an involution. -/
theorem circleReflectionCLM_apply_self
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    circleReflectionCLM (circleReflectionCLM f) = f := by
  refine Lp.ext ?_
  have h1 := circleReflectionCLM_coeFn (circleReflectionCLM f)
  have h2 := circleReflectionCLM_coeFn f
  have h3 : (fun x : AddCircle (1 : ℝ) =>
      (circleReflectionCLM f : AddCircle (1 : ℝ) → ℂ) (-x))
      =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
        fun x : AddCircle (1 : ℝ) => (f : AddCircle (1 : ℝ) → ℂ) (- -x) :=
    measurePreserving_neg_circle.quasiMeasurePreserving.ae
      (p := fun y : AddCircle (1 : ℝ) =>
        (circleReflectionCLM f : AddCircle (1 : ℝ) → ℂ) y = (f : AddCircle (1 : ℝ) → ℂ) (-y)) h2
  have h4 : (fun x : AddCircle (1 : ℝ) => (f : AddCircle (1 : ℝ) → ℂ) (- -x))
      =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] (f : AddCircle (1 : ℝ) → ℂ) := by
    filter_upwards with x
    rw [neg_neg]
  exact h1.trans (h3.trans h4)

set_option maxHeartbeats 1000000 in
theorem circleReflectionCLM_comp_self :
    circleReflectionCLM ∘L circleReflectionCLM
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :=
  ContinuousLinearMap.ext fun f => by
    simpa using circleReflectionCLM_apply_self f

set_option maxHeartbeats 1000000 in
theorem circleReflectionCLM_fourierLp (n : ℤ) :
    circleReflectionCLM (fourierLp 2 n) = fourierLp 2 (-n) := by
  refine Lp.ext ?_
  have h1 := circleReflectionCLM_coeFn (fourierLp 2 n)
  have h2 := coeFn_fourierLp (T := (1 : ℝ)) 2 n
  have h3 := coeFn_fourierLp (T := (1 : ℝ)) 2 (-n)
  have h4 : (fun x : AddCircle (1 : ℝ) => (fourierLp 2 n : AddCircle (1 : ℝ) → ℂ) (-x))
      =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
        fun x : AddCircle (1 : ℝ) => (fourier n : AddCircle (1 : ℝ) → ℂ) (-x) :=
    measurePreserving_neg_circle.quasiMeasurePreserving.ae
      (p := fun y : AddCircle (1 : ℝ) =>
        (fourierLp 2 n : AddCircle (1 : ℝ) → ℂ) y = (fourier n : AddCircle (1 : ℝ) → ℂ) y) h2
  have h5 : (fun x : AddCircle (1 : ℝ) => (fourier n : AddCircle (1 : ℝ) → ℂ) (-x))
      =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
        (fourier (-n) : AddCircle (1 : ℝ) → ℂ) := by
    filter_upwards with x
    exact fourier_neg_arg n x
  exact h1.trans (h4.trans (h5.trans h3.symm))


theorem dense_span_fourierBasis :
    Dense ((Submodule.span ℂ (Set.range (fourierBasis (T := (1 : ℝ)))))
      : Set (Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
    (fourierBasis (T := (1 : ℝ))).dense_span]
  rfl

/-- **`I D I = D*`**: the reflection conjugates the diagonal block into its adjoint symbol. -/
theorem circleReflection_gaussDiagonalBlock_conj {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) :
    circleReflectionCLM ∘L gaussDiagonalBlock hm k p ∘L circleReflectionCLM
      = gaussDiagonalBlockStar hm k p := by
  apply ContinuousLinearMap.ext_on dense_span_fourierBasis
  rintro _ ⟨j, rfl⟩
  rw [coe_fourierBasis]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [circleReflectionCLM_fourierLp, gaussDiagonalBlock_fourierLp, map_smul,
    circleReflectionCLM_fourierLp, neg_neg, gaussDiagonalBlockStar_fourierLp,
    gaussSampleValue_neg]

end

end RHTower
