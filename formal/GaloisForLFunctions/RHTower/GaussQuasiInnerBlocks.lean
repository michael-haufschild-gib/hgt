import GaloisForLFunctions.RHTower.GaussDiagonalBlock
import GaloisForLFunctions.RHTower.GaussPrimeScaleOperator

/-!
# The quasi-inner block `G`

Equation (1) of the source reduction writes the square of the paired block without any reflection:

`G = C² = p · B D B^{-2} D* B`.

All four factors are already available: `B` is multiplication by the prime-scale amplitude, `D` is
the Fourier multiplier with symbol the sampled Gauss component, `D*` is the multiplier with the
conjugate symbol, and `B^{-2}` is multiplication by `b_p^{-2} = p^{x-1}`, whose values lie in
`[1/p, 1]`.

This module builds `B^{-2}` and `D*` and assembles `G`.
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-! ## The reciprocal square of the prime scale -/

/-- The reciprocal square `b_p(x)^{-2} = p^{x-1}` of the prime-scale amplitude. -/
def gaussPrimeScaleInvSq (p : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-((1 - x) * Real.log p))

theorem gaussPrimeScaleInvSq_pos (p x : ℝ) : 0 < gaussPrimeScaleInvSq p x := Real.exp_pos _

/-- The reciprocal square really is the reciprocal of the square. -/
theorem gaussPrimeScaleInvSq_mul_sq (p x : ℝ) :
    gaussPrimeScaleInvSq p x * gaussPrimeScale p x ^ (2 : ℕ) = 1 := by
  rw [gaussPrimeScaleInvSq, gaussPrimeScale, ← Real.exp_nat_mul, ← Real.exp_add]
  norm_num
  ring

theorem continuous_gaussPrimeScaleInvSq (p : ℝ) : Continuous (gaussPrimeScaleInvSq p) := by
  unfold gaussPrimeScaleInvSq
  fun_prop

/-- The reciprocal square as a function on the circle. -/
def gaussPrimeScaleInvSqCircle (p : ℝ) : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 (fun x => (gaussPrimeScaleInvSq p x : ℂ))

theorem measurable_gaussPrimeScaleInvSqCircle (p : ℝ) :
    Measurable (gaussPrimeScaleInvSqCircle p) := by
  rw [gaussPrimeScaleInvSqCircle, AddCircle.liftIoc]
  refine Measurable.comp ?_ (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable
  exact ((Complex.measurable_ofReal.comp
    (continuous_gaussPrimeScaleInvSq p).measurable).comp measurable_subtype_coe)

theorem gaussPrimeScaleInvSq_le_one {p : ℝ} (hp : 1 < p) {x : ℝ} (hx : x ≤ 1) :
    gaussPrimeScaleInvSq p x ≤ 1 := by
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hnn : 0 ≤ (1 - x) * Real.log p := mul_nonneg (by linarith) hlog.le
  rw [gaussPrimeScaleInvSq]
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem norm_gaussPrimeScaleInvSqCircle_le {p : ℝ} (hp : 1 < p) (z : AddCircle (1 : ℝ)) :
    ‖gaussPrimeScaleInvSqCircle p z‖ ≤ 1 := by
  have hmem := (AddCircle.equivIoc (1 : ℝ) 0 z).2
  have hval : gaussPrimeScaleInvSqCircle p z =
      ((gaussPrimeScaleInvSq p
        ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) : ℝ) : ℂ) := rfl
  rw [hval, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (gaussPrimeScaleInvSq_pos p _)]
  refine gaussPrimeScaleInvSq_le_one hp ?_
  simpa using hmem.2

/-- The block `B^{-2}`: multiplication by the reciprocal square of the prime-scale amplitude. -/
def gaussPrimeScaleInvSqBlock {p : ℝ} (hp : 1 < p) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  MeasureTheory.lpBoundedMulCLM (measurable_gaussPrimeScaleInvSqCircle p)
    zero_le_one (norm_gaussPrimeScaleInvSqCircle_le hp)

theorem norm_gaussPrimeScaleInvSqBlock_le {p : ℝ} (hp : 1 < p) :
    ‖gaussPrimeScaleInvSqBlock hp‖ ≤ 1 :=
  MeasureTheory.norm_lpBoundedMulCLM_le _ _ _

/-! ## The conjugate diagonal block -/

theorem norm_conj_gaussSampleValue_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (i : ℤ) :
    ‖starRingEnd ℂ (gaussSampleValue k p i)‖ ≤ gaussSampleValueBound hm k p := by
  rw [Complex.norm_conj]
  exact norm_gaussSampleValue_le hm k p i

/-- The conjugate diagonal block `D*`. -/
def gaussDiagonalBlockStar {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  conjugateOperator (fourierBasis (T := (1 : ℝ))).repr.toContinuousLinearEquiv
    (GaloisForLFunctions.lpDiagonalCLM
      (fun i : ℤ => starRingEnd ℂ (gaussSampleValue k p i))
      (gaussSampleValueBound_nonneg hm k p) (norm_conj_gaussSampleValue_le hm k p))

/-- The exponential monomials are eigenvectors of the conjugate diagonal block. -/
theorem gaussDiagonalBlockStar_fourierLp {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (j : ℤ) :
    gaussDiagonalBlockStar hm k p (fourierLp 2 j)
      = starRingEnd ℂ (gaussSampleValue k p j) • fourierLp 2 j := by
  have hbasis : (fourierLp 2 j : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
      = (fourierBasis (T := (1 : ℝ))) j := by
    rw [coe_fourierBasis]
  have hsingle : lp.single (E := fun _ : ℤ => ℂ) 2 j
        (starRingEnd ℂ (gaussSampleValue k p j))
      = starRingEnd ℂ (gaussSampleValue k p j) •
        lp.single (E := fun _ : ℤ => ℂ) 2 j (1 : ℂ) := by
    rw [← lp.single_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  rw [hbasis, gaussDiagonalBlockStar, conjugateOperator]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [HilbertBasis.repr_self, GaloisForLFunctions.lpDiagonalCLM_single, hsingle, map_smul]
  congr 1
  simp

/-! ## The quasi-inner block -/

/-- The quasi-inner block `G = p · B D B^{-2} D* B` of equation (1). -/
def gaussQuasiInnerG {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ((p : ℝ) : ℂ) •
    (gaussPrimeScaleBlock (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt) ∘L
      gaussDiagonalBlock hm k p ∘L
        gaussPrimeScaleInvSqBlock (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt) ∘L
          gaussDiagonalBlockStar hm k p ∘L
            gaussPrimeScaleBlock (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt))

end

end RHTower
