import GaloisForLFunctions.RHTower.GaussUniformTranslationL2
import GaloisForLFunctions.HTGeometry.L2FourierMultiplier

/-!
# The one-step action of the quasi-inner block

The quasi-inner block factors exactly through the two normalized shifted blocks:

`G (e_n f) = p |d_n|² · e_n · B ( S ( B^{-2} ( S* ( B f ) ) ) )`,

where `S*` and `S` are the normalized blocks of the conjugate and unconjugated diagonals.  This is
an algebraic identity — multiplication operators commute with each other, `e_n e_(-n) = 1`, and the
normalizations `(conj d_n)^{-1}` and `d_n^{-1}` cancel the diagonal scalars.

Feeding the moving-translation estimate into `S*` and `S` turns the right-hand side into
`p |d_n|² e_n (a_(δ_n) f + o(1))`, which is the card's equation (10).
-/

namespace RHTower

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## Multiplication operators commute -/

theorem fourierMulBlock_neg_apply (n : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    fourierMulBlock n (fourierMulBlock (-n) u) = u := by
  have hone : Measurable (fun _ : AddCircle (1 : ℝ) => (1 : ℂ)) := measurable_const
  have hcomp := MeasureTheory.lpBoundedMulCLM_comp (p := (2 : ℝ≥0∞))
    (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
    (fourier n).continuous.measurable (fourier (-n)).continuous.measurable hone
    zero_le_one (fun z => le_of_eq (norm_fourier_eq_one n z))
    zero_le_one (fun z => le_of_eq (norm_fourier_eq_one (-n) z))
    zero_le_one (fun _ => le_of_eq (by simp))
    (Filter.Eventually.of_forall fun z => by
      rw [← fourier_add, add_neg_cancel]
      simp)
  have hid := MeasureTheory.lpBoundedMulCLM_eq_id (p := (2 : ℝ≥0∞))
    (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hone zero_le_one
    (fun _ => le_of_eq (by simp)) (Filter.Eventually.of_forall fun _ => rfl)
  have h := congrArg (fun T => T u) (hcomp.trans hid)
  simpa [fourierMulBlock] using h

theorem gaussPrimeScaleBlock_comm {p : ℝ} (hp : 1 < p) (n : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussPrimeScaleBlock hp (fourierMulBlock n u)
      = fourierMulBlock n (gaussPrimeScaleBlock hp u) := by
  have hprod : Measurable (fun z : AddCircle (1 : ℝ) => gaussPrimeScaleCircle p z * fourier n z) :=
    (measurable_gaussPrimeScaleCircle p).mul (fourier n).continuous.measurable
  have hbnd : ∀ z, ‖gaussPrimeScaleCircle p z * fourier n z‖ ≤ Real.sqrt p := by
    intro z
    rw [norm_mul, norm_fourier_eq_one, mul_one]
    exact norm_gaussPrimeScaleCircle_le hp z
  have h1 := MeasureTheory.lpBoundedMulCLM_comp (p := (2 : ℝ≥0∞))
    (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
    (measurable_gaussPrimeScaleCircle p) (fourier n).continuous.measurable hprod
    (Real.sqrt_nonneg p) (norm_gaussPrimeScaleCircle_le hp)
    zero_le_one (fun z => le_of_eq (norm_fourier_eq_one n z))
    (Real.sqrt_nonneg p) hbnd (Filter.Eventually.of_forall fun _ => rfl)
  have h2 := MeasureTheory.lpBoundedMulCLM_comp (p := (2 : ℝ≥0∞))
    (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
    (fourier n).continuous.measurable (measurable_gaussPrimeScaleCircle p) hprod
    zero_le_one (fun z => le_of_eq (norm_fourier_eq_one n z))
    (Real.sqrt_nonneg p) (norm_gaussPrimeScaleCircle_le hp)
    (Real.sqrt_nonneg p) hbnd (Filter.Eventually.of_forall fun _ => by ring)
  have h := congrArg (fun T => T u) (h1.trans h2.symm)
  simpa [gaussPrimeScaleBlock, fourierMulBlock] using h

theorem gaussPrimeScaleInvSqBlock_comm {p : ℝ} (hp : 1 < p) (n : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussPrimeScaleInvSqBlock hp (fourierMulBlock n u)
      = fourierMulBlock n (gaussPrimeScaleInvSqBlock hp u) := by
  have hprod : Measurable
      (fun z : AddCircle (1 : ℝ) => gaussPrimeScaleInvSqCircle p z * fourier n z) :=
    (measurable_gaussPrimeScaleInvSqCircle p).mul (fourier n).continuous.measurable
  have hbnd : ∀ z, ‖gaussPrimeScaleInvSqCircle p z * fourier n z‖ ≤ 1 := by
    intro z
    rw [norm_mul, norm_fourier_eq_one, mul_one]
    exact norm_gaussPrimeScaleInvSqCircle_le hp z
  have h1 := MeasureTheory.lpBoundedMulCLM_comp (p := (2 : ℝ≥0∞))
    (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
    (measurable_gaussPrimeScaleInvSqCircle p) (fourier n).continuous.measurable hprod
    zero_le_one (norm_gaussPrimeScaleInvSqCircle_le hp)
    zero_le_one (fun z => le_of_eq (norm_fourier_eq_one n z))
    zero_le_one hbnd (Filter.Eventually.of_forall fun _ => rfl)
  have h2 := MeasureTheory.lpBoundedMulCLM_comp (p := (2 : ℝ≥0∞))
    (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
    (fourier n).continuous.measurable (measurable_gaussPrimeScaleInvSqCircle p) hprod
    zero_le_one (fun z => le_of_eq (norm_fourier_eq_one n z))
    zero_le_one (norm_gaussPrimeScaleInvSqCircle_le hp)
    zero_le_one hbnd (Filter.Eventually.of_forall fun _ => by ring)
  have h := congrArg (fun T => T u) (h1.trans h2.symm)
  simpa [gaussPrimeScaleInvSqBlock, fourierMulBlock] using h

/-! ## Recovering the diagonals from the normalized blocks -/

theorem gaussDiagonalBlockStar_fourierMulBlock {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {n : ℤ} (hn : n ≠ 0) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussDiagonalBlockStar hm k p (fourierMulBlock n u)
      = starRingEnd ℂ (gaussSampleValue k p n) •
        fourierMulBlock n (gaussShiftedBlockOf hm k p n u) := by
  have hne : starRingEnd ℂ (gaussSampleValue k p n) ≠ 0 := by
    simpa using gaussSampleValue_ne_zero hm k p hn
  rw [gaussShiftedBlockOf, map_smul, fourierMulBlock_neg_apply, smul_smul,
    mul_inv_cancel₀ hne, one_smul]

theorem gaussDiagonalBlock_fourierMulBlock {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {n : ℤ} (hn : n ≠ 0) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussDiagonalBlock hm k p (fourierMulBlock n u)
      = gaussSampleValue k p n •
        fourierMulBlock n (gaussShiftedBlockDiag hm k p n u) := by
  have hne : gaussSampleValue k p n ≠ 0 := gaussSampleValue_ne_zero hm k p hn
  rw [gaussShiftedBlockDiag, map_smul, fourierMulBlock_neg_apply, smul_smul,
    mul_inv_cancel₀ hne, one_smul]

/-! ## The exact factorization -/

/-- **The one-step factorization.**  The quasi-inner block acts on a twisted amplitude through the
two normalized shifted blocks, with the scalar `p |d_n|²`. -/
theorem gaussQuasiInnerG_fourierMulBlock {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {n : ℤ} (hn : n ≠ 0)
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussQuasiInnerG hm k p (fourierMulBlock n f)
      = (((p : ℝ) : ℂ) *
          (starRingEnd ℂ (gaussSampleValue k p n) * gaussSampleValue k p n)) •
        fourierMulBlock n
          (gaussPrimeScaleBlock hp
            (gaussShiftedBlockDiag hm k p n
              (gaussPrimeScaleInvSqBlock hp
                (gaussShiftedBlockOf hm k p n
                  (gaussPrimeScaleBlock hp f))))) := by
  rw [gaussQuasiInnerG]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [gaussPrimeScaleBlock_comm hp n f,
    gaussDiagonalBlockStar_fourierMulBlock hm k p hn]
  simp only [map_smul, gaussPrimeScaleInvSqBlock_comm hp n,
    gaussDiagonalBlock_fourierMulBlock hm k p hn, gaussPrimeScaleBlock_comm hp n, smul_smul]

end

end RHTower
