import GaloisForLFunctions.RHTower.SelbergMaassRationalTraceSummandFourier

/-!
# Common-width Fourier windows of a rational Maass trace

Every literal rational principal trace has one target Fourier window. This file
expresses that coefficient as the exact finite sum of integral-translate source
windows at the individual rational cusp scales and shifts. Thus neither quotient
representatives nor a common-period assumption is hidden in the trace step. The
remaining Selberg obstruction is the arithmetic orientation of this explicit
finite window sum in the off-diagonal current identity.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open _root_.RHTower
open Complex UpperHalfPlane SelbergMaassMean Matrix SpecialLinearGroup GeneralLinearGroup
open SelbergMaassCuspTransport
open scoped BigOperators MatrixGroups

noncomputable section

theorem deningerFourierKernel_continuous (w : ℝ) (n : ℤ) :
    Continuous (deningerFourierKernel w n) :=
  continuous_iff_continuousAt.mpr
    (fun x => (deningerFourierKernel_hasDerivAt w n x).continuousAt)

theorem deningerFourierCoeff_fintype_sum {ι : Type*} [Fintype ι]
    (w : ℝ) (n : ℤ) (F : ι → ℝ → ℂ) (hF : ∀ i, Continuous (F i)) :
    deningerFourierCoeff w (fun x => ∑ i, F i x) n =
      ∑ i, deningerFourierCoeff w (F i) n := by
  classical
  unfold deningerFourierCoeff
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum
    (f := fun i x => deningerFourierKernel w n x * F i x)
    (fun i _ => ((deningerFourierKernel_continuous w n).mul (hF i)).intervalIntegrable _ _)]
  rw [Finset.mul_sum]

theorem rationalPrincipalTrace_cusp_fourier_window_sum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val) (B : SL2Z)
    {w y : ℝ} (hw : w ≠ 0) (hy : 0 < y) (n : ℤ) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI := Fintype.ofFinite (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    ∃ A : (principalCongruenceGL N ⧸
        ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) → SL2Z,
      ∃ U : (principalCongruenceGL N ⧸
        ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) → GL (Fin 2) ℝ,
        (∀ q, (U q).val 1 0 = 0 ∧ 0 < (U q).det.val) ∧
        deningerFourierCoeff w
          (fun x => rationalPrincipalTraceFunction N g hg lam
            (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)
            (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) n =
          ∑ q, deningerFourierCoeff (upperTriangularScale (U q) * w)
            (fun x => (translate (N + 1) (A q) f).1.1
              (UpperHalfPlane.ofComplex (point (x + upperTriangularShift (U q))
                (upperTriangularScale (U q) * y)))) n := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI := Fintype.ofFinite
    (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
  choose A U hU hdet hAffine using fun q =>
    rationalPrincipalTrace_summand_cusp_affine N f g hg B q hy
  refine ⟨A, U, fun q => ⟨hU q, hdet q⟩, ?_⟩
  let F : (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) → ℝ → ℂ :=
    fun q x => maassTraceQuotientFunc
      (rationalMaassPullback N g hg lam
        (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)).1 q
      (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))
  let G : (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) → ℝ → ℂ :=
    fun q x => (translate (N + 1) (A q) f).1.1
      (UpperHalfPlane.ofComplex (point
        (upperTriangularScale (U q) * x + upperTriangularShift (U q))
        (upperTriangularScale (U q) * y)))
  have hFG (q) : F q = G q := by
    funext x
    exact hAffine q x
  have hG (q) : Continuous (G q) := by
    have hheight : 0 < upperTriangularScale (U q) * y :=
      mul_pos (upperTriangular_scale_pos (U q) (hU q) (hdet q)) hy
    have hslice : Continuous (fun x => (translate (N + 1) (A q) f).1.1
        (UpperHalfPlane.ofComplex (point x (upperTriangularScale (U q) * y)))) :=
      slice_continuous (translate (N + 1) (A q) f).2.2.1.1.continuousOn hheight
    exact hslice.comp ((continuous_const.mul continuous_id).add continuous_const)
  have hF (q) : Continuous (F q) := by
    rw [hFG q]
    exact hG q
  unfold rationalPrincipalTraceFunction
  change deningerFourierCoeff w (fun x => ∑ q, F q x) n = _
  rw [deningerFourierCoeff_fintype_sum w n F hF]
  apply Finset.sum_congr rfl
  intro q _
  rw [hFG q]
  let H : ℝ → ℂ := fun x => (translate (N + 1) (A q) f).1.1
    (UpperHalfPlane.ofComplex (point (x + upperTriangularShift (U q))
      (upperTriangularScale (U q) * y)))
  have hscale : upperTriangularScale (U q) ≠ 0 :=
    ne_of_gt (upperTriangular_scale_pos (U q) (hU q) (hdet q))
  simpa only [G, H] using deningerFourierCoeff_comp_mul hw hscale (F := H) n

end

end GaloisForLFunctions.RHTower
