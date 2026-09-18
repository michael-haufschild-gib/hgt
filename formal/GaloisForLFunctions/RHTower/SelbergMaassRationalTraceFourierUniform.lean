import GaloisForLFunctions.RHTower.SelbergMaassRationalTraceFourierAggregation
import GaloisForLFunctions.RHTower.SelbergMaassFourierModes

/-!
# Height-uniform rational-trace Fourier transport

The rational cusp factor attached to each trace summand is independent of
height. This module makes that independence explicit, then aggregates the
summands into one height-uniform Fourier identity. Consequently the exact
finite translated-window formula is available as an identity of height
functions, which is the prerequisite for inserting it into differentiated
phase-current identities.

No orientation or positivity of the resulting finite window sum is asserted.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open _root_.RHTower
open Complex UpperHalfPlane SelbergMaassMean Matrix SpecialLinearGroup GeneralLinearGroup
open SelbergMaassCuspTransport SelbergMaassFourier
open scoped BigOperators MatrixGroups

noncomputable section

/-- The rational cusp factor for one trace summand can be selected before the
height is fixed. -/
theorem rationalPrincipalTrace_summand_cusp_affine_uniform (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val) (B : SL2Z)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) :
    ∃ A : SL2Z, ∃ U : GL (Fin 2) ℝ,
      U 1 0 = 0 ∧ 0 < U.det.val ∧ ∀ {y : ℝ}, 0 < y → ∀ x : ℝ,
        maassTraceQuotientFunc
          (rationalMaassPullback N g hg lam
            (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)).1 q
          (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)) =
        (translate (N + 1) A f).1.1 (UpperHalfPlane.ofComplex
          (point (upperTriangularScale U * x + upperTriangularShift U)
            (upperTriangularScale U * y))) := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨a, ha, hapos⟩ := principalCongruenceGL_hasPositiveRationalLifts N r⁻¹
    have hga : 0 < ((g * a).map (algebraMap ℚ ℝ)).det.val :=
      rationalGL_map_det_mul_pos g a hg hapos
    obtain ⟨A, U, hU, hdet, hfactor⟩ := rationalGL_integral_cusp_factor (g * a) hga B
    refine ⟨A, U, hU, hdet, ?_⟩
    intro y hy x
    have hpoint : U • UpperHalfPlane.ofComplex (point x y) =
        UpperHalfPlane.ofComplex
          (point (upperTriangularScale U * x + upperTriangularShift U)
            (upperTriangularScale U * y)) := by
      apply UpperHalfPlane.ext
      rw [upperTriangular_smul_point U hU hdet x y hy]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos]
      simp [point, upperTriangular_scale_pos U hU hdet, hy]
    rw [maassTraceQuotientFunc_mk]
    change f.1.1 (g.map (algebraMap ℚ ℝ) •
      ((r⁻¹).val • (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)))) =
      (translate (N + 1) A f).1.1 (UpperHalfPlane.ofComplex
        (point (upperTriangularScale U * x + upperTriangularShift U)
          (upperTriangularScale U * y)))
    simp only [translate_apply]
    calc
      f.1.1 (g.map (algebraMap ℚ ℝ) •
          ((r⁻¹).val • (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)))) =
          f.1.1 ((g.map (algebraMap ℚ ℝ) * (r⁻¹).val) •
            (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) := by
        rw [mul_smul]
      _ = f.1.1 ((g.map (algebraMap ℚ ℝ) * a.map (algebraMap ℚ ℝ)) •
          (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) := by rw [ha]
      _ = f.1.1 ((g * a).map (algebraMap ℚ ℝ) •
          (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) := by
        rw [← Matrix.GeneralLinearGroup.map_mul]
      _ = f.1.1 (((g * a).map (algebraMap ℚ ℝ) * mapGL ℝ B) •
          UpperHalfPlane.ofComplex (point x y)) := by
        rw [mul_smul]
      _ = f.1.1 ((mapGL ℝ A * U) • UpperHalfPlane.ofComplex (point x y)) :=
        congrArg (fun M : GL (Fin 2) ℝ =>
          f.1.1 (M • UpperHalfPlane.ofComplex (point x y))) hfactor
      _ = f.1.1 (mapGL ℝ A • (U • UpperHalfPlane.ofComplex (point x y))) := by
        rw [mul_smul]
      _ = f.1.1 (mapGL ℝ A • UpperHalfPlane.ofComplex
          (point (upperTriangularScale U * x + upperTriangularShift U)
            (upperTriangularScale U * y))) := by rw [hpoint]

/-- One finite family of rational cusp factors gives the trace Fourier formula
at every positive height. -/
theorem rationalPrincipalTrace_cusp_fourier_window_sum_uniform (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val) (B : SL2Z) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI := Fintype.ofFinite (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    ∃ A : (principalCongruenceGL N ⧸
        ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) → SL2Z,
      ∃ U : (principalCongruenceGL N ⧸
        ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) → GL (Fin 2) ℝ,
        (∀ q, (U q).val 1 0 = 0 ∧ 0 < (U q).det.val) ∧
        ∀ {w y : ℝ}, w ≠ 0 → 0 < y → ∀ n : ℤ,
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
    rationalPrincipalTrace_summand_cusp_affine_uniform N f g hg B q
  refine ⟨A, U, fun q => ⟨hU q, hdet q⟩, ?_⟩
  intro w y hw hy n
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
    exact hAffine q hy x
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

/-- The height-uniform rational trace identity on the bundled Maass carrier. -/
theorem rationalPrincipalTrace_cusp_maassCoefficient_sum_uniform (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (F : GLMaassCuspEigenform (principalCongruenceGL N) lam)
    (hF : F.1.1 = rationalPrincipalTraceFunction N g hg lam
      (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI := Fintype.ofFinite (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    ∃ A : (principalCongruenceGL N ⧸
        ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) → SL2Z,
      ∃ U : (principalCongruenceGL N ⧸
        ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) → GL (Fin 2) ℝ,
        (∀ q, (U q).val 1 0 = 0 ∧ 0 < (U q).det.val) ∧
        ∀ {y : ℝ}, 0 < y → ∀ n : ℤ,
          maassCoefficient N
            (glIntegralMaassCuspEigenformToMaass (CongruenceSubgroup.Gamma (N + 1)) lam F) n y =
            ∑ q, deningerFourierCoeff (upperTriangularScale (U q) * (N + 1 : ℕ))
              (fun x => (translate (N + 1) (A q) f).1.1
                (UpperHalfPlane.ofComplex (point (x + upperTriangularShift (U q))
                  (upperTriangularScale (U q) * y)))) n := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI := Fintype.ofFinite
    (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
  obtain ⟨A, U, hU, hsum⟩ :=
    rationalPrincipalTrace_cusp_fourier_window_sum_uniform N f g hg (1 : SL2Z)
  refine ⟨A, U, hU, ?_⟩
  intro y hy n
  rw [maassCoefficient, coefficient]
  change deningerFourierCoeff (N + 1 : ℕ)
    (fun x => F.1.1 (UpperHalfPlane.ofComplex (point x y))) n = _
  rw [hF]
  simpa using hsum (w := (N + 1 : ℕ)) (by positivity) hy n

end

end GaloisForLFunctions.RHTower
