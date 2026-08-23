import GaloisForLFunctions.RHTower.MellinTrivialZeros
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling
import GaloisForLFunctions.HTGeometry.SimplePoleResidueValue
import GaloisForLFunctions.HTGeometry.RectangleResidueTheorem
import GaloisForLFunctions.HTGeometry.ZetaJetFreeness

/-!
# The integrand of Burnol's Theorem 5.2

Theorem 5.2 integrates

`H(s) = G(s)·ζ(Z)/(ζ(s)(Z − s))`

around a rectangle.  This module assembles the hypotheses of the general-order rectangle residue
theorem for that integrand: `H` is meromorphic wherever `G` is, it is analytic at every point of the
rectangle that is neither a zero of `ζ`, nor `1`, nor `Z`, nor a singularity of `G`, and its residue
at `Z` is `−G(Z)`.  Only finitely many points of a rectangle are zeros of `ζ`.

## Main results

* `burnolIntegrand`
* `meromorphicAt_burnolIntegrand`, `analyticAt_burnolIntegrand`
* `laurentCoeff_burnolIntegrand_self`
* `finite_riemannZeta_zeros_rectangle`
-/

open Complex Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The integrand of Burnol's residue contour. -/
def burnolIntegrand (G : ℂ → ℂ) (Z : ℂ) : ℂ → ℂ :=
  fun s => G s * riemannZeta Z / (riemannZeta s * (Z - s))

theorem burnolIntegrand_eq_mul_inv (G : ℂ → ℂ) (Z : ℂ) (s : ℂ) :
    burnolIntegrand G Z s = (G s * riemannZeta Z / riemannZeta s) * (Z - s)⁻¹ := by
  rw [burnolIntegrand, div_mul_eq_div_div, div_eq_mul_inv]

theorem meromorphicAt_riemannZeta_everywhere (s : ℂ) : MeromorphicAt riemannZeta s := by
  rcases eq_or_ne s 1 with rfl | hs1
  · exact GaloisForLFunctions.meromorphicAt_riemannZeta_one
  · exact (analyticOn_riemannZeta s (by simpa using hs1)).meromorphicAt

theorem meromorphicAt_burnolIntegrand {G : ℂ → ℂ} {Z s : ℂ} (hG : MeromorphicAt G s) :
    MeromorphicAt (burnolIntegrand G Z) s := by
  have hζ : MeromorphicAt riemannZeta s := meromorphicAt_riemannZeta_everywhere s
  have hnum : MeromorphicAt (fun u : ℂ => G u * riemannZeta Z) s := hG.mul analyticAt_const.meromorphicAt
  have hden : MeromorphicAt (fun u : ℂ => riemannZeta u * (Z - u)) s :=
    hζ.mul ((analyticAt_const.sub analyticAt_id).meromorphicAt)
  exact hnum.div hden

/-- Away from the zeros of `ζ`, from `1`, from `Z` and from the singularities of `G`, the integrand
is analytic. -/
theorem analyticAt_burnolIntegrand {G : ℂ → ℂ} {Z s : ℂ} (hG : AnalyticAt ℂ G s)
    (hζ : riemannZeta s ≠ 0) (hs1 : s ≠ 1) (hsZ : s ≠ Z) :
    AnalyticAt ℂ (burnolIntegrand G Z) s := by
  have hζa : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hs1)
  have hZs : (Z - s) ≠ 0 := sub_ne_zero.2 fun h => hsZ h.symm
  refine AnalyticAt.div (hG.mul analyticAt_const) (hζa.mul (analyticAt_const.sub analyticAt_id)) ?_
  exact mul_ne_zero hζ hZs

/-- **The residue at `Z` is `−G(Z)`.** -/
theorem laurentCoeff_burnolIntegrand_self {G : ℂ → ℂ} {Z : ℂ} (hG : AnalyticAt ℂ G Z)
    (hζ : riemannZeta Z ≠ 0) (hZ1 : Z ≠ 1) :
    laurentCoeff (burnolIntegrand G Z) Z (-1) = -G Z := by
  have hζa : AnalyticAt ℂ riemannZeta Z := analyticOn_riemannZeta Z (by simpa using hZ1)
  set A : ℂ → ℂ := fun s : ℂ => G s * riemannZeta Z / riemannZeta s with hAdef
  have hA : AnalyticAt ℂ A Z := (hG.mul analyticAt_const).div hζa hζ
  have hAval : A Z = G Z := by
    rw [hAdef]
    field_simp
  have hfun : burnolIntegrand G Z = fun s => A s * (Z - s)⁻¹ := by
    funext s
    rw [burnolIntegrand_eq_mul_inv, hAdef]
  rw [hfun, laurentCoeff_analytic_mul_inv_sub hA, hAval]

/-- Only finitely many points of a rectangle are zeros of `ζ`. -/
theorem finite_riemannZeta_zeros_rectangle (z w : ℂ) :
    {s : ℂ | s ∈ Rectangle z w ∧ riemannZeta s = 0}.Finite := by
  have hfin := RHTower.Sieve.zetaResidueUnit_zeros_closedRectangle_finite z w
  refine (hfin.union (Set.finite_singleton (1 : ℂ))).subset ?_
  rintro s ⟨hs, hzero⟩
  rcases eq_or_ne s 1 with rfl | hs1
  · exact Or.inr rfl
  · refine Or.inl ⟨hs, ?_⟩
    rw [zetaResidueUnit, Function.update_of_ne hs1]
    rw [hzero, mul_zero]

end

end RHTower
