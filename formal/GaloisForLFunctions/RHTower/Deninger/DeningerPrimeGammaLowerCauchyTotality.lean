import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticPrimeGammaHilbert
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeGammaEulerSectorObstruction
import GaloisForLFunctions.RHTower.XiCauchyTransformCompleteness
import GaloisForLFunctions.RHTower.XiWeilDivisorHilbert
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticAssociatedGraded

/-!
# Lower prime--Gamma Cauchy totality

The finite lower Euler sector is not a merely local source chart: its Cauchy atoms have the same
closed Hilbert span as every regular Xi Cauchy atom.  The proof does not cross an Euler pole.
Instead, a vector orthogonal to all lower atoms has Cauchy transform with zero real part on a
lower zero-free ball.  Existing Cauchy-transform completeness propagates this to the whole regular
set and forces each Xi multiplicity-fibre sum to vanish.  The already formalized fibre annihilator
then identifies the two closed spans.

This is a reachability theorem only.  It supplies neither a reflected source diagonal nor a
positivity law; those remain the substantive Route P obstruction.
-/

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section

/-- The regular Xi Cauchy base point associated with a lower absolute-Euler parameter. -/
def deningerPrimeGammaLowerCauchyRegularPoint
    (z : DeningerPrimeGammaLowerPoint) : XiCRegularPoint :=
  ⟨z, XiC_ne_zero_of_half_le_abs_im (by
    have hz := deningerPrimeGammaLowerPoint_im_lt z
    rw [abs_of_neg (by linarith : (z : ℂ).im < 0)]
    linarith)⟩

/-- The Xi-divisor Hilbert vector of one lower prime--Gamma Cauchy atom. -/
def deningerPrimeGammaLowerCauchyLp
    (z : DeningerPrimeGammaLowerPoint) : lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilCauchyLp (deningerPrimeGammaLowerCauchyRegularPoint z)

/-- Algebraic span of lower absolute-Euler Cauchy atoms in the Xi divisor Hilbert carrier. -/
def deningerPrimeGammaLowerCauchyAlgebraicSubspace :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Submodule.span ℂ (Set.range deningerPrimeGammaLowerCauchyLp)

theorem deningerPrimeGammaLowerCauchyAlgebraicSubspace_le_xiWeilCauchyAlgebraicSubspace :
    deningerPrimeGammaLowerCauchyAlgebraicSubspace ≤ xiWeilCauchyAlgebraicSubspace := by
  apply Submodule.span_le.mpr
  rintro v ⟨z, rfl⟩
  exact Submodule.subset_span ⟨deningerPrimeGammaLowerCauchyRegularPoint z, rfl⟩

/-- A convenient open lower Euler ball. -/
def deningerPrimeGammaLowerPointOfMemNegIBall
    (z : ℂ) (hz : z ∈ ball (-Complex.I) (1 / 4 : ℝ)) :
    DeningerPrimeGammaLowerPoint := by
  rw [mem_ball, Complex.dist_eq] at hz
  have him : |z.im + 1| < 1 / 4 := by
    have h := Complex.abs_im_le_norm (z + Complex.I)
    have hnorm : ‖z + Complex.I‖ < 1 / 4 := by
      simpa [norm_sub_rev] using hz
    simpa using h.trans_lt hnorm
  have hneg : z.im < -(1 / 2 : ℝ) := by
    have hupper := (le_abs_self (z.im + 1)).trans_lt him
    linarith
  exact ⟨z, by
    norm_num [Complex.mul_re]
    linarith⟩

theorem XiC_ne_zero_of_mem_deningerPrimeGammaNegIBall
    (z : ℂ) (hz : z ∈ ball (-Complex.I) (1 / 4 : ℝ)) : XiC z ≠ 0 := by
  have hneg : z.im < -(1 / 2 : ℝ) := by
    simpa [deningerPrimeGammaLowerPointOfMemNegIBall] using
      (deningerPrimeGammaLowerPoint_im_lt
        (deningerPrimeGammaLowerPointOfMemNegIBall z hz))
  apply XiC_ne_zero_of_half_le_abs_im
  rw [abs_of_neg (by linarith : z.im < 0)]
  linarith

/-- Orthogonality to all lower Euler atoms kills each exact Xi multiplicity-fibre sum. -/
theorem xiWeilFiberSum_eq_zero_of_inner_deningerPrimeGammaLowerCauchyLp_eq_zero
    (u : lp (fun _ : XiZeroCopy => ℂ) 2)
    (h : ∀ z : DeningerPrimeGammaLowerPoint,
      inner ℂ (deningerPrimeGammaLowerCauchyLp z) u = 0)
    (rho : XiDivisorSupport) :
    xiWeilFiberSum (fun q => u q) rho = 0 := by
  refine xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball u
    (z₀ := -Complex.I) (r := 1 / 4) (by norm_num)
    (fun z hz => XiC_ne_zero_of_mem_deningerPrimeGammaNegIBall z hz) ?_ rho
  intro z hz
  let zl : DeningerPrimeGammaLowerPoint :=
    deningerPrimeGammaLowerPointOfMemNegIBall z hz
  have hzreg : XiC z ≠ 0 := XiC_ne_zero_of_mem_deningerPrimeGammaNegIBall z hz
  have hpoint : deningerPrimeGammaLowerCauchyRegularPoint zl = ⟨z, hzreg⟩ := by
    apply Subtype.ext
    rfl
  have hzero := h zl
  change inner ℂ (xiWeilCauchyLp (deningerPrimeGammaLowerCauchyRegularPoint zl)) u = 0 at hzero
  rw [hpoint] at hzero
  have hzero' : inner ℂ u (xiWeilCauchyLp ⟨z, hzreg⟩) = 0 := by
    have hconj := congrArg (starRingEnd ℂ) hzero
    rw [inner_conj_symm, map_zero] at hconj
    exact hconj
  rw [xiCauchyTransform_eq_inner u ⟨z, hzreg⟩]
  exact congrArg Complex.re hzero'

theorem inner_eq_zero_on_deningerPrimeGammaLowerCauchyAlgebraicSubspace_iff
    (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    (∀ x ∈ deningerPrimeGammaLowerCauchyAlgebraicSubspace, inner ℂ x u = 0) ↔
      ∀ rho : XiDivisorSupport, xiWeilFiberSum (fun q => u q) rho = 0 := by
  constructor
  · intro h rho
    apply xiWeilFiberSum_eq_zero_of_inner_deningerPrimeGammaLowerCauchyLp_eq_zero u
      (fun z => ?_) rho
    exact h _ (Submodule.subset_span ⟨z, rfl⟩)
  · intro hfib x hx
    have hfull : ∀ y ∈ xiWeilCauchyAlgebraicSubspace, inner ℂ y u = 0 :=
      (inner_eq_zero_on_xiWeilCauchyAlgebraicSubspace_iff u).mpr hfib
    exact hfull x (deningerPrimeGammaLowerCauchyAlgebraicSubspace_le_xiWeilCauchyAlgebraicSubspace hx)

theorem deningerPrimeGammaLowerCauchyAlgebraicSubspace_orthogonal_eq :
    deningerPrimeGammaLowerCauchyAlgebraicSubspaceᗮ =
      xiWeilCauchyAlgebraicSubspaceᗮ := by
  ext u
  rw [Submodule.mem_orthogonal, Submodule.mem_orthogonal,
    inner_eq_zero_on_deningerPrimeGammaLowerCauchyAlgebraicSubspace_iff,
    inner_eq_zero_on_xiWeilCauchyAlgebraicSubspace_iff]

/-- Lower absolute-Euler Cauchy atoms are Hilbert-total in the full regular Xi Cauchy core. -/
theorem deningerPrimeGammaLowerCauchyHilbertSubspace_eq_xiWeilCauchyHilbertSubspace :
    deningerPrimeGammaLowerCauchyAlgebraicSubspace.topologicalClosure =
      xiWeilCauchyHilbertSubspace := by
  rw [show deningerPrimeGammaLowerCauchyAlgebraicSubspace.topologicalClosure =
      deningerPrimeGammaLowerCauchyAlgebraicSubspaceᗮᗮ by
        exact (Submodule.orthogonal_orthogonal_eq_closure _).symm,
    show xiWeilCauchyHilbertSubspace = xiWeilCauchyAlgebraicSubspaceᗮᗮ by
        exact (Submodule.orthogonal_orthogonal_eq_closure _).symm,
    deningerPrimeGammaLowerCauchyAlgebraicSubspace_orthogonal_eq]

/-- The canonical source-jet identification sends one prime--Gamma packet atom to its lower
Xi Cauchy vector. -/
def deningerPrimeGammaLowerToXiHilbert :
    DeningerPrimeGammaLowerPacket →ₗ[ℂ] XiDivisorL2 :=
  deningerArithmeticGradedHilbertEquivSourceJets.symm.toLinearMap.comp
    deningerPrimeGammaLowerToJetHilbert

theorem deningerPrimeGammaLowerCauchyLp_eq_deningerPrimeGammaLowerToXiHilbert_single
    (z : DeningerPrimeGammaLowerPoint) :
    deningerPrimeGammaLowerCauchyLp z =
      deningerPrimeGammaLowerToXiHilbert (Finsupp.single z 1) := by
  apply deningerArithmeticGradedHilbertEquivSourceJets.injective
  calc
    deningerArithmeticGradedHilbertEquivSourceJets (deningerPrimeGammaLowerCauchyLp z) =
        deningerPrimeGammaLowerToJetHilbert (Finsupp.single z 1) := by
      apply Subtype.ext
      funext q
      change deningerPrimeGammaLowerCauchyLp z q =
        deningerPrimeGammaLowerToJetHilbert (Finsupp.single z 1) q
      rw [deningerPrimeGammaLowerToJetHilbert_apply]
      simp [deningerPrimeGammaLowerCauchyLp, xiWeilCauchyLp_apply,
        deningerPrimeGammaLowerCauchyRegularPoint,
        deningerPrimeGammaLowerCauchyTest_single]
    _ = deningerArithmeticGradedHilbertEquivSourceJets
        (deningerPrimeGammaLowerToXiHilbert (Finsupp.single z 1)) := by
      simp [deningerPrimeGammaLowerToXiHilbert]

end

end RHTower
