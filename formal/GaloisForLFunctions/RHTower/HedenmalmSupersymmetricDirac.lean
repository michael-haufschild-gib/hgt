import GaloisForLFunctions.RHTower.HedenmalmShiftedSourceEquationExact
import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Supersymmetric Dirac operator of the closed Hedenmalm derivative

This module constructs the actual off-diagonal unbounded operator

`Q = [[0, A†], [A, 0]]`

on the Hilbert direct sum.  Its nonreal resolvent is built from the compact graph coordinate of
`A`, rather than postulated abstractly.
-/

open Complex Function MeasureTheory Module Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmClosedWeightedDerivative

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmThetaSource

private abbrev H := Lp ℂ 2 unitIntervalMeasure
private abbrev D := WithLp 2 (H × H)

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance : CompleteSpace thetaCentered := thetaCentered_isClosed.completeSpace_coe

/-! ### Bounded Gram inverse used by the nonreal Dirac resolvent -/

/-- Coercive bounded Gram operator `1 + B†B` on the centered graph coordinate. -/
def thetaDiracGram : thetaCentered →L[ℂ] thetaCentered :=
  1 + thetaCenteredSourceInverse.adjoint.comp thetaCenteredSourceInverse

theorem thetaDiracGram_reCoercive (k : thetaCentered) :
    1 * ‖k‖ ^ 2 ≤ (inner ℂ (thetaDiracGram k) k).re := by
  calc
    1 * ‖k‖ ^ 2 ≤ ‖k‖ ^ 2 + ‖thetaCenteredSourceInverse k‖ ^ 2 := by
      rw [one_mul]
      exact le_add_of_nonneg_right (sq_nonneg _)
    _ = (inner ℂ (thetaDiracGram k) k).re := by
      rw [thetaDiracGram, add_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply, inner_add_left,
        thetaCenteredSourceInverse.adjoint_inner_left, Complex.add_re]
      exact congrArg₂ (fun a b : ℝ => a + b)
        (norm_sq_eq_re_inner (𝕜 := ℂ) k)
        (norm_sq_eq_re_inner (𝕜 := ℂ) (thetaCenteredSourceInverse k))

theorem thetaDiracGram_injective : Function.Injective thetaDiracGram := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hco := thetaDiracGram_reCoercive (x - y)
  have hzero : thetaDiracGram (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  simp only [hzero, inner_zero_left, Complex.zero_re, one_mul] at hco
  have hnorm : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact norm_eq_zero.mp hnorm

theorem thetaDiracGram_surjective : Function.Surjective thetaDiracGram :=
  ContinuousLinearMap.surjective_of_reCoercive (c := 1) one_pos
    thetaDiracGram_reCoercive

/-- Bounded inverse of `1 + B†B`. -/
def thetaDiracGramEquiv : thetaCentered ≃L[ℂ] thetaCentered :=
  ContinuousLinearEquiv.ofBijective thetaDiracGram
    (LinearMap.ker_eq_bot.mpr thetaDiracGram_injective)
    (LinearMap.range_eq_top.mpr thetaDiracGram_surjective)

def thetaDiracGramInverse : thetaCentered →L[ℂ] thetaCentered :=
  thetaDiracGramEquiv.symm.toContinuousLinearMap

theorem thetaDiracGram_apply_inverse (k : thetaCentered) :
    thetaDiracGram (thetaDiracGramInverse k) = k :=
  thetaDiracGramEquiv.apply_symm_apply k

theorem thetaDiracGram_inverse_apply (k : thetaCentered) :
    thetaDiracGramInverse (thetaDiracGram k) = k :=
  thetaDiracGramEquiv.symm_apply_apply k

/-! ### Actual off-diagonal partial operator -/

def thetaSupersymmetricDiracDomain : Submodule ℂ D where
  carrier := {p | p.ofLp.1 ∈ thetaWeightedDerivative.domain ∧
    p.ofLp.2 ∈ thetaWeightedDerivative.adjoint.domain}
  zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  add_mem' := by
    rintro x y hx hy
    exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' := by
    intro c x hx
    exact ⟨Submodule.smul_mem _ c hx.1, Submodule.smul_mem _ c hx.2⟩

/-- The unbounded supersymmetric block `[[0,A†],[A,0]]` on its natural product domain. -/
def thetaSupersymmetricDirac : D →ₗ.[ℂ] D where
  domain := thetaSupersymmetricDiracDomain
  toFun :=
    { toFun := fun p => WithLp.toLp 2
        (thetaWeightedDerivative.adjoint ⟨p.1.ofLp.2, p.2.2⟩,
          thetaWeightedDerivative ⟨p.1.ofLp.1, p.2.1⟩)
      map_add' := by
        intro x y
        apply (WithLp.prodContinuousLinearEquiv 2 ℂ H H).injective
        apply Prod.ext
        · exact LinearPMap.map_add thetaWeightedDerivative.adjoint
            ⟨x.1.ofLp.2, x.2.2⟩ ⟨y.1.ofLp.2, y.2.2⟩
        · exact LinearPMap.map_add thetaWeightedDerivative
            ⟨x.1.ofLp.1, x.2.1⟩ ⟨y.1.ofLp.1, y.2.1⟩
      map_smul' := by
        intro c x
        apply (WithLp.prodContinuousLinearEquiv 2 ℂ H H).injective
        apply Prod.ext
        · exact LinearPMap.map_smul thetaWeightedDerivative.adjoint c
            ⟨x.1.ofLp.2, x.2.2⟩
        · exact LinearPMap.map_smul thetaWeightedDerivative c
            ⟨x.1.ofLp.1, x.2.1⟩ }

theorem thetaSupersymmetricDirac_domain :
    thetaSupersymmetricDirac.domain = thetaSupersymmetricDiracDomain := rfl

theorem thetaSupersymmetricDirac_apply
    (p : thetaSupersymmetricDirac.domain) :
    thetaSupersymmetricDirac p = WithLp.toLp 2
      (thetaWeightedDerivative.adjoint ⟨p.1.ofLp.2, p.2.2⟩,
        thetaWeightedDerivative ⟨p.1.ofLp.1, p.2.1⟩) := rfl

/-! ### Explicit resolvent at `i` -/

private def thetaDiracFst : D →L[ℂ] H := WithLp.fstL 2 ℂ H H

private def thetaDiracSnd : D →L[ℂ] H := WithLp.sndL 2 ℂ H H

/-- Centered graph coordinate of the solution to `(Q - i)(x,y) = (f,g)`. -/
def thetaDiracResolventK : D →L[ℂ] thetaCentered :=
  thetaDiracGramInverse.comp
    (thetaCentered.orthogonalProjectionOnto.comp thetaDiracSnd +
      Complex.I • thetaCenteredSourceInverse.adjoint.comp thetaDiracFst)

/-- First component of the nonreal Dirac resolvent. -/
def thetaDiracResolventX : D →L[ℂ] H :=
  thetaCenteredSourceInverse.comp thetaDiracResolventK

/-- Second component of the nonreal Dirac resolvent.  Its orthogonal summand is the
one-dimensional kernel of `A†`. -/
def thetaDiracResolventY : D →L[ℂ] H :=
  thetaCentered.subtypeL.comp
      (thetaCenteredSourceInverse.adjoint.comp
        (thetaDiracFst + Complex.I • thetaDiracResolventX)) +
    Complex.I • (thetaCenteredᗮ.starProjection.comp thetaDiracSnd)

/-- Bounded inverse candidate for `Q - i`, assembled from its two exact components. -/
def thetaSupersymmetricDiracResolventAtI : D →L[ℂ] D :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (thetaDiracResolventX.prod thetaDiracResolventY)

@[simp] theorem thetaDiracResolventAtI_fst (p : D) :
    (thetaSupersymmetricDiracResolventAtI p).ofLp.1 = thetaDiracResolventX p := rfl

@[simp] theorem thetaDiracResolventAtI_snd (p : D) :
    (thetaSupersymmetricDiracResolventAtI p).ofLp.2 = thetaDiracResolventY p := rfl

theorem thetaDiracResolventK_gram (p : D) :
    thetaDiracGram (thetaDiracResolventK p) =
      thetaCentered.orthogonalProjectionOnto p.ofLp.2 +
        Complex.I • thetaCenteredSourceInverse.adjoint p.ofLp.1 := by
  exact thetaDiracGram_apply_inverse _

theorem thetaDiracResolventX_eq (p : D) :
    thetaDiracResolventX p =
      thetaCenteredSourceInverse (thetaDiracResolventK p) := rfl

theorem thetaDiracResolventY_eq (p : D) :
    thetaDiracResolventY p =
      (thetaCenteredSourceInverse.adjoint
          (p.ofLp.1 + Complex.I • thetaDiracResolventX p) : H) +
        Complex.I • thetaCenteredᗮ.starProjection p.ofLp.2 := rfl

theorem thetaDiracResolventX_mem_domain (p : D) :
    thetaDiracResolventX p ∈ thetaWeightedDerivative.domain := by
  rw [thetaDiracResolventX_eq]
  change thetaCenteredSourceInverse (thetaDiracResolventK p) ∈
    (closedHyperplaneInverse thetaCentered thetaCenteredSourceInverse).domain
  exact (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
    thetaCenteredSourceInverse_injective (thetaDiracResolventK p)).1

theorem thetaWeightedDerivative_apply_thetaDiracResolventX
    (p : D) (hp : thetaDiracResolventX p ∈ thetaWeightedDerivative.domain) :
    thetaWeightedDerivative ⟨thetaDiracResolventX p, hp⟩ =
      (thetaDiracResolventK p : H) := by
  have hpair := closedHyperplaneInverse_apply_B thetaCentered
    thetaCenteredSourceInverse thetaCenteredSourceInverse_injective
      (thetaDiracResolventK p)
  have heq : (⟨thetaDiracResolventX p, hp⟩ : thetaWeightedDerivative.domain) =
      ⟨thetaCenteredSourceInverse (thetaDiracResolventK p), hpair.1⟩ := by
    apply Subtype.ext
    exact thetaDiracResolventX_eq p
  rw [heq]
  exact hpair.2

private theorem thetaOrthogonalProjection_mem_adjoint_domain (g : H) :
    thetaCenteredᗮ.starProjection g ∈ thetaWeightedDerivative.adjoint.domain := by
  have hker : thetaWeightedDerivative.adjoint.kernel = thetaCenteredᗮ :=
    closedHyperplaneInverse_adjoint_kernel thetaCentered thetaCenteredSourceInverse
      thetaCenteredSourceInverse_injective thetaCenteredSourceInverse_dense_range
  have hmem : thetaCenteredᗮ.starProjection g ∈
      thetaWeightedDerivative.adjoint.kernel := by
    rw [hker]
    exact thetaCenteredᗮ.starProjection_apply_mem g
  exact (LinearPMap.mem_kernel_iff.mp hmem).1

private theorem thetaWeightedDerivative_adjoint_apply_orthogonalProjection
    (g : H) (hg : thetaCenteredᗮ.starProjection g ∈
      thetaWeightedDerivative.adjoint.domain) :
    thetaWeightedDerivative.adjoint
        ⟨thetaCenteredᗮ.starProjection g, hg⟩ = 0 := by
  have hker : thetaWeightedDerivative.adjoint.kernel = thetaCenteredᗮ :=
    closedHyperplaneInverse_adjoint_kernel thetaCentered thetaCenteredSourceInverse
      thetaCenteredSourceInverse_injective thetaCenteredSourceInverse_dense_range
  have hmem : thetaCenteredᗮ.starProjection g ∈
      thetaWeightedDerivative.adjoint.kernel := by
    rw [hker]
    exact thetaCenteredᗮ.starProjection_apply_mem g
  exact (LinearPMap.mem_kernel_iff.mp hmem).2

theorem thetaDiracResolventY_mem_adjoint_domain (p : D) :
    thetaDiracResolventY p ∈ thetaWeightedDerivative.adjoint.domain := by
  let h : H := p.ofLp.1 + Complex.I • thetaDiracResolventX p
  obtain ⟨hBdom, _⟩ := closedHyperplaneInverse_adjoint_apply_adjoint
    thetaCentered thetaCenteredSourceInverse thetaCenteredSourceInverse_injective
      thetaCenteredSourceInverse_dense_range h
  have hOdom := thetaOrthogonalProjection_mem_adjoint_domain p.ofLp.2
  rw [thetaDiracResolventY_eq]
  exact Submodule.add_mem _ hBdom (Submodule.smul_mem _ Complex.I hOdom)

theorem thetaWeightedDerivative_adjoint_apply_thetaDiracResolventY
    (p : D) (hp : thetaDiracResolventY p ∈ thetaWeightedDerivative.adjoint.domain) :
    thetaWeightedDerivative.adjoint ⟨thetaDiracResolventY p, hp⟩ =
      p.ofLp.1 + Complex.I • thetaDiracResolventX p := by
  let h : H := p.ofLp.1 + Complex.I • thetaDiracResolventX p
  obtain ⟨hBdom, hBapply⟩ := closedHyperplaneInverse_adjoint_apply_adjoint
    thetaCentered thetaCenteredSourceInverse thetaCenteredSourceInverse_injective
      thetaCenteredSourceInverse_dense_range h
  have hOdom := thetaOrthogonalProjection_mem_adjoint_domain p.ofLp.2
  have hOapply := thetaWeightedDerivative_adjoint_apply_orthogonalProjection
    p.ofLp.2 hOdom
  let yB : thetaWeightedDerivative.adjoint.domain :=
    ⟨(thetaCenteredSourceInverse.adjoint h : thetaCentered), hBdom⟩
  let yO : thetaWeightedDerivative.adjoint.domain :=
    ⟨thetaCenteredᗮ.starProjection p.ofLp.2, hOdom⟩
  have hBapply' : thetaWeightedDerivative.adjoint yB = h := by
    change (closedHyperplaneInverse thetaCentered
      thetaCenteredSourceInverse).adjoint
        ⟨(thetaCenteredSourceInverse.adjoint h : thetaCentered), hBdom⟩ = h
    exact hBapply
  have hsum : ⟨thetaDiracResolventY p, hp⟩ = yB + Complex.I • yO := by
    apply Subtype.ext
    exact thetaDiracResolventY_eq p
  rw [hsum, LinearPMap.map_add, LinearPMap.map_smul, hBapply', hOapply, smul_zero,
    add_zero]

theorem thetaCentered_projection_add_orthogonal (g : H) :
    (thetaCentered.orthogonalProjectionOnto g : H) +
      thetaCenteredᗮ.starProjection g = g := by
  exact thetaCentered.starProjection_add_starProjection_orthogonal g

theorem thetaDiracResolventK_balance (p : D) :
    (thetaDiracResolventK p : H) +
        (thetaCenteredSourceInverse.adjoint (thetaDiracResolventX p) : H) =
      (thetaCentered.orthogonalProjectionOnto p.ofLp.2 : H) +
        Complex.I • (thetaCenteredSourceInverse.adjoint p.ofLp.1 : H) := by
  have h := congrArg (fun k : thetaCentered => (k : H))
    (thetaDiracResolventK_gram p)
  simpa only [thetaDiracGram, add_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply, thetaDiracResolventX_eq,
    Submodule.coe_add, Submodule.coe_smul_of_tower] using h

theorem thetaSupersymmetricDiracResolventAtI_firstEquation
    (p : D) (hp : thetaDiracResolventY p ∈ thetaWeightedDerivative.adjoint.domain) :
    thetaWeightedDerivative.adjoint ⟨thetaDiracResolventY p, hp⟩ -
      Complex.I • thetaDiracResolventX p = p.ofLp.1 := by
  rw [thetaWeightedDerivative_adjoint_apply_thetaDiracResolventY p hp]
  abel

theorem thetaSupersymmetricDiracResolventAtI_secondEquation
    (p : D) (hp : thetaDiracResolventX p ∈ thetaWeightedDerivative.domain) :
    thetaWeightedDerivative ⟨thetaDiracResolventX p, hp⟩ -
      Complex.I • thetaDiracResolventY p = p.ofLp.2 := by
  rw [thetaWeightedDerivative_apply_thetaDiracResolventX p hp,
    thetaDiracResolventY_eq, map_add, map_smul]
  have hbalance := thetaDiracResolventK_balance p
  have hprojection := thetaCentered_projection_add_orthogonal p.ofLp.2
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, smul_add, smul_smul,
    Complex.I_mul_I, neg_one_smul]
  trace_state
  exact hprojection

end HedenmalmClosedWeightedDerivative

end

end RHTower
