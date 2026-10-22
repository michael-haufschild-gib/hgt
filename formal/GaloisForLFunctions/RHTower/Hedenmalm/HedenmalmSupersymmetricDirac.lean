import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmShiftedSourceEquationExact
import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import GaloisForLFunctions.HTGeometry.CompactAdjoint
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

local instance hedenmalmSupersymmetricDiracLocalInst1 : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance hedenmalmSupersymmetricDiracLocalInst2 : CompleteSpace thetaCentered := thetaCentered_isClosed.completeSpace_coe

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
  exact add_sub_cancel_right p.ofLp.1 (Complex.I • thetaDiracResolventX p)

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
  have hcenter :
      ((thetaDiracResolventK p : H) +
          (thetaCenteredSourceInverse.adjoint (thetaDiracResolventX p) : H)) -
        Complex.I • (thetaCenteredSourceInverse.adjoint p.ofLp.1 : H) =
      (thetaCentered.orthogonalProjectionOnto p.ofLp.2 : H) :=
    sub_eq_iff_eq_add.mpr hbalance
  calc
    (thetaDiracResolventK p : H) -
        (Complex.I • (thetaCenteredSourceInverse.adjoint p.ofLp.1 : H) +
            -(thetaCenteredSourceInverse.adjoint (thetaDiracResolventX p) : H) +
          -thetaCenteredᗮ.starProjection p.ofLp.2) =
      (((thetaDiracResolventK p : H) +
          (thetaCenteredSourceInverse.adjoint (thetaDiracResolventX p) : H)) -
        Complex.I • (thetaCenteredSourceInverse.adjoint p.ofLp.1 : H)) +
          thetaCenteredᗮ.starProjection p.ofLp.2 := by
            simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
            ac_rfl
    _ = (thetaCentered.orthogonalProjectionOnto p.ofLp.2 : H) +
        thetaCenteredᗮ.starProjection p.ofLp.2 := by rw [hcenter]
    _ = p.ofLp.2 := hprojection

theorem thetaSupersymmetricDiracResolventAtI_mem_domain (p : D) :
    thetaSupersymmetricDiracResolventAtI p ∈ thetaSupersymmetricDirac.domain := by
  exact ⟨thetaDiracResolventX_mem_domain p,
    thetaDiracResolventY_mem_adjoint_domain p⟩

theorem thetaSupersymmetricDiracResolventAtI_rightInverse (p : D) :
    thetaSupersymmetricDirac
        ⟨thetaSupersymmetricDiracResolventAtI p,
          thetaSupersymmetricDiracResolventAtI_mem_domain p⟩ -
      Complex.I • thetaSupersymmetricDiracResolventAtI p = p := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H H).injective
  apply Prod.ext
  · exact thetaSupersymmetricDiracResolventAtI_firstEquation p
      (thetaDiracResolventY_mem_adjoint_domain p)
  · exact thetaSupersymmetricDiracResolventAtI_secondEquation p
      (thetaDiracResolventX_mem_domain p)

/-! ### Symmetry and injectivity of the nonreal shift -/

theorem thetaSupersymmetricDirac_isFormalSelfAdjoint :
    thetaSupersymmetricDirac.IsFormalAdjoint thetaSupersymmetricDirac := by
  intro x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change inner ℂ
      (thetaWeightedDerivative.adjoint ⟨x.1.ofLp.2, x.2.2⟩)
        y.1.ofLp.1 +
      inner ℂ (thetaWeightedDerivative ⟨x.1.ofLp.1, x.2.1⟩)
        y.1.ofLp.2 =
    inner ℂ x.1.ofLp.1
        (thetaWeightedDerivative.adjoint ⟨y.1.ofLp.2, y.2.2⟩) +
      inner ℂ x.1.ofLp.2
        (thetaWeightedDerivative ⟨y.1.ofLp.1, y.2.1⟩)
  have hformal := LinearPMap.adjoint_isFormalAdjoint
    thetaWeightedDerivative_dense_domain
  rw [hformal ⟨x.1.ofLp.2, x.2.2⟩ ⟨y.1.ofLp.1, y.2.1⟩,
    hformal.symm ⟨x.1.ofLp.1, x.2.1⟩ ⟨y.1.ofLp.2, y.2.2⟩]
  exact add_comm _ _

theorem thetaSupersymmetricDirac_sub_I_eq_zero
    (x : thetaSupersymmetricDirac.domain)
    (hx : thetaSupersymmetricDirac x - Complex.I • (x : D) = 0) :
    (x : D) = 0 := by
  have hQ : thetaSupersymmetricDirac x = Complex.I • (x : D) :=
    sub_eq_zero.mp hx
  have hformal := thetaSupersymmetricDirac_isFormalSelfAdjoint x x
  rw [hQ] at hformal
  have him := congrArg Complex.im hformal
  simp only [inner_smul_left, inner_smul_right, Complex.conj_I] at him
  simp [Complex.mul_im] at him
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at him
  have hnorm : ‖(x : D)‖ = 0 := by nlinarith [norm_nonneg (x : D)]
  exact norm_eq_zero.mp hnorm

theorem thetaSupersymmetricDirac_sub_I_injective :
    Function.Injective (fun x : thetaSupersymmetricDirac.domain =>
      thetaSupersymmetricDirac x - Complex.I • (x : D)) := by
  intro x y hxy
  have hzero :
      thetaSupersymmetricDirac (x - y) - Complex.I • ((x - y :
        thetaSupersymmetricDirac.domain) : D) = 0 := by
    calc
      thetaSupersymmetricDirac (x - y) - Complex.I • ((x - y :
          thetaSupersymmetricDirac.domain) : D) =
        (thetaSupersymmetricDirac x - Complex.I • (x : D)) -
          (thetaSupersymmetricDirac y - Complex.I • (y : D)) := by
            rw [LinearPMap.map_sub, Submodule.coe_sub, smul_sub]
            abel
      _ = 0 := sub_eq_zero.mpr hxy
  have hsub := thetaSupersymmetricDirac_sub_I_eq_zero (x - y) hzero
  apply Subtype.ext
  exact sub_eq_zero.mp hsub

theorem thetaSupersymmetricDiracResolventAtI_leftInverse
    (x : thetaSupersymmetricDirac.domain) :
    thetaSupersymmetricDiracResolventAtI
        (thetaSupersymmetricDirac x - Complex.I • (x : D)) = (x : D) := by
  let p : D := thetaSupersymmetricDirac x - Complex.I • (x : D)
  let y : thetaSupersymmetricDirac.domain :=
    ⟨thetaSupersymmetricDiracResolventAtI p,
      thetaSupersymmetricDiracResolventAtI_mem_domain p⟩
  have hyx : y = x := thetaSupersymmetricDirac_sub_I_injective
    (thetaSupersymmetricDiracResolventAtI_rightInverse p)
  exact congrArg Subtype.val hyx

/-! ### Compactness of the explicit resolvent -/

theorem thetaDiracResolventX_compact :
    IsCompactOperator thetaDiracResolventX := by
  have hB : IsCompactOperator thetaCenteredSourceInverse :=
    isCompactOperator_thetaCompactSourceInverse.comp_clm thetaCentered.subtypeL
  exact hB.comp_clm thetaDiracResolventK

theorem thetaDiracResolventY_compact :
    IsCompactOperator thetaDiracResolventY := by
  have hB : IsCompactOperator thetaCenteredSourceInverse :=
    isCompactOperator_thetaCompactSourceInverse.comp_clm thetaCentered.subtypeL
  have hBadj : IsCompactOperator thetaCenteredSourceInverse.adjoint :=
    isCompactOperator_adjoint_rectangular thetaCenteredSourceInverse hB
  have hmain : IsCompactOperator
      (thetaCentered.subtypeL.comp
        (thetaCenteredSourceInverse.adjoint.comp
          (thetaDiracFst + Complex.I • thetaDiracResolventX))) :=
    (hBadj.comp_clm
      (thetaDiracFst + Complex.I • thetaDiracResolventX)).clm_comp
        thetaCentered.subtypeL
  have hline : thetaCenteredᗮ = ℂ ∙ pinnedOne := by
    have hker : thetaWeightedDerivative.adjoint.kernel = thetaCenteredᗮ :=
      closedHyperplaneInverse_adjoint_kernel thetaCentered thetaCenteredSourceInverse
        thetaCenteredSourceInverse_injective thetaCenteredSourceInverse_dense_range
    exact hker.symm.trans thetaWeightedDerivative_adjoint_kernel
  letI : FiniteDimensional ℂ thetaCenteredᗮ := by
    rw [hline]
    infer_instance
  have horth : IsCompactOperator
      (Complex.I • (thetaCenteredᗮ.starProjection.comp thetaDiracSnd)) :=
    (isCompactOperator_starProjection_finiteDimensional thetaCenteredᗮ).comp_clm
      thetaDiracSnd |>.smul Complex.I
  exact hmain.add horth

private theorem isCompactOperator_prod_of_compact
    {E F G : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [TopologicalSpace F] [AddCommMonoid F] [ContinuousAdd F]
    [TopologicalSpace G] [AddCommMonoid G] [ContinuousAdd G]
    [Module ℂ E] [Module ℂ F] [Module ℂ G]
    (f : E →L[ℂ] F) (g : E →L[ℂ] G)
    (hf : IsCompactOperator f) (hg : IsCompactOperator g) :
    IsCompactOperator (f.prod g) := by
  have hf' := hf.clm_comp (ContinuousLinearMap.inl ℂ F G)
  have hg' := hg.clm_comp (ContinuousLinearMap.inr ℂ F G)
  convert hf'.add hg' using 1
  funext x
  simp only [ContinuousLinearMap.prod_apply, Function.comp_apply, Pi.add_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
    add_zero, zero_add]

theorem thetaSupersymmetricDiracResolventAtI_compact :
    IsCompactOperator thetaSupersymmetricDiracResolventAtI := by
  have hpair : IsCompactOperator
      (thetaDiracResolventX.prod thetaDiracResolventY) :=
    isCompactOperator_prod_of_compact thetaDiracResolventX thetaDiracResolventY
      thetaDiracResolventX_compact thetaDiracResolventY_compact
  exact hpair.clm_comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap

theorem thetaSupersymmetricDirac_hasCompactResolventAt_I :
    LinearPMap.HasCompactResolventAt thetaSupersymmetricDirac Complex.I := by
  exact ⟨thetaSupersymmetricDiracResolventAtI,
    thetaSupersymmetricDiracResolventAtI_compact,
    ⟨thetaSupersymmetricDiracResolventAtI_mem_domain,
      thetaSupersymmetricDiracResolventAtI_rightInverse⟩,
    thetaSupersymmetricDiracResolventAtI_leftInverse⟩

/-! ### Opposite nonreal shift and self-adjointness -/

theorem thetaSupersymmetricDirac_add_I_surjective (p : D) :
    ∃ x : thetaSupersymmetricDirac.domain,
      thetaSupersymmetricDirac x + Complex.I • (x : D) = p := by
  let gp : D := WithLp.toLp 2 (p.ofLp.1, -p.ofLp.2)
  let u : thetaSupersymmetricDirac.domain :=
    ⟨thetaSupersymmetricDiracResolventAtI gp,
      thetaSupersymmetricDiracResolventAtI_mem_domain gp⟩
  let x : thetaSupersymmetricDirac.domain :=
    ⟨WithLp.toLp 2 (-u.1.ofLp.1, u.1.ofLp.2),
      ⟨Submodule.neg_mem _ u.2.1, u.2.2⟩⟩
  have hu := thetaSupersymmetricDiracResolventAtI_rightInverse gp
  change thetaSupersymmetricDirac u - Complex.I • (u : D) = gp at hu
  have hu1 := congrArg (fun z : D => z.ofLp.1) hu
  have hu2 := congrArg (fun z : D => z.ofLp.2) hu
  change thetaWeightedDerivative.adjoint ⟨u.1.ofLp.2, u.2.2⟩ -
      Complex.I • u.1.ofLp.1 = p.ofLp.1 at hu1
  change thetaWeightedDerivative ⟨u.1.ofLp.1, u.2.1⟩ -
      Complex.I • u.1.ofLp.2 = -p.ofLp.2 at hu2
  refine ⟨x, ?_⟩
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H H).injective
  apply Prod.ext
  · change thetaWeightedDerivative.adjoint ⟨u.1.ofLp.2, u.2.2⟩ +
      Complex.I • (-u.1.ofLp.1) = p.ofLp.1
    simpa only [smul_neg, sub_eq_add_neg] using hu1
  · have hneg := congrArg Neg.neg hu2
    simp only [neg_sub, neg_neg] at hneg
    have hmapneg :
        thetaWeightedDerivative
            ⟨-u.1.ofLp.1, Submodule.neg_mem _ u.2.1⟩ =
          -thetaWeightedDerivative ⟨u.1.ofLp.1, u.2.1⟩ := by
      exact LinearPMap.map_neg thetaWeightedDerivative
        ⟨u.1.ofLp.1, u.2.1⟩
    change thetaWeightedDerivative ⟨-u.1.ofLp.1, Submodule.neg_mem _ u.2.1⟩ +
      Complex.I • u.1.ofLp.2 = p.ofLp.2
    rw [hmapneg]
    calc
      -thetaWeightedDerivative ⟨u.1.ofLp.1, u.2.1⟩ +
          Complex.I • u.1.ofLp.2 =
        Complex.I • u.1.ofLp.2 +
          -thetaWeightedDerivative ⟨u.1.ofLp.1, u.2.1⟩ := add_comm _ _
      _ = p.ofLp.2 := by simpa only [sub_eq_add_neg] using hneg

theorem thetaSupersymmetricDirac_dense_domain :
    Dense (thetaSupersymmetricDirac.domain : Set D) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.eq_bot_iff]
  intro z hz
  rw [Submodule.mem_orthogonal'] at hz
  let x : thetaSupersymmetricDirac.domain :=
    ⟨thetaSupersymmetricDiracResolventAtI z,
      thetaSupersymmetricDiracResolventAtI_mem_domain z⟩
  have hzinner : inner ℂ z (x : D) = 0 :=
    hz (x : D) (subset_closure x.property)
  have hshift := thetaSupersymmetricDiracResolventAtI_rightInverse z
  change thetaSupersymmetricDirac x - Complex.I • (x : D) = z at hshift
  have hzero : inner ℂ
      (thetaSupersymmetricDirac x - Complex.I • (x : D)) (x : D) = 0 := by
    rw [hshift]
    exact hzinner
  have hformal := thetaSupersymmetricDirac_isFormalSelfAdjoint x x
  have hconj : (starRingEnd ℂ) (inner ℂ (thetaSupersymmetricDirac x) (x : D)) =
      inner ℂ (thetaSupersymmetricDirac x) (x : D) := by
    calc
      (starRingEnd ℂ) (inner ℂ (thetaSupersymmetricDirac x) (x : D)) =
          inner ℂ (x : D) (thetaSupersymmetricDirac x) :=
        inner_conj_symm _ _
      _ = inner ℂ (thetaSupersymmetricDirac x) (x : D) := hformal.symm
  have hQim : (inner ℂ (thetaSupersymmetricDirac x) (x : D)).im = 0 :=
    Complex.conj_eq_iff_im.mp hconj
  have him := congrArg Complex.im hzero
  rw [inner_sub_left, Complex.sub_im, hQim, Complex.zero_im, zero_sub] at him
  simp only [inner_smul_left, Complex.conj_I] at him
  simp [Complex.mul_im] at him
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at him
  have hnorm : ‖(x : D)‖ = 0 := by nlinarith [norm_nonneg (x : D)]
  have hxD : (x : D) = 0 := norm_eq_zero.mp hnorm
  have hx : x = 0 := Subtype.ext hxD
  rw [← hshift, hx, LinearPMap.map_zero, Submodule.coe_zero, smul_zero, sub_zero]

private theorem thetaSupersymmetricDirac_adjoint_mem_domain
    (y : D) (hy : y ∈ thetaSupersymmetricDirac.adjoint.domain) :
    y ∈ thetaSupersymmetricDirac.domain := by
  have hle : thetaSupersymmetricDirac ≤ thetaSupersymmetricDirac.adjoint :=
    thetaSupersymmetricDirac_isFormalSelfAdjoint.le_adjoint
      thetaSupersymmetricDirac_dense_domain
  let yAdj : thetaSupersymmetricDirac.adjoint.domain := ⟨y, hy⟩
  let w : D := thetaSupersymmetricDirac.adjoint yAdj
  let p : D := w - Complex.I • y
  let x : thetaSupersymmetricDirac.domain :=
    ⟨thetaSupersymmetricDiracResolventAtI p,
      thetaSupersymmetricDiracResolventAtI_mem_domain p⟩
  have hshift := thetaSupersymmetricDiracResolventAtI_rightInverse p
  change thetaSupersymmetricDirac x - Complex.I • (x : D) =
    w - Complex.I • y at hshift
  have hxAdjMem : (x : D) ∈ thetaSupersymmetricDirac.adjoint.domain :=
    hle.1 x.property
  let xAdj : thetaSupersymmetricDirac.adjoint.domain := ⟨(x : D), hxAdjMem⟩
  have hAdjx : thetaSupersymmetricDirac.adjoint xAdj =
      thetaSupersymmetricDirac x := (hle.2 rfl).symm
  have hdAdjMem : y - (x : D) ∈ thetaSupersymmetricDirac.adjoint.domain :=
    Submodule.sub_mem _ hy hxAdjMem
  let dAdj : thetaSupersymmetricDirac.adjoint.domain :=
    ⟨y - (x : D), hdAdjMem⟩
  have hmove : w - thetaSupersymmetricDirac x =
      Complex.I • (y - (x : D)) := by
    rw [smul_sub, sub_eq_sub_iff_add_eq_add]
    have hadd := sub_eq_sub_iff_add_eq_add.mp hshift
    calc
      w + Complex.I • (x : D) =
          thetaSupersymmetricDirac x + Complex.I • y := hadd.symm
      _ = Complex.I • y + thetaSupersymmetricDirac x := add_comm _ _
  have hAdjd : thetaSupersymmetricDirac.adjoint dAdj =
      Complex.I • (y - (x : D)) := by
    calc
      thetaSupersymmetricDirac.adjoint dAdj =
          thetaSupersymmetricDirac.adjoint yAdj -
            thetaSupersymmetricDirac.adjoint xAdj := by
        exact LinearPMap.map_sub thetaSupersymmetricDirac.adjoint yAdj xAdj
      _ = w - thetaSupersymmetricDirac x := by rw [hAdjx]
      _ = Complex.I • (y - (x : D)) := hmove
  obtain ⟨t, ht⟩ := thetaSupersymmetricDirac_add_I_surjective (y - (x : D))
  have hformal := LinearPMap.adjoint_isFormalAdjoint
    thetaSupersymmetricDirac_dense_domain dAdj t
  have hdinner : inner ℂ (y - (x : D)) (y - (x : D)) = 0 := by
    calc
      inner ℂ (y - (x : D)) (y - (x : D)) =
          inner ℂ (y - (x : D))
            (thetaSupersymmetricDirac t + Complex.I • (t : D)) :=
        congrArg (inner ℂ (y - (x : D))) ht.symm
      _ = inner ℂ (y - (x : D)) (thetaSupersymmetricDirac t) +
          inner ℂ (y - (x : D)) (Complex.I • (t : D)) :=
        inner_add_right _ _ _
      _ = inner ℂ (thetaSupersymmetricDirac.adjoint dAdj) (t : D) +
          inner ℂ (y - (x : D)) (Complex.I • (t : D)) := by
        rw [hformal]
      _ = inner ℂ (Complex.I • (y - (x : D))) (t : D) +
          inner ℂ (y - (x : D)) (Complex.I • (t : D)) := by rw [hAdjd]
      _ = 0 := by
        rw [inner_smul_left, inner_smul_right, Complex.conj_I]
        ring
  have hd : y - (x : D) = 0 := inner_self_eq_zero.mp hdinner
  have hyx : y = (x : D) := sub_eq_zero.mp hd
  exact hyx.symm ▸ x.property

theorem thetaSupersymmetricDirac_isSelfAdjoint :
    IsSelfAdjoint thetaSupersymmetricDirac := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hle : thetaSupersymmetricDirac ≤ thetaSupersymmetricDirac.adjoint :=
    thetaSupersymmetricDirac_isFormalSelfAdjoint.le_adjoint
      thetaSupersymmetricDirac_dense_domain
  apply le_antisymm
  · refine ⟨thetaSupersymmetricDirac_adjoint_mem_domain, ?_⟩
    intro y x hyx
    exact (hle.2 hyx.symm).symm
  · exact hle

/-! ### Fredholm and supersymmetric indices -/

/-- Odd copy of the normalized constant vector, generating the Dirac kernel. -/
def thetaSupersymmetricPinnedOne : D := WithLp.toLp 2 (0, pinnedOne)

theorem thetaSupersymmetricPinnedOne_ne_zero : thetaSupersymmetricPinnedOne ≠ 0 := by
  intro h
  have h2 := congrArg (fun z : D => z.ofLp.2) h
  exact pinnedOne_ne_zero (by
    simpa only [thetaSupersymmetricPinnedOne, WithLp.ofLp_toLp,
      WithLp.ofLp_zero, Prod.snd_zero] using h2)

/-- Bounded functional cutting out the range of the supersymmetric Dirac operator. -/
def thetaSupersymmetricPinnedMeanCLM : D →L[ℂ] ℂ :=
  thetaPinnedMeanCLM.comp thetaDiracSnd

theorem thetaSupersymmetricPinnedMeanCLM_apply (p : D) :
    thetaSupersymmetricPinnedMeanCLM p = pinnedMean p.ofLp.2 := by
  exact thetaPinnedMeanCLM_apply p.ofLp.2

theorem thetaSupersymmetricPinnedMeanCLM_surjective :
    Function.Surjective thetaSupersymmetricPinnedMeanCLM := by
  intro c
  obtain ⟨g, hg⟩ := thetaPinnedMeanCLM_surjective c
  exact ⟨WithLp.toLp 2 (0, g), hg⟩

theorem thetaSupersymmetricPinnedMeanCLM_eq_inner (p : D) :
    thetaSupersymmetricPinnedMeanCLM p =
      inner ℂ thetaSupersymmetricPinnedOne p := by
  rw [thetaSupersymmetricPinnedMeanCLM_apply, thetaSupersymmetricPinnedOne,
    WithLp.prod_inner_apply]
  simp only [inner_zero_left, zero_add]
  change pinnedMean p.ofLp.2 = inner ℂ pinnedOne p.ofLp.2
  exact (thetaPinnedMeanCLM_apply p.ofLp.2).symm

theorem thetaSupersymmetricDirac_range_eq_ker_pinnedMean :
    thetaSupersymmetricDirac.rangeSubmodule =
      LinearMap.ker thetaSupersymmetricPinnedMeanCLM.toLinearMap := by
  ext p
  constructor
  · rintro ⟨x, hx⟩
    rw [LinearMap.mem_ker]
    have hcenter : thetaWeightedDerivative
        ⟨x.1.ofLp.1, x.2.1⟩ ∈ thetaCentered := by
      rw [← thetaWeightedDerivative_range]
      exact ⟨⟨x.1.ofLp.1, x.2.1⟩, rfl⟩
    change thetaPinnedMeanCLM p.ofLp.2 = 0
    rw [← hx]
    rw [thetaPinnedMeanCLM_apply]
    exact (mem_thetaCentered_iff _).mp hcenter
  · intro hp
    rw [LinearMap.mem_ker] at hp
    have hpmean : pinnedMean p.ofLp.2 = 0 := by
      change thetaSupersymmetricPinnedMeanCLM p = 0 at hp
      simpa only [thetaSupersymmetricPinnedMeanCLM_apply] using hp
    have hpcenter : p.ofLp.2 ∈ thetaCentered :=
      (mem_thetaCentered_iff p.ofLp.2).mpr hpmean
    have hpRange : p.ofLp.2 ∈ thetaWeightedDerivative.rangeSubmodule := by
      rw [thetaWeightedDerivative_range]
      exact hpcenter
    obtain ⟨u, hu⟩ := LinearPMap.mem_rangeSubmodule_iff.mp hpRange
    obtain ⟨hyDom, hyApply⟩ := closedHyperplaneInverse_adjoint_apply_adjoint
      thetaCentered thetaCenteredSourceInverse thetaCenteredSourceInverse_injective
        thetaCenteredSourceInverse_dense_range p.ofLp.1
    let x : thetaSupersymmetricDirac.domain :=
      ⟨WithLp.toLp 2 ((u : H),
          (thetaCenteredSourceInverse.adjoint p.ofLp.1 : H)), ⟨u.2, hyDom⟩⟩
    refine ⟨x, ?_⟩
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ H H).injective
    apply Prod.ext
    · exact hyApply
    · exact hu

theorem thetaSupersymmetricDirac_range :
    thetaSupersymmetricDirac.rangeSubmodule =
      (ℂ ∙ thetaSupersymmetricPinnedOne)ᗮ := by
  rw [thetaSupersymmetricDirac_range_eq_ker_pinnedMean]
  ext p
  rw [LinearMap.mem_ker, Submodule.mem_orthogonal_singleton_iff_inner_right]
  change thetaSupersymmetricPinnedMeanCLM p = 0 ↔
    inner ℂ thetaSupersymmetricPinnedOne p = 0
  rw [thetaSupersymmetricPinnedMeanCLM_eq_inner]

theorem thetaSupersymmetricDirac_kernel :
    thetaSupersymmetricDirac.kernel =
      ℂ ∙ thetaSupersymmetricPinnedOne := by
  have hself : thetaSupersymmetricDirac.adjoint = thetaSupersymmetricDirac :=
    LinearPMap.isSelfAdjoint_def.mp thetaSupersymmetricDirac_isSelfAdjoint
  calc
    thetaSupersymmetricDirac.kernel =
        thetaSupersymmetricDirac.adjoint.kernel :=
      congrArg (fun T : D →ₗ.[ℂ] D => T.kernel) hself.symm
    _ = thetaSupersymmetricDirac.rangeSubmoduleᗮ :=
      LinearPMap.adjoint_kernel_eq_orthogonal_range
        thetaSupersymmetricDirac thetaSupersymmetricDirac_dense_domain
    _ = ((ℂ ∙ thetaSupersymmetricPinnedOne)ᗮ)ᗮ := by
      rw [thetaSupersymmetricDirac_range]
    _ = ℂ ∙ thetaSupersymmetricPinnedOne := by
      rw [Submodule.orthogonal_orthogonal]

theorem thetaSupersymmetricDirac_isFredholm :
    thetaSupersymmetricDirac.IsFredholm where
  finiteDimensional_kernel := by
    rw [thetaSupersymmetricDirac_kernel]
    infer_instance
  isClosed_range := by
    rw [thetaSupersymmetricDirac_range]
    exact Submodule.isClosed_orthogonal _
  finiteDimensional_cokernel :=
    ((Submodule.quotEquivOfEq _ _
      thetaSupersymmetricDirac_range_eq_ker_pinnedMean).trans
        (thetaSupersymmetricPinnedMeanCLM.toLinearMap.quotKerEquivOfSurjective
          thetaSupersymmetricPinnedMeanCLM_surjective)).symm.finiteDimensional

theorem thetaSupersymmetricDirac_index :
    thetaSupersymmetricDirac.index = 0 := by
  rw [LinearPMap.index_eq, thetaSupersymmetricDirac_kernel,
    finrank_span_singleton thetaSupersymmetricPinnedOne_ne_zero,
    LinearPMap.finrank_quotient_eq_one_of_eq_ker
      thetaSupersymmetricPinnedMeanCLM_surjective
      thetaSupersymmetricDirac_range_eq_ker_pinnedMean]
  norm_num

/-- Supersymmetric/Witten index of the odd Hedenmalm differential. -/
def thetaSupersymmetricWittenIndex : ℤ := thetaWeightedDerivative.index

theorem thetaSupersymmetricWittenIndex_eq_neg_one :
    thetaSupersymmetricWittenIndex = -1 := thetaWeightedDerivative_index

end HedenmalmClosedWeightedDerivative

end

end RHTower
