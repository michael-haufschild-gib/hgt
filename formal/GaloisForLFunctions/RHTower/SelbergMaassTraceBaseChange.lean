import GaloisForLFunctions.RHTower.SelbergMaassRationalConjugateTrace

/-!
# Rational pullback commutes with finite Maass trace

Conjugation by a rational matrix explicitly identifies relative-coset quotients.
Under this identification, every summand in a finite Maass trace is carried to
the corresponding summand after rational pullback.  Consequently rational
pullback commutes exactly with finite trace; this is the base-change identity
needed to calculate compositions of rational double-coset operators.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- Conjugation by a rational matrix identifies a subgroup with its rational
pullback-conjugate. -/
def maassConjugateSubgroupEquiv (Γ : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℚ) :
    Γ ≃* rationalPullbackConjugateGroup Γ g where
  toFun x := ⟨(g.map (algebraMap ℚ ℝ))⁻¹ * x.val * g.map (algebraMap ℚ ℝ), by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change g.map (algebraMap ℚ ℝ) *
        ((g.map (algebraMap ℚ ℝ))⁻¹ * x.val * g.map (algebraMap ℚ ℝ)) *
        (g.map (algebraMap ℚ ℝ))⁻¹ ∈ Γ
    have hcancel : g.map (algebraMap ℚ ℝ) *
        ((g.map (algebraMap ℚ ℝ))⁻¹ * x.val * g.map (algebraMap ℚ ℝ)) *
        (g.map (algebraMap ℚ ℝ))⁻¹ = x.val := by
      group
    rw [hcancel]
    exact x.2⟩
  invFun y := ⟨g.map (algebraMap ℚ ℝ) * y.val * (g.map (algebraMap ℚ ℝ))⁻¹, by
    have hy := y.2
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa only [ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul] using hy⟩
  left_inv x := by
    apply Subtype.ext
    group
  right_inv y := by
    apply Subtype.ext
    group
  map_mul' x y := by
    apply Subtype.ext
    change (g.map (algebraMap ℚ ℝ))⁻¹ * (x.val * y.val) * g.map (algebraMap ℚ ℝ) =
      ((g.map (algebraMap ℚ ℝ))⁻¹ * x.val * g.map (algebraMap ℚ ℝ)) *
        ((g.map (algebraMap ℚ ℝ))⁻¹ * y.val * g.map (algebraMap ℚ ℝ))
    group

/-- Conjugation identifies the relative-coset quotients used by finite trace. -/
noncomputable def maassConjugateRelativeCosetEquiv
    (Γ H : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℚ) :
    H ⧸ (Γ.subgroupOf H) ≃
      rationalPullbackConjugateGroup H g ⧸
        ((rationalPullbackConjugateGroup Γ g).subgroupOf
          (rationalPullbackConjugateGroup H g)) :=
  Quotient.congr (maassConjugateSubgroupEquiv H g).toEquiv (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    change x.val⁻¹ * y.val ∈ Γ ↔ _
    constructor
    · intro hxy
      change ((maassConjugateSubgroupEquiv H g x)⁻¹ *
        maassConjugateSubgroupEquiv H g y).val ∈ rationalPullbackConjugateGroup Γ g
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      change g.map (algebraMap ℚ ℝ) *
          ((maassConjugateSubgroupEquiv H g x)⁻¹ *
            maassConjugateSubgroupEquiv H g y).val *
          (g.map (algebraMap ℚ ℝ))⁻¹ ∈ Γ
      change g.map (algebraMap ℚ ℝ) *
          (((g.map (algebraMap ℚ ℝ))⁻¹ * x.val * g.map (algebraMap ℚ ℝ))⁻¹ *
            ((g.map (algebraMap ℚ ℝ))⁻¹ * y.val * g.map (algebraMap ℚ ℝ))) *
          (g.map (algebraMap ℚ ℝ))⁻¹ ∈ Γ
      have hcancel : g.map (algebraMap ℚ ℝ) *
          (((g.map (algebraMap ℚ ℝ))⁻¹ * x.val * g.map (algebraMap ℚ ℝ))⁻¹ *
            ((g.map (algebraMap ℚ ℝ))⁻¹ * y.val * g.map (algebraMap ℚ ℝ))) *
          (g.map (algebraMap ℚ ℝ))⁻¹ = x.val⁻¹ * y.val := by
        group
      rw [hcancel]
      exact hxy
    · intro hxy
      change ((maassConjugateSubgroupEquiv H g x)⁻¹ *
        maassConjugateSubgroupEquiv H g y).val ∈ rationalPullbackConjugateGroup Γ g at hxy
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxy
      change g.map (algebraMap ℚ ℝ) *
          ((maassConjugateSubgroupEquiv H g x)⁻¹ *
            maassConjugateSubgroupEquiv H g y).val *
          (g.map (algebraMap ℚ ℝ))⁻¹ ∈ Γ at hxy
      change g.map (algebraMap ℚ ℝ) *
          (((g.map (algebraMap ℚ ℝ))⁻¹ * x.val * g.map (algebraMap ℚ ℝ))⁻¹ *
            ((g.map (algebraMap ℚ ℝ))⁻¹ * y.val * g.map (algebraMap ℚ ℝ))) *
          (g.map (algebraMap ℚ ℝ))⁻¹ ∈ Γ at hxy
      have hcancel : x.val⁻¹ * y.val = g.map (algebraMap ℚ ℝ) *
          (((g.map (algebraMap ℚ ℝ))⁻¹ * x.val * g.map (algebraMap ℚ ℝ))⁻¹ *
            ((g.map (algebraMap ℚ ℝ))⁻¹ * y.val * g.map (algebraMap ℚ ℝ))) *
          (g.map (algebraMap ℚ ℝ))⁻¹ := by
        group
      rw [hcancel]
      exact hxy)

/-- The relative-coset conjugation equivalence on a literal representative. -/
@[simp] theorem maassConjugateRelativeCosetEquiv_mk
    (Γ H : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℚ) (h : H) :
    maassConjugateRelativeCosetEquiv Γ H g (QuotientGroup.mk h) =
      QuotientGroup.mk (maassConjugateSubgroupEquiv H g h) :=
  rfl

/-- Rational pullback preserves finite relative index. -/
theorem rationalPullback_isFiniteRelIndex
    (Γ H : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℚ) [Γ.IsFiniteRelIndex H] :
    (rationalPullbackConjugateGroup Γ g).IsFiniteRelIndex
      (rationalPullbackConjugateGroup H g) := by
  letI : Finite (H ⧸ (Γ.subgroupOf H)) := inferInstance
  letI : Finite (rationalPullbackConjugateGroup H g ⧸
      ((rationalPullbackConjugateGroup Γ g).subgroupOf
        (rationalPullbackConjugateGroup H g))) :=
    Finite.of_equiv (H ⧸ (Γ.subgroupOf H))
      (maassConjugateRelativeCosetEquiv Γ H g)
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Rational pullback commutes exactly with finite trace. -/
theorem maassTrace_rationalPullback_baseChange
    (Γ H : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℚ)
    [Γ.IsFiniteRelIndex H] (f : glUpperHalfPlaneInvariantFunctions Γ) :
    letI : (rationalPullbackConjugateGroup Γ g).IsFiniteRelIndex
        (rationalPullbackConjugateGroup H g) := rationalPullback_isFiniteRelIndex Γ H g
    maassTraceFunction (H := rationalPullbackConjugateGroup H g)
      (rationalMaassPullbackInvariant_general Γ g f) =
      (rationalMaassPullbackInvariant_general H g
        (maassTraceInvariant (H := H) f)).1 := by
  letI : (rationalPullbackConjugateGroup Γ g).IsFiniteRelIndex
      (rationalPullbackConjugateGroup H g) := rationalPullback_isFiniteRelIndex Γ H g
  let e := maassConjugateRelativeCosetEquiv Γ H g
  letI : Fintype (H ⧸ (Γ.subgroupOf H)) := Fintype.ofFinite _
  letI : Fintype (rationalPullbackConjugateGroup H g ⧸
      ((rationalPullbackConjugateGroup Γ g).subgroupOf
        (rationalPullbackConjugateGroup H g))) := Fintype.ofFinite _
  funext z
  unfold maassTraceFunction
  rw [← Equiv.sum_comp e (fun q =>
    maassTraceQuotientFunc (rationalMaassPullbackInvariant_general Γ g f) q z)]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | h r =>
    simp only [maassTraceQuotientFunc_mk]
    change f.1 (g.map (algebraMap ℚ ℝ) •
      (((g.map (algebraMap ℚ ℝ))⁻¹ * r.val * g.map (algebraMap ℚ ℝ))⁻¹ • z)) =
      f.1 (r.val⁻¹ • (g.map (algebraMap ℚ ℝ) • z))
    rw [← mul_smul, ← mul_smul]
    group

end

end GaloisForLFunctions.RHTower
