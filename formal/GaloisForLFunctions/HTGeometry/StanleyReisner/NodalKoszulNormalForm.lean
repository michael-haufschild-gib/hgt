import GaloisForLFunctions.HTGeometry.KoszulCohomology
import Mathlib.Algebra.Polynomial.Div

/-!
# Normal forms for the nodal Koszul complex

Evaluation on the two coordinate axes identifies the nodal algebra with their
fiber product. The two branch coefficients give a complete invariant of first
Koszul homology.
-/

namespace GaloisForLFunctions
open Polynomial
open scoped Classical
noncomputable section
variable {F : Type*} [Field F]

local notation "Q" => NodalStanleyReisnerRing F
local notation "B" => nodalBoundarySubring F

private theorem quotient_xy : (nodalStanleyReisnerX : Q) * nodalStanleyReisnerY = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The canonical evaluation on the two axes as an algebra homomorphism. -/
def nodalAxesMap : Q →ₐ[F] B where
  __ := nodalStanleyReisnerBoundaryMap
  commutes' a := by
    change nodalBoundaryEvaluation (MvPolynomial.C a) = algebraMap F _ a
    simp [nodalBoundaryEvaluation]

private def glueAxes (u : B) : Q :=
  aeval nodalStanleyReisnerX u.val.1 + aeval nodalStanleyReisnerY u.val.2 -
    algebraMap F _ (u.val.1.coeff 0)

private theorem axes_zeroProduct {x y : Q} (hxy : x*y=0) (p : F[X]) :
    (aeval y p-algebraMap F _ (p.coeff 0))*x=0 := by
  have hh : X ∣ p-C (p.coeff 0) := X_dvd_iff.mpr (by simp)
  obtain ⟨q,hq⟩ := hh
  have h := congrArg (aeval y : F[X] →ₐ[F] Q) hq
  simp only [map_sub,aeval_C,map_mul,aeval_X] at h
  rw [h,mul_right_comm,mul_comm y x,hxy,zero_mul]

private theorem glue_x (u : B) : glueAxes (u*nodalBoundaryX) = glueAxes u*nodalStanleyReisnerX := by
  have h := axes_zeroProduct quotient_xy u.val.2
  have h₀ := u.property
  change u.val.1.coeff 0 = u.val.2.coeff 0 at h₀
  simp only [glueAxes,nodalBoundaryX,Subalgebra.coe_mul,Prod.fst_mul,Prod.snd_mul,mul_zero,map_zero,
    add_zero,map_mul,aeval_X,mul_coeff_zero,coeff_X_zero,sub_zero]
  rw [h₀]
  linear_combination -h

private theorem glue_y (u : B) : glueAxes (u*nodalBoundaryY) = glueAxes u*nodalStanleyReisnerY := by
  have h := axes_zeroProduct (mul_comm _ _ ▸ quotient_xy (F:=F)) u.val.1
  simp only [glueAxes,nodalBoundaryY,Subalgebra.coe_mul,Prod.fst_mul,Prod.snd_mul,mul_zero,map_zero,
    zero_add,map_mul,aeval_X,coeff_zero,sub_zero]
  linear_combination -h

private theorem axes_x : nodalAxesMap (nodalStanleyReisnerX : Q) = nodalBoundaryX :=
  nodalStanleyReisnerBoundaryMap_X

private theorem axes_y : nodalAxesMap (nodalStanleyReisnerY : Q) = nodalBoundaryY :=
  nodalStanleyReisnerBoundaryMap_Y

private theorem glue_add (u v : B) : glueAxes (u+v) = glueAxes u+glueAxes v := by
  simp only [glueAxes,Subalgebra.coe_add,Prod.fst_add,Prod.snd_add,coeff_add,map_add]
  ring

private theorem glue_left (v : Q) : glueAxes (nodalAxesMap v)=v := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective v
  induction p using MvPolynomial.induction_on with
  | C a =>
    change glueAxes (nodalAxesMap (algebraMap F Q a)) = algebraMap F Q a
    simp [glueAxes,AlgHom.commutes]
  | add p q hp hq =>
    rw [map_add,map_add,glue_add,hp,hq]
  | mul_X p i hp =>
    rw [map_mul,map_mul]
    fin_cases i
    · change glueAxes (_*nodalAxesMap nodalStanleyReisnerX) = _*nodalStanleyReisnerX
      rw [axes_x,glue_x,hp]
    · change glueAxes (_*nodalAxesMap nodalStanleyReisnerY) = _*nodalStanleyReisnerY
      rw [axes_y,glue_y,hp]

private theorem unpack_evaluation (v : Q) (h : Q →ₐ[F] F[X]) (p : F[X]) :
    h (aeval v p) = aeval (h v) p := (aeval_algHom_apply h v p).symm

private theorem glue_right (u : B) : nodalAxesMap (glueAxes u)=u := by
  let f := ((AlgHom.fst F (F[X]) (F[X])).comp (nodalBoundarySubring F).val).comp nodalAxesMap
  let g := ((AlgHom.snd F (F[X]) (F[X])).comp (nodalBoundarySubring F).val).comp nodalAxesMap
  have fx : f nodalStanleyReisnerX = X := congrArg (fun u : B => u.val.1) axes_x
  have fy : f nodalStanleyReisnerY = 0 := congrArg (fun u : B => u.val.1) axes_y
  have gx : g nodalStanleyReisnerX = 0 := congrArg (fun u : B => u.val.2) axes_x
  have gy : g nodalStanleyReisnerY = X := congrArg (fun u : B => u.val.2) axes_y
  apply Subtype.ext
  apply Prod.ext
  · change f (glueAxes u)=u.val.1
    rw [glueAxes,map_sub,map_add,unpack_evaluation,unpack_evaluation,fx,fy,
      aeval_X_left_apply,← coeff_zero_eq_aeval_zero',AlgHom.commutes]
    rw [show u.val.1.coeff 0 = u.val.2.coeff 0 from u.property,add_sub_cancel_right]
  · change g (glueAxes u)=u.val.2
    rw [glueAxes,map_sub,map_add,unpack_evaluation,unpack_evaluation,gx,gy,
      aeval_X_left_apply,← coeff_zero_eq_aeval_zero',AlgHom.commutes,add_sub_cancel_left]

/-- Exact fiber-product presentation of the actual nodal Stanley--Reisner
quotient. Its inverse glues univariate polynomials with the same constant term. -/
def nodalAxesEquiv : NodalStanleyReisnerRing F ≃ₐ[F] nodalBoundarySubring F :=
  AlgEquiv.ofBijective nodalAxesMap ⟨Function.LeftInverse.injective glue_left,Function.RightInverse.surjective glue_right⟩

/-- First Koszul homology coordinate in the two-axis model. -/
def nodalKoszulResidue (v : Fin 2 → B) : F := (v 0).val.2.coeff 1+(v 1).val.1.coeff 1

private theorem boundary_residue (c : B) : nodalKoszulResidue (nodalKoszulBoundary c) = 0 := by
  have hc : c.val.1.coeff 0=c.val.2.coeff 0 := c.property
  simp [nodalKoszulResidue,nodalKoszulBoundary,nodalBoundaryX,nodalBoundaryY,coeff_mul_X,hc]

private theorem boundary_inj : Function.Injective (nodalKoszulBoundary (F:=F)) := by
  intro c d h
  have h₁ := congrArg (fun z : B => z.val.1) (congrFun h 1)
  have h₂ := congrArg (fun z : B => z.val.2) (congrFun h 0)
  apply Subtype.ext
  apply Prod.ext
  · apply mul_right_cancel₀ (X_ne_zero (R:=F))
    simpa [nodalKoszulBoundary,nodalBoundaryX] using h₁
  · apply mul_right_cancel₀ (X_ne_zero (R:=F))
    simpa [nodalKoszulBoundary,nodalBoundaryY] using h₂

/-- A pair is a first cycle precisely when each entry lives on the opposite
axis and has vanishing constant term. Removing the coordinate factors
produces two unrestricted univariate polynomials. -/
theorem nodalKoszulRelation_iff (v : Fin 2 → B) : nodalKoszulRelation v = 0 ↔
    ∃ p q : F[X], (v 0).val = (0,p*X) ∧ (v 1).val = (q*X,0) := by
  constructor
  · intro h
    have h₁ := congrArg (fun z : B => z.val.1) h
    have h₂ := congrArg (fun z : B => z.val.2) h
    have hv₀ : (v 0).val.1=0 := by
      apply (mul_eq_zero.mp _).resolve_right X_ne_zero
      simpa [nodalKoszulRelation,nodalBoundaryX,nodalBoundaryY] using h₁
    have hv₁ : (v 1).val.2=0 := by
      apply (mul_eq_zero.mp _).resolve_right X_ne_zero
      simpa [nodalKoszulRelation,nodalBoundaryX,nodalBoundaryY] using h₂
    have h₀ : (v 0).val.2.coeff 0=0 := (v 0).property.symm.trans (by rw [hv₀]; simp)
    have h₁' : (v 1).val.1.coeff 0=0 := (v 1).property.trans (by rw [hv₁]; simp)
    obtain ⟨p,hp⟩ := X_dvd_iff.mpr h₀
    obtain ⟨q,hq⟩ := X_dvd_iff.mpr h₁'
    exact ⟨p,q,Prod.ext hv₀ (hp.trans (mul_comm _ _)),Prod.ext (hq.trans (mul_comm _ _)) hv₁⟩
  · rintro ⟨p,q,hp,hq⟩
    apply Subtype.ext
    apply Prod.ext <;> simp [nodalKoszulRelation,nodalBoundaryX,nodalBoundaryY,hp,hq]

private theorem residue_normal (c : B) (a : F) :
    nodalKoszulResidue (nodalKoszulBoundary c+a • nodalDisconnectCycle) = a := by
  have he : c.val.1.coeff 0 = c.val.2.coeff 0 := c.property
  simp [nodalKoszulResidue,nodalKoszulBoundary,nodalDisconnectCycle,nodalBoundaryX,nodalBoundaryY,
    Polynomial.coeff_mul_X,Polynomial.coeff_smul,he]

/-- Each cycle has a unique decomposition into an actual Koszul boundary
and a scalar multiple of the disconnected-vertex class. In particular
the degree-one quotient is exactly one-dimensional and degree two vanishes. -/
theorem nodalKoszul_normalForm (v : Fin 2 → B) :
    nodalKoszulRelation v = 0 ↔
      ∃! z : B × F, v = nodalKoszulBoundary z.1 + z.2 • nodalDisconnectCycle := by
  constructor
  · intro h
    obtain ⟨p,q,hp,hq⟩ := (nodalKoszulRelation_iff v).mp h
    let a := p.coeff 0+q.coeff 0
    let c : B := ⟨(q,C a-p),by change q.coeff 0=(C a-p).coeff 0; simp [a]⟩
    have he : v = nodalKoszulBoundary c + a • nodalDisconnectCycle := by
      funext i
      apply Subtype.ext
      fin_cases i
      · rw [hp]
        apply Prod.ext <;> simp [nodalKoszulBoundary,nodalDisconnectCycle,nodalBoundaryY,
          c,Algebra.smul_def,sub_mul] <;> ring
      · rw [hq]
        apply Prod.ext <;> simp [nodalKoszulBoundary,nodalDisconnectCycle,nodalBoundaryX,c]
    refine ⟨(c,a),he,?_⟩
    rintro ⟨w,b⟩ hh
    have hab := congrArg nodalKoszulResidue (hh.symm.trans he)
    simp only [residue_normal] at hab
    subst b
    exact Prod.ext (boundary_inj (add_right_cancel (hh.symm.trans he))) rfl
  · rintro ⟨⟨c,a⟩,rfl,_⟩
    change ((-c*nodalBoundaryY)+a • nodalBoundaryY)*nodalBoundaryX +
      ((c*nodalBoundaryX)+a • (0:B))*nodalBoundaryY=0
    simp only [smul_zero,add_zero,add_mul,smul_mul_assoc,nodalBoundaryX_mul_Y,
      mul_comm (nodalBoundaryY : B) nodalBoundaryX,smul_zero]
    ring

/-- The residue gives a complete boundary test for actual cycles. -/
theorem nodalKoszul_boundary_iff (v : Fin 2 → B) (h : nodalKoszulRelation v=0) :
    (∃ c : B, v=nodalKoszulBoundary c) ↔ nodalKoszulResidue v=0 := by
  constructor
  · rintro ⟨c,rfl⟩
    exact boundary_residue c
  · intro hv
    obtain ⟨⟨c,a⟩,he,_⟩ := (nodalKoszul_normalForm v).mp h
    rw [he,residue_normal] at hv
    exact ⟨c,by simpa [hv] using he⟩

/-- First and second Koszul differentials over the base field. -/
def nodalFirstDifferential : (Fin 2 → B) →ₗ[F] B where
  toFun := nodalKoszulRelation
  map_add' v w := by simp [nodalKoszulRelation,add_mul]; ring
  map_smul' r v := by simp [nodalKoszulRelation,smul_mul_assoc,smul_add]

def nodalSecondDifferential : B →ₗ[F] (Fin 2 → B) where
  toFun := nodalKoszulBoundary
  map_add' c d := by funext i; fin_cases i <;> simp [nodalKoszulBoundary,add_mul]
  map_smul' r c := by funext i; fin_cases i <;> simp [nodalKoszulBoundary,smul_mul_assoc]

/-- First Koszul homology of the two coordinate functions, as an actual
quotient of the kernel by the boundaries. -/
abbrev NodalKoszulH1 (F : Type*) [Field F] :=
  (nodalFirstDifferential (F:=F)).ker ⧸ (nodalSecondDifferential (F:=F)).range.comap
    (nodalFirstDifferential (F:=F)).ker.subtype

private def nodalResidueLinear : (nodalFirstDifferential (F:=F)).ker →ₗ[F] F where
  toFun v := nodalKoszulResidue v.val
  map_add' v w := by
    simp [nodalKoszulResidue,coeff_add]
    ring
  map_smul' r v := by simp [nodalKoszulResidue,coeff_smul,mul_add]

/-- The disconnected-vertex class supplies the full first homology without
a grading or finite-dimensional truncation. The residue is its coordinate. -/
def nodalKoszulH1Equiv : NodalKoszulH1 F ≃ₗ[F] F := by
  have he : (nodalSecondDifferential (F:=F)).range.comap nodalFirstDifferential.ker.subtype =
      nodalResidueLinear.ker := by
    ext v
    change (∃ c : B, nodalKoszulBoundary c=v.val) ↔ nodalKoszulResidue v.val=0
    simpa only [eq_comm (a:=nodalKoszulBoundary _)] using nodalKoszul_boundary_iff v.val v.property
  have hsurj : Function.Surjective (nodalResidueLinear (F:=F)) := by
    intro a
    let v : Fin 2 → B := nodalKoszulBoundary 0+a • nodalDisconnectCycle
    have h₁ : nodalKoszulRelation v=0 := by
      change (-0*nodalBoundaryY+a • nodalBoundaryY)*nodalBoundaryX+
        (0*nodalBoundaryX+a • (0:B))*nodalBoundaryY=0
      simp [smul_mul_assoc,mul_comm (nodalBoundaryY : B) nodalBoundaryX]
    exact ⟨⟨v,h₁⟩,residue_normal 0 a⟩
  exact (Submodule.quotEquivOfEq _ _ he).trans (nodalResidueLinear.quotKerEquivOfSurjective hsurj)

theorem nodalKoszulH2_trivial : (nodalSecondDifferential (F:=F)).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr boundary_inj

/-- In the Stanley--Reisner quotient itself every first cycle has the
same unique decomposition, through its two genuine coordinate classes. -/
theorem nodalStanleyReisner_normalForm (v : Fin 2 → Q) :
    v 0*nodalStanleyReisnerX+v 1*nodalStanleyReisnerY=0 ↔
      ∃! z : Q × F, v=nodalStanleyReisnerKoszulBoundary z.1+z.2 • nodalStanleyReisnerDisconnectCycle := by
  let E := nodalAxesEquiv (F:=F)
  have hrel : nodalKoszulRelation (E ∘ v) = E (v 0*nodalStanleyReisnerX+v 1*nodalStanleyReisnerY) := by
    simp only [nodalKoszulRelation,map_add,map_mul,Function.comp_apply]
    rfl
  have hx (z : Q × F) :
      v=nodalStanleyReisnerKoszulBoundary z.1+z.2 • nodalStanleyReisnerDisconnectCycle ↔
      E ∘ v=nodalKoszulBoundary (E z.1)+z.2 • nodalDisconnectCycle := by
    rw [funext_iff,funext_iff]
    apply forall_congr'
    intro i
    rw [← E.injective.eq_iff]
    simp only [Pi.add_apply,Pi.smul_apply,map_add,map_smul,Function.comp_apply]
    change _ ↔ _=nodalKoszulBoundary (nodalStanleyReisnerBoundaryMap z.1) i+_
    rw [← nodalStanleyReisnerKoszulBoundary_map,← nodalStanleyReisnerDisconnectCycle_map (F:=F) i]
    rfl
  have hzero : nodalKoszulRelation (E ∘ v)=0 ↔
      v 0*nodalStanleyReisnerX+v 1*nodalStanleyReisnerY=0 := by rw [hrel,map_eq_zero_iff _ E.injective]
  rw [← hzero,nodalKoszul_normalForm]
  constructor
  · rintro ⟨⟨c,a⟩,he,hu⟩
    refine ⟨(E.symm c,a),(hx _).mpr (by simpa using he),?_⟩
    rintro ⟨w,b⟩ hw
    have hz := hu (E w,b) ((hx _).mp hw)
    exact Prod.ext ((E.eq_symm_apply).mpr (congrArg Prod.fst hz)) (congrArg Prod.snd hz)
  · rintro ⟨⟨c,a⟩,he,hu⟩
    refine ⟨(E c,a),(hx _).mp he,?_⟩
    rintro ⟨w,b⟩ hw
    have hz := hu (E.symm w,b) ((hx _).mpr (by simpa using hw))
    exact Prod.ext (by simpa using congrArg E (congrArg Prod.fst hz)) (congrArg Prod.snd hz)
end
end GaloisForLFunctions
