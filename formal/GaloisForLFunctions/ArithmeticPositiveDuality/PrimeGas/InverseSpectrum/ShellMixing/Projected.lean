import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.FullSpace
import GaloisForLFunctions.RHTower.HilbertDouglasFactorization
import GaloisForLFunctions.RHTower.WeylSpectrumCompactTransfer
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Classification by the missing range

Every positive conserving propagator is the positive square root of a
compression of the critical square heat. Douglas factorization reconstructs
the range isometry from the projection alone.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

abbrev Projection := {P : GasOp // IsStarProjection P}

def projected (P : Projection) : GasOp := CFC.sqrt (criticalOperator*(P.val*criticalOperator))

private theorem self_critical : star criticalOperator = criticalOperator :=
  critical_isPositive.isSelfAdjoint.star_eq

private theorem projection_gram (P : Projection) :
    star (P.val*criticalOperator)*(P.val*criticalOperator) = criticalOperator*(P.val*criticalOperator) := by
  rw [star_mul,self_critical,P.property.isSelfAdjoint.star_eq,mul_assoc,← mul_assoc P.val,
    P.property.isIdempotentElem.eq]

theorem projected_positive (P : Projection) : (projected P).IsPositive :=
  (nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg _)

theorem projected_square (P : Projection) : projected P^2 = criticalOperator*(P.val*criticalOperator) := by
  apply CFC.sq_sqrt
  rw [← projection_gram]
  exact (nonneg_iff_isPositive _).mpr (isPositive_adjoint_comp_self _)

private theorem cancel_outer {C X Y : GasOp} (hi : Function.Injective C)
    (h : C*X*star C = C*Y*star C) : X = Y := by
  have left {A B : GasOp} (he : C*A = C*B) : A = B :=
    ContinuousLinearMap.ext fun f => hi (congrArg (fun T : GasOp => T f) he)
  have hr : X*star C = Y*star C := left (by simpa only [mul_assoc] using h)
  have hh := congrArg star hr
  simp only [star_mul,star_star] at hh
  exact star_injective (left hh)

private theorem projected_injective : Function.Injective projected := by
  intro P Q h
  apply Subtype.ext
  apply cancel_outer critical_injective
  rw [self_critical,mul_assoc,mul_assoc,← projected_square,← projected_square,h]

theorem projected_eq_critical_iff (P : Projection) : projected P = criticalOperator ↔ P.val = 1 := by
  let I : Projection := ⟨1,IsStarProjection.one⟩
  have hI : projected I = criticalOperator := by
    change CFC.sqrt (criticalOperator*(1*criticalOperator)) = criticalOperator
    rw [one_mul,← pow_two,CFC.sqrt_sq _ ((nonneg_iff_isPositive _).mpr critical_isPositive)]
  constructor
  · intro h
    exact congrArg Subtype.val (projected_injective (h.trans hI.symm))
  · intro h
    have hp : P = I := Subtype.ext h
    exact hp ▸ hI

/-- The square root propagates isometrically exactly for projections injective on the range of D. -/
theorem projected_conserves_iff (P : Projection) :
    Conserving (projected P) ↔ Function.Injective (P.val*criticalOperator) := by
  let D := criticalOperator
  let F := projected P
  have hF : F^2 = D*(P.val*D) := projected_square P
  have hsa : star F = F := (projected_positive P).isSelfAdjoint.star_eq
  constructor
  · intro hc
    obtain ⟨U,hu,_⟩ := (full_isometry_iff F).mp hc
    have hi : Function.Injective F := hu ▸ critical_injective.comp U.injective
    intro x y hxy
    apply hi
    apply hi
    change (F^2) x = (F^2) y
    rw [hF]
    exact congrArg D hxy
  · intro hp
    have hFi : Function.Injective F := by
      intro x y hxy
      apply hp
      apply critical_injective
      change (D*(P.val*D)) x = (D*(P.val*D)) y
      rw [← hF]
      exact congrArg F hxy
    let Q : Projection := ⟨1-P.val,P.property.one_sub⟩
    have hdiff : D*star D-F*star F = star (Q.val*D)*(Q.val*D) := by
      rw [show star D = D from self_critical,hsa,← pow_two,hF,projection_gram]
      change D*D-D*(P.val*D) = D*((1-P.val)*D)
      noncomm_ring
    have hpos : (D ∘L adjoint D-F ∘L adjoint F).IsPositive := by
      change (D*star D-F*star F).IsPositive
      rw [hdiff]
      exact isPositive_adjoint_comp_self _
    obtain ⟨C,_,hC⟩ := _root_.RHTower.exists_contractive_rightFactor_of_gram_sub_gram_isPositive F D hpos
    change F = D*C at hC
    have hCi : Function.Injective C := fun x y he => hFi (by rw [hC]; exact congrArg D he)
    have hCC : C*star C = P.val := by
      apply cancel_outer critical_injective
      change D*(C*star C)*star D = D*P.val*star D
      calc
        _ = (D*C)*star (D*C) := by rw [star_mul]; noncomm_ring
        _ = F^2 := by rw [← hC,hsa,pow_two]
        _ = _ := by rw [hF,show star D = D from self_critical,mul_assoc]
    have hinit : star C*C = 1 := by
      apply cancel_outer hCi
      calc
        C*(star C*C)*star C = (C*star C)*(C*star C) := by noncomm_ring
        _ = P.val := by rw [hCC,P.property.isIdempotentElem.eq]
        _ = C*1*star C := by rw [mul_one,hCC]
    let U : Gas →ₗᵢ[ℂ] Gas := { C.toLinearMap with
      norm_map' := _root_.RHTower.norm_apply_of_adjoint_comp_eq_id hinit }
    change Conserving F
    rw [hC]
    exact conserves_factor U

private def rangeProjection (U : Gas →ₗᵢ[ℂ] Gas) : Projection := by
  let V := U.toContinuousLinearMap
  refine ⟨V*star V,?_,?_⟩
  · change (V*star V)*(V*star V) = V*star V
    rw [mul_assoc V,← mul_assoc (star V),show star V*V = 1 from U.adjoint_comp_self,one_mul]
  · change star (V*star V) = V*star V
    rw [star_mul,star_star]

/-- The admissible orthogonal projection is a complete invariant for positive conserving propagation. -/
theorem positive_propagators_iff (G : GasOp) :
    G.IsPositive ∧ Conserving G ↔
      ∃! P : Projection, Function.Injective (P.val*criticalOperator) ∧ G = projected P := by
  constructor
  · rintro ⟨hg,hc⟩
    obtain ⟨U,hu,_⟩ := (full_isometry_iff G).mp hc
    let P := rangeProjection U
    have hsq : G^2 = projected P^2 := by
      rw [projected_square]
      calc
        G^2 = G*star G := by rw [hg.isSelfAdjoint.star_eq,pow_two]
        _ = criticalOperator*((U.toContinuousLinearMap*star U.toContinuousLinearMap)*criticalOperator) := by
          rw [hu,star_mul,self_critical]
          noncomm_ring
    have he : G = projected P :=
      (CFC.sqrt_sq G ((nonneg_iff_isPositive _).mpr hg)).symm.trans
        ((congrArg (fun A : GasOp => CFC.sqrt A) hsq).trans (CFC.sqrt_sq _ (CFC.sqrt_nonneg _)))
    refine ⟨P,⟨(projected_conserves_iff P).mp (he ▸ hc),he⟩,?_⟩
    exact fun R hr => projected_injective (hr.2.symm.trans he)
  · rintro ⟨P,⟨hi,rfl⟩,_⟩
    exact ⟨projected_positive P,(projected_conserves_iff P).mpr hi⟩

#print axioms projected_conserves_iff
#print axioms positive_propagators_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
