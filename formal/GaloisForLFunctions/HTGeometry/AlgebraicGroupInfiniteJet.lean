import GaloisForLFunctions.HTGeometry.MaurerCartanJetQuotient

/-!
# Coherent infinite algebraic-group jets

This file constructs the inverse-limit functor of the finite truncated-arc jet tower.  An infinite
jet is a family of finite jets compatible with every order-restriction map.  The construction is a
subgroup of the product of all finite jet groups, so it applies to arbitrary group schemes and does
not assume representability of the inverse limit by a finite-type scheme.

For commutative group schemes the constant section splits evaluation.  The general
`SplitJetEvaluation` theorem therefore gives unconditional infinite-order Maurer–Cartan
coordinates and identifies the quotient by constant jets with identity-based infinite jets.
-/

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R : Type u} [CommRing K] [CommRing R] [Algebra K R]
variable (G : Over (Spec (.of K))) [GrpObj G]

/-- Coherent families in the inverse system of all finite algebraic jet groups. -/
def coherentAlgebraicJetFamilies :
    Subgroup (∀ n : ℕ, AlgebraicJetPoint (K := K) (R := R) G n) where
  carrier j := ∀ {n m : ℕ} (h : n ≤ m),
    truncateJet (K := K) (R := R) G h (j m) = j n
  one_mem' := by
    intro n m h
    exact map_one _
  mul_mem' {j k} hj hk := by
    intro n m h
    change truncateJet (K := K) (R := R) G h (j m * k m) = j n * k n
    rw [map_mul, hj h, hk h]
  inv_mem' {j} hj := by
    intro n m h
    change truncateJet (K := K) (R := R) G h ((j m)⁻¹) = (j n)⁻¹
    rw [map_inv, hj h]

/-- Infinite algebraic jets as the inverse limit of all finite jet groups. -/
abbrev AlgebraicInfiniteJetPoint := coherentAlgebraicJetFamilies (K := K) (R := R) G

/-- Projection of a coherent infinite jet to order `n`. -/
def infiniteJetProjection (n : ℕ) :
    AlgebraicInfiniteJetPoint (K := K) (R := R) G →*
      AlgebraicJetPoint (K := K) (R := R) G n where
  toFun j := j.1 n
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Inclusion of an algebraic point as a coherent constant infinite jet. -/
def constantInfiniteJet :
    AlgebraicPoint (K := K) (R := R) G →*
      AlgebraicInfiniteJetPoint (K := K) (R := R) G where
  toFun p := ⟨fun n => constantJet (K := K) (R := R) G n p, by
    intro n m h
    exact DFunLike.congr_fun (truncateJet_constantJet (K := K) (R := R) G h) p⟩
  map_one' := by
    apply Subtype.ext
    funext n
    exact map_one _
  map_mul' p q := by
    apply Subtype.ext
    funext n
    exact map_mul _ p q

/-- Evaluation of an infinite jet at its common base point. -/
def evaluateInfiniteJet :
    AlgebraicInfiniteJetPoint (K := K) (R := R) G →*
      AlgebraicPoint (K := K) (R := R) G :=
  (evaluateJet (K := K) (R := R) G 0).comp
    (infiniteJetProjection (K := K) (R := R) G 0)

/-- Every finite projection of an infinite jet has the same evaluated base point. -/
theorem evaluateJet_comp_infiniteJetProjection (n : ℕ) :
    (evaluateJet (K := K) (R := R) G n).comp
      (infiniteJetProjection (K := K) (R := R) G n) =
        evaluateInfiniteJet (K := K) (R := R) G := by
  apply MonoidHom.ext
  intro j
  have hj := j.2 (show 0 ≤ n by omega)
  have he := DFunLike.congr_fun
    (evaluateJet_truncateJet (K := K) (R := R) G (show 0 ≤ n by omega)) (j.1 n)
  change evaluateJet (K := K) (R := R) G n (j.1 n) =
    evaluateJet (K := K) (R := R) G 0 (j.1 0)
  rw [← hj]
  exact he.symm

/-- Infinite-jet evaluation is a left inverse to the constant section. -/
theorem evaluateInfiniteJet_comp_constantInfiniteJet :
    (evaluateInfiniteJet (K := K) (R := R) G).comp
      (constantInfiniteJet (K := K) (R := R) G) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro p
  exact DFunLike.congr_fun (evaluateJet_comp_constantJet (K := K) (R := R) G 0) p

variable [IsCommMonObj G]

/-- Split evaluation for coherent infinite jets of a commutative group scheme. -/
def algebraicInfiniteJetSplitEvaluation :
    SplitJetEvaluation (AlgebraicInfiniteJetPoint (K := K) (R := R) G)
      (AlgebraicPoint (K := K) (R := R) G) where
  eval := evaluateInfiniteJet (K := K) (R := R) G
  const := constantInfiniteJet (K := K) (R := R) G
  eval_const := evaluateInfiniteJet_comp_constantInfiniteJet (K := K) (R := R) G

/-- Identity-based coherent infinite jets. -/
abbrev AlgebraicBasedInfiniteJetPoint :=
  (evaluateInfiniteJet (K := K) (R := R) G).ker

/-- Infinite-order position/Maurer–Cartan product coordinates. -/
def algebraicInfiniteJetMaurerCartanTrivialization :
    AlgebraicInfiniteJetPoint (K := K) (R := R) G ≃*
      AlgebraicPoint (K := K) (R := R) G ×
        AlgebraicBasedInfiniteJetPoint (K := K) (R := R) G :=
  (algebraicInfiniteJetSplitEvaluation (K := K) (R := R) G).trivialization

/-- Quotient of coherent infinite jets by constant jets equals identity-based infinite jets. -/
def algebraicInfiniteJetQuotientConstantsEquivBased :
    AlgebraicInfiniteJetPoint (K := K) (R := R) G ⧸
        (constantInfiniteJet (K := K) (R := R) G).range ≃*
      AlgebraicBasedInfiniteJetPoint (K := K) (R := R) G :=
  (algebraicInfiniteJetSplitEvaluation (K := K) (R := R) G).quotientEquivBased

/-- Infinite jets modulo any subgroup of constant points split into quotient position and based
Maurer–Cartan data. -/
def algebraicInfiniteJetQuotientConstantSubgroupEquivPositionVelocity
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G)) :
    AlgebraicInfiniteJetPoint (K := K) (R := R) G ⧸
        H.map (constantInfiniteJet (K := K) (R := R) G) ≃*
      (AlgebraicPoint (K := K) (R := R) G ⧸ H) ×
        AlgebraicBasedInfiniteJetPoint (K := K) (R := R) G :=
  (algebraicInfiniteJetSplitEvaluation (K := K) (R := R) G)
    |>.quotientSubgroupEquivPositionVelocity H

end

end GaloisForLFunctions.HTGeometry
