import GaloisForLFunctions.HTGeometry.AlgebraicGroupJet
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Maurer–Cartan normalization and constant-jet quotients

For a commutative group `J` with a split evaluation `J → P`, every element has canonical
coordinates

`j ↦ (eval j, j / const (eval j))`.

The second coordinate lies in the identity-based subgroup `ker eval`.  It is the finite-order,
functor-of-points Maurer–Cartan coordinate: it removes the constant position while retaining every
higher jet coefficient.  This file proves both the product trivialization

`J ≃ P × ker eval`

and the quotient theorem

`J / range const ≃ ker eval`.

The result is then instantiated for the algebraic jet tower of every commutative group scheme.
It does not assume a coordinate chart, a Lie-algebra identification, smoothness, or an invariant
function-field theorem.
-/

open CategoryTheory
open AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable (J : Type u) (P : Type v) [CommGroup J] [CommGroup P]

/-- A group evaluation equipped with its constant section. -/
structure SplitJetEvaluation where
  /-- Evaluation of a jet at its base point. -/
  eval : J →* P
  /-- Inclusion of base points as constant jets. -/
  const : P →* J
  /-- Evaluation is a left inverse to the constant section. -/
  eval_const : eval.comp const = MonoidHom.id P

variable {J P}

namespace SplitJetEvaluation

variable (S : SplitJetEvaluation J P)

@[simp]
theorem eval_const_apply (p : P) : S.eval (S.const p) = p := by
  exact DFunLike.congr_fun S.eval_const p

/-- Remove the constant position of a jet.  The result is based at the identity. -/
def normalize : J →* S.eval.ker where
  toFun j := ⟨j / S.const (S.eval j), by
    rw [MonoidHom.mem_ker]
    simp⟩
  map_one' := by
    ext
    simp
  map_mul' j k := by
    ext
    simp only [Subgroup.coe_mul, map_mul, div_eq_mul_inv, mul_inv_rev]
    ac_rfl

@[simp]
theorem normalize_coe (j : J) :
    (S.normalize j : J) = j / S.const (S.eval j) := rfl

/-- Every identity-based jet is already normalized. -/
theorem normalize_surjective : Function.Surjective S.normalize := by
  intro j
  refine ⟨j.1, Subtype.ext ?_⟩
  have hj : S.eval j.1 = 1 := j.2
  simp [normalize, hj]

/-- A jet normalizes to the identity exactly when it is constant. -/
theorem normalize_ker : S.normalize.ker = S.const.range := by
  ext j
  constructor
  · intro hj
    rw [MonoidHom.mem_ker] at hj
    have hnorm : j / S.const (S.eval j) = 1 := congrArg Subtype.val hj
    refine ⟨S.eval j, ?_⟩
    exact (div_eq_one.mp hnorm).symm
  · rintro ⟨p, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    simp [normalize]

/-- Quotient by constant jets is canonically the group of identity-based jets. -/
def quotientEquivBased : J ⧸ S.const.range ≃* S.eval.ker :=
  (QuotientGroup.quotientMulEquivOfEq S.normalize_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective S.normalize S.normalize_surjective)

/-- Maurer–Cartan coordinates split every jet into its base point and normalized jet. -/
def trivialization : J ≃* P × S.eval.ker where
  toFun j := (S.eval j, S.normalize j)
  invFun z := S.const z.1 * z.2.1
  left_inv j := by
    simp [normalize]
  right_inv z := by
    rcases z with ⟨p, z⟩
    have hz : S.eval z.1 = 1 := z.2
    apply Prod.ext
    · simp [hz]
    · apply Subtype.ext
      simp [normalize, hz]
  map_mul' j k := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change (S.normalize (j * k) : J) = (S.normalize j : J) * (S.normalize k : J)
      simp only [normalize_coe, Subgroup.coe_mul, map_mul, div_eq_mul_inv]

@[simp]
theorem trivialization_apply (j : J) :
    S.trivialization j = (S.eval j, S.normalize j) := rfl

@[simp]
theorem trivialization_symm_apply (z : P × S.eval.ker) :
    S.trivialization.symm z = S.const z.1 * z.2.1 := rfl

/-- Position modulo a constant subgroup, together with normalized Maurer–Cartan data. -/
def positionVelocityHom (H : Subgroup P) : J →* (P ⧸ H) × S.eval.ker :=
  ((QuotientGroup.mk' H).comp S.eval).prod S.normalize

/-- Every quotient position and identity-based jet has a position–velocity lift. -/
theorem positionVelocityHom_surjective (H : Subgroup P) :
    Function.Surjective (S.positionVelocityHom H) := by
  rintro ⟨q, b⟩
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨S.trivialization.symm (p, b), ?_⟩
  apply Prod.ext
  · change QuotientGroup.mk (S.eval (S.trivialization.symm (p, b))) = QuotientGroup.mk p
    rw [S.trivialization_symm_apply]
    have hb : S.eval b.1 = 1 := b.2
    simp [hb]
  · change S.normalize (S.trivialization.symm (p, b)) = b
    exact congrArg Prod.snd (S.trivialization.apply_symm_apply (p, b))

/-- Kernel of the position–velocity map is exactly the chosen subgroup of constant jets. -/
theorem positionVelocityHom_ker (H : Subgroup P) :
    (S.positionVelocityHom H).ker = H.map S.const := by
  ext j
  constructor
  · intro hj
    rw [MonoidHom.mem_ker] at hj
    have hq : QuotientGroup.mk (S.eval j) = (1 : P ⧸ H) := congrArg Prod.fst hj
    have hn : S.normalize j = 1 := congrArg Prod.snd hj
    have hej : S.eval j ∈ H := by
      simpa using (QuotientGroup.eq_one_iff (N := H) (S.eval j)).mp hq
    refine ⟨S.eval j, hej, ?_⟩
    have hnorm : j / S.const (S.eval j) = 1 := congrArg Subtype.val hn
    exact (div_eq_one.mp hnorm).symm
  · rintro ⟨p, hp, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Prod.ext
    · change QuotientGroup.mk (S.eval (S.const p)) = 1
      rw [S.eval_const_apply]
      exact (QuotientGroup.eq_one_iff (N := H) p).mpr hp
    · change S.normalize (S.const p) = 1
      apply Subtype.ext
      simp [normalize]

/-- Quotient by any constant subgroup splits into quotient position and Maurer–Cartan data. -/
def quotientSubgroupEquivPositionVelocity (H : Subgroup P) :
    J ⧸ H.map S.const ≃* (P ⧸ H) × S.eval.ker :=
  (QuotientGroup.quotientMulEquivOfEq (S.positionVelocityHom_ker H).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (S.positionVelocityHom H)
      (S.positionVelocityHom_surjective H))

end SplitJetEvaluation

universe w

variable {K R : Type w} [CommRing K] [CommRing R] [Algebra K R]
variable (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G]

/-- The split evaluation carried by order-`n` algebraic jets of a commutative group scheme. -/
def algebraicJetSplitEvaluation (n : ℕ) :
    SplitJetEvaluation (AlgebraicJetPoint (K := K) (R := R) G n)
      (AlgebraicPoint (K := K) (R := R) G) where
  eval := evaluateJet (K := K) (R := R) G n
  const := constantJet (K := K) (R := R) G n
  eval_const := evaluateJet_comp_constantJet (K := K) (R := R) G n

/-- Identity-based order-`n` algebraic jets, the finite Maurer–Cartan target. -/
abbrev AlgebraicBasedJetPoint (n : ℕ) :=
  (evaluateJet (K := K) (R := R) G n).ker

/-- Finite-order Maurer–Cartan normalization for a commutative group scheme. -/
def algebraicJetMaurerCartanNormalize (n : ℕ) :
    AlgebraicJetPoint (K := K) (R := R) G n →*
      AlgebraicBasedJetPoint (K := K) (R := R) G n :=
  (algebraicJetSplitEvaluation (K := K) (R := R) G n).normalize

/-- Algebraic jets split canonically into position and identity-based Maurer–Cartan data. -/
def algebraicJetMaurerCartanTrivialization (n : ℕ) :
    AlgebraicJetPoint (K := K) (R := R) G n ≃*
      AlgebraicPoint (K := K) (R := R) G ×
        AlgebraicBasedJetPoint (K := K) (R := R) G n :=
  (algebraicJetSplitEvaluation (K := K) (R := R) G n).trivialization

/-- Constant-translation quotient of finite algebraic jets equals identity-based jets. -/
def algebraicJetQuotientConstantsEquivBased (n : ℕ) :
    AlgebraicJetPoint (K := K) (R := R) G n ⧸
        (constantJet (K := K) (R := R) G n).range ≃*
      AlgebraicBasedJetPoint (K := K) (R := R) G n :=
  (algebraicJetSplitEvaluation (K := K) (R := R) G n).quotientEquivBased

/-- Finite jets modulo any subgroup of constant points split into quotient position and based
Maurer–Cartan data. -/
def algebraicJetQuotientConstantSubgroupEquivPositionVelocity (n : ℕ)
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G)) :
    AlgebraicJetPoint (K := K) (R := R) G n ⧸
        H.map (constantJet (K := K) (R := R) G n) ≃*
      (AlgebraicPoint (K := K) (R := R) G ⧸ H) ×
        AlgebraicBasedJetPoint (K := K) (R := R) G n :=
  (algebraicJetSplitEvaluation (K := K) (R := R) G n)
    |>.quotientSubgroupEquivPositionVelocity H

@[simp]
theorem algebraicJetMaurerCartanNormalize_coe (n : ℕ)
    (j : AlgebraicJetPoint (K := K) (R := R) G n) :
    (algebraicJetMaurerCartanNormalize (K := K) (R := R) G n j :
      AlgebraicJetPoint (K := K) (R := R) G n) =
        j / constantJet (K := K) (R := R) G n
          (evaluateJet (K := K) (R := R) G n j) := by
  rfl

@[simp]
theorem algebraicJetMaurerCartanTrivialization_apply (n : ℕ)
    (j : AlgebraicJetPoint (K := K) (R := R) G n) :
    algebraicJetMaurerCartanTrivialization (K := K) (R := R) G n j =
      (evaluateJet (K := K) (R := R) G n j,
        algebraicJetMaurerCartanNormalize (K := K) (R := R) G n j) := by
  rfl

end


end GaloisForLFunctions.HTGeometry
