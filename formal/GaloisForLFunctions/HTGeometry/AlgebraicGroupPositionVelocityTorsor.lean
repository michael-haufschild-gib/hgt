import GaloisForLFunctions.HTGeometry.AlgebraicGroupInfiniteJet

/-!
# Concrete position--velocity quotients and Maurer--Cartan torsors

For any commutative group scheme, any coefficient algebra `R`, and any subgroup `H` of its
`R`-points, this file constructs the concrete point quotient `G(R) / H`.  Finite and coherent
infinite jets map to quotient position together with based Maurer--Cartan data.  These maps are
surjective and every fiber is a torsor under the unique constant `H`-translation.

This is a functor-of-points theorem.  It does not identify the point quotient with the points of a
representing scheme unless a separate quotient-representability theorem supplies that comparison.
-/

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {J : Type u} {P : Type v} [CommGroup J] [CommGroup P]

namespace SplitJetEvaluation

variable (S : SplitJetEvaluation J P)

/-- Constant jets embed faithfully because evaluation is their left inverse. -/
theorem const_injective : Function.Injective S.const := by
  intro p q hpq
  have := congrArg S.eval hpq
  simpa using this

/-- Two jets have equal position--velocity data exactly when their ratio is a constant in `H`. -/
theorem positionVelocityHom_eq_iff_div_mem (H : Subgroup P) (j₁ j₂ : J) :
    S.positionVelocityHom H j₁ = S.positionVelocityHom H j₂ ↔
      j₁ / j₂ ∈ H.map S.const := by
  rw [← S.positionVelocityHom_ker H]
  simp only [MonoidHom.mem_ker, map_div]
  exact (@div_eq_one ((P ⧸ H) × S.eval.ker) _
    (S.positionVelocityHom H j₁) (S.positionVelocityHom H j₂)).symm

/-- Equal position--velocity data are exactly one constant `H`-translation apart. -/
theorem positionVelocityHom_eq_iff_exists_constant_mul (H : Subgroup P) (j₁ j₂ : J) :
    S.positionVelocityHom H j₁ = S.positionVelocityHom H j₂ ↔
      ∃ h : P, h ∈ H ∧ j₁ = S.const h * j₂ := by
  rw [S.positionVelocityHom_eq_iff_div_mem H]
  constructor
  · rintro ⟨h, hh, heq⟩
    refine ⟨h, hh, ?_⟩
    calc
      j₁ = (j₁ / j₂) * j₂ := by simp
      _ = S.const h * j₂ := by rw [← heq]
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simp⟩

/-- Position--velocity data are invariant under constant `H`-translation. -/
theorem positionVelocityHom_constant_mul_eq (H : Subgroup P) {h : P} (hh : h ∈ H) (j : J) :
    S.positionVelocityHom H (S.const h * j) = S.positionVelocityHom H j := by
  exact (S.positionVelocityHom_eq_iff_exists_constant_mul H _ _).2 ⟨h, hh, rfl⟩

/-- Every position--velocity fiber is a torsor under its constant subgroup: the translating
constant exists and is unique. -/
theorem positionVelocityHom_eq_iff_existsUnique_constant_mul
    (H : Subgroup P) (j₁ j₂ : J) :
    S.positionVelocityHom H j₁ = S.positionVelocityHom H j₂ ↔
      ∃! h : H, j₁ = S.const h.1 * j₂ := by
  constructor
  · intro hj
    obtain ⟨h, hh, hmul⟩ :=
      (S.positionVelocityHom_eq_iff_exists_constant_mul H j₁ j₂).1 hj
    refine ⟨⟨h, hh⟩, hmul, ?_⟩
    intro k hk
    apply Subtype.ext
    apply S.const_injective
    apply mul_right_cancel (b := j₂)
    exact hk.symm.trans hmul
  · rintro ⟨h, hmul, -⟩
    exact (S.positionVelocityHom_eq_iff_exists_constant_mul H j₁ j₂).2
      ⟨h.1, h.2, hmul⟩

/-- Maurer--Cartan normalization is a torsor quotient by all constant jets. -/
theorem normalize_eq_iff_existsUnique_constant_mul (j₁ j₂ : J) :
    S.normalize j₁ = S.normalize j₂ ↔
      ∃! p : P, j₁ = S.const p * j₂ := by
  constructor
  · intro hn
    have hker : j₁ / j₂ ∈ S.normalize.ker := by
      rw [MonoidHom.mem_ker, map_div, div_eq_one]
      exact hn
    rw [S.normalize_ker] at hker
    obtain ⟨p, hp⟩ := hker
    have hmul : j₁ = S.const p * j₂ := by
      calc
        j₁ = (j₁ / j₂) * j₂ := by simp
        _ = S.const p * j₂ := by rw [← hp]
    refine ⟨p, hmul, ?_⟩
    intro q hq
    apply S.const_injective
    apply mul_right_cancel (b := j₂)
    exact hq.symm.trans hmul
  · rintro ⟨p, hmul, -⟩
    rw [hmul, map_mul]
    have hp : S.normalize (S.const p) = 1 := by
      rw [← MonoidHom.mem_ker, S.normalize_ker]
      exact ⟨p, rfl⟩
    rw [hp, _root_.one_mul]

end SplitJetEvaluation

universe w

variable {K R : Type w} [CommRing K] [CommRing R] [Algebra K R]
variable (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G]

/-- Concrete quotient group of `R`-points by a subgroup of constant points. -/
abbrev AlgebraicPointQuotient
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G)) :=
  AlgebraicPoint (K := K) (R := R) G ⧸ H

/-- Concrete quotient map on `R`-valued algebraic points. -/
def algebraicPointQuotientHom
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G)) :
    AlgebraicPoint (K := K) (R := R) G →*
      AlgebraicPointQuotient (K := K) (R := R) G H :=
  QuotientGroup.mk' H

/-- Every concrete quotient point has a representative. -/
theorem algebraicPointQuotientHom_surjective
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G)) :
    Function.Surjective (algebraicPointQuotientHom (K := K) (R := R) G H) :=
  QuotientGroup.mk_surjective

/-- Concrete `G(R) / H` fibers are exactly the free `H`-translation orbits. -/
theorem algebraicPointQuotientHom_eq_iff_existsUnique_mul
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G))
    (p q : AlgebraicPoint (K := K) (R := R) G) :
    algebraicPointQuotientHom (K := K) (R := R) G H p =
        algebraicPointQuotientHom (K := K) (R := R) G H q ↔
      ∃! h : H, p = h.1 * q := by
  change (QuotientGroup.mk p : AlgebraicPointQuotient (K := K) (R := R) G H) =
      QuotientGroup.mk q ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  constructor
  · intro hh
    have hmul : p = (p / q) * q := by simp
    refine ⟨⟨p / q, hh⟩, hmul, ?_⟩
    intro k hk
    apply Subtype.ext
    apply mul_right_cancel (b := q)
    exact hk.symm.trans hmul
  · rintro ⟨h, hmul, -⟩
    have hpq : p / q = h.1 := by
      rw [hmul]
      simp
    rw [hpq]
    exact h.2

/-- Finite position/Maurer--Cartan map for a concrete subgroup of algebraic points. -/
def algebraicJetPositionVelocityHom (n : ℕ)
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G)) :
    AlgebraicJetPoint (K := K) (R := R) G n →*
      AlgebraicPointQuotient (K := K) (R := R) G H ×
        AlgebraicBasedJetPoint (K := K) (R := R) G n :=
  (algebraicJetSplitEvaluation (K := K) (R := R) G n).positionVelocityHom H

/-- Finite position--velocity map is surjective, hence pointwise dominant. -/
theorem algebraicJetPositionVelocityHom_surjective (n : ℕ)
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G)) :
    Function.Surjective (algebraicJetPositionVelocityHom (K := K) (R := R) G n H) :=
  (algebraicJetSplitEvaluation (K := K) (R := R) G n).positionVelocityHom_surjective H

/-- Finite Maurer--Cartan normalization is surjective onto every based jet. -/
theorem algebraicJetMaurerCartanNormalize_surjective (n : ℕ) :
    Function.Surjective (algebraicJetMaurerCartanNormalize (K := K) (R := R) G n) :=
  (algebraicJetSplitEvaluation (K := K) (R := R) G n).normalize_surjective

/-- Fibers of finite Maurer--Cartan normalization are torsors under all constant points. -/
theorem algebraicJetMaurerCartanNormalize_eq_iff_existsUnique_constant_mul (n : ℕ)
    (j₁ j₂ : AlgebraicJetPoint (K := K) (R := R) G n) :
    algebraicJetMaurerCartanNormalize (K := K) (R := R) G n j₁ =
        algebraicJetMaurerCartanNormalize (K := K) (R := R) G n j₂ ↔
      ∃! p : AlgebraicPoint (K := K) (R := R) G,
        j₁ = constantJet (K := K) (R := R) G n p * j₂ :=
  (algebraicJetSplitEvaluation (K := K) (R := R) G n)
    |>.normalize_eq_iff_existsUnique_constant_mul j₁ j₂

theorem algebraicJetPositionVelocityHom_eq_iff_exists_constant_mul (n : ℕ)
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G))
    (j₁ j₂ : AlgebraicJetPoint (K := K) (R := R) G n) :
    algebraicJetPositionVelocityHom (K := K) (R := R) G n H j₁ =
        algebraicJetPositionVelocityHom (K := K) (R := R) G n H j₂ ↔
      ∃ h : AlgebraicPoint (K := K) (R := R) G,
        h ∈ H ∧ j₁ = constantJet (K := K) (R := R) G n h * j₂ :=
  (algebraicJetSplitEvaluation (K := K) (R := R) G n)
    |>.positionVelocityHom_eq_iff_exists_constant_mul H j₁ j₂

/-- Finite Maurer--Cartan fibers are principal homogeneous spaces under constant `H`-jets. -/
theorem algebraicJetPositionVelocityHom_eq_iff_existsUnique_constant_mul (n : ℕ)
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G))
    (j₁ j₂ : AlgebraicJetPoint (K := K) (R := R) G n) :
    algebraicJetPositionVelocityHom (K := K) (R := R) G n H j₁ =
        algebraicJetPositionVelocityHom (K := K) (R := R) G n H j₂ ↔
      ∃! h : H, j₁ = constantJet (K := K) (R := R) G n h.1 * j₂ :=
  (algebraicJetSplitEvaluation (K := K) (R := R) G n)
    |>.positionVelocityHom_eq_iff_existsUnique_constant_mul H j₁ j₂

/-- Infinite position/Maurer--Cartan map for a concrete subgroup of algebraic points. -/
def algebraicInfiniteJetPositionVelocityHom
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G)) :
    AlgebraicInfiniteJetPoint (K := K) (R := R) G →*
      AlgebraicPointQuotient (K := K) (R := R) G H ×
        AlgebraicBasedInfiniteJetPoint (K := K) (R := R) G :=
  (algebraicInfiniteJetSplitEvaluation (K := K) (R := R) G).positionVelocityHom H

/-- Infinite-order Maurer--Cartan normalization to coherent based jets. -/
def algebraicInfiniteJetMaurerCartanNormalize :
    AlgebraicInfiniteJetPoint (K := K) (R := R) G →*
      AlgebraicBasedInfiniteJetPoint (K := K) (R := R) G :=
  (algebraicInfiniteJetSplitEvaluation (K := K) (R := R) G).normalize

/-- Infinite-order Maurer--Cartan normalization is surjective onto coherent based jets. -/
theorem algebraicInfiniteJetMaurerCartanNormalize_surjective :
    Function.Surjective
      (algebraicInfiniteJetMaurerCartanNormalize (K := K) (R := R) G) :=
  (algebraicInfiniteJetSplitEvaluation (K := K) (R := R) G).normalize_surjective

/-- Fibers of infinite Maurer--Cartan normalization are torsors under all constant points. -/
theorem algebraicInfiniteJetMaurerCartanNormalize_eq_iff_existsUnique_constant_mul
    (j₁ j₂ : AlgebraicInfiniteJetPoint (K := K) (R := R) G) :
    algebraicInfiniteJetMaurerCartanNormalize (K := K) (R := R) G j₁ =
        algebraicInfiniteJetMaurerCartanNormalize (K := K) (R := R) G j₂ ↔
      ∃! p : AlgebraicPoint (K := K) (R := R) G,
        j₁ = constantInfiniteJet (K := K) (R := R) G p * j₂ :=
  (algebraicInfiniteJetSplitEvaluation (K := K) (R := R) G)
    |>.normalize_eq_iff_existsUnique_constant_mul j₁ j₂

/-- Coherent infinite position--velocity map is surjective, hence pointwise dominant. -/
theorem algebraicInfiniteJetPositionVelocityHom_surjective
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G)) :
    Function.Surjective
      (algebraicInfiniteJetPositionVelocityHom (K := K) (R := R) G H) :=
  (algebraicInfiniteJetSplitEvaluation (K := K) (R := R) G)
    |>.positionVelocityHom_surjective H

theorem algebraicInfiniteJetPositionVelocityHom_eq_iff_exists_constant_mul
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G))
    (j₁ j₂ : AlgebraicInfiniteJetPoint (K := K) (R := R) G) :
    algebraicInfiniteJetPositionVelocityHom (K := K) (R := R) G H j₁ =
        algebraicInfiniteJetPositionVelocityHom (K := K) (R := R) G H j₂ ↔
      ∃ h : AlgebraicPoint (K := K) (R := R) G,
        h ∈ H ∧ j₁ = constantInfiniteJet (K := K) (R := R) G h * j₂ :=
  (algebraicInfiniteJetSplitEvaluation (K := K) (R := R) G)
    |>.positionVelocityHom_eq_iff_exists_constant_mul H j₁ j₂

/-- Coherent infinite Maurer--Cartan fibers are torsors under constant `H`-jets. -/
theorem algebraicInfiniteJetPositionVelocityHom_eq_iff_existsUnique_constant_mul
    (H : Subgroup (AlgebraicPoint (K := K) (R := R) G))
    (j₁ j₂ : AlgebraicInfiniteJetPoint (K := K) (R := R) G) :
    algebraicInfiniteJetPositionVelocityHom (K := K) (R := R) G H j₁ =
        algebraicInfiniteJetPositionVelocityHom (K := K) (R := R) G H j₂ ↔
      ∃! h : H, j₁ = constantInfiniteJet (K := K) (R := R) G h.1 * j₂ :=
  (algebraicInfiniteJetSplitEvaluation (K := K) (R := R) G)
    |>.positionVelocityHom_eq_iff_existsUnique_constant_mul H j₁ j₂

end

end GaloisForLFunctions.HTGeometry
