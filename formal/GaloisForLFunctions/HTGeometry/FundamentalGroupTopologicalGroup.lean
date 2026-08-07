import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.EckmannHilton

/-!
# Fundamental groups of topological groups are abelian

Loops based at the identity carry two products: concatenation and pointwise multiplication.
Pointwise multiplication has the constant loop as a two-sided unit, and it satisfies the
interchange law with concatenation. The Eckmann--Hilton argument therefore makes the existing
fundamental group commutative.

This supplies the topological input for torus-chart monodromy: every permutation representation of
the fundamental group of a topological group has abelian image.
-/

namespace GaloisForLFunctions.HTGeometry

open Path

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Pointwise product of two loops based at the identity. -/
def loopPointwiseMulPath (p q : Path (1 : G) 1) : Path (1 : G) 1 where
  toFun t := p t * q t
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- Pointwise multiplication preserves endpoint-fixed path homotopies. -/
def loopPointwiseMulHomotopy {p p' q q' : Path (1 : G) 1}
    (F : p.Homotopy p') (H : q.Homotopy q') :
    (loopPointwiseMulPath p q).Homotopy (loopPointwiseMulPath p' q') where
  toFun z := F z * H z
  continuous_toFun := by fun_prop
  map_zero_left t := by simp [loopPointwiseMulPath]
  map_one_left t := by simp [loopPointwiseMulPath]
  prop' t s hs := by
    rcases hs with rfl | hs
    · simp
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      simp

/-- Pointwise multiplication descended to loops modulo endpoint-fixed homotopy. -/
def fundamentalGroupPointwiseMul
    (a b : FundamentalGroup G 1) : FundamentalGroup G 1 :=
  Quotient.map₂ loopPointwiseMulPath
    (fun _ _ hp _ _ hq => by
      rcases hp with ⟨F⟩
      rcases hq with ⟨H⟩
      exact ⟨loopPointwiseMulHomotopy F H⟩) a b

@[simp] theorem fundamentalGroupPointwiseMul_mk (p q : Path (1 : G) 1) :
    fundamentalGroupPointwiseMul (Path.Homotopic.Quotient.mk p)
        (Path.Homotopic.Quotient.mk q) =
      Path.Homotopic.Quotient.mk (loopPointwiseMulPath p q) :=
  rfl

theorem fundamentalGroupPointwiseMul_one_left (a : FundamentalGroup G 1) :
    fundamentalGroupPointwiseMul 1 a = a := by
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
      change fundamentalGroupPointwiseMul
        (Path.Homotopic.Quotient.mk (Path.refl 1))
        (Path.Homotopic.Quotient.mk p) = Path.Homotopic.Quotient.mk p
      rw [fundamentalGroupPointwiseMul_mk]
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      simp [loopPointwiseMulPath]

theorem fundamentalGroupPointwiseMul_one_right (a : FundamentalGroup G 1) :
    fundamentalGroupPointwiseMul a 1 = a := by
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
      change fundamentalGroupPointwiseMul
        (Path.Homotopic.Quotient.mk p)
        (Path.Homotopic.Quotient.mk (Path.refl 1)) = Path.Homotopic.Quotient.mk p
      rw [fundamentalGroupPointwiseMul_mk]
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      simp [loopPointwiseMulPath]

/-- Pointwise loop multiplication has the same unit as fundamental-group multiplication. -/
theorem fundamentalGroupPointwiseMul_isUnital :
    EckmannHilton.IsUnital (fundamentalGroupPointwiseMul (G := G))
      (1 : FundamentalGroup G 1) where
  left_id := fundamentalGroupPointwiseMul_one_left
  right_id := fundamentalGroupPointwiseMul_one_right

/-- Pointwise multiplication distributes across path concatenation. -/
theorem fundamentalGroupPointwiseMul_trans (a b c d : FundamentalGroup G 1) :
    fundamentalGroupPointwiseMul (a.trans b) (c.trans d) =
      (fundamentalGroupPointwiseMul a c).trans
        (fundamentalGroupPointwiseMul b d) := by
  induction a, c using Path.Homotopic.Quotient.ind₂ with
  | mk p r =>
    induction b, d using Path.Homotopic.Quotient.ind₂ with
    | mk q s =>
      simp only [← Path.Homotopic.Quotient.mk_trans,
        fundamentalGroupPointwiseMul_mk]
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      simp only [loopPointwiseMulPath, Path.trans_apply, Path.coe_mk_mk]
      split_ifs <;> rfl

/-- Eckmann--Hilton interchange between fundamental-group multiplication and pointwise loop
multiplication. -/
theorem fundamentalGroupPointwiseMul_interchange
    (a b c d : FundamentalGroup G 1) :
    fundamentalGroupPointwiseMul (a * b) (c * d) =
      fundamentalGroupPointwiseMul a c * fundamentalGroupPointwiseMul b d := by
  simp only [FundamentalGroup.mul_def]
  exact fundamentalGroupPointwiseMul_trans b a d c

/-- **The fundamental group of a topological group is a commutative group.** -/
@[reducible] noncomputable def fundamentalGroupCommGroup :
    CommGroup (FundamentalGroup G 1) :=
  EckmannHilton.commGroup fundamentalGroupPointwiseMul_isUnital
    fundamentalGroupPointwiseMul_interchange

/-- Multiplication in the existing fundamental-group structure is commutative. -/
theorem fundamentalGroup_mul_comm (a b : FundamentalGroup G 1) : a * b = b * a :=
  fundamentalGroupCommGroup.mul_comm a b

variable {H : Type v} [Group H]

/-- Every group-valued representation of a topological group's fundamental group has abelian
image. In particular this applies to a covering map's monodromy representation. -/
@[reducible] noncomputable def fundamentalGroupMapRangeCommGroup
    (φ : FundamentalGroup G 1 →* H) : CommGroup φ.range := by
  letI : CommGroup (FundamentalGroup G 1) := fundamentalGroupCommGroup
  exact φ.rangeRestrict.commGroupOfSurjective φ.rangeRestrict_surjective

/-! ## The complex torus times affine space -/

/-- Analytic group model of `(𝔾ₘ)² × 𝔸ᵏ` over `ℂ`. The affine factor is written
multiplicatively from its additive group, so the whole chart is a topological group. -/
abbrev ComplexTorusAffineChart (k : ℕ) :=
  Units ℂ × Units ℂ × Multiplicative (Fin k → ℂ)

/-- The analytic chart `(ℂˣ)² × ℂᵏ` has abelian fundamental group, without computing that group. -/
theorem complexTorusAffineChart_fundamentalGroup_mul_comm (k : ℕ)
    (a b : FundamentalGroup (ComplexTorusAffineChart k) 1) : a * b = b * a :=
  fundamentalGroup_mul_comm a b

variable {E : Type v} [TopologicalSpace E] {k : ℕ}
  (p : E → ComplexTorusAffineChart k) (cov : IsCoveringMap p)

/-- **Every topological covering of `(ℂˣ)² × ℂᵏ` has abelian monodromy image.** -/
@[reducible] noncomputable def torusChartMonodromyRangeCommGroup :
    CommGroup (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range :=
  fundamentalGroupMapRangeCommGroup (cov.monodromyPerm 1)

end GaloisForLFunctions.HTGeometry
