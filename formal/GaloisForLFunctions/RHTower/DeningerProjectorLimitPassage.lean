import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Passage of compatible projectors to limits and weighted sums

A family of continuous projectors on the stages of a projective system, compatible with the
transition maps, defines a continuous coordinatewise projector on the limit.  It is the unique
continuous linear map with those coordinates, it is idempotent, its range is the set of families
whose coordinates are all in the stagewise ranges, that range is closed, and any identity between
coordinatewise operators — in particular a Green identity — passes to the limit because equality
in a limit is detected coordinatewise.

For restricted sums the passage is quantitative: a stagewise bound with a constant independent of
the stage gives the same bound for the weighted sum seminorm, so the coordinatewise projector is
continuous for it.  Orthogonal projections give the constant `1`.

* `deningerCoordinateOperator` : the coordinatewise operator on the limit.
* `deningerCoordinateOperator_unique`, `_idem`, `_range_eq`, `_range_isClosed`.
* `deningerLimitGreen` : the Green identity passes.
* `deningerWeightedSum_summable`, `deningerWeightedSum_le` : the weighted estimate.
* `deningerEnergyProjection_weightedSum_le` : the orthogonal case, with constant `1`.
-/

namespace RHTower

section ProjectiveLimit

variable {R : Type*} [Ring R]
variable {ι : Type*} [Preorder ι] {E : ι → Type*}
variable [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
variable [∀ i, TopologicalSpace (E i)]

/-- The projective limit of a system of topological modules, as a submodule of the product. -/
def deningerProjectiveLimit (r : ∀ i j, i ≤ j → (E j →L[R] E i)) : Submodule R (∀ i, E i) where
  carrier := {x | ∀ i j (h : i ≤ j), r i j h (x j) = x i}
  add_mem' := by
    intro a b ha hb i j h
    rw [Pi.add_apply, map_add, ha i j h, hb i j h]
    rfl
  zero_mem' := by
    intro i j h
    rw [Pi.zero_apply, map_zero]
    rfl
  smul_mem' := by
    intro c a ha i j h
    rw [Pi.smul_apply, map_smul, ha i j h]
    rfl

theorem deningerMem_projectiveLimit {r : ∀ i j, i ≤ j → (E j →L[R] E i)} {x : ∀ i, E i} :
    x ∈ deningerProjectiveLimit r ↔ ∀ i j (h : i ≤ j), r i j h (x j) = x i := Iff.rfl

/-- **The coordinatewise operator of a compatible family.**  Compatibility makes it preserve
compatible families, and the initial topology of the limit makes it continuous. -/
def deningerCoordinateOperator (r : ∀ i j, i ≤ j → (E j →L[R] E i)) (T : ∀ i, E i →L[R] E i)
    (hT : ∀ i j (h : i ≤ j) (y : E j), r i j h (T j y) = T i (r i j h y)) :
    deningerProjectiveLimit r →L[R] deningerProjectiveLimit r :=
  ContinuousLinearMap.codRestrict
    (((ContinuousLinearMap.pi fun i => (T i).comp (ContinuousLinearMap.proj i)).comp
      (deningerProjectiveLimit r).subtypeL)) _ (by
      intro x i j h
      show r i j h (T j ((x : ∀ i, E i) j)) = T i ((x : ∀ i, E i) i)
      rw [hT, x.2 i j h])

@[simp]
theorem deningerCoordinateOperator_apply {r : ∀ i j, i ≤ j → (E j →L[R] E i)}
    {T : ∀ i, E i →L[R] E i}
    (hT : ∀ i j (h : i ≤ j) (y : E j), r i j h (T j y) = T i (r i j h y))
    (x : deningerProjectiveLimit r) (i : ι) :
    ((deningerCoordinateOperator r T hT x : deningerProjectiveLimit r) : ∀ i, E i) i
      = T i ((x : ∀ i, E i) i) := rfl

/-- **Uniqueness.**  A continuous linear map on the limit is determined by its coordinates. -/
theorem deningerCoordinateOperator_unique {r : ∀ i j, i ≤ j → (E j →L[R] E i)}
    {T : ∀ i, E i →L[R] E i}
    (hT : ∀ i j (h : i ≤ j) (y : E j), r i j h (T j y) = T i (r i j h y))
    (S : deningerProjectiveLimit r →L[R] deningerProjectiveLimit r)
    (hS : ∀ (x : deningerProjectiveLimit r) (i : ι),
      ((S x : deningerProjectiveLimit r) : ∀ i, E i) i = T i ((x : ∀ i, E i) i)) :
    S = deningerCoordinateOperator r T hT := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine Subtype.ext ?_
  funext i
  rw [hS x i]
  rfl

/-- **Idempotence passes to the limit.** -/
theorem deningerCoordinateOperator_idem {r : ∀ i j, i ≤ j → (E j →L[R] E i)}
    {T : ∀ i, E i →L[R] E i}
    (hT : ∀ i j (h : i ≤ j) (y : E j), r i j h (T j y) = T i (r i j h y))
    (hidem : ∀ i (y : E i), T i (T i y) = T i y) (x : deningerProjectiveLimit r) :
    deningerCoordinateOperator r T hT (deningerCoordinateOperator r T hT x)
      = deningerCoordinateOperator r T hT x := by
  refine Subtype.ext ?_
  funext i
  exact hidem i ((x : ∀ i, E i) i)

/-- **The range of the limit projector is the limit of the ranges.**  A compatible family is in the
image exactly when each of its coordinates is. -/
theorem deningerCoordinateOperator_mem_range_iff {r : ∀ i j, i ≤ j → (E j →L[R] E i)}
    {T : ∀ i, E i →L[R] E i}
    (hT : ∀ i j (h : i ≤ j) (y : E j), r i j h (T j y) = T i (r i j h y))
    (hidem : ∀ i (y : E i), T i (T i y) = T i y) (x : deningerProjectiveLimit r) :
    x ∈ LinearMap.range (deningerCoordinateOperator r T hT).toLinearMap
      ↔ ∀ i, ((x : ∀ i, E i) i) ∈ LinearMap.range (T i).toLinearMap := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨(y : ∀ i, E i) i, rfl⟩
  · intro hx
    refine ⟨x, ?_⟩
    refine Subtype.ext ?_
    funext i
    obtain ⟨y, hy⟩ := hx i
    show T i ((x : ∀ i, E i) i) = (x : ∀ i, E i) i
    rw [← hy]
    exact hidem i y

/-- **The range of the limit projector is closed**, being the kernel of `1 - P`. -/
theorem deningerCoordinateOperator_range_isClosed [∀ i, T1Space (E i)]
    [∀ i, IsTopologicalAddGroup (E i)]
    {r : ∀ i j, i ≤ j → (E j →L[R] E i)} {T : ∀ i, E i →L[R] E i}
    (hT : ∀ i j (h : i ≤ j) (y : E j), r i j h (T j y) = T i (r i j h y))
    (hidem : ∀ i (y : E i), T i (T i y) = T i y) :
    IsClosed (Set.range (deningerCoordinateOperator r T hT)) := by
  have hker : Set.range (deningerCoordinateOperator r T hT)
      = (LinearMap.ker (ContinuousLinearMap.id R (deningerProjectiveLimit r)
        - deningerCoordinateOperator r T hT).toLinearMap :
          Set (deningerProjectiveLimit r)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show (ContinuousLinearMap.id R (deningerProjectiveLimit r)
        - deningerCoordinateOperator r T hT) (deningerCoordinateOperator r T hT y) = 0
      rw [sub_apply, ContinuousLinearMap.id_apply,
        deningerCoordinateOperator_idem hT hidem y, sub_self]
    · intro hx
      refine ⟨x, ?_⟩
      have hx' : (ContinuousLinearMap.id R (deningerProjectiveLimit r)
        - deningerCoordinateOperator r T hT) x = 0 := hx
      rw [sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at hx'
      exact hx'.symm
  rw [hker]
  exact ContinuousLinearMap.isClosed_ker _

/-- **The Green identity passes to the limit.**  Equality in a projective limit is detected
coordinatewise, so the stagewise Hodge decomposition holds verbatim on the limit. -/
theorem deningerLimitGreen {r : ∀ i j, i ≤ j → (E j →L[R] E i)}
    {Pr Q Qd G : ∀ i, E i →L[R] E i}
    (hP : ∀ i j (h : i ≤ j) (y : E j), r i j h (Pr j y) = Pr i (r i j h y))
    (hQ : ∀ i j (h : i ≤ j) (y : E j), r i j h (Q j y) = Q i (r i j h y))
    (hQd : ∀ i j (h : i ≤ j) (y : E j), r i j h (Qd j y) = Qd i (r i j h y))
    (hG : ∀ i j (h : i ≤ j) (y : E j), r i j h (G j y) = G i (r i j h y))
    (hgreen : ∀ i (y : E i), y - Pr i y = Q i (Qd i (G i y)) + Qd i (Q i (G i y)))
    (x : deningerProjectiveLimit r) :
    x - deningerCoordinateOperator r Pr hP x
      = deningerCoordinateOperator r Q hQ
          (deningerCoordinateOperator r Qd hQd (deningerCoordinateOperator r G hG x))
        + deningerCoordinateOperator r Qd hQd
          (deningerCoordinateOperator r Q hQ (deningerCoordinateOperator r G hG x)) := by
  refine Subtype.ext ?_
  funext i
  exact hgreen i ((x : ∀ i, E i) i)

end ProjectiveLimit

section WeightedSum

variable {ι : Type*}

/-- **Uniform stagewise bounds keep the weighted sum finite.** -/
theorem deningerWeightedSum_summable {w p q : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i)
    {C : ℝ} (hle : ∀ i, p i ≤ C * q i) (hsum : Summable fun i => w i * q i) :
    Summable fun i => w i * p i := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (hp i)) (fun i => ?_)
    (hsum.mul_left C)
  calc w i * p i ≤ w i * (C * q i) := mul_le_mul_of_nonneg_left (hle i) (hw i)
    _ = C * (w i * q i) := by ring

/-- **The weighted sum estimate.**  A stagewise bound with a constant independent of the stage
gives the same bound for the weighted sum seminorm. -/
theorem deningerWeightedSum_le {w p q : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i)
    {C : ℝ} (hle : ∀ i, p i ≤ C * q i) (hsum : Summable fun i => w i * q i) :
    (∑' i, w i * p i) ≤ C * ∑' i, w i * q i := by
  have hmono : (∑' i, w i * p i) ≤ ∑' i, C * (w i * q i) := by
    refine Summable.tsum_mono (deningerWeightedSum_summable hw hp hle hsum) (hsum.mul_left C)
      fun i => ?_
    calc w i * p i ≤ w i * (C * q i) := mul_le_mul_of_nonneg_left (hle i) (hw i)
      _ = C * (w i * q i) := by ring
  rwa [tsum_mul_left] at hmono

variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

/-- **The orthogonal case.**  Each stagewise energy projection is norm nonincreasing, so the
coordinatewise projection contracts every weighted sum seminorm: the constant is `1`, uniformly in
the stage. -/
theorem deningerEnergyProjection_weightedSum_le (K : ∀ i, Submodule ℝ (E i))
    [∀ i, (K i).HasOrthogonalProjection] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (x : ∀ i, E i)
    (hsum : Summable fun i => w i * ‖x i‖) :
    (∑' i, w i * ‖(K i).orthogonalProjectionOnto (x i)‖) ≤ ∑' i, w i * ‖x i‖ := by
  have hle : ∀ i, ‖(K i).orthogonalProjectionOnto (x i)‖ ≤ 1 * ‖x i‖ := by
    intro i
    rw [one_mul]
    exact (K i).norm_orthogonalProjectionOnto_apply_le (x i)
  have h := deningerWeightedSum_le (w := w)
    (p := fun i => ‖(K i).orthogonalProjectionOnto (x i)‖) (q := fun i => ‖x i‖)
    hw (fun i => norm_nonneg _) hle hsum
  rwa [one_mul] at h

end WeightedSum

end RHTower
