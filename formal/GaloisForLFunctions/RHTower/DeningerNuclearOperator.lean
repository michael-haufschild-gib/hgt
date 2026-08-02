import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Nuclear operators between normed spaces

A continuous linear map is nuclear when it is the sum of a family of rank-one maps whose norms are
absolutely summable.  Nuclear maps form a two-sided ideal: they are closed under sums and scalar
multiples, and composing with any bounded map on either side keeps them nuclear.

A nuclear map is the sum of its rank-one terms in the operator norm, so its norm is at most the
sum of the norms of the terms, and — being an operator-norm limit of finite-rank maps — it is
compact.

* `DeningerIsNuclear` : the definition.
* `deningerIsNuclear_smulRight`, `DeningerIsNuclear.add`, `.smul`, `.compL`, `.compR` : the ideal
  properties.
* `DeningerIsNuclear.hasSum_smulRight`, `.norm_le` : convergence in the operator norm.
* `DeningerIsNuclear.isCompactOperator` : a nuclear map is compact.
-/

namespace RHTower

open scoped Topology

section Definition

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **A nuclear map**: a sum of rank-one maps with absolutely summable norms. -/
def DeningerIsNuclear (T : X →L[𝕜] Y) : Prop :=
  ∃ (ι : Type) (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y),
    (Summable fun i => ‖φ i‖ * ‖y i‖) ∧ ∀ x, HasSum (fun i => φ i x • y i) (T x)

theorem deningerIsNuclear_zero : DeningerIsNuclear (0 : X →L[𝕜] Y) := by
  refine ⟨Empty, Empty.elim, Empty.elim, ?_, ?_⟩
  · exact summable_empty
  · intro x
    simp

/-- **A rank-one map is nuclear.** -/
theorem deningerIsNuclear_smulRight (φ : X →L[𝕜] 𝕜) (y : Y) :
    DeningerIsNuclear (φ.smulRight y) := by
  refine ⟨Unit, fun _ => φ, fun _ => y, ?_, ?_⟩
  · exact (hasSum_fintype fun _ : Unit => ‖φ‖ * ‖y‖).summable
  · intro x
    simp

theorem DeningerIsNuclear.add {S T : X →L[𝕜] Y} (hS : DeningerIsNuclear S)
    (hT : DeningerIsNuclear T) : DeningerIsNuclear (S + T) := by
  obtain ⟨ι, φ, y, hsum, happ⟩ := hS
  obtain ⟨κ, ψ, z, hsum', happ'⟩ := hT
  refine ⟨ι ⊕ κ, Sum.elim φ ψ, Sum.elim y z, ?_, ?_⟩
  · exact (HasSum.sum (f := fun p : ι ⊕ κ => ‖Sum.elim φ ψ p‖ * ‖Sum.elim y z p‖)
      hsum.hasSum hsum'.hasSum).summable
  · intro x
    exact HasSum.sum (f := fun p : ι ⊕ κ => Sum.elim φ ψ p x • Sum.elim y z p)
      (happ x) (happ' x)

theorem DeningerIsNuclear.smul {T : X →L[𝕜] Y} (hT : DeningerIsNuclear T) (c : 𝕜) :
    DeningerIsNuclear (c • T) := by
  obtain ⟨ι, φ, y, hsum, happ⟩ := hT
  refine ⟨ι, fun i => c • φ i, y, ?_, ?_⟩
  · have hle : ∀ i, ‖c • φ i‖ * ‖y i‖ = ‖c‖ * (‖φ i‖ * ‖y i‖) := by
      intro i
      rw [norm_smul, mul_assoc]
    simp only [hle]
    exact hsum.mul_left _
  · intro x
    have heq : (fun i => (c • φ i) x • y i) = fun i => c • (φ i x • y i) := by
      funext i
      rw [smul_apply, smul_assoc]
    rw [heq]
    simpa using (happ x).const_smul c

/-- **Composing on the left with a bounded map keeps nuclearity.** -/
theorem DeningerIsNuclear.compL {Z : Type*} [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {T : X →L[𝕜] Y} (hT : DeningerIsNuclear T) (S : Y →L[𝕜] Z) :
    DeningerIsNuclear (S.comp T) := by
  obtain ⟨ι, φ, y, hsum, happ⟩ := hT
  refine ⟨ι, φ, fun i => S (y i), ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hsum.mul_left ‖S‖)
    calc ‖φ i‖ * ‖S (y i)‖ ≤ ‖φ i‖ * (‖S‖ * ‖y i‖) := by
          exact mul_le_mul_of_nonneg_left (S.le_opNorm (y i)) (norm_nonneg _)
      _ = ‖S‖ * (‖φ i‖ * ‖y i‖) := by ring
  · intro x
    have h := S.hasSum (happ x)
    have heq : (fun i => S (φ i x • y i)) = fun i => φ i x • S (y i) := by
      funext i
      rw [map_smul]
    rw [heq] at h
    exact h

/-- **Composing on the right with a bounded map keeps nuclearity.** -/
theorem DeningerIsNuclear.compR {W : Type*} [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
    {T : X →L[𝕜] Y} (hT : DeningerIsNuclear T) (S : W →L[𝕜] X) :
    DeningerIsNuclear (T.comp S) := by
  obtain ⟨ι, φ, y, hsum, happ⟩ := hT
  refine ⟨ι, fun i => (φ i).comp S, y, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hsum.mul_right ‖S‖)
    calc ‖(φ i).comp S‖ * ‖y i‖ ≤ (‖φ i‖ * ‖S‖) * ‖y i‖ := by
          exact mul_le_mul_of_nonneg_right ((φ i).opNorm_comp_le S) (norm_nonneg _)
      _ = ‖φ i‖ * ‖y i‖ * ‖S‖ := by ring
  · intro w
    exact happ (S w)

end Definition

section OperatorNorm

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

/-- **A nuclear map is the sum of its rank-one terms in the operator norm.** -/
theorem DeningerIsNuclear.hasSum_smulRight {T : X →L[𝕜] Y}
    (hT : DeningerIsNuclear T) :
    ∃ (ι : Type) (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y),
      (Summable fun i => ‖φ i‖ * ‖y i‖)
        ∧ HasSum (fun i => (φ i).smulRight (y i)) T := by
  obtain ⟨ι, φ, y, hsum, happ⟩ := hT
  refine ⟨ι, φ, y, hsum, ?_⟩
  have hnorm : (fun i => ‖(φ i).smulRight (y i)‖) = fun i => ‖φ i‖ * ‖y i‖ := by
    funext i
    exact ContinuousLinearMap.norm_smulRight_apply (φ i) (y i)
  have hsummable : Summable fun i => (φ i).smulRight (y i) := by
    refine Summable.of_norm ?_
    rw [hnorm]
    exact hsum
  obtain ⟨S, hS⟩ := hsummable
  have hval : S = T := by
    refine ContinuousLinearMap.ext fun x => ?_
    have h1 := (ContinuousLinearMap.apply 𝕜 Y x).hasSum hS
    have heq : (fun i => (ContinuousLinearMap.apply 𝕜 Y x) ((φ i).smulRight (y i)))
        = fun i => φ i x • y i := by
      funext i
      exact ContinuousLinearMap.smulRight_apply
    rw [heq] at h1
    exact h1.unique (happ x)
  rwa [hval] at hS

omit [CompleteSpace Y] in
/-- **The operator norm is at most the sum of the norms of the rank-one terms.** -/
theorem DeningerIsNuclear.norm_le {T : X →L[𝕜] Y} {ι : Type}
    {φ : ι → (X →L[𝕜] 𝕜)} {y : ι → Y}
    (hsum : Summable fun i => ‖φ i‖ * ‖y i‖)
    (happ : HasSum (fun i => (φ i).smulRight (y i)) T) :
    ‖T‖ ≤ ∑' i, ‖φ i‖ * ‖y i‖ := by
  have hnorm : (fun i => ‖(φ i).smulRight (y i)‖) = fun i => ‖φ i‖ * ‖y i‖ := by
    funext i
    exact ContinuousLinearMap.norm_smulRight_apply (φ i) (y i)
  have hsummable : Summable fun i => ‖(φ i).smulRight (y i)‖ := by
    rw [hnorm]
    exact hsum
  have := norm_tsum_le_tsum_norm hsummable
  rw [happ.tsum_eq, hnorm] at this
  exact this

end OperatorNorm

section Compactness

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

omit [CompleteSpace Y] in
/-- **A rank-one map is compact.**  The image of the unit ball lies in the image of a closed ball
of scalars under scaling by a fixed vector, which is compact. -/
theorem deningerSmulRight_isCompactOperator (φ : X →L[𝕜] 𝕜) (y : Y) :
    IsCompactOperator (φ.smulRight y) := by
  show IsCompactOperator (⇑((φ.smulRight y : X →L[𝕜] Y) : X →ₗ[𝕜] Y))
  rw [isCompactOperator_iff_isCompact_closure_image_ball
    ((φ.smulRight y) : X →ₗ[𝕜] Y) (r := 1) one_pos]
  have hK : IsCompact ((fun c : 𝕜 => c • y) '' Metric.closedBall 0 ‖φ‖) :=
    (isCompact_closedBall 0 ‖φ‖).image (continuous_id.smul continuous_const)
  refine hK.of_isClosed_subset isClosed_closure ?_
  refine closure_minimal ?_ hK.isClosed
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨φ x, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖φ x‖ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
      _ ≤ ‖φ‖ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact le_of_lt (by simpa [dist_zero_right] using hx)
      _ = ‖φ‖ := mul_one _
  · exact ContinuousLinearMap.smulRight_apply.symm

/-- **A nuclear map is compact.**  Its finite partial sums are finite sums of rank-one maps, hence
compact, and they converge to it in the operator norm. -/
theorem DeningerIsNuclear.isCompactOperator {T : X →L[𝕜] Y} (hT : DeningerIsNuclear T) :
    IsCompactOperator T := by
  obtain ⟨ι, φ, y, -, hS⟩ := hT.hasSum_smulRight
  refine isCompactOperator_of_tendsto (l := (Filter.atTop : Filter (Finset ι)))
    (F := fun s : Finset ι => ∑ i ∈ s, (φ i).smulRight (y i)) hS ?_
  refine Filter.Eventually.of_forall fun s => ?_
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty]
      exact isCompactOperator_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (deningerSmulRight_isCompactOperator (φ a) (y a)).add ih

end Compactness

end RHTower

