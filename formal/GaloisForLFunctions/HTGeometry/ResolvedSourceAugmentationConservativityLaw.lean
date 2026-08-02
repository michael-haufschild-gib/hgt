import GaloisForLFunctions.HTGeometry.ResolvedDefectConservationLaw
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Resolved source augmentation conservativity

Every finite compositional conservation law augments a family of transported factor defects by
adding them.  This file identifies the whole cancellation module of that augmentation, proves the
finite Leibniz law for arbitrary products, and isolates the exact source-sector criterion under
which augmented conservation recovers the resolved defect.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R Z X : Type*}
variable [CommRing R]
variable [AddCommGroup Z] [Module R Z]
variable [AddCommGroup X] [Module R X]

/-- Addition of all channels of a finite resolved defect. -/
def finiteResolvedDefectAugmentation (n : ℕ) :
    (Fin n → Z) →ₗ[R] Z where
  toFun z := ∑ i, z i
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]

@[simp]
theorem finiteResolvedDefectAugmentation_apply (n : ℕ) (z : Fin n → Z) :
    finiteResolvedDefectAugmentation (R := R) n z = ∑ i, z i :=
  rfl

/-- Anchored coordinates for the universal zero-sum cancellation module. -/
def finiteResolvedDefectBoundary (n : ℕ) :
    (Fin n → Z) →ₗ[R] (Fin (n + 1) → Z) where
  toFun w := Fin.cases (-∑ i, w i) w
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero, Pi.add_apply, Finset.sum_add_distrib, neg_add_rev]
      rw [add_comm]
    · simp
  map_smul' c x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.smul_sum]
    · simp

@[simp]
theorem finiteResolvedDefectBoundary_zero (n : ℕ) (w : Fin n → Z) :
    finiteResolvedDefectBoundary (R := R) n w 0 = -∑ i, w i :=
  rfl

@[simp]
theorem finiteResolvedDefectBoundary_succ (n : ℕ) (w : Fin n → Z) (i : Fin n) :
    finiteResolvedDefectBoundary (R := R) n w i.succ = w i :=
  rfl

/-- Every anchored cancellation vector has zero augmentation. -/
theorem finiteResolvedDefectAugmentation_comp_boundary (n : ℕ) :
    (finiteResolvedDefectAugmentation (R := R) (Z := Z) (n + 1)).comp
        (finiteResolvedDefectBoundary (R := R) (Z := Z) n) = 0 := by
  apply LinearMap.ext
  intro w
  rw [LinearMap.comp_apply, finiteResolvedDefectAugmentation_apply, Fin.sum_univ_succ]
  simp

/-- The anchored cancellation coordinates retain every input channel. -/
theorem finiteResolvedDefectBoundary_injective (n : ℕ) :
    Function.Injective (finiteResolvedDefectBoundary (R := R) (Z := Z) n) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i.succ
  simpa using hi

/-- Finite augmentation is split by the distinguished zeroth channel. -/
theorem finiteResolvedDefectAugmentation_surjective (n : ℕ) :
    Function.Surjective
      (finiteResolvedDefectAugmentation (R := R) (Z := Z) (n + 1)) := by
  intro z
  let x : Fin (n + 1) → Z := Fin.cases z (fun _ => 0)
  refine ⟨x, ?_⟩
  rw [finiteResolvedDefectAugmentation_apply, Fin.sum_univ_succ]
  simp [x]

/-- **Universal finite cancellation sequence.**  The entire kernel of finite augmentation is the
range of the anchored zero-sum boundary; there are no other hidden resolved defects. -/
theorem ker_finiteResolvedDefectAugmentation_eq_range_boundary (n : ℕ) :
    LinearMap.ker (finiteResolvedDefectAugmentation (R := R) (Z := Z) (n + 1)) =
      LinearMap.range (finiteResolvedDefectBoundary (R := R) (Z := Z) n) := by
  ext z
  constructor
  · intro hz
    let w : Fin n → Z := fun i => z i.succ
    refine ⟨w, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change -∑ j : Fin n, z j.succ = z 0
      change (∑ i, z i) = 0 at hz
      rw [Fin.sum_univ_succ] at hz
      exact (eq_neg_of_add_eq_zero_left hz).symm
    · rfl
  · rintro ⟨w, rfl⟩
    change finiteResolvedDefectAugmentation (R := R) (Z := Z) (n + 1)
      (finiteResolvedDefectBoundary (R := R) (Z := Z) n w) = 0
    exact LinearMap.congr_fun
      (finiteResolvedDefectAugmentation_comp_boundary (R := R) (Z := Z) n) w

/-- Source-sector conservativity is exactly disjointness from the universal cancellation range. -/
theorem finiteResolvedDefect_conservativeOn_iff_disjoint_boundaryRange
    (n : ℕ) (S : Submodule R (Fin (n + 1) → Z)) :
    IsConservativeOn
        (finiteResolvedDefectAugmentation (R := R) (Z := Z) (n + 1)) S ↔
      Disjoint S
        (LinearMap.range (finiteResolvedDefectBoundary (R := R) (Z := Z) n)) := by
  rw [IsConservativeOn, ← ker_finiteResolvedDefectAugmentation_eq_range_boundary]

/-- Pointwise form of resolved source-sector conservativity. -/
theorem finiteResolvedDefect_conservativeOn_iff
    (n : ℕ) (S : Submodule R (Fin (n + 1) → Z)) :
    IsConservativeOn
        (finiteResolvedDefectAugmentation (R := R) (Z := Z) (n + 1)) S ↔
      ∀ z, z ∈ S →
        finiteResolvedDefectAugmentation (R := R) (Z := Z) (n + 1) z = 0 → z = 0 := by
  rw [IsConservativeOn, Submodule.disjoint_def]
  rfl

/-- **Resolved source-support law.**  Augmented conservation recovers a resolved defect exactly on
a source sector where augmentation is conservative. -/
theorem finiteResolvedDefect_eq_zero_iff_of_conservativeOn
    (n : ℕ) (D : X →ₗ[R] (Fin (n + 1) → Z))
    (S : Submodule R (Fin (n + 1) → Z))
    (hrange : LinearMap.range D ≤ S)
    (hconservative : IsConservativeOn
      (finiteResolvedDefectAugmentation (R := R) (Z := Z) (n + 1)) S) :
    (finiteResolvedDefectAugmentation (R := R) (Z := Z) (n + 1)).comp D = 0 ↔
      D = 0 :=
  observedDefect_eq_zero_iff_of_conservativeOn D
    (finiteResolvedDefectAugmentation (R := R) (Z := Z) (n + 1))
    S hrange hconservative

/-! ## Arbitrary-factor covariance -/

/-- Covariance defect of one factor relative to an ambient evolution. -/
def innerCovarianceDefect {A : Type*} [Ring A] (c a : A) : A :=
  c * a - a * c

/-- Factor-resolved summands in the covariance defect of an ordered product. -/
def resolvedProductCovarianceDefects {A : Type*} [Ring A] (c : A) : List A → List A
  | [] => []
  | a :: factors =>
      innerCovarianceDefect c a * factors.prod ::
        (resolvedProductCovarianceDefects c factors).map (fun d => a * d)

theorem length_resolvedProductCovarianceDefects
    {A : Type*} [Ring A] (c : A) (factors : List A) :
    (resolvedProductCovarianceDefects c factors).length = factors.length := by
  induction factors with
  | nil => rfl
  | cons a factors ih => simp [resolvedProductCovarianceDefects, ih]

/-- **Finite Leibniz augmentation law.**  The covariance defect of an arbitrary ordered product is
the sum of all transported factor defects. -/
theorem sum_resolvedProductCovarianceDefects
    {A : Type*} [Ring A] (c : A) (factors : List A) :
    (resolvedProductCovarianceDefects c factors).sum =
      innerCovarianceDefect c factors.prod := by
  induction factors with
  | nil => simp [resolvedProductCovarianceDefects, innerCovarianceDefect]
  | cons a factors ih =>
      have hmap :
          ((resolvedProductCovarianceDefects c factors).map (fun d => a * d)).sum =
            a * (resolvedProductCovarianceDefects c factors).sum := by
        simpa using
          (List.sum_map_mul_left (resolvedProductCovarianceDefects c factors)
            (fun d => d) a)
      rw [resolvedProductCovarianceDefects, List.sum_cons, hmap, ih, List.prod_cons]
      unfold innerCovarianceDefect
      noncomm_ring

/-! ## Quantitative stability -/

/-- Uniform source-sector conservativity: observation is bounded below on the selected sector. -/
def IsUniformlyConservativeOn
    {K E F : Type*} [NormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup F] [NormedSpace K F]
    (observe : E →ₗ[K] F) (sector : Submodule K E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x, x ∈ sector → c * ‖x‖ ≤ ‖observe x‖

/-- A uniform positive lower bound prevents every algebraic cancellation vector in the sector. -/
theorem isConservativeOn_of_isUniformlyConservativeOn
    {K E F : Type*} [NormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [SeminormedAddCommGroup F] [NormedSpace K F]
    (observe : E →ₗ[K] F) (sector : Submodule K E)
    (huniform : IsUniformlyConservativeOn observe sector) :
    IsConservativeOn observe sector := by
  rw [IsConservativeOn, Submodule.disjoint_def]
  intro x hxSector hxKernel
  obtain ⟨c, hc, hbound⟩ := huniform
  have hxBound := hbound x hxSector
  change observe x = 0 at hxKernel
  rw [hxKernel, norm_zero] at hxBound
  have hxNorm : ‖x‖ = 0 := by
    nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hxNorm

end

end GaloisForLFunctions.HTGeometry
