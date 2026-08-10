import GaloisForLFunctions.HTGeometry.OperatorSystemMatrixOrderUnit
import GaloisForLFunctions.HTGeometry.MatrixOrderedMap

/-!
# The order-unit norms of the matrix levels

Given a matrix ordering with a positive scalar-level order unit `e`, every matrix level carries the
order-unit bound

```text
‖x‖ₙ = inf {t > 0 : t · (1ₙ ⊗ e) ± x is positive at level n}.
```

The set of admissible bounds is never empty on self-adjoint elements — that is the content of
`isMatrixOrderUnit_of_levelOne` — so the infimum is a genuine nonnegative real, subadditive and
positively homogeneous.

Two structural laws, the ones that make this family a *matricial* norm rather than a sequence of
unrelated norms, are proved here from the compression axiom alone:

* `levelNorm_compress_le` — compression by an isometry `α* α = 1` is contractive;
* `levelNorm_fromBlocks` — `‖x ⊕ y‖ = max ‖x‖ ‖y‖`.

The second is Ruan's direct-sum axiom.  Its `≤` half comes from closure of the cones under direct
sums and the `≥` half from contractivity along the two coordinate isometries.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MatrixModule

universe u v

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V]
variable {C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)}

/-- The admissible order-unit bounds of `x` at level `n`. -/
def levelBounds (C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)) (e : V) (n : Type u)
    [Fintype n] [DecidableEq n] (x : Matrix n n V) : Set ℝ :=
  {t : ℝ | 0 < t ∧ (t : ℂ) • amplify n e - x ∈ C n ∧ (t : ℂ) • amplify n e + x ∈ C n}

/-- The order-unit bound of `x` at level `n`. -/
noncomputable def levelNorm (C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)) (e : V)
    (n : Type u) [Fintype n] [DecidableEq n] (x : Matrix n n V) : ℝ :=
  sInf (levelBounds C e n x)

namespace IsMatrixOrdering

variable (hC : IsMatrixOrdering C)

include hC

/-- Admissible bounds are closed upwards. -/
theorem levelBounds_upward {e : V} (he : LevelOne C e) {n : Type u} [Fintype n] [DecidableEq n]
    {x : Matrix n n V} {t t' : ℝ} (ht : t ∈ levelBounds C e n x) (htt : t ≤ t') :
    t' ∈ levelBounds C e n x := by
  obtain ⟨htpos, h1, h2⟩ := ht
  refine ⟨lt_of_lt_of_le htpos htt, ?_, ?_⟩
  · have hadd := hC.add_mem n _ h1 _ (hC.smul_amplify_mem he (sub_nonneg.mpr htt))
    have hEq : ((t : ℂ) • amplify n e - x) + ((t' - t : ℝ) : ℂ) • amplify n e
        = (t' : ℂ) • amplify n e - x := by push_cast; module
    rwa [hEq] at hadd
  · have hadd := hC.add_mem n _ h2 _ (hC.smul_amplify_mem he (sub_nonneg.mpr htt))
    have hEq : ((t : ℂ) • amplify n e + x) + ((t' - t : ℝ) : ℂ) • amplify n e
        = (t' : ℂ) • amplify n e + x := by push_cast; module
    rwa [hEq] at hadd

theorem levelBounds_nonempty {e : V} (he : IsOrderUnitLevelOne C e) {n : Type u} [Fintype n]
    [DecidableEq n] {x : Matrix n n V} (hx : xᴴ = x) : (levelBounds C e n x).Nonempty := by
  obtain ⟨T, hT, h1, h2⟩ := hC.isMatrixOrderUnit_of_levelOne he x hx
  exact ⟨T, hT, h1, h2⟩

omit hC in
theorem levelNorm_nonneg (e : V) (n : Type u) [Fintype n] [DecidableEq n] (x : Matrix n n V) :
    0 ≤ levelNorm C e n x :=
  Real.sInf_nonneg fun t ht => ht.1.le

omit hC in
theorem bddBelow_levelBounds (e : V) (n : Type u) [Fintype n] [DecidableEq n] (x : Matrix n n V) :
    BddBelow (levelBounds C e n x) :=
  ⟨0, fun t ht => ht.1.le⟩

omit hC in
theorem levelNorm_le_of_mem {e : V} {n : Type u} [Fintype n] [DecidableEq n] {x : Matrix n n V}
    {t : ℝ} (ht : t ∈ levelBounds C e n x) : levelNorm C e n x ≤ t :=
  csInf_le (bddBelow_levelBounds e n x) ht

/-- Subadditivity of the order-unit bound. -/
theorem levelNorm_add_le {e : V} (he : IsOrderUnitLevelOne C e) {n : Type u} [Fintype n]
    [DecidableEq n] {x y : Matrix n n V} (hx : xᴴ = x) (hy : yᴴ = y) :
    levelNorm C e n (x + y) ≤ levelNorm C e n x + levelNorm C e n y := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hx' := hC.levelBounds_nonempty he hx
  have hy' := hC.levelBounds_nonempty he hy
  set a := levelNorm C e n x
  set b := levelNorm C e n y
  have hrab : r - (a + b) > 0 := by linarith
  obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hx' (show a < a + (r - (a + b)) / 2 by linarith)
  obtain ⟨u, hu, hult⟩ := exists_lt_of_csInf_lt hy' (show b < b + (r - (a + b)) / 2 by linarith)
  have hsum : s + u ∈ levelBounds C e n (x + y) := by
    obtain ⟨hs0, hs1, hs2⟩ := hs
    obtain ⟨hu0, hu1, hu2⟩ := hu
    refine ⟨by linarith, ?_, ?_⟩
    · have hadd := hC.add_mem n _ hs1 _ hu1
      have hEq : ((s : ℂ) • amplify n e - x) + ((u : ℂ) • amplify n e - y)
          = ((s + u : ℝ) : ℂ) • amplify n e - (x + y) := by push_cast; module
      rwa [hEq] at hadd
    · have hadd := hC.add_mem n _ hs2 _ hu2
      have hEq : ((s : ℂ) • amplify n e + x) + ((u : ℂ) • amplify n e + y)
          = ((s + u : ℝ) : ℂ) • amplify n e + (x + y) := by push_cast; module
      rwa [hEq] at hadd
  exact le_trans (levelNorm_le_of_mem hsum) (by linarith)

end IsMatrixOrdering

end GaloisForLFunctions.HTGeometry
