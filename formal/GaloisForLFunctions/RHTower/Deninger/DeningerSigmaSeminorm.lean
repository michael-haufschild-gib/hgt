import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearProduct

/-!
# The seminorms of a locally convex direct sum

The direct sum of a family of locally convex spaces carries the seminorms that add one seminorm per
coordinate.  A vector of the direct sum has finite support, so the sum is finite and no convergence
question arises; writing it as an unconditional sum avoids any decidability hypothesis on the
coordinates.

Each coordinate seminorm is dominated by the direct sum seminorm, and the direct sum seminorm of a
coordinate vector is its coordinate seminorm — the two facts that make the coordinate projections
and inclusions bounded.

* `deningerSigmaSummable` : the coordinate seminorms of a vector are summable, being finitely
  supported.
* `deningerSigmaSeminorm` : **the direct sum seminorm.**
* `deningerSigmaSeminorm_proj_le`, `deningerSigmaSeminorm_single` : the projection and inclusion
  bounds.
* `deningerSigmaFamily` : **the direct sum presentation**, indexed by a choice of coordinate
  seminorm and a weight for each coordinate.
-/

namespace RHTower

open scoped NNReal

section SigmaSeminorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type*} {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]

/-- The coordinate seminorms of a vector of the direct sum are summable: only finitely many
coordinates are nonzero. -/
theorem deningerSigmaSummable (q : ∀ i, Seminorm 𝕜 (F i)) (x : Π₀ i, F i) :
    Summable fun i => q i (x i) := by
  have hfin := x.finite_support
  refine summable_of_ne_finset_zero (s := hfin.toFinset) ?_
  intro i hi
  have hx : x i = 0 := by
    by_contra h
    exact hi (hfin.mem_toFinset.mpr h)
  rw [hx, map_zero]

/-- **The direct sum seminorm**: the sum of one seminorm per coordinate. -/
noncomputable def deningerSigmaSeminorm (q : ∀ i, Seminorm 𝕜 (F i)) : Seminorm 𝕜 (Π₀ i, F i) where
  toFun x := ∑' i, q i (x i)
  map_zero' := by simp
  add_le' x y := by
    have hx := deningerSigmaSummable q x
    have hy := deningerSigmaSummable q y
    have hxy := deningerSigmaSummable q (x + y)
    calc ∑' i, q i ((x + y) i) ≤ ∑' i, (q i (x i) + q i (y i)) := by
          refine hxy.tsum_le_tsum (fun i => ?_) (hx.add hy)
          rw [DFinsupp.add_apply]
          exact map_add_le_add (q i) _ _
      _ = ∑' i, q i (x i) + ∑' i, q i (y i) := hx.tsum_add hy
  neg' x := by
    have h : ∀ i, q i ((-x) i) = q i (x i) := by
      intro i
      rw [DFinsupp.neg_apply, map_neg_eq_map]
    simp only [h]
  smul' c x := by
    have h : ∀ i, q i ((c • x) i) = ‖c‖ * q i (x i) := by
      intro i
      rw [DFinsupp.smul_apply, map_smul_eq_mul]
    simp only [h]
    exact tsum_mul_left

@[simp]
theorem deningerSigmaSeminorm_apply (q : ∀ i, Seminorm 𝕜 (F i)) (x : Π₀ i, F i) :
    deningerSigmaSeminorm q x = ∑' i, q i (x i) := rfl

/-- Every coordinate seminorm is dominated by the direct sum seminorm. -/
theorem deningerSigmaSeminorm_proj_le (q : ∀ i, Seminorm 𝕜 (F i)) (x : Π₀ i, F i) (i : ι) :
    q i (x i) ≤ deningerSigmaSeminorm q x :=
  (deningerSigmaSummable q x).le_tsum i fun j _ => apply_nonneg (q j) (x j)

/-- The direct sum seminorm of a coordinate vector is its coordinate seminorm. -/
theorem deningerSigmaSeminorm_single [DecidableEq ι] (q : ∀ i, Seminorm 𝕜 (F i)) (i : ι)
    (v : F i) : deningerSigmaSeminorm q (DFinsupp.single i v) = q i v := by
  rw [deningerSigmaSeminorm_apply]
  refine (tsum_eq_single i ?_).trans ?_
  · intro j hj
    rw [DFinsupp.single_eq_of_ne hj, map_zero]
  · rw [DFinsupp.single_eq_same]

end SigmaSeminorm

section SigmaFamily

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type*} {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]

/-- **The direct sum presentation** of a direct sum of locally convex spaces: one seminorm for each
choice of a coordinate seminorm and a weight per coordinate. -/
noncomputable def deningerSigmaFamily {κ : ι → Type*} (P : ∀ i, SeminormFamily 𝕜 (F i) (κ i)) :
    SeminormFamily 𝕜 (Π₀ i, F i) ((∀ i, κ i) × (ι → ℝ≥0)) :=
  fun ac => deningerSigmaSeminorm fun i => ac.2 i • P i (ac.1 i)

theorem deningerSigmaFamily_apply {κ : ι → Type*} (P : ∀ i, SeminormFamily 𝕜 (F i) (κ i))
    (ac : (∀ i, κ i) × (ι → ℝ≥0)) (x : Π₀ i, F i) :
    deningerSigmaFamily P ac x = ∑' i, (ac.2 i : ℝ) * P i (ac.1 i) (x i) := by
  rw [deningerSigmaFamily, deningerSigmaSeminorm_apply]
  exact tsum_congr fun i => by rw [smul_apply, NNReal.smul_def, smul_eq_mul]

theorem deningerSigmaFamily_single [DecidableEq ι] {κ : ι → Type*}
    (P : ∀ i, SeminormFamily 𝕜 (F i) (κ i)) (ac : (∀ i, κ i) × (ι → ℝ≥0)) (i : ι) (u : F i) :
    deningerSigmaFamily P ac (DFinsupp.lsingle (R := 𝕜) i u)
      = (ac.2 i : ℝ) * P i (ac.1 i) u := by
  rw [DFinsupp.lsingle_apply, deningerSigmaFamily, deningerSigmaSeminorm_single,
    smul_apply, NNReal.smul_def, smul_eq_mul]

end SigmaFamily

end RHTower
