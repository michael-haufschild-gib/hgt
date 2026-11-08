import Mathlib
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanCalibration

/-!
# Weil towers and their level sums

A **Weil tower** is a family of complex modes `z_i`, indexed with multiplicity, closed under complex
conjugation and under the functional equation `z ↦ 1/z`. A curve datum of genus `g` over `𝔽_q` is a
tower of rank `2g` (its normalized Frobenius eigenvalues); the prime tower of `ζ` at base `ℓ` is the
tower of rank `∞` with modes `e^{ℓ(ρ−½)}`.

With weights `b_i`, the **level sum** `S(ν) = Σ_i b_i z_iᵛ`, `ν ∈ ℤ`, is the infinite-rank power sum:
for a curve with unit weights it is the trace of Frobenius at level `ν`; for `ζ` it samples a Weil lag
or Lefschetz sequence along the tower.

* `levelSum_neg`: for weights compatible with the reflection `z ↦ 1/z̄`, `S(−ν) = conj S(ν)`. The
  functional equation acts on level sums only through this symmetry, so the reflected inner layer adds
  no information to the outer one.
* `norm_levelSum_le`: `|S(ν)| ≤ (Σ|b_i|) Rᵛ` when every mode has modulus `≤ R`, the trace-norm bound.
* The reflection maps the outer part `|z| > 1` bijectively onto the inner part `|z| < 1`
  (`reflPerm_mapsTo_outer`, `reflPerm_outer_image`).
* `CurveDatum.toWeilTower`: a curve datum is a tower of finite rank whose unit-weight level sums are the
  power sums of the datum (`levelSum_toWeilTower_one`).
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- A **Weil tower**: modes `z i` closed under conjugation and under inversion. -/
structure WeilTower (ι : Type*) where
  z : ι → ℂ
  conjPerm : Equiv.Perm ι
  z_conjPerm : ∀ i, z (conjPerm i) = starRingEnd ℂ (z i)
  invPerm : Equiv.Perm ι
  z_invPerm : ∀ i, z (invPerm i) * z i = 1

/-- The **level sum** `S(ν) = Σ_i b_i z_iᵛ`. -/
def levelSum {ι : Type*} (z b : ι → ℂ) (ν : ℤ) : ℂ := ∑' i, b i * z i ^ ν

namespace WeilTower

variable {ι : Type*} (T : WeilTower ι)

theorem z_ne_zero (i : ι) : T.z i ≠ 0 := right_ne_zero_of_mul_eq_one (T.z_invPerm i)

theorem z_invPerm_eq (i : ι) : T.z (T.invPerm i) = (T.z i)⁻¹ :=
  eq_inv_of_mul_eq_one_left (T.z_invPerm i)

/-- The reflection `z ↦ 1/z̄`: the functional equation followed by conjugation. -/
def reflPerm : Equiv.Perm ι := T.invPerm.trans T.conjPerm

theorem z_reflPerm (i : ι) : T.z (T.reflPerm i) = (starRingEnd ℂ (T.z i))⁻¹ := by
  simp only [reflPerm, Equiv.trans_apply, T.z_conjPerm, T.z_invPerm_eq, map_inv₀]

theorem norm_z_reflPerm (i : ι) : ‖T.z (T.reflPerm i)‖ = ‖T.z i‖⁻¹ := by
  rw [z_reflPerm, norm_inv, Complex.norm_conj]

/-- **The functional equation on level sums.** For weights compatible with the reflection,
`S(−ν) = conj S(ν)`. -/
theorem levelSum_neg {b : ι → ℂ} (hb : ∀ i, b (T.reflPerm i) = starRingEnd ℂ (b i)) (ν : ℤ) :
    levelSum T.z b (-ν) = starRingEnd ℂ (levelSum T.z b ν) := by
  unfold levelSum
  conv_lhs => rw [← Equiv.tsum_eq T.reflPerm]
  rw [conj_tsum]
  refine tsum_congr fun i => ?_
  rw [hb, T.z_reflPerm, inv_zpow', neg_neg, map_mul, map_zpow₀]

/-- The reflection maps the outer part into the inner part. -/
theorem reflPerm_mapsTo_outer :
    Set.MapsTo T.reflPerm {i | 1 < ‖T.z i‖} {i | ‖T.z i‖ < 1} := by
  intro i hi
  simp only [Set.mem_setOf_eq, T.norm_z_reflPerm] at hi ⊢
  exact inv_lt_one_of_one_lt₀ hi

/-- The reflection maps the outer part **onto** the inner part: the two layers have equal rank. -/
theorem reflPerm_outer_image :
    T.reflPerm '' {i | 1 < ‖T.z i‖} = {i | ‖T.z i‖ < 1} := by
  refine Set.Subset.antisymm (T.reflPerm_mapsTo_outer.image_subset) fun j hj => ?_
  refine ⟨T.reflPerm.symm j, ?_, T.reflPerm.apply_symm_apply j⟩
  have hj' : ‖T.z (T.reflPerm (T.reflPerm.symm j))‖ < 1 := by
    rwa [T.reflPerm.apply_symm_apply]
  rw [T.norm_z_reflPerm] at hj'
  have hpos : 0 < ‖T.z (T.reflPerm.symm j)‖ := norm_pos_iff.mpr (T.z_ne_zero _)
  exact (inv_lt_one₀ hpos).mp hj'

theorem encard_outer_eq_encard_inner :
    {i | 1 < ‖T.z i‖}.encard = {i | ‖T.z i‖ < 1}.encard := by
  rw [← T.reflPerm_outer_image, T.reflPerm.injective.encard_image]

end WeilTower

/-- **Trace-norm bound.** If every mode has modulus `≤ R` and the weights are summable, then
`|S(ν)| ≤ (Σ|b_i|) Rᵛ` at every level `ν ≥ 0`. -/
theorem norm_levelSum_le {ι : Type*} {z b : ι → ℂ} {R : ℝ}
    (hz : ∀ i, ‖z i‖ ≤ R) (hb : Summable fun i => ‖b i‖) (ν : ℕ) :
    ‖levelSum z b ν‖ ≤ (∑' i, ‖b i‖) * R ^ ν := by
  unfold levelSum
  have hterm : ∀ i, ‖b i * z i ^ (ν : ℤ)‖ ≤ ‖b i‖ * R ^ ν := fun i => by
    rw [norm_mul, zpow_natCast, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hz i) ν) (norm_nonneg _)
  have hs : Summable fun i => ‖b i‖ * R ^ ν := hb.mul_right _
  calc ‖∑' i, b i * z i ^ (ν : ℤ)‖ ≤ ∑' i, ‖b i * z i ^ (ν : ℤ)‖ :=
        norm_tsum_le_tsum_norm (hs.of_nonneg_of_le (fun _ => norm_nonneg _) hterm)
    _ ≤ ∑' i, ‖b i‖ * R ^ ν :=
        (hs.of_nonneg_of_le (fun _ => norm_nonneg _) hterm).tsum_le_tsum hterm hs
    _ = (∑' i, ‖b i‖) * R ^ ν := tsum_mul_right

/-- Summability of a weighted level sum at a level `ν ≥ 0` for bounded modes. -/
theorem summable_levelTerm {ι : Type*} {z b : ι → ℂ} {R : ℝ}
    (hz : ∀ i, ‖z i‖ ≤ R) (hb : Summable fun i => ‖b i‖) (ν : ℕ) :
    Summable fun i => b i * z i ^ (ν : ℤ) := by
  refine Summable.of_norm ((hb.mul_right (R ^ ν)).of_nonneg_of_le (fun _ => norm_nonneg _) ?_)
  intro i
  rw [norm_mul, zpow_natCast, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hz i) ν) (norm_nonneg _)

/-! ### Curves are towers of finite rank -/

open ArithmeticCastelnuovoSeveri in
/-- A curve datum is a Weil tower of finite rank `2g`. -/
def _root_.GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum.toWeilTower {ι : Type*}
    [Fintype ι] (D : CurveDatum ι) : WeilTower ι where
  z := D.β
  conjPerm := D.conjPerm
  z_conjPerm := D.β_conjPerm
  invPerm := D.fePerm
  z_invPerm := D.β_fePerm

open ArithmeticCastelnuovoSeveri in
/-- The unit-weight level sums of a curve datum are its power sums. -/
theorem levelSum_toWeilTower_one {ι : Type*} [Fintype ι] (D : CurveDatum ι) (ν : ℕ) :
    levelSum D.toWeilTower.z (fun _ => 1) ν = D.powerSum ν := by
  simp [levelSum, CurveDatum.toWeilTower, CurveDatum.powerSum, tsum_fintype]

end GaloisForLFunctions.InfiniteRankWeilTheory
