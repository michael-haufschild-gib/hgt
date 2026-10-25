import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The algebraic size of infinite Hilbert images

An infinite-dimensional continuous image of a complex Banach space contains
continuum many independent vectors. Summable geometric source curves and
orthonormal image coordinates reduce independence to Dedekind's theorem.
A source of cardinality at most continuum gives equality of the rank.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {W H : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [CompleteSpace W] in
/-- An infinite-dimensional Hilbert image contains an orthonormal sequence with source preimages. -/
theorem exists_orthonormal_image_sequence (q : W →L[ℂ] H)
    (h : ¬ FiniteDimensional ℂ q.range) :
    ∃ x : ℕ → W, Orthonormal ℂ (fun n => q (x n)) := by
  classical
  let b := Module.Free.chooseBasis ℂ q.range
  haveI : Infinite (Module.Free.ChooseBasisIndex ℂ q.range) := by
    rw [← not_finite_iff_infinite]
    intro hfin
    letI := hfin
    exact h (FiniteDimensional.of_injective b.repr.toLinearMap b.repr.injective)
  let e := Infinite.natEmbedding (Module.Free.ChooseBasisIndex ℂ q.range)
  let v : ℕ → q.range := fun n => b (e n)
  have hv : LinearIndependent ℂ v := b.linearIndependent.comp _ e.injective
  let u := InnerProductSpace.gramSchmidtNormed ℂ v
  have hu : Orthonormal ℂ u := InnerProductSpace.gramSchmidtNormed_orthonormal hv
  choose x hx using fun n => (u n).property
  refine ⟨x, ?_⟩
  have hu' := hu.comp_linearIsometry q.range.subtypeₗᵢ
  change Orthonormal ℂ (fun n => (u n : H)) at hu'
  have heq : (fun n => q (x n)) = fun n => (u n : H) := by
    funext n
    exact hx n
  rw [heq]
  exact hu'

/-- Positive geometric weights make every chosen sequence summable after rescaling. -/
def geometricSourceWeight (x : ℕ → W) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n / (1 + ‖x n‖)

omit [NormedSpace ℂ W] [CompleteSpace W] in
theorem geometricSourceWeight_pos (x : ℕ → W) (n : ℕ) :
    0 < geometricSourceWeight x n := by
  unfold geometricSourceWeight
  positivity

theorem summable_geometricSource (x : ℕ → W) (t : Ioo (0 : ℝ) 1) :
    Summable (fun n => ((geometricSourceWeight x n * (t : ℝ) ^ n : ℝ) : ℂ) • x n) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1))
  intro n
  have ht : (t : ℝ) ^ n ≤ 1 := pow_le_one₀ t.property.1.le t.property.2.le
  have hratio : ‖x n‖ / (1 + ‖x n‖) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith only [norm_nonneg (x n)])
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (geometricSourceWeight_pos x n).le (pow_nonneg t.property.1.le n))]
  calc
    _ = (1 / 2 : ℝ) ^ n * ((t : ℝ) ^ n * (‖x n‖ / (1 + ‖x n‖))) := by
      unfold geometricSourceWeight
      ring
    _ ≤ (1 / 2 : ℝ) ^ n * (1 * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul ht hratio (by positivity) zero_le_one) (by positivity)
    _ = _ := by ring

def geometricSourceCurve (x : ℕ → W) (t : Ioo (0 : ℝ) 1) : W :=
  ∑' n, ((geometricSourceWeight x n * (t : ℝ) ^ n : ℝ) : ℂ) • x n

/-- Orthonormal image coordinates recover every geometric coefficient exactly. -/
theorem inner_geometricSourceCurve (q : W →L[ℂ] H) (x : ℕ → W)
    (hx : Orthonormal ℂ (fun n => q (x n))) (t : Ioo (0 : ℝ) 1) (m : ℕ) :
    ⟪q (x m), q (geometricSourceCurve x t)⟫_ℂ =
      ((geometricSourceWeight x m * (t : ℝ) ^ m : ℝ) : ℂ) := by
  let f : W →L[ℂ] ℂ := (innerSL ℂ (q (x m))).comp q
  have hs := f.hasSum (summable_geometricSource x t).hasSum
  have heq (n : ℕ) :
      f (((geometricSourceWeight x n * (t : ℝ) ^ n : ℝ) : ℂ) • x n) =
        if n = m then ((geometricSourceWeight x m * (t : ℝ) ^ m : ℝ) : ℂ) else 0 := by
    rw [map_smul]
    change ((geometricSourceWeight x n * (t : ℝ) ^ n : ℝ) : ℂ) *
      ⟪q (x m), q (x n)⟫_ℂ = _
    rw [orthonormal_iff_ite.mp hx m n]
    by_cases hnm : n = m
    · subst n
      simp only [ite_true, mul_one]
    · rw [if_neg (Ne.symm hnm), if_neg hnm, mul_zero]
  simp_rw [heq] at hs
  have ht := hs.tsum_eq
  rw [tsum_ite_eq] at ht
  exact ht.symm

/-- Distinct geometric power sequences are independent, by Dedekind's character theorem. -/
theorem geometricPowerSequences_linearIndependent :
    LinearIndependent ℂ (fun t : Ioo (0 : ℝ) 1 =>
      (powersHom ℂ ((t : ℝ) : ℂ) : Multiplicative ℕ → ℂ)) := by
  have h := (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp
    (powersHom ℂ) (powersHom ℂ).injective
  apply h.comp
  intro t s hts
  exact Subtype.ext (Complex.ofReal_injective hts)

/-- A summable analytic source family has continuum many independent Hilbert images. -/
theorem geometricSourceCurve_image_linearIndependent (q : W →L[ℂ] H) (x : ℕ → W)
    (hx : Orthonormal ℂ (fun n => q (x n))) :
    LinearIndependent ℂ (fun t : Ioo (0 : ℝ) 1 => q (geometricSourceCurve x t)) := by
  let f : H →ₗ[ℂ] (Multiplicative ℕ → ℂ) :=
    LinearMap.pi fun n => ((geometricSourceWeight x n.toAdd : ℂ)⁻¹) •
      (innerSL ℂ (q (x n.toAdd))).toLinearMap
  apply LinearIndependent.of_comp f
  have heq : f ∘ (fun t : Ioo (0 : ℝ) 1 => q (geometricSourceCurve x t)) =
      fun t : Ioo (0 : ℝ) 1 => (powersHom ℂ ((t : ℝ) : ℂ) : Multiplicative ℕ → ℂ) := by
    funext t n
    change (geometricSourceWeight x n.toAdd : ℂ)⁻¹ *
      ⟪q (x n.toAdd), q (geometricSourceCurve x t)⟫_ℂ = _
    rw [inner_geometricSourceCurve q x hx, Complex.ofReal_mul,
      inv_mul_cancel_left₀ (by exact_mod_cast (geometricSourceWeight_pos x n.toAdd).ne')]
    simp only [powersHom_apply, Complex.ofReal_pow]
  rw [heq]
  exact geometricPowerSequences_linearIndependent

/-- Every infinite-dimensional Hilbert image of a complex Banach space has Hamel rank at least continuum. -/
theorem continuum_le_rank_hilbert_image (q : W →L[ℂ] H)
    (h : ¬ FiniteDimensional ℂ q.range) : Cardinal.continuum ≤ Module.rank ℂ q.range := by
  obtain ⟨x, hx⟩ := exists_orthonormal_image_sequence q h
  let v : Ioo (0 : ℝ) 1 → q.range := fun t =>
    ⟨q (geometricSourceCurve x t), geometricSourceCurve x t, rfl⟩
  have hv : LinearIndependent ℂ v := by
    apply LinearIndependent.of_comp q.range.subtype
    exact geometricSourceCurve_image_linearIndependent q x hx
  have hr := hv.cardinal_le_rank
  rwa [Cardinal.mk_Ioo_real (by norm_num : (0 : ℝ) < 1)] at hr

/-- A source of cardinality at most continuum gives the exact infinite image rank. -/
theorem rank_hilbert_image_eq_continuum (q : W →L[ℂ] H)
    (hW : Cardinal.mk W ≤ Cardinal.continuum)
    (h : ¬ FiniteDimensional ℂ q.range) :
    Module.rank ℂ q.range = Cardinal.continuum := by
  apply le_antisymm _ (continuum_le_rank_hilbert_image q h)
  have hsurj : Function.Surjective (fun x : W => (⟨q x, x, rfl⟩ : q.range)) := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  exact (rank_le_card ℂ q.range).trans ((Cardinal.mk_le_of_surjective hsurj).trans hW)

end GaloisForLFunctions.HTGeometry
