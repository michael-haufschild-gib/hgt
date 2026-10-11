import GaloisForLFunctions.RHTower.WeilLogShiftObservableLaw
import GaloisForLFunctions.HTGeometry.QuantileCoupling

/-! Every interior quantile of a finite canonical observable law is one of its atoms. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry Set
open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalObservableLaw_cdf (r k : ℕ) (f : Fin (r + 1) → ℝ) (x : ℝ) :
    cdf (finiteWeilCanonicalObservableLaw r k f : Measure ℝ) x =
      ∑ i, finiteWeilCanonicalEdgeMass r k i * (if f i ≤ x then (1 : ℝ) else 0) := by
  classical
  rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic,
    finiteWeilCanonicalObservableLaw_integral_real]
  rfl

theorem finiteWeilCanonicalObservableLaw_quantile_eq_atom (r k : ℕ)
    (f : Fin (r + 1) → ℝ) (p : {p : ℝ // p ∈ Ioo 0 1}) :
    ∃ i, quantile (finiteWeilCanonicalObservableLaw r k f : Measure ℝ) p.val = f i := by
  classical
  let μ : Measure ℝ := finiteWeilCanonicalObservableLaw r k f
  let q := quantile μ p.val
  have hq : p.val ≤ cdf μ q := le_cdf_quantile p.property.1 p.property.2
  have hex : ∃ i, f i ≤ q := by
    by_contra! hn
    have hc : cdf μ q = 0 := by
      change cdf (finiteWeilCanonicalObservableLaw r k f : Measure ℝ) q = 0
      rw [finiteWeilCanonicalObservableLaw_cdf]
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg (not_le.mpr (hn i)), mul_zero]
    rw [hc] at hq
    exact (not_le_of_gt p.property.1) hq
  let A : Finset ℝ := (Finset.univ.image f).filter (fun x => x ≤ q)
  have hA : A.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨f i, Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩⟩
  let m := A.max' hA
  have hm : m ∈ A := Finset.max'_mem A hA
  have hmq : m ≤ q := (Finset.mem_filter.mp hm).2
  have hiff (i : Fin (r + 1)) : f i ≤ m ↔ f i ≤ q := by
    constructor
    · exact fun h => h.trans hmq
    · intro hi
      exact Finset.le_max' A (f i) (Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩)
  have hc : cdf μ m = cdf μ q := by
    change cdf (finiteWeilCanonicalObservableLaw r k f : Measure ℝ) m =
      cdf (finiteWeilCanonicalObservableLaw r k f : Measure ℝ) q
    rw [finiteWeilCanonicalObservableLaw_cdf, finiteWeilCanonicalObservableLaw_cdf]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hiff i]
  have hqm : q ≤ m := (quantile_le_iff p.property.1 p.property.2).mpr (by rw [hc]; exact hq)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hm).1
  exact ⟨i, (le_antisymm hqm hmq).trans hi.symm⟩

end RHTower
