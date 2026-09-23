import GaloisForLFunctions.HTGeometry.SourcePairRealGradedHigherTraceAnomaly
import GaloisForLFunctions.HTGeometry.FredholmDeterminantExamples

/-!
# Source-pair odd cells

This file assembles the four-channel odd cell of a complex kernel entrywise.  It proves finite
support, exact Hilbert--Schmidt energy, a uniform norm bound, and diagonal-trace cancellation.
No eigenvalue, zero, or spectral projection enters the construction.
-/

open Complex Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Entrywise four-channel odd cell, scaled by the real source aperture `r`. -/
def sourcePairOddCellKernel (r : ℝ) (K : ι × ι → ℂ) :
    (ι × Fin 4) × (ι × Fin 4) → ℂ :=
  fun p => sourcePairRealOddBlock (K (p.1.1, p.2.1)).im p.1.2 p.2.2 / (r : ℂ)

omit [DecidableEq ι] in
theorem sourcePairOddCellKernel_cell (r : ℝ) (K : ι × ι → ℂ)
    (i j : ι) (c d : Fin 4) :
    sourcePairOddCellKernel r K ((i, c), (j, d)) =
      sourcePairRealOddBlock (K (i, j)).im c d / (r : ℂ) := rfl

/-- Product aperture induced canonically from a base aperture. -/
def sourcePairOddCellCutoff (s : Finset ι) : Finset (ι × Fin 4) :=
  s ×ˢ Finset.univ

omit [DecidableEq ι] in
theorem sourcePairOddCellKernel_support (r : ℝ) {K : ι × ι → ℂ} (s : Finset ι)
    (hK : ∀ p : ι × ι, p ∉ s ×ˢ s → K p = 0)
    (p : (ι × Fin 4) × (ι × Fin 4))
    (hp : p ∉ sourcePairOddCellCutoff s ×ˢ sourcePairOddCellCutoff s) :
    sourcePairOddCellKernel r K p = 0 := by
  have hbase : (p.1.1, p.2.1) ∉ s ×ˢ s := by
    intro hmem
    exact hp (Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hmem).1, Finset.mem_univ _⟩,
        Finset.mem_product.mpr ⟨(Finset.mem_product.mp hmem).2, Finset.mem_univ _⟩⟩)
  rw [sourcePairOddCellKernel, hK _ hbase]
  obtain ⟨⟨i, c⟩, ⟨j, d⟩⟩ := p
  fin_cases c <;> fin_cases d <;>
    simp [sourcePairRealOddBlock]

/-- Reindex source coordinates independently from four internal odd channels. -/
def pairShuffle : ((ι × Fin 4) × (ι × Fin 4)) ≃ ((ι × ι) × (Fin 4 × Fin 4)) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem internal_sum (r b : ℝ) :
    ∑ q : Fin 4 × Fin 4,
      ‖sourcePairRealOddBlock b q.1 q.2 / (r : ℂ)‖ ^ (2 : ℕ) =
      4 * (|b| / |r|) ^ (2 : ℕ) := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_four, sourcePairRealOddBlock,
    Complex.norm_real]
  ring

omit [DecidableEq ι] in
theorem isHS_sourcePairOddCellKernel {r : ℝ} (hr : 1 ≤ r)
    {K : ι × ι → ℂ} (hK : HilbertSchmidt.IsHS K) :
    HilbertSchmidt.IsHS (sourcePairOddCellKernel r K) := by
  rw [HilbertSchmidt.IsHS]
  apply ((pairShuffle (ι := ι)).summable_iff (f := fun q =>
    ‖sourcePairOddCellKernel r K
      (((pairShuffle (ι := ι)).symm q))‖ ^ (2 : ℕ))).mpr
  change Summable (fun p : (ι × ι) × (Fin 4 × Fin 4) =>
    ‖sourcePairOddCellKernel r K ((p.1.1, p.2.1), (p.1.2, p.2.2))‖ ^ (2 : ℕ))
  rw [summable_prod_of_nonneg (fun _ => by positivity)]
  constructor
  · intro p
    exact Summable.of_finite
  · rw [show (fun p : ι × ι => ∑' q : Fin 4 × Fin 4,
          ‖sourcePairOddCellKernel r K ((p.1, q.1), (p.2, q.2))‖ ^ (2 : ℕ)) =
        (fun p => 4 * (|(K p).im| / |r|) ^ (2 : ℕ)) by
        funext p
        rw [tsum_fintype]
        simpa [sourcePairOddCellKernel, Complex.norm_real] using
          internal_sum r (K p).im]
    apply Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun p => ?_) (hK.mul_left 4)
    have hrabs : 1 ≤ |r| := by simpa [abs_of_nonneg (le_trans zero_le_one hr)] using hr
    have him : |(K p).im| ≤ ‖K p‖ := Complex.abs_im_le_norm _
    have hdiv : |(K p).im| / |r| ≤ ‖K p‖ := by
      calc
        |(K p).im| / |r| ≤ |(K p).im| := div_le_self (abs_nonneg _) hrabs
        _ ≤ ‖K p‖ := him
    have hleft : 0 ≤ |(K p).im| / |r| := div_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [sq_nonneg (|(K p).im| / |r|), sq_nonneg ‖K p‖]

omit [DecidableEq ι] in
theorem hsNormSq_sourcePairOddCellKernel {r : ℝ} (hr : 1 ≤ r)
    {K : ι × ι → ℂ} (hK : HilbertSchmidt.IsHS K) :
    HilbertSchmidt.hsNormSq (sourcePairOddCellKernel r K) =
      ∑' p : ι × ι, 4 * (|(K p).im| / |r|) ^ (2 : ℕ) := by
  let f : (ι × ι) × (Fin 4 × Fin 4) → ℝ := fun p =>
    ‖sourcePairOddCellKernel r K ((p.1.1, p.2.1), (p.1.2, p.2.2))‖ ^ (2 : ℕ)
  have hodd := isHS_sourcePairOddCellKernel hr hK
  change Summable (fun p => ‖sourcePairOddCellKernel r K p‖ ^ (2 : ℕ)) at hodd
  have hf : Summable f := by
    apply ((pairShuffle (ι := ι)).summable_iff (f := f)).mp
    convert hodd using 1 <;> rfl
  rw [HilbertSchmidt.hsNormSq]
  calc
    (∑' p : (ι × Fin 4) × (ι × Fin 4),
        ‖sourcePairOddCellKernel r K p‖ ^ (2 : ℕ)) = ∑' p, f p := by
      exact (pairShuffle (ι := ι)).tsum_eq f
    _ = ∑' p : ι × ι, ∑' q : Fin 4 × Fin 4, f (p, q) := hf.tsum_prod
    _ = ∑' p : ι × ι, 4 * (|(K p).im| / |r|) ^ (2 : ℕ) := by
      apply tsum_congr
      intro p
      rw [tsum_fintype]
      simpa [f, sourcePairOddCellKernel, Complex.norm_real] using
        internal_sum r (K p).im

omit [DecidableEq ι] in
theorem hsNormSq_sourcePairOddCellKernel_le {r : ℝ} (hr : 1 ≤ r)
    {K : ι × ι → ℂ} (hK : HilbertSchmidt.IsHS K) :
    HilbertSchmidt.hsNormSq (sourcePairOddCellKernel r K) ≤
      (4 / r ^ (2 : ℕ)) * HilbertSchmidt.hsNormSq K := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hleft : Summable (fun p : ι × ι => 4 * (|(K p).im| / |r|) ^ (2 : ℕ)) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun p => ?_) (hK.mul_left 4)
    have hrabs : 1 ≤ |r| := by simpa [abs_of_pos hr0] using hr
    have hdiv : |(K p).im| / |r| ≤ ‖K p‖ :=
      (div_le_self (abs_nonneg _) hrabs).trans (Complex.abs_im_le_norm _)
    have hnonneg : 0 ≤ |(K p).im| / |r| := div_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [sq_nonneg (|(K p).im| / |r|), sq_nonneg ‖K p‖]
  rw [hsNormSq_sourcePairOddCellKernel hr hK, HilbertSchmidt.hsNormSq,
    ← tsum_mul_left]
  apply Summable.tsum_le_tsum (f := fun p : ι × ι => 4 * (|(K p).im| / |r|) ^ (2 : ℕ))
    (g := fun p => (4 / r ^ (2 : ℕ)) * ‖K p‖ ^ (2 : ℕ)) (fun p => ?_) hleft
    (hK.mul_left (4 / r ^ (2 : ℕ)))
  rw [abs_of_pos hr0]
  have him : |(K p).im| ≤ ‖K p‖ := Complex.abs_im_le_norm _
  have hnonneg : 0 ≤ |(K p).im| := abs_nonneg _
  have hrne : r ≠ 0 := ne_of_gt hr0
  field_simp
  nlinarith [sq_nonneg ‖K p‖]

omit [DecidableEq ι] in
theorem hsTraceDiag_sourcePairOddCellKernel_eq_zero (r : ℝ)
    {K : ι × ι → ℂ} {s : Finset ι}
    (hK : ∀ p : ι × ι, p ∉ s ×ˢ s → K p = 0) :
    HilbertSchmidt.hsTraceDiag (sourcePairOddCellKernel r K) = 0 := by
  have hsummable : Summable (fun p : ι × Fin 4 =>
      sourcePairOddCellKernel r K (p, p)) := by
    apply summable_of_ne_finset_zero (s := sourcePairOddCellCutoff s)
    intro p hp
    apply sourcePairOddCellKernel_support r s hK (p, p)
    intro hpair
    exact hp (Finset.mem_product.mp hpair).1
  rw [HilbertSchmidt.hsTraceDiag, hsummable.tsum_prod]
  have hinner : ∀ i : ι, (∑' c : Fin 4,
      sourcePairOddCellKernel r K ((i, c), (i, c))) = 0 := by
    intro i
    rw [tsum_fintype]
    simp [sourcePairOddCellKernel, sourcePairRealOddBlock, Fin.sum_univ_four]
    ring
  simp_rw [hinner]
  exact tsum_zero

end
end GaloisForLFunctions.HTGeometry
