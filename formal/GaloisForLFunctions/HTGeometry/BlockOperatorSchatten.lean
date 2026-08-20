/-
# The Schatten energy of a diagonal block

Approximating a diagonal block by its restriction to the `j` largest entries leaves the block on
the remaining entries, whose norm is the `j`-th largest entry.  So the `j`-th approximation number
of a block is at most its `j`-th largest entry, and the whole Schatten `p`-energy of a block is at
most the `p`-energy of its entries -- with no constant.  Sorting the entries is a permutation of
the orthonormal family, which leaves the block unchanged, so no ordering hypothesis is needed.

Main results:
* `approxNumber_blockOp_le_of_antitone` — the approximation numbers of a sorted block.
* `tsum_rpow_approxNumber_blockOp_le` — **the block energy is at most the entry energy**.
* `schattenNorm_blockOp_rpow_le` — the same statement for the Schatten norm.
-/
import GaloisForLFunctions.HTGeometry.DiagonalBlockOperator
import GaloisForLFunctions.HTGeometry.SchattenApproximationAdditivity

open ContinuousLinearMap
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {m : ℕ} {e : Fin m → H}

theorem approxNumber_blockOp_eq_zero (e : Fin m → H) (μ : Fin m → ℂ) {j : ℕ} (hj : m ≤ j) :
    approxNumber (blockOp e μ) j = 0 := by
  refine le_antisymm ?_ (approxNumber_nonneg _ _)
  simpa using approxNumber_le (blockOp e μ) j (blockOp e μ) ((hasRankLE_blockOp e μ).mono hj)

/-- **The approximation numbers of a sorted block** are its entries. -/
theorem approxNumber_blockOp_le_of_antitone (he : Orthonormal ℂ e) {μ : Fin m → ℂ}
    (hanti : ∀ i j : Fin m, i ≤ j → ‖μ j‖ ≤ ‖μ i‖) {j : ℕ} (hj : j < m) :
    approxNumber (blockOp e μ) j ≤ ‖μ ⟨j, hj⟩‖ := by
  classical
  set s : Finset (Fin m) := Finset.univ.filter (fun i => (i : ℕ) < j) with hs
  have hcard : s.card ≤ j := by
    have himg : s.image (fun i : Fin m => (i : ℕ)) ⊆ Finset.range j := by
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      rw [hs, Finset.mem_filter] at hi
      exact Finset.mem_range.mpr hi.2
    have hinj : (s.image (fun i : Fin m => (i : ℕ))).card = s.card :=
      Finset.card_image_of_injective s Fin.val_injective
    calc s.card = (s.image (fun i : Fin m => (i : ℕ))).card := hinj.symm
      _ ≤ (Finset.range j).card := Finset.card_le_card himg
      _ = j := Finset.card_range j
  have hrank : HasRankLE (blockOpOn s e μ) j := (hasRankLE_blockOpOn s e μ).mono hcard
  have hsub : blockOp e μ - blockOpOn s e μ = blockOpOn sᶜ e μ := blockOp_sub_blockOpOn s e μ
  have hnorm : ‖blockOpOn sᶜ e μ‖ ≤ ‖μ ⟨j, hj⟩‖ := by
    refine norm_blockOpOn_le he _ μ (norm_nonneg _) fun i hi => ?_
    have hnotmem : i ∉ s := Finset.mem_compl.mp hi
    have hge : j ≤ (i : ℕ) := by
      rw [hs, Finset.mem_filter] at hnotmem
      have hlt : ¬ ((i : ℕ) < j) := fun h => hnotmem ⟨Finset.mem_univ i, h⟩
      exact not_lt.mp hlt
    exact hanti ⟨j, hj⟩ i (by rw [Fin.le_def]; exact hge)
  calc approxNumber (blockOp e μ) j ≤ ‖blockOp e μ - blockOpOn s e μ‖ :=
        approxNumber_le _ _ _ hrank
    _ = ‖blockOpOn sᶜ e μ‖ := by rw [hsub]
    _ ≤ ‖μ ⟨j, hj⟩‖ := hnorm

theorem tsum_rpow_approxNumber_blockOp_le_of_antitone (he : Orthonormal ℂ e) {μ : Fin m → ℂ}
    (hanti : ∀ i j : Fin m, i ≤ j → ‖μ j‖ ≤ ‖μ i‖) {p : ℝ} (hp : 0 < p) :
    (∑' j, approxNumber (blockOp e μ) j ^ p) ≤ ∑ i, ‖μ i‖ ^ p := by
  classical
  have hzero : ∀ j ∉ Finset.range m, approxNumber (blockOp e μ) j ^ p = 0 := by
    intro j hj
    rw [approxNumber_blockOp_eq_zero e μ (by simpa using Finset.mem_range.not.mp hj),
      Real.zero_rpow hp.ne']
  rw [tsum_eq_sum hzero, ← Fin.sum_univ_eq_sum_range
    (fun j => approxNumber (blockOp e μ) j ^ p) m]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle := approxNumber_blockOp_le_of_antitone he hanti i.isLt
  have hfin : (⟨(i : ℕ), i.isLt⟩ : Fin m) = i := Fin.eta i i.isLt
  rw [hfin] at hle
  exact Real.rpow_le_rpow (approxNumber_nonneg _ _) hle hp.le

/-- **The Schatten `p`-energy of a diagonal block is at most the `p`-energy of its entries.** -/
theorem tsum_rpow_approxNumber_blockOp_le (he : Orthonormal ℂ e) (μ : Fin m → ℂ) {p : ℝ}
    (hp : 0 < p) : (∑' j, approxNumber (blockOp e μ) j ^ p) ≤ ∑ i, ‖μ i‖ ^ p := by
  classical
  set σ : Equiv.Perm (Fin m) := Tuple.sort (fun i => -‖μ i‖) with hσ
  have hmono : Monotone ((fun i => -‖μ i‖) ∘ σ) := Tuple.monotone_sort _
  have hanti : ∀ i j : Fin m, i ≤ j → ‖(μ ∘ σ) j‖ ≤ ‖(μ ∘ σ) i‖ := by
    intro i j hij
    have h := hmono hij
    simp only [Function.comp_apply] at h ⊢
    linarith
  have he' : Orthonormal ℂ (e ∘ σ) := he.comp (σ : Fin m → Fin m) σ.injective
  have hblock : blockOp (e ∘ σ) (μ ∘ σ) = blockOp e μ := by
    rw [blockOp, blockOp, blockOpOn, blockOpOn]
    exact Equiv.sum_comp σ (fun i => (innerSL ℂ (e i)).smulRight (μ i • e i))
  have hsum : (∑ i, ‖(μ ∘ σ) i‖ ^ p) = ∑ i, ‖μ i‖ ^ p :=
    Equiv.sum_comp σ (fun i => ‖μ i‖ ^ p)
  rw [← hblock, ← hsum]
  exact tsum_rpow_approxNumber_blockOp_le_of_antitone he' hanti hp

theorem schattenNorm_blockOp_rpow_le (he : Orthonormal ℂ e) (μ : Fin m → ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm p (blockOp e μ) ^ p ≤ ∑ i, ‖μ i‖ ^ p := by
  rw [schattenNorm_rpow_eq_tsum hp]
  exact tsum_rpow_approxNumber_blockOp_le he μ hp

end

end GaloisForLFunctions.HTGeometry
