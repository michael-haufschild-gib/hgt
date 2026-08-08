/-
# Finite truncations of a Hilbert–Schmidt kernel

The truncation of a kernel `K` to a finite index block `s × s` is again Hilbert–Schmidt, has no
larger Hilbert–Schmidt norm, and converges to `K` in that norm as the block exhausts the index
type.  Combined with the Lipschitz estimate for the power traces this makes every trace `tr(Kⁿ)`
the limit of the corresponding traces of finite blocks — the passage that turns the finite
regularized determinant into the entire one.

Main results:
* `truncKernel`, `isHS_truncKernel`, `hsNorm_truncKernel_le`.
* `tendsto_hsNorm_sub_truncKernel` — truncations converge in Hilbert–Schmidt norm.
* `tendsto_hsTrace_hsPow_truncKernel` — hence every power trace is the limit of truncated traces.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtContinuity

namespace HilbertSchmidt

open Filter

variable {ι : Type*} [DecidableEq ι]

/-- The truncation of a kernel to the finite block `s × s`. -/
def truncKernel (K : ι × ι → ℂ) (s : Finset ι) : ι × ι → ℂ :=
  fun p => if p.1 ∈ s ∧ p.2 ∈ s then K p else 0

theorem norm_truncKernel_le (K : ι × ι → ℂ) (s : Finset ι) (p : ι × ι) :
    ‖truncKernel K s p‖ ^ 2 ≤ ‖K p‖ ^ 2 := by
  unfold truncKernel
  split
  · exact le_rfl
  · simp [pow_nonneg (norm_nonneg (K p)) 2]

theorem isHS_truncKernel {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) :
    IsHS (truncKernel K s) :=
  Summable.of_nonneg_of_le (fun p => by positivity) (norm_truncKernel_le K s) hK

theorem hsNormSq_truncKernel_le {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) :
    hsNormSq (truncKernel K s) ≤ hsNormSq K :=
  Summable.tsum_le_tsum (norm_truncKernel_le K s) (isHS_truncKernel hK s) hK

theorem hsNorm_truncKernel_le {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) :
    hsNorm (truncKernel K s) ≤ hsNorm K :=
  Real.sqrt_le_sqrt (hsNormSq_truncKernel_le hK s)

/-- The truncation error is summable: its entries are dominated by those of `K`. -/
theorem isHS_sub_truncKernel {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) :
    Summable fun p : ι × ι => if p ∈ s ×ˢ s then (0 : ℝ) else ‖K p‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hK
  split
  · positivity
  · exact le_rfl

/-- The Hilbert–Schmidt energy of the truncation error is the tail of the entry series outside the
block. -/
theorem hsNormSq_sub_truncKernel (K : ι × ι → ℂ) (s : Finset ι) :
    hsNormSq (K - truncKernel K s)
      = ∑' p : ι × ι, if p ∈ s ×ˢ s then (0 : ℝ) else ‖K p‖ ^ 2 := by
  rw [hsNormSq]
  refine tsum_congr fun p => ?_
  simp only [truncKernel, Pi.sub_apply, Finset.mem_product]
  by_cases h : p.1 ∈ s ∧ p.2 ∈ s <;> simp [h]

/-- The energy of the truncation is the partial sum over the block. -/
theorem hsNormSq_truncKernel_eq_sum (K : ι × ι → ℂ) (s : Finset ι) :
    hsNormSq (truncKernel K s) = ∑ p ∈ s ×ˢ s, ‖K p‖ ^ 2 := by
  rw [hsNormSq]
  refine (tsum_eq_sum (f := fun p : ι × ι => ‖truncKernel K s p‖ ^ 2) (s := s ×ˢ s) ?_).trans ?_
  · intro p hp
    rw [Finset.mem_product] at hp
    simp [truncKernel, hp]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_product] at hp
    simp [truncKernel, hp.1, hp.2]

/-- The two energies add up to the total. -/
theorem hsNormSq_split {K : ι × ι → ℂ} (hK : IsHS K) (s : Finset ι) :
    hsNormSq (K - truncKernel K s) = hsNormSq K - ∑ p ∈ s ×ˢ s, ‖K p‖ ^ 2 := by
  have hin : Summable fun p : ι × ι => if p ∈ s ×ˢ s then ‖K p‖ ^ 2 else (0 : ℝ) := by
    refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hK
    split
    · exact le_rfl
    · positivity
  have hsum : hsNormSq K
      = (∑' p : ι × ι, if p ∈ s ×ˢ s then ‖K p‖ ^ 2 else (0 : ℝ))
        + ∑' p : ι × ι, if p ∈ s ×ˢ s then (0 : ℝ) else ‖K p‖ ^ 2 := by
    rw [← hin.tsum_add (isHS_sub_truncKernel hK s), hsNormSq]
    refine tsum_congr fun p => ?_
    by_cases h : p ∈ s ×ˢ s <;> simp [h]
  have hpart : (∑' p : ι × ι, if p ∈ s ×ˢ s then ‖K p‖ ^ 2 else (0 : ℝ))
      = ∑ p ∈ s ×ˢ s, ‖K p‖ ^ 2 := by
    refine (tsum_eq_sum (s := s ×ˢ s) ?_).trans (Finset.sum_congr rfl fun p hp => by simp [hp])
    intro p hp; simp [hp]
  rw [hsNormSq_sub_truncKernel K s, hsum, hpart]
  ring

/-- Square blocks are cofinal among finite sets of pairs. -/
theorem tendsto_finset_product_atTop :
    Tendsto (fun s : Finset ι => s ×ˢ s) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun t => ?_
  refine ⟨t.image Prod.fst ∪ t.image Prod.snd, fun s hs p hp => ?_⟩
  rw [Finset.mem_product]
  exact ⟨hs (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)),
    hs (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))⟩

/-- **Truncations converge in Hilbert–Schmidt norm.** -/
theorem tendsto_hsNorm_sub_truncKernel {K : ι × ι → ℂ} (hK : IsHS K) :
    Tendsto (fun s : Finset ι => hsNorm (K - truncKernel K s)) atTop (nhds 0) := by
  have hpart : Tendsto (fun s : Finset ι => ∑ p ∈ s ×ˢ s, ‖K p‖ ^ 2) atTop (nhds (hsNormSq K)) :=
    (hK.hasSum : Tendsto (fun t : Finset (ι × ι) => ∑ p ∈ t, ‖K p‖ ^ 2) atTop
      (nhds (∑' p : ι × ι, ‖K p‖ ^ 2))).comp (tendsto_finset_product_atTop (ι := ι))
  have hsq : Tendsto (fun s : Finset ι => hsNormSq (K - truncKernel K s)) atTop (nhds 0) := by
    have := tendsto_const_nhds (x := hsNormSq K) (f := (atTop : Filter (Finset ι))) |>.sub hpart
    rw [sub_self] at this
    exact this.congr fun s => (hsNormSq_split hK s).symm
  have hcomp := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  rw [Real.sqrt_zero] at hcomp
  simp only [hsNorm]
  exact hcomp

/-- **Every power trace is the limit of the truncated power traces.**  This is the passage from the
finite regularized determinants to the entire one. -/
theorem tendsto_hsTrace_hsPow_truncKernel {K : ι × ι → ℂ} (hK : IsHS K) (n : ℕ) :
    Tendsto (fun s : Finset ι => ∑' i : ι, hsPow (truncKernel K s) (n + 1) (i, i)) atTop
      (nhds (∑' i : ι, hsPow K (n + 1) (i, i))) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hsub : ∀ s : Finset ι, hsNorm (truncKernel K s - K) = hsNorm (K - truncKernel K s) := by
    intro s
    have hneg : truncKernel K s - K = -(K - truncKernel K s) := by funext p; simp
    rw [hneg, hsNorm_neg]
  have hbound : ∀ s : Finset ι,
      ‖(∑' i : ι, hsPow (truncKernel K s) (n + 1) (i, i)) - ∑' i : ι, hsPow K (n + 1) (i, i)‖
        ≤ (n + 2 : ℝ) * hsNorm K ^ (n + 1) * hsNorm (K - truncKernel K s) := by
    intro s
    rw [← hsub s]
    exact hsTrace_hsPow_sub_norm_le (isHS_truncKernel hK s) hK
      (hsNorm_truncKernel_le hK s) le_rfl n
  have htend : Tendsto (fun s : Finset ι =>
      (n + 2 : ℝ) * hsNorm K ^ (n + 1) * hsNorm (K - truncKernel K s)) atTop (nhds 0) := by
    have := (tendsto_hsNorm_sub_truncKernel hK).const_mul ((n + 2 : ℝ) * hsNorm K ^ (n + 1))
    simpa using this
  exact squeeze_zero (fun s => norm_nonneg _) hbound htend

end HilbertSchmidt
