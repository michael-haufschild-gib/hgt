import GaloisForLFunctions.HeckeKreinToeplitz.EveryReceiverAtEveryWidthIsBoundedByTheIndex
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle

/-!
# Shrinking atoms carry the whole index

The lower half of the transfer at shrinking widths. An atomic receiver of width `w` on `{1, …, N}`
is the Weil Gram matrix of the translates `B_w(· − log n)`, `n ≤ N`, of the dilated cubic spline
`B_w = B(·/w)` (`shrinkGram`).

* **Every width sees every right zero** (`seenRightZeros_dilate_cubicSpline`). The transform of
  `B_w` is `w B̂(wz)`, and `B̂ = (sin z/z)⁴` has no zeros off the real axis.
* **At each fixed width the windows reach the index** (`negIndex_zetaKernel_eq_iSup_shrinkGram`).
  The integers carry the whole index of the orbit kernel of `B_w`, which is `κ(K_ζ)`. The index is
  nondecreasing in `N`, since a smaller window is a principal submatrix
  (`hermNegIndex_shrinkGram_mono`).
* **A shrinking schedule reaches the index** (`exists_shrinking_schedule`). Some widths `w_N → 0`
  give atomic receivers whose indices are always at most `κ(K_ζ)` and eventually at least every
  `m ≤ κ(K_ζ)`. So shrinking atomic families alone carry the whole index, not only `κ ≥ 1`. The
  schedule comes from a diagonal choice over the widths `1/(k + 1)`. Whether the explicit schedule
  `(log log N)^α/N` already reaches it is left open.
-/

open Complex Finset Filter Topology
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests weilGram weilGram_eq_zeroGram
  cx_contDiff cx_hasCompactSupport translate_contDiff translate_hasCompactSupport rightZeros)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros dilateTest dilateTest_mem
  paperFT_dilateTest)
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig im_gammaOf_ne_zero)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline paperFT_cubicSpline_ne_zero)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- The atomic receiver of width `w` on `{1, …, N}`: the Weil Gram matrix of `B_w(· − log n)`. -/
def shrinkGram (w : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    fun i : Fin N => shiftTest (Real.log ((i : ℝ) + 1)) (cx (dilateTest w cubicSpline))

/-- **Every dilated spline sees every right zero.** -/
theorem seenRightZeros_dilate_cubicSpline {w : ℝ} (hw : 0 < w) :
    seenRightZeros zetaZeroConfig (dilateTest w cubicSpline) = rightZeros zetaZeroConfig := by
  ext ρ
  simp only [seenRightZeros, rightZeros, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hre : ρ.re ≠ 1 / 2 := ne_of_gt h2
    have habs : ((|w| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (abs_ne_zero.mpr hw.ne')
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [paperFT_dilateTest hw.ne']
      refine mul_ne_zero habs (paperFT_cubicSpline_ne_zero ?_)
      rw [im_ofReal_mul]
      exact mul_ne_zero hw.ne' (im_gammaOf_ne_zero hre)
    · rw [paperFT_dilateTest hw.ne']
      refine mul_ne_zero habs (paperFT_cubicSpline_ne_zero ?_)
      rw [im_ofReal_mul, conj_im]
      exact mul_ne_zero hw.ne' (neg_ne_zero.mpr (im_gammaOf_ne_zero hre))

/-- **At each width the integer windows reach the index of the Weil kernel.** -/
theorem negIndex_zetaKernel_eq_iSup_shrinkGram {w : ℝ} (hw : 0 < w) :
    negIndex zetaKernel = ⨆ N : ℕ, (hermNegIndex (shrinkGram w N) : ℕ∞) := by
  have hf : dilateTest w cubicSpline ∈ realTests := dilateTest_mem hw.ne' cubicSpline_mem_realTests
  rw [negIndex_zetaKernel, ← seenRightZeros_dilate_cubicSpline hw,
    ← negIndex_orbitKernel _ temperedConfig_zetaZeroConfig hf, negIndex_eq_iSup_intWindow]
  refine iSup_congr fun N => ?_
  rw [gram_orbitKernel, shrinkGram, weilGram_eq_zeroGram _
    (fun _ => translate_contDiff (cx_contDiff hf.1) _)
    (fun _ => translate_hasCompactSupport (cx_hasCompactSupport hf.2) _)]
  simp only [scale_intWindow]

/-- A smaller window is a principal submatrix. -/
theorem hermNegIndex_shrinkGram_mono (w : ℝ) {N N' : ℕ} (h : N ≤ N') :
    hermNegIndex (shrinkGram w N) ≤ hermNegIndex (shrinkGram w N') :=
  hermNegIndex_submatrix_le (shrinkGram w N') (Fin.castLE h)

/-- Every receiver is bounded by the index. -/
theorem hermNegIndex_shrinkGram_le {w : ℝ} (hw : 0 < w) (N : ℕ) :
    (hermNegIndex (shrinkGram w N) : ℕ∞) ≤ negIndex zetaKernel :=
  hermNegIndex_weilGram_le_negIndex_zetaKernel
    (dilateTest_mem hw.ne' cubicSpline_mem_realTests) _

/-- A natural number below a supremum of naturals is reached by some term. -/
theorem exists_le_of_le_iSup_nat {f : ℕ → ℕ} {j : ℕ} (h : (j : ℕ∞) ≤ ⨆ N, (f N : ℕ∞)) :
    ∃ N, j ≤ f N := by
  by_contra hc
  push Not at hc
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact absurd (hc 0) (Nat.not_lt_zero _)
  have hle : (⨆ N, (f N : ℕ∞)) ≤ ((j - 1 : ℕ) : ℕ∞) :=
    iSup_le fun N => by exact_mod_cast Nat.le_sub_one_of_lt (hc N)
  have := h.trans hle
  norm_cast at this
  omega

/-- **A shrinking schedule reaches the index.** There are widths `w_N → 0` such that the atomic
receivers of width `w_N` on `{1, …, N}` have at most `κ(K_ζ)` negative squares, and eventually at
least `m` for every `m ≤ κ(K_ζ)`. -/
theorem exists_shrinking_schedule :
    ∃ w : ℕ → ℝ, (∀ N, 0 < w N) ∧ Tendsto w atTop (𝓝 0) ∧
      (∀ N, (hermNegIndex (shrinkGram (w N) N) : ℕ∞) ≤ negIndex zetaKernel) ∧
      ∀ m : ℕ, (m : ℕ∞) ≤ negIndex zetaKernel →
        ∀ᶠ N in atTop, m ≤ hermNegIndex (shrinkGram (w N) N) := by
  classical
  set v : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
  have hv : ∀ k, 0 < v k := fun k => by positivity
  -- the target at stage `k`: `min(k, κ)` negative squares
  set tgt : ℕ → ℕ := fun k => (min (k : ℕ∞) (negIndex zetaKernel)).toNat
  have htgt : ∀ k, (tgt k : ℕ∞) = min (k : ℕ∞) (negIndex zetaKernel) := fun k =>
    ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top k) (min_le_left _ _))
  have hex : ∀ k, ∃ N, tgt k ≤ hermNegIndex (shrinkGram (v k) N) := fun k =>
    exists_le_of_le_iSup_nat (by
      rw [htgt, ← negIndex_zetaKernel_eq_iSup_shrinkGram (hv k)]
      exact min_le_right _ _)
  choose M hM using hex
  -- the stage at window `N`: the largest `k ≤ N` whose threshold has been passed
  set K : ℕ → ℕ := fun N => Nat.findGreatest (fun k => M k ≤ N) N
  have hK : ∀ k N, k ≤ N → M k ≤ N → k ≤ K N := fun k N hkN hMN =>
    Nat.le_findGreatest hkN hMN
  have hKspec : ∀ k N, k ≤ N → M k ≤ N → M (K N) ≤ N := fun k N hkN hMN =>
    Nat.findGreatest_spec (P := fun k => M k ≤ N) hkN hMN
  refine ⟨fun N => v (K N), fun N => hv _, ?_, fun N => hermNegIndex_shrinkGram_le (hv _) N, ?_⟩
  · have hKt : Tendsto K atTop atTop := tendsto_atTop_atTop.mpr fun k =>
      ⟨max k (M k), fun N hN => hK k N (le_of_max_le_left hN) (le_of_max_le_right hN)⟩
    have hvt : Tendsto v atTop (𝓝 0) := by
      simpa [v] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact hvt.comp hKt
  · intro m hm
    filter_upwards [eventually_ge_atTop (max m (M m))] with N hN
    have hmN : m ≤ N := le_of_max_le_left hN
    have hMN : M m ≤ N := le_of_max_le_right hN
    have hKN := hK m N hmN hMN
    have hstage := (hM (K N)).trans (hermNegIndex_shrinkGram_mono _ (hKspec m N hmN hMN))
    have hmt : m ≤ tgt (K N) := by
      have : ((m : ℕ) : ℕ∞) ≤ (tgt (K N) : ℕ∞) := by
        rw [htgt]
        exact le_min (by exact_mod_cast hKN) hm
      exact_mod_cast this
    exact hmt.trans hstage

end GaloisForLFunctions.HeckeKreinToeplitz
