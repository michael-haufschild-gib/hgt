import GaloisForLFunctions.RHTower.HighBlockDualWeightVariation
import GaloisForLFunctions.RHTower.HighBlockDirectVariation
import GaloisForLFunctions.RHTower.HighBlockDualMeanSquare

/-!
# High-block law: the frozen dual coefficients have bounded variation

The conjugate frozen dual coefficient factors as
`[(n+1)^{−d} · conj W_{d,T}((n+1)x)] · (n+1)^{−½}`: a decreasing factor in `(0,1]` times a bounded
function of bounded variation (`HighBlockDualWeightVariation`) times the critical sharp head. Its
forward differences have `ℓ¹` norm at most `2 sup‖W‖ + TV(W)`, so the frozen dual energy against
any mollifier is at most a uniform constant times the largest sharp-cutoff critical energy.
-/

open Finset Complex

namespace RHTower

noncomputable section

/-- The smooth weight of the conjugate frozen dual coefficient. -/
def dualWeightFrozen (d x T : ℝ) (n : ℕ) : ℂ :=
  (((n + 1 : ℝ) ^ (-d) : ℝ) : ℂ) *
    (starRingEnd ℂ) (smoothAFEZetaDisplacedDualWeight d T (dualPt x n))

/-- Factorization of the conjugate frozen dual coefficient. -/
theorem conj_highBlockDualCoeffFrozen_eq (d x T : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (highBlockDualCoeffFrozen d x T n) =
      dualWeightFrozen d x T n * criticalHeadCoeff n := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hpt : displacedLinePt d 0 - 1 = (((-(1 / 2) - d : ℝ)) : ℂ) := by
    simp [displacedLinePt]
    try ring
  have hcast : ((n : ℂ) + 1) = (((n + 1 : ℝ)) : ℂ) := by push_cast; ring
  have hcpow : (n + 1 : ℂ) ^ (displacedLinePt d 0 - 1) =
      (((n + 1 : ℝ) ^ (-(1 / 2) - d) : ℝ) : ℂ) := by
    rw [hpt, hcast, Complex.ofReal_cpow hn.le]
  have hsplit : (n + 1 : ℝ) ^ (-(1 / 2) - d) = (n + 1 : ℝ) ^ (-d) * (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hn]
    ring_nf
  have hpt' : dualPt x n = (n + 1 : ℝ) * x := rfl
  unfold highBlockDualCoeffFrozen dualWeightFrozen criticalHeadCoeff
  rw [hcpow, hsplit, map_mul, Complex.conj_ofReal, hpt']
  push_cast
  ring

/-- Total variation of a product of a decreasing sequence in `[0,1]` with a bounded sequence of
bounded variation, with the `g(L) := 0` convention. -/
theorem sum_norm_headDiff_prod_bv_le {a : ℕ → ℝ} {w : ℕ → ℂ} (ha : Antitone a)
    (ha0 : ∀ u, 0 ≤ a u) (ha1 : ∀ u, a u ≤ 1) {Wsup TV : ℝ} (hw : ∀ u, ‖w u‖ ≤ Wsup)
    (L : ℕ) (hTV : ∑ u ∈ Finset.range L, ‖w u - w (u + 1)‖ ≤ TV) :
    ∑ u ∈ Finset.range L, ‖headDiff (fun n => ((a n : ℝ) : ℂ) * w n) L u‖ ≤ 2 * Wsup + TV := by
  have hWsup : 0 ≤ Wsup := le_trans (norm_nonneg _) (hw 0)
  have hTV0 : 0 ≤ TV := le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) hTV
  cases L with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    linarith
  | succ K =>
    rw [Finset.sum_range_succ]
    have hlast : ‖headDiff (fun n => ((a n : ℝ) : ℂ) * w n) (K + 1) K‖ ≤ Wsup := by
      simp only [headDiff, if_neg (lt_irrefl (K + 1)), sub_zero, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (ha0 K)]
      calc a K * ‖w K‖ ≤ 1 * Wsup := mul_le_mul (ha1 K) (hw K) (norm_nonneg _) zero_le_one
        _ = Wsup := one_mul _
    have hinner : ∀ u ∈ Finset.range K,
        ‖headDiff (fun n => ((a n : ℝ) : ℂ) * w n) (K + 1) u‖ ≤
          (a u - a (u + 1)) * Wsup + ‖w u - w (u + 1)‖ := by
      intro u hu
      rw [Finset.mem_range] at hu
      have hlt : u + 1 < K + 1 := by omega
      simp only [headDiff, if_pos hlt]
      have hsplit : ((a u : ℝ) : ℂ) * w u - ((a (u + 1) : ℝ) : ℂ) * w (u + 1) =
          (((a u : ℝ) : ℂ) - ((a (u + 1) : ℝ) : ℂ)) * w u +
            ((a (u + 1) : ℝ) : ℂ) * (w u - w (u + 1)) := by ring
      rw [hsplit]
      have hau : a (u + 1) ≤ a u := ha (Nat.le_succ u)
      calc ‖(((a u : ℝ) : ℂ) - ((a (u + 1) : ℝ) : ℂ)) * w u +
            ((a (u + 1) : ℝ) : ℂ) * (w u - w (u + 1))‖
          ≤ ‖(((a u : ℝ) : ℂ) - ((a (u + 1) : ℝ) : ℂ)) * w u‖ +
            ‖((a (u + 1) : ℝ) : ℂ) * (w u - w (u + 1))‖ := norm_add_le _ _
        _ = (a u - a (u + 1)) * ‖w u‖ + a (u + 1) * ‖w u - w (u + 1)‖ := by
            rw [norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
              abs_of_nonneg (ha0 (u + 1))]
        _ ≤ (a u - a (u + 1)) * Wsup + 1 * ‖w u - w (u + 1)‖ :=
            add_le_add (mul_le_mul_of_nonneg_left (hw u) (by linarith))
              (mul_le_mul_of_nonneg_right (ha1 (u + 1)) (norm_nonneg _))
        _ = (a u - a (u + 1)) * Wsup + ‖w u - w (u + 1)‖ := by ring
    have hsum : ∑ u ∈ Finset.range K, ((a u - a (u + 1)) * Wsup + ‖w u - w (u + 1)‖) =
        (a 0 - a K) * Wsup + ∑ u ∈ Finset.range K, ‖w u - w (u + 1)‖ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_range_sub']
    have hsub : ∑ u ∈ Finset.range K, ‖w u - w (u + 1)‖ ≤ TV := by
      refine le_trans ?_ hTV
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ K))
        (fun _ _ _ => norm_nonneg _)
    calc (∑ u ∈ Finset.range K, ‖headDiff (fun n => ((a n : ℝ) : ℂ) * w n) (K + 1) u‖) +
          ‖headDiff (fun n => ((a n : ℝ) : ℂ) * w n) (K + 1) K‖
        ≤ (∑ u ∈ Finset.range K, ((a u - a (u + 1)) * Wsup + ‖w u - w (u + 1)‖)) + Wsup :=
          add_le_add (Finset.sum_le_sum hinner) hlast
      _ = (a 0 - a K) * Wsup + (∑ u ∈ Finset.range K, ‖w u - w (u + 1)‖) + Wsup := by rw [hsum]
      _ ≤ 2 * Wsup + TV := by
          have h1 : (a 0 - a K) * Wsup ≤ 1 * Wsup :=
            mul_le_mul_of_nonneg_right (by linarith [ha1 0, ha0 K]) hWsup
          linarith

/-- **Frozen dual energy against any mollifier is controlled by the sharp critical energies.** -/
theorem exists_highBlockDualEnergy_le_sharp :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ d : ℝ, 0 < d → d ≤ 1 / 4 → ∀ T x : ℝ, 1 ≤ T → 0 < x → x ≤ T →
      ∀ (L N : ℕ) (b : Fin N → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ u ∈ Finset.range L,
        ∑ r : Fin (L * N), ‖Sieve.dirConv L N (sharpHead criticalHeadCoeff L u) b r‖ ^ 2 ≤ C) →
      highBlockDualEnergy d x T L N b ≤ Cv ^ 2 * C := by
  obtain ⟨Csup, hCsup0, hsup⟩ := exists_norm_smoothAFEZetaDisplacedDualWeight_le_uniform
  obtain ⟨Ctv, hCtv0, htv⟩ := exists_sum_norm_dualWeight_diff_le
  refine ⟨2 * Csup + Ctv, by positivity, ?_⟩
  intro d hd hd4 T x hT hx hxT L N b C hC0 hC
  set a : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ (-d) with ha_def
  set w : ℕ → ℂ := fun n => (starRingEnd ℂ) (smoothAFEZetaDisplacedDualWeight d T (dualPt x n))
    with hw_def
  have hhead : (fun n : Fin L => (starRingEnd ℂ) (highBlockDualCoeffFrozen d x T n)) =
      fun n : Fin L => ((a n : ℝ) : ℂ) * w n * criticalHeadCoeff n := by
    funext n
    rw [conj_highBlockDualCoeffFrozen_eq]
    rfl
  unfold highBlockDualEnergy
  rw [hhead]
  have htrans := energy_smooth_le_sharp L N (fun n => ((a n : ℝ) : ℂ) * w n) criticalHeadCoeff b hC
  refine htrans.trans ?_
  have ha : Antitone a := by
    intro u u' huu'
    simp only [ha_def]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast Nat.succ_le_succ huu') (by linarith)
  have ha0 : ∀ u, 0 ≤ a u := fun u => by simp only [ha_def]; positivity
  have ha1 : ∀ u, a u ≤ 1 := fun u => by
    simp only [ha_def]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [(Nat.cast_nonneg u : (0 : ℝ) ≤ u)])
      (by linarith)
  have hwb : ∀ u, ‖w u‖ ≤ Csup := fun u => by
    simp only [hw_def]
    rw [Complex.norm_conj]
    exact hsup d hd hd4 T (dualPt x u) hT (dualPt_pos hx u)
  have hTV : ∑ u ∈ Finset.range L, ‖w u - w (u + 1)‖ ≤ Ctv := by
    have := htv d hd hd4 T x hT hx hxT L
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hw_def]
    rw [← map_sub, Complex.norm_conj]
  have hW := sum_norm_headDiff_prod_bv_le ha ha0 ha1 hwb L hTV
  have hW0 : 0 ≤ ∑ u ∈ Finset.range L, ‖headDiff (fun n => ((a n : ℝ) : ℂ) * w n) L u‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hW0 hW 2) hC0

end

end RHTower
