import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SubLogarithmicWindowsMissTheMinimalFace

/-!
# The minimal-face counterexample has zero relative density

The base ordinates double between levels, so all levels through `k`
contain at most `64(k+1)Γ_k` points. Their logarithms grow at least
quadratically in `k`. Consequently the counting function is `o(T log T)`.
-/

open Finset Filter Topology
open Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open SplineTower

/-- Doubling of the ordinates bounds their entire prefix by twice its last term. -/
theorem sum_faceBaseFreq_le (γ_min C Θ : ℝ) (K : ℕ) :
    ∑ k ∈ range (K + 1), faceBaseFreq γ_min C Θ k ≤
      2 * faceBaseFreq γ_min C Θ K := by
  induction K with
  | zero => simp only [sum_range_one]; omega
  | succ K ih =>
    rw [sum_range_succ]
    have h := two_mul_faceBaseFreq_add_four_le_succ γ_min C Θ K
    omega

/-- The four copies of each harmonic give a linear level count. -/
theorem faceHarmonics_card_bound (γ_min C Θ : ℝ) (k : ℕ) :
    (faceHarmonics γ_min C Θ k).card * 4 ≤
      32 * (k + 1) * faceBaseFreq γ_min C Θ k := by
  have hΓ := one_le_faceBaseFreq γ_min C Θ k
  unfold faceHarmonics levelStart
  rw [Nat.card_Icc]
  have he : 2 * (4 * (k + 1) * faceBaseFreq γ_min C Θ k) + 1 -
      4 * (k + 1) * faceBaseFreq γ_min C Θ k =
      4 * (k + 1) * faceBaseFreq γ_min C Θ k + 1 := by omega
  rw [he]
  have hm : 1 ≤ 4 * (k + 1) * faceBaseFreq γ_min C Θ k := by positivity
  omega

/-- Counting every point in the active levels bounds any ordinate prefix. -/
theorem minimalFace_count_le_levels (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (T : ℝ) (K : ℕ)
    (hcut : ∀ k : ℕ, (faceBaseFreq γ_min C Θ k : ℝ) < T → k ≤ K) :
    (minimalFaceCounterConfig γ_min C hΘ hΘ2).N 0 T ≤
      64 * (K + 1) * faceBaseFreq γ_min C Θ K := by
  classical
  let Z := minimalFaceCounterConfig γ_min C hΘ hΘ2
  let S : ℕ → Finset ℂ := fun k =>
    (faceHarmonics γ_min C Θ k ×ˢ (univ : Finset (Bool × Bool))).image
      (facePtAtLevel γ_min C Θ k)
  let F : Finset ℂ := (range (K + 1)).biUnion S
  have hfin := Z.finite_window 0 T
  have hsub : hfin.toFinset ⊆ F := by
    intro ρ hρ
    obtain ⟨⟨idx, rfl⟩, _, hT⟩ := hfin.mem_toFinset.mp hρ
    apply mem_biUnion.mpr
    refine ⟨idx.1, mem_range.mpr (Nat.lt_succ_of_le
      (hcut idx.1 ((facePt_im_bounds γ_min C Θ idx).1.trans_le hT))), ?_⟩
    apply mem_image.mpr
    refine ⟨(idx.2.1.1, idx.2.2), mem_product.mpr ⟨idx.2.1.2, mem_univ _⟩, ?_⟩
    exact (facePt_eq_facePtAtLevel γ_min C Θ idx).symm
  have hcard (k : ℕ) : (S k).card ≤ 32 * (k + 1) * faceBaseFreq γ_min C Θ k := by
    calc (S k).card ≤ (faceHarmonics γ_min C Θ k ×ˢ
          (univ : Finset (Bool × Bool))).card := card_image_le
      _ = (faceHarmonics γ_min C Θ k).card * 4 := by rw [card_product]; rfl
      _ ≤ _ := faceHarmonics_card_bound γ_min C Θ k
  calc Z.N 0 T = hfin.toFinset.card := by
        rw [ZeroConfig.N, ZeroConfig.window, finsum_mem_eq_finite_toFinset_sum _ hfin]
        simp only [Z, minimalFaceCounterConfig, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ F.card := card_le_card hsub
    _ ≤ ∑ k ∈ range (K + 1), (S k).card := card_biUnion_le
    _ ≤ ∑ k ∈ range (K + 1), 32 * (k + 1) * faceBaseFreq γ_min C Θ k :=
      sum_le_sum fun k _ => hcard k
    _ ≤ ∑ k ∈ range (K + 1), 32 * (K + 1) * faceBaseFreq γ_min C Θ k := by
      apply sum_le_sum
      intro k hk
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 32 (by omega))
    _ = 32 * (K + 1) * ∑ k ∈ range (K + 1), faceBaseFreq γ_min C Θ k :=
      (mul_sum _ _ _).symm
    _ ≤ 32 * (K + 1) * (2 * faceBaseFreq γ_min C Θ K) :=
      Nat.mul_le_mul_left _ (sum_faceBaseFreq_le γ_min C Θ K)
    _ = _ := by ring

/-- The logarithm of each late base ordinate dominates the square of its level. -/
theorem quadratic_le_log_faceBaseFreq (γ_min C : ℝ) {Θ : ℝ} (hΘ : 0 < Θ)
    {K : ℕ} (hK : 2 ≤ K) :
    (Θ / 7) * (K : ℝ) ^ 2 ≤ Real.log (faceBaseFreq γ_min C Θ K) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hK
  have he := exp_levelRadius_sq_le_winCenter γ_min C Θ k
  have hexp := Real.add_one_le_exp (levelRadius (k + 1) ^ 2)
  have hcenter : ((2 + k : ℕ) : ℝ) ^ 2 ≤ (winRight γ_min C Θ (k + 1) : ℝ) := by
    rw [winRight_cast]
    unfold levelRadius at he hexp ⊢
    push_cast at he hexp ⊢
    nlinarith only [he, hexp, Nat.cast_nonneg (α := ℝ) k]
  have hbase : 1 ≤ faceBaseConst γ_min C (k + 1 + 1) :=
    (by norm_num : 1 ≤ 10).trans (ten_le_faceBaseConst γ_min C _)
  have hmul : ⌈Real.exp ((Θ / 7) * (winRight γ_min C Θ (k + 1) : ℝ))⌉₊ ≤
      faceBaseConst γ_min C (k + 1 + 1) *
        ⌈Real.exp ((Θ / 7) * (winRight γ_min C Θ (k + 1) : ℝ))⌉₊ := by
    simpa only [one_mul] using Nat.mul_le_mul_right
      ⌈Real.exp ((Θ / 7) * (winRight γ_min C Θ (k + 1) : ℝ))⌉₊ hbase
  have hnat := hmul.trans (le_max_right
    (2 * faceBaseFreq γ_min C Θ (k + 1) + 4) _)
  rw [← faceBaseFreq_succ] at hnat
  have hE : Real.exp ((Θ / 7) * (winRight γ_min C Θ (k + 1) : ℝ)) ≤
      (faceBaseFreq γ_min C Θ (k + 1 + 1) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnat)
  have hlog := Real.log_le_log (Real.exp_pos _) hE
  rw [Real.log_exp] at hlog
  have h := (mul_le_mul_of_nonneg_left hcenter (by positivity : 0 ≤ Θ / 7)).trans hlog
  simpa only [show k + 1 + 1 = 2 + k by omega] using h

/-- The counterexample contributes arbitrarily little of the `T log T` density. -/
theorem minimalFace_count_small_relative_to_T_log_T (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℝ, ∀ T : ℝ, U ≤ T →
      ((minimalFaceCounterConfig γ_min C hΘ hΘ2).N 0 T : ℝ) ≤
        ε * T * Real.log T := by
  classical
  let d : ℝ := Θ / 7
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (max 2 (128 / (ε * d)))
  have hM2 : 2 ≤ M := by
    exact_mod_cast ((le_max_left 2 (128 / (ε * d))).trans hM.le)
  refine ⟨max 1 (faceBaseFreq γ_min C Θ M : ℝ), fun T hT => ?_⟩
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hMT : (faceBaseFreq γ_min C Θ M : ℝ) ≤ T := (le_max_right _ _).trans hT
  let K := Nat.findGreatest (fun k => (faceBaseFreq γ_min C Θ k : ℝ) ≤ T) ⌊T⌋₊
  have hMG : (M : ℝ) ≤ (faceBaseFreq γ_min C Θ M : ℝ) := by
    exact_mod_cast k_le_faceBaseFreq γ_min C Θ M
  have hMK : M ≤ K := Nat.le_findGreatest
    (Nat.le_floor (hMG.trans hMT)) hMT
  have hK2 : 2 ≤ K := hM2.trans hMK
  have hKT : (faceBaseFreq γ_min C Θ K : ℝ) ≤ T :=
    (Nat.findGreatest_eq_iff.mp (show
      Nat.findGreatest (fun k => (faceBaseFreq γ_min C Θ k : ℝ) ≤ T) ⌊T⌋₊ = K from rfl)).2.1
      (by omega)
  have hcut (k : ℕ) (hk : (faceBaseFreq γ_min C Θ k : ℝ) < T) : k ≤ K := by
    have hkG : (k : ℝ) ≤ (faceBaseFreq γ_min C Θ k : ℝ) := by
      exact_mod_cast k_le_faceBaseFreq γ_min C Θ k
    exact Nat.le_findGreatest (Nat.le_floor (hkG.trans hk.le)) hk.le
  have hcount := minimalFace_count_le_levels γ_min C hΘ hΘ2 T K hcut
  have hcountR : ((minimalFaceCounterConfig γ_min C hΘ hΘ2).N 0 T : ℝ) ≤
      64 * ((K : ℝ) + 1) * (faceBaseFreq γ_min C Θ K : ℝ) := by exact_mod_cast hcount
  have hlog : d * (K : ℝ) ^ 2 ≤ Real.log T :=
    (quadratic_le_log_faceBaseFreq γ_min C hΘ hK2).trans
      (Real.log_le_log (lt_of_lt_of_le zero_lt_one
        (by exact_mod_cast (one_le_faceBaseFreq γ_min C Θ K))) hKT)
  have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hMK_R : (M : ℝ) ≤ K := by exact_mod_cast hMK
  have h128 : 128 ≤ ε * d * (K : ℝ) := by
    have hm := (div_lt_iff₀ (mul_pos hε hd)).mp
      ((le_max_right 2 (128 / (ε * d))).trans_lt hM)
    have hmono := mul_le_mul_of_nonneg_left hMK_R (mul_pos hε hd).le
    nlinarith only [hm, hmono]
  have hscale := mul_le_mul_of_nonneg_right h128 (Nat.cast_nonneg (α := ℝ) K)
  have hεlog := mul_le_mul_of_nonneg_left hlog hε.le
  have hcoef : 64 * ((K : ℝ) + 1) ≤ ε * Real.log T := by
    nlinarith only [hK1R, hscale, hεlog]
  calc ((minimalFaceCounterConfig γ_min C hΘ hΘ2).N 0 T : ℝ)
      ≤ 64 * ((K : ℝ) + 1) * (faceBaseFreq γ_min C Θ K : ℝ) := hcountR
    _ ≤ 64 * ((K : ℝ) + 1) * T := mul_le_mul_of_nonneg_left hKT (by positivity)
    _ ≤ (ε * Real.log T) * T := mul_le_mul_of_nonneg_right hcoef (zero_le_one.trans hT1)
    _ = _ := by ring


end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
