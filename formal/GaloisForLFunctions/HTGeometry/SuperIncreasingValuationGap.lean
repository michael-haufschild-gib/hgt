import Mathlib

/-!
# Super-increasing valuation gap

For a nonnegative sequence `b` that is `(C+1)`-super-increasing
(`(C+1) · ∑_{n<k} b n ≤ b k`), the weighted sum `∑ g n · b n` of any nonzero integer sequence `g`
with entries bounded by `C` is bounded away from zero by `b K / (C+1)`, where `K` is the top index of
`g`'s support (`valuation_gap_of_superIncreasing`).

This is the numeral-system uniqueness underlying magnitude hypertranscendence: distinct convolution
atoms of a superlacunary Taylor-magnitude series have distinct valuations, separated by a gap that
grows with the scale.  It supplies the off-balanced-vs-off-balanced valuation separation that the
balanced-atom estimates (`MagnitudeBalancedGap`) do not provide, letting the *minimal-valuation
appearing* atom dominate regardless of leading-symbol degeneracy.
-/

open Finset Filter Topology

namespace GaloisForLFunctions

/-- **Superlacunary implies super-increasing on a tail.**  If `b` is positive with successive ratios
tending to infinity, then for every bound `C` there is a threshold past which `b` is
`(C+1)`-super-increasing: `(C+1) · ∑_{n<k} b n ≤ b k`.  The tail of the partial sum is geometrically
dominated by its last term, and `b → ∞` absorbs the fixed head. -/
theorem exists_superIncreasing_of_ratio {b : ℕ → ℝ} (hbpos : ∀ n, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) (C : ℕ) :
    ∃ N₀, ∀ k, N₀ ≤ k → ((C : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k := by
  obtain ⟨N₁, hN₁⟩ := (hratio.eventually_ge_atTop (3 * ((C : ℝ) + 1))).exists_forall_of_atTop
  have hstep : ∀ n, N₁ ≤ n → 3 * ((C : ℝ) + 1) * b n ≤ b (n + 1) := by
    intro n hn
    have h := hN₁ n hn
    rw [le_div_iff₀ (hbpos n)] at h
    linarith [h]
  have hgeo : ∀ j, ∑ n ∈ Finset.Ico N₁ (N₁ + j + 1), b n ≤ 2 * b (N₁ + j) := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.add_zero, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
        Finset.sum_range_one, Nat.add_zero]
      linarith [hbpos N₁]
    | succ j ih =>
      have hsplit : ∑ n ∈ Finset.Ico N₁ (N₁ + j + 1 + 1), b n
          = (∑ n ∈ Finset.Ico N₁ (N₁ + j + 1), b n) + b (N₁ + j + 1) :=
        Finset.sum_Ico_succ_top (by omega) b
      have hs := hstep (N₁ + j) (by omega)
      have h2 : (2:ℝ) * b (N₁ + j) ≤ b (N₁ + j + 1) := by nlinarith [hbpos (N₁ + j)]
      rw [show N₁ + (j + 1) = N₁ + j + 1 by omega, hsplit]
      linarith [ih, h2]
  have hgrow : ∀ j, (2:ℝ) ^ j * b N₁ ≤ b (N₁ + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hs := hstep (N₁ + j) (by omega)
      have h2 : (2:ℝ) * b (N₁ + j) ≤ b (N₁ + j + 1) := by nlinarith [hbpos (N₁ + j)]
      calc (2:ℝ) ^ (j + 1) * b N₁ = 2 * ((2:ℝ) ^ j * b N₁) := by ring
        _ ≤ 2 * b (N₁ + j) := by linarith [ih]
        _ ≤ b (N₁ + j + 1) := h2
        _ = b (N₁ + (j + 1)) := by congr 1
  set H := ∑ n ∈ Finset.range N₁, b n with hHdef
  have hpow : Tendsto (fun j => (2:ℝ) ^ j * b N₁) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ) < 2 by norm_num)).atTop_mul_const (hbpos N₁)
  obtain ⟨j₀, hj₀⟩ := (hpow.eventually_ge_atTop H).exists_forall_of_atTop
  refine ⟨N₁ + j₀ + 1, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = N₁ + m + 1 := ⟨k - N₁ - 1, by omega⟩
  have hmj₀ : j₀ ≤ m := by omega
  have hrangesplit : ∑ n ∈ Finset.range (N₁ + m + 1), b n
      = H + ∑ n ∈ Finset.Ico N₁ (N₁ + m + 1), b n := by
    rw [hHdef]
    exact (Finset.sum_range_add_sum_Ico b (show N₁ ≤ N₁ + m + 1 by omega)).symm
  have hHle : H ≤ b (N₁ + m) := le_trans (hj₀ m hmj₀) (hgrow m)
  have hgeom := hgeo m
  have hsm := hstep (N₁ + m) (by omega)
  rw [hrangesplit]
  calc ((C : ℝ) + 1) * (H + ∑ n ∈ Finset.Ico N₁ (N₁ + m + 1), b n)
      ≤ ((C : ℝ) + 1) * (b (N₁ + m) + 2 * b (N₁ + m)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith [hHle, hgeom]
    _ = 3 * ((C : ℝ) + 1) * b (N₁ + m) := by ring
    _ ≤ b (N₁ + m + 1) := hsm

/-- **Super-increasing valuation gap.**  If `b` is nonnegative and `(C+1)`-super-increasing, then for a
nonzero `g : ℕ →₀ ℤ` with `|g n| ≤ C`, the weighted valuation `∑ g n · b n` has absolute value at least
`b K / (C+1)`, where `K` is the greatest index in `g`'s support. -/
theorem valuation_gap_of_superIncreasing {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {C : ℕ}
    (hsi : ∀ k, ((C : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {g : ℕ →₀ ℤ} (hg : ∀ n, (g n).natAbs ≤ C) (hg0 : g ≠ 0) :
    b (g.support.max' (Finsupp.support_nonempty_iff.mpr hg0)) / ((C : ℝ) + 1)
      ≤ |∑ n ∈ g.support, (g n : ℝ) * b n| := by
  classical
  set K := g.support.max' (Finsupp.support_nonempty_iff.mpr hg0) with hKdef
  have hKmem : K ∈ g.support := Finset.max'_mem _ _
  have hKle : ∀ n ∈ g.support, n ≤ K := fun n hn => Finset.le_max' _ _ hn
  have hsplit : ∑ n ∈ g.support, (g n : ℝ) * b n
      = (g K : ℝ) * b K + ∑ n ∈ g.support.erase K, (g n : ℝ) * b n :=
    (Finset.add_sum_erase _ _ hKmem).symm
  have hsub : g.support.erase K ⊆ Finset.range K := by
    intro n hn
    rw [Finset.mem_erase] at hn
    exact Finset.mem_range.mpr (lt_of_le_of_ne (hKle n hn.2) hn.1)
  have htail : |∑ n ∈ g.support.erase K, (g n : ℝ) * b n| ≤ (C : ℝ) * ∑ n ∈ Finset.range K, b n := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hbnd : ∀ n ∈ g.support.erase K, |(g n : ℝ) * b n| ≤ (C : ℝ) * b n := by
      intro n _
      rw [abs_mul, abs_of_nonneg (hb n)]
      have hle : |(g n : ℝ)| ≤ (C : ℝ) := by
        have hz : (|g n| : ℤ) ≤ (C : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hg n
        rw [← Int.cast_abs]; exact_mod_cast hz
      exact mul_le_mul_of_nonneg_right hle (hb n)
    refine le_trans (Finset.sum_le_sum hbnd) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hb n)
  have hgK1 : (1 : ℝ) ≤ |(g K : ℝ)| := by
    have hne : g K ≠ 0 := Finsupp.mem_support_iff.mp hKmem
    have hz : (1 : ℤ) ≤ |g K| := by rw [Int.abs_eq_natAbs]; exact_mod_cast Int.natAbs_pos.mpr hne
    rw [← Int.cast_abs]; exact_mod_cast hz
  have hsiK := hsi K
  have hbK : 0 ≤ b K := hb K
  rw [hsplit]
  have hrev := abs_sub_abs_le_abs_add ((g K : ℝ) * b K)
      (∑ n ∈ g.support.erase K, (g n : ℝ) * b n)
  have habsGK : |(g K : ℝ) * b K| = |(g K : ℝ)| * b K := by rw [abs_mul, abs_of_nonneg hbK]
  have hsum_le : ∑ n ∈ Finset.range K, b n ≤ b K / ((C:ℝ)+1) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [hsiK]
  have hstep : b K / ((C : ℝ) + 1) ≤ |(g K : ℝ)| * b K
      - |∑ n ∈ g.support.erase K, (g n : ℝ) * b n| := by
    have h1 : (C : ℝ) * ∑ n ∈ Finset.range K, b n ≤ (C : ℝ) / ((C:ℝ)+1) * b K := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    have h2 : b K ≤ |(g K : ℝ)| * b K := by
      calc b K = 1 * b K := (one_mul _).symm
        _ ≤ |(g K : ℝ)| * b K := mul_le_mul_of_nonneg_right hgK1 hbK
    have h3 : b K - (C : ℝ) / ((C:ℝ)+1) * b K = b K / ((C:ℝ)+1) := by field_simp; ring
    linarith [htail]
  linarith [hrev, hstep, habsGK]

end GaloisForLFunctions
