import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.SampledJumpsAdmitLipschitzApproximation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarCenterRowHasItsStrongProfile

/-!
# Cutoffs regularize the sampled polar center

A pair of affine ramps removes the origin and terminal logarithm. The resulting
center profile is continuous, while its error on a fixed terminal fraction is
supported entirely in the terminal strip and dominated by the original profile.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- A cutoff equal to one between the left fraction and the terminal strip. -/
def polarCenterCutoff (δ η x : ℝ) : ℝ :=
  (1 - descendingRamp (3 * δ / 4) (δ / 4) x) * descendingRamp (1 - η / 2) (η / 2) x

lemma polarCenterCutoff_bounds (δ η x : ℝ) :
    0 ≤ polarCenterCutoff δ η x ∧ polarCenterCutoff δ η x ≤ 1 := by
  obtain ⟨hl0, hl1⟩ := descendingRamp_bounds (3 * δ / 4) (δ / 4) x
  obtain ⟨hr0, hr1⟩ := descendingRamp_bounds (1 - η / 2) (η / 2) x
  unfold polarCenterCutoff
  exact ⟨mul_nonneg (sub_nonneg.mpr hl1) hr0,
    (mul_le_mul (by linarith only [hl0] : 1 - descendingRamp (3 * δ / 4) (δ / 4) x ≤ 1)
      hr1 hr0 zero_le_one).trans_eq (one_mul _)⟩

lemma polarCenterCutoff_eq_zero_left {δ η x : ℝ} (hδ : 0 < δ) (hx : x ≤ δ / 2) :
    polarCenterCutoff δ η x = 0 := by
  unfold polarCenterCutoff
  rw [descendingRamp_eq_one (by positivity : 0 < δ / 4) (by linarith only [hx]), sub_self, zero_mul]

lemma polarCenterCutoff_eq_right {δ η x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) :
    polarCenterCutoff δ η x = descendingRamp (1 - η / 2) (η / 2) x := by
  unfold polarCenterCutoff
  rw [descendingRamp_eq_zero (by positivity : 0 < δ / 4) (by linarith only [hx]), sub_zero, one_mul]

lemma polarCenterCutoff_eq_zero_one {δ η : ℝ} (hη : 0 < η) :
    polarCenterCutoff δ η 1 = 0 := by
  unfold polarCenterCutoff
  rw [descendingRamp_eq_zero (by positivity : 0 < η / 2) (by linarith), mul_zero]

/-- The two-ramp center cutoff has an explicit global Lipschitz bound. -/
lemma abs_polarCenterCutoff_sub_le {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (x y : ℝ) :
    |polarCenterCutoff δ η x - polarCenterCutoff δ η y| ≤ (2 / δ + 1 / η) * |x - y| := by
  let L := fun x => 1 - descendingRamp (3 * δ / 4) (δ / 4) x
  let H := descendingRamp (1 - η / 2) (η / 2)
  have hL : |L x - L y| ≤ (2 / δ) * |x - y| := by
    have hh := (lipschitzWith_descendingRamp (by positivity : 0 < δ / 4) (3 * δ / 4)).dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at hh
    dsimp only [L]
    have he : (1 - descendingRamp (3 * δ / 4) (δ / 4) x) -
        (1 - descendingRamp (3 * δ / 4) (δ / 4) y) =
        -(descendingRamp (3 * δ / 4) (δ / 4) x - descendingRamp (3 * δ / 4) (δ / 4) y) := by ring
    rw [he, abs_neg]
    exact hh.trans_eq (by congr 1 <;> field_simp <;> ring)
  have hH : |H x - H y| ≤ (1 / η) * |x - y| := by
    have hh := (lipschitzWith_descendingRamp (by positivity : 0 < η / 2) (1 - η / 2)).dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at hh
    exact hh.trans_eq (by congr 1 <;> field_simp <;> ring)
  have hL1 : |L y| ≤ 1 := by
    obtain ⟨h0, h1⟩ := descendingRamp_bounds (3 * δ / 4) (δ / 4) y
    rw [abs_of_nonneg (sub_nonneg.mpr h1)]
    linarith only [h0]
  have hH1 : |H x| ≤ 1 := by
    obtain ⟨h0, h1⟩ := descendingRamp_bounds (1 - η / 2) (η / 2) x
    rw [abs_of_nonneg h0]
    exact h1
  have he : polarCenterCutoff δ η x - polarCenterCutoff δ η y =
      (L x - L y) * H x + L y * (H x - H y) := by dsimp only [polarCenterCutoff, L, H]; ring
  rw [he]
  have hp := mul_le_mul hL hH1 (abs_nonneg _) (by positivity)
  have hq := mul_le_mul hL1 hH (abs_nonneg _) zero_le_one
  simp only [mul_one, one_mul, ← abs_mul] at hp hq
  exact ((abs_add_le _ _).trans (add_le_add hp hq)).trans_eq (by ring)

/-- The cutoff removes both singular endpoints of the polar center profile. -/
theorem continuousOn_polarCenterProfile_cutoff {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ContinuousOn (polarCenterProfile (polarCenterCutoff δ η)) (Set.Icc 0 1) := by
  exact continuousOn_polarCenterProfile (by positivity : 0 ≤ 2 / δ + 1 / η)
    (fun x _ y _ => abs_polarCenterCutoff_sub_le hδ hη x y)
    (polarCenterCutoff_eq_zero_one hη) (by positivity : 0 < δ / 2)
    (fun x _ hx => polarCenterCutoff_eq_zero_left hδ hx)

/-- On the retained terminal fraction, only the terminal strip contributes to the center error. -/
theorem polarCenterProfile_sub_cutoff_sq_le {δ η x : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hx : δ ≤ x) :
    (polarCenterProfile (fun _ => 1) x - polarCenterProfile (polarCenterCutoff δ η) x) ^ 2 ≤
      if 1 - η < x then polarCenterProfile (fun _ => 1) x ^ 2 else 0 := by
  have he : polarCenterProfile (polarCenterCutoff δ η) x =
      descendingRamp (1 - η / 2) (η / 2) x * polarCenterProfile (fun _ => 1) x := by
    unfold polarCenterProfile
    rw [polarCenterCutoff_eq_right hδ hx]
    ring
  rw [he]
  by_cases htop : 1 - η < x
  · rw [if_pos htop]
    obtain ⟨h0, h1⟩ := descendingRamp_bounds (1 - η / 2) (η / 2) x
    have hsq : (1 - descendingRamp (1 - η / 2) (η / 2) x) ^ 2 ≤ 1 := by
      nlinarith only [h0, h1, mul_nonneg h0 (sub_nonneg.mpr h1)]
    have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (polarCenterProfile (fun _ => 1) x))
    nlinarith only [hh]
  · rw [if_neg htop, descendingRamp_eq_one (by positivity : 0 < η / 2)
      (by have hh := le_of_not_gt htop; linarith only [hh]), one_mul, sub_self, zero_pow (by decide : 2 ≠ 0)]

/-- The terminal cutoff has uniformly small sampled square error, including endpoint atoms. -/
theorem normalized_sum_polarCenterProfile_sub_cutoff_sq_le {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hη4 : η ≤ 1 / 4) {N : ℕ} (hN8 : 8 ≤ N) :
    (∑ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (polarCenterProfile (fun _ => 1) ((n : ℝ) / N) -
        polarCenterProfile (polarCenterCutoff δ η) ((n : ℝ) / N)) ^ 2) / N ≤
      18 * (η + 1 / N) + 64 * Real.sqrt (η + 1 / N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  let K : ℕ := ⌊η * (N : ℝ)⌋₊ + 1
  have hKlo : η * (N : ℝ) ≤ K := by
    simpa only [K, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (η * (N : ℝ))).le
  have hKhi : (K : ℝ) ≤ η * N + 1 := by
    dsimp only [K]
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add_right (Nat.floor_le (by positivity)) _
  have h2K : 2 * K ≤ N := by
    have hh := mul_le_mul_of_nonneg_right hη4 hN0.le
    have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN8
    have hKr : 2 * (K : ℝ) ≤ N := by linarith only [hKhi, hh, hNr]
    exact_mod_cast hKr
  have hKN : K ≤ N := by omega
  let S := (Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N).filter (fun n : ℕ => 1 - η < (n : ℝ) / N)
  have hsub : S ⊆ Finset.Ioc (N - K) N := by
    intro n hn
    obtain ⟨hnI, hnη⟩ := Finset.mem_filter.mp hn
    have hlt := (lt_div_iff₀ hN0).mp hnη
    have hlo : ((N - K : ℕ) : ℝ) < n := by
      rw [Nat.cast_sub hKN]
      linarith only [hlt, hKlo]
    exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast hlo, (Finset.mem_Ioc.mp hnI).2⟩
  have hsum : (∑ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (polarCenterProfile (fun _ => 1) ((n : ℝ) / N) -
        polarCenterProfile (polarCenterCutoff δ η) ((n : ℝ) / N)) ^ 2) ≤
      ∑ n ∈ Finset.Ioc (N - K) N, polarCenterProfile (fun _ => 1) ((n : ℝ) / N) ^ 2 := by
    have hp : ∀ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N,
        (polarCenterProfile (fun _ => 1) ((n : ℝ) / N) -
          polarCenterProfile (polarCenterCutoff δ η) ((n : ℝ) / N)) ^ 2 ≤
        if 1 - η < (n : ℝ) / N then polarCenterProfile (fun _ => 1) ((n : ℝ) / N) ^ 2 else 0 := by
      intro n hn
      have hx : δ ≤ (n : ℝ) / N := (le_div_iff₀ hN0).mpr
        (le_of_lt ((Nat.floor_lt (by positivity : 0 ≤ δ * (N : ℝ))).mp (Finset.mem_Ioc.mp hn).1))
      exact polarCenterProfile_sub_cutoff_sq_le hδ hη hx
    have hh := Finset.sum_le_sum hp
    rw [← Finset.sum_filter] at hh
    exact hh.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _))
  have hratio : (K : ℝ) / N ≤ η + 1 / N :=
    (div_le_div_of_nonneg_right hKhi hN0.le).trans_eq (by field_simp [hN0.ne'])
  exact ((div_le_div_of_nonneg_right hsum hN0.le).trans
    (normalized_sum_terminal_polarCenterProfile_sq_le hN1 h2K)).trans
      (add_le_add (mul_le_mul_of_nonneg_left hratio (by norm_num))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) (by norm_num)))

#print axioms normalized_sum_polarCenterProfile_sub_cutoff_sq_le

#print axioms continuousOn_polarCenterProfile_cutoff
#print axioms polarCenterProfile_sub_cutoff_sq_le
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
