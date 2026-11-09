import GaloisForLFunctions.InfiniteRankWeilTheory.TopCoefficientWindowDensity
import GaloisForLFunctions.InfiniteRankWeilTheory.TheExceptionalRankDecidesTheWindow

/-!
# Coefficient density for infinite-rank towers

An isolated finite top forces a proportion of excursions determined by its merged coefficients.
The infinite remainder and the sub-top threshold contribute only bounded geometric errors to
the count in an arbitrary window. No restriction on the remainder's rank is needed.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- Total variation after merging equal modes in a finite top layer. -/
def mergedTopMass {ι : Type*} (F : Finset ι) (z b : ι → ℂ) : ℝ :=
  ∑ w ∈ F.image z, ‖∑ i ∈ F with z i = w, b i‖

/-- A finite top differs from the full trace by at most the remainder's trace-norm bound. -/
theorem norm_top_le_norm_levelSum_add {ι : Type*} (z b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) (F : Finset ι) {R r : ℝ}
    (hrest : ∀ i ∉ F, ‖z i‖ ≤ r) (htop : ∀ i ∈ F, ‖z i‖ ≤ R)
    (hr : 0 ≤ r) (n : ℕ) :
    ‖∑ i ∈ F, b i * z i ^ n‖ ≤ ‖levelSum z b n‖ + (∑' i, ‖b i‖) * r ^ n := by
  classical
  have hz : ∀ i, ‖z i‖ ≤ max R r := by
    intro i
    by_cases hi : i ∈ F
    · exact (htop i hi).trans (le_max_left _ _)
    · exact (hrest i hi).trans (le_max_right _ _)
  have hs := summable_levelTerm hz hb n
  let rest := levelSum (fun i : ↑((F : Set ι)ᶜ) => z i)
    (fun i : ↑((F : Set ι)ᶜ) => b i) n
  have hsplit : levelSum z b n = (∑ i ∈ F, b i * z i ^ n) + rest := by
    simpa only [rest, levelSum, zpow_natCast] using (hs.sum_add_tsum_compl (s := F)).symm
  have hrbound : ‖rest‖ ≤ (∑' i, ‖b i‖) * r ^ n := by
    calc ‖rest‖ ≤ (∑' i : ↑((F : Set ι)ᶜ), ‖b i‖) * r ^ n :=
          norm_levelSum_le (fun i : ↑((F : Set ι)ᶜ) => hrest i i.2) (hb.subtype _) n
      _ ≤ (∑' i, ‖b i‖) * r ^ n :=
          mul_le_mul_of_nonneg_right
            (Summable.tsum_subtype_le (fun i => ‖b i‖) _ (fun _ => norm_nonneg _) hb)
            (pow_nonneg hr n)
  have htri := norm_sub_le (levelSum z b n) rest
  rw [hsplit, add_sub_cancel_right] at htri
  rw [← hsplit] at htri
  exact htri.trans (add_le_add le_rfl hrbound)

/-- Every window obeys a linear excursion-count bound with an explicit bounded discrepancy.
Coincident top modes are merged before taking the coefficient ratio. -/
theorem isolatedTop_excursion_count {ι : Type*} (z b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) (F : Finset ι) {R r ρ C : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hrest : ∀ i ∉ F, ‖z i‖ ≤ r) (htop : ∀ i ∈ F, ‖z i‖ = R)
    (hρ : 0 ≤ ρ) (hρR : ρ < R) (hC : 0 ≤ C) {j : ι} (hj : j ∈ F) (M N : ℕ) :
    (N : ℝ) * ‖∑ i ∈ F with z i = z j, b i‖ ≤
      mergedTopMass F z b * ((range N).filter fun n =>
        C * ρ ^ (M + n) < ‖levelSum z b (M + n : ℕ)‖).card +
      coefficientInterference (F.image z) (fun w => w / (R : ℂ))
        (fun w => ∑ i ∈ F with z i = w, b i) (z j) +
      C / (1 - ρ / R) + (∑' i, ‖b i‖) / (1 - r / R) := by
  classical
  let P := F.image z
  let p : ℂ → ℂ := fun w => w / (R : ℂ)
  let c : ℂ → ℂ := fun w => ∑ i ∈ F with z i = w, b i
  let W : ℝ := ∑' i, ‖b i‖
  have hW : 0 ≤ W := tsum_nonneg fun _ => norm_nonneg _
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hp : Set.InjOn p (P : Set ℂ) := by
    intro x _ y _ h
    exact (div_left_inj' hRc).mp h
  have hu : ∀ w ∈ P, ‖p w‖ = 1 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hw
    change ‖z i / (R : ℂ)‖ = 1
    rw [norm_div, htop i hi, Complex.norm_real, Real.norm_of_nonneg hR.le,
      div_self hR.ne']
  have hnorm (n : ℕ) : ‖∑ w ∈ P, c w * p w ^ n‖ =
      ‖∑ i ∈ F, b i * z i ^ n‖ / R ^ n := by
    have heq : (∑ w ∈ P, c w * p w ^ n) =
        (∑ i ∈ F, b i * z i ^ n) / (R : ℂ) ^ n := by
      rw [sum_mul_pow_eq_sum_image z b F n, Finset.sum_div]
      refine Finset.sum_congr rfl fun w _ => ?_
      change c w * (w / (R : ℂ)) ^ n = c w * w ^ n / (R : ℂ) ^ n
      rw [div_pow, mul_div_assoc]
    rw [heq, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
  let E : ℕ → Prop := fun n => C * ρ ^ n < ‖levelSum z b n‖
  let a : ℕ → ℝ := fun n => C * (ρ / R) ^ n + W * (r / R) ^ n
  have ha : ∀ n, 0 ≤ a n := fun n =>
    add_nonneg (mul_nonneg hC (pow_nonneg (div_nonneg hρ hR.le) n))
      (mul_nonneg hW (pow_nonneg (div_nonneg hr hR.le) n))
  have hsmall : ∀ n, ¬ E n → ‖∑ w ∈ P, c w * p w ^ n‖ ≤ a n := by
    intro n hn
    have hn' : ‖levelSum z b n‖ ≤ C * ρ ^ n := le_of_not_gt hn
    rw [hnorm]
    calc ‖∑ i ∈ F, b i * z i ^ n‖ / R ^ n ≤
        (C * ρ ^ n + W * r ^ n) / R ^ n := by
          exact div_le_div_of_nonneg_right
            ((norm_top_le_norm_levelSum_add z b hb F hrest (fun i hi => (htop i hi).le)
              hr n).trans (add_le_add hn' le_rfl)) (pow_nonneg hR.le n)
      _ = a n := by dsimp [a]; rw [add_div, div_pow, div_pow]; ring
  have hcount := coefficient_le_excursion_count_add_error P p c hp hu
    (mem_image_of_mem z hj) E a ha hsmall M N
  have haSum : ∑ n ∈ range N, a (M + n) ≤ C / (1 - ρ / R) + W / (1 - r / R) := by
    simp only [a, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left
      (sum_window_pow_le (div_nonneg hρ hR.le) ((div_lt_one hR).mpr hρR) M N) hC
    have h2 := mul_le_mul_of_nonneg_left
      (sum_window_pow_le (div_nonneg hr hR.le) ((div_lt_one hR).mpr hrR) M N) hW
    simpa only [mul_one_div] using add_le_add h1 h2
  have hfinal := hcount.trans (add_le_add (add_le_add le_rfl haSum) le_rfl)
  simpa only [E, P, p, c, W, mergedTopMass, Nat.cast_add,
    add_assoc, add_comm, add_left_comm] using hfinal

/-- Every proportion below one merged coefficient's share holds in every sufficiently long
window, uniformly over all starting levels. -/
theorem isolatedTop_uniform_excursion_density {ι : Type*} (z b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) (F : Finset ι) {R r ρ C d : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hrest : ∀ i ∉ F, ‖z i‖ ≤ r) (htop : ∀ i ∈ F, ‖z i‖ = R)
    (hρ : 0 ≤ ρ) (hρR : ρ < R) (hC : 0 ≤ C) {j : ι} (hj : j ∈ F)
    (hd : d * mergedTopMass F z b < ‖∑ i ∈ F with z i = z j, b i‖) :
    ∃ N₀ : ℕ, ∀ M N : ℕ, N₀ ≤ N →
      d * N ≤ (((range N).filter fun n =>
        C * ρ ^ (M + n) < ‖levelSum z b (M + n : ℕ)‖).card : ℝ) := by
  classical
  let H := mergedTopMass F z b
  let B := ‖∑ i ∈ F with z i = z j, b i‖
  let K := coefficientInterference (F.image z) (fun w => w / (R : ℂ))
    (fun w => ∑ i ∈ F with z i = w, b i) (z j) +
    C / (1 - ρ / R) + (∑' i, ‖b i‖) / (1 - r / R)
  have hgap : 0 < B - d * H := sub_pos.mpr hd
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (K / (B - d * H))
  refine ⟨N₀, fun M N hN => ?_⟩
  have hlarge : K < (N : ℝ) * (B - d * H) := by
    apply (div_lt_iff₀ hgap).mp
    exact hN₀.trans_le (by exact_mod_cast hN)
  have hcount := isolatedTop_excursion_count z b hb F hR hr hrR hrest htop hρ hρR hC hj M N
  change (N : ℝ) * B ≤ H * _ + _ + _ + _ at hcount
  by_contra h
  have hlt := lt_of_not_ge h
  have hmul := mul_le_mul_of_nonneg_left hlt.le hH
  dsimp [K] at hlarge
  nlinarith only [hlarge, hcount, hmul]

#print axioms isolatedTop_excursion_count
#print axioms isolatedTop_uniform_excursion_density

end GaloisForLFunctions.InfiniteRankWeilTheory
