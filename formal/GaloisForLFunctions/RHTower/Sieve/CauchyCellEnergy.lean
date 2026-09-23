import GaloisForLFunctions.RHTower.Sieve.PerronCutoffComparisons

/-!
# The unit-cell decomposition of a Cauchy-weighted energy

A Cauchy-weighted energy `∫ B(t)F(t)/(1+t²) dt` over `[-T, T]` is cut into the unit cells centred
at the integers.  On the cell around `c` the Cauchy weight is comparable to its value at the
centre, `1/(1+t²) ≤ 4/(1+c²)`, and the slowly varying factor `F` is replaced by its supremum over
the cell; what is left is the integral of `B` alone over a unit interval, which is exactly the
input a bounded-height mean-square estimate provides.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- The centre of the `k`-th unit cell of `[-H - 1/2, H + 1/2]`. -/
def cellCentre (H k : ℕ) : ℝ := (k : ℝ) - (H : ℝ)

theorem cellCentre_sub (H k : ℕ) : cellCentre H k - 1 / 2 = -(H : ℝ) - 1 / 2 + (k : ℝ) := by
  rw [cellCentre]; ring

theorem cellCentre_add (H k : ℕ) : cellCentre H k + 1 / 2 = -(H : ℝ) - 1 / 2 + ((k : ℝ) + 1) := by
  rw [cellCentre]; ring

/-- **The cell decomposition of a Cauchy-weighted energy.**  `Φ` bounds the slowly varying factor
on each cell and `E` bounds the integral of the rapidly varying factor over each cell. -/
theorem cell_energy_le {T : ℝ} (hT : 0 ≤ T) (H : ℕ) (hH : T ≤ (H : ℝ))
    {B F : ℝ → ℝ} (hB : Continuous B) (hF : Continuous F)
    (hBnn : ∀ t, 0 ≤ B t) (hFnn : ∀ t, 0 ≤ F t) (Φ E : ℕ → ℝ)
    (hΦ : ∀ k : ℕ, ∀ t : ℝ, |t - cellCentre H k| ≤ 1 / 2 → F t ≤ Φ k)
    (hE : ∀ k : ℕ,
      (∫ t in (cellCentre H k - 1 / 2)..(cellCentre H k + 1 / 2), B t) ≤ E k) :
    (∫ t in (-T)..T, B t * F t / (1 + t ^ (2 : ℕ)))
      ≤ ∑ k ∈ Finset.range (2 * H + 1), 4 * Φ k * E k / (1 + (cellCentre H k) ^ (2 : ℕ)) := by
  classical
  set g : ℝ → ℝ := fun t => B t * F t / (1 + t ^ (2 : ℕ)) with hg
  have hgc : Continuous g := by
    refine (hB.mul hF).div (by continuity) fun t => ?_
    positivity
  have hgnn : ∀ t, 0 ≤ g t := fun t => by
    have h1 : (0 : ℝ) < 1 + t ^ (2 : ℕ) := by positivity
    exact div_nonneg (mul_nonneg (hBnn t) (hFnn t)) h1.le
  set a : ℕ → ℝ := fun k => -(H : ℝ) - 1 / 2 + (k : ℝ) with ha
  have hint : ∀ k, IntervalIntegrable g volume (a k) (a (k + 1)) :=
    fun k => hgc.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := g) (μ := volume) (a := a) (n := 2 * H + 1) (fun k _ => hint k)
  have ha0 : a 0 = -(H : ℝ) - 1 / 2 := by rw [ha]; norm_num
  have haN : a (2 * H + 1) = (H : ℝ) + 1 / 2 := by
    rw [ha]; push_cast; ring
  -- enlarge the interval
  have hwide : (∫ t in (-T)..T, g t) ≤ ∫ t in (-(H : ℝ) - 1 / 2)..((H : ℝ) + 1 / 2), g t := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      ?_ (hgc.intervalIntegrable _ _)
    filter_upwards with t using hgnn t
  -- the per-cell bound
  have hcell : ∀ k ∈ Finset.range (2 * H + 1),
      (∫ t in (a k)..(a (k + 1)), g t) ≤ 4 * Φ k * E k / (1 + (cellCentre H k) ^ (2 : ℕ)) := by
    intro k _
    have hak : a k = cellCentre H k - 1 / 2 := by rw [ha, cellCentre_sub]
    have hak1 : a (k + 1) = cellCentre H k + 1 / 2 := by
      rw [ha, cellCentre_add]; push_cast; ring
    have hΦ0 : 0 ≤ Φ k := by
      have := hΦ k (cellCentre H k) (by simp)
      exact le_trans (hFnn _) this
    have hc0 : (0 : ℝ) < 1 + (cellCentre H k) ^ (2 : ℕ) := by positivity
    have hcoef0 : (0 : ℝ) ≤ 4 * Φ k / (1 + (cellCentre H k) ^ (2 : ℕ)) := by positivity
    have hle : a k ≤ a (k + 1) := by rw [hak, hak1]; linarith
    have hpt : ∀ t ∈ Set.Icc (a k) (a (k + 1)),
        g t ≤ (4 * Φ k / (1 + (cellCentre H k) ^ (2 : ℕ))) * B t := by
      intro t ht
      rw [hak, hak1] at ht
      have habs : |t - cellCentre H k| ≤ 1 / 2 := by
        rw [abs_le]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hFt : F t ≤ Φ k := hΦ k t habs
      have hcell : 1 / (1 + t ^ (2 : ℕ)) ≤ 4 / (1 + (cellCentre H k) ^ (2 : ℕ)) :=
        inv_one_add_sq_le_cell habs
      have ht0 : (0 : ℝ) < 1 + t ^ (2 : ℕ) := by positivity
      show B t * F t / (1 + t ^ (2 : ℕ)) ≤ _
      have hrw : B t * F t / (1 + t ^ (2 : ℕ)) = (B t * F t) * (1 / (1 + t ^ (2 : ℕ))) := by
        field_simp
      rw [hrw]
      have h1 : (B t * F t) * (1 / (1 + t ^ (2 : ℕ))) ≤ (B t * Φ k) * (1 / (1 + t ^ (2 : ℕ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hFt (hBnn t)
      have h2 : (B t * Φ k) * (1 / (1 + t ^ (2 : ℕ)))
          ≤ (B t * Φ k) * (4 / (1 + (cellCentre H k) ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hcell (mul_nonneg (hBnn t) hΦ0)
      have h3 : (B t * Φ k) * (4 / (1 + (cellCentre H k) ^ (2 : ℕ)))
          = (4 * Φ k / (1 + (cellCentre H k) ^ (2 : ℕ))) * B t := by ring
      linarith [h1, h2, h3.le, h3.ge]
    have hcont2 : Continuous fun t : ℝ =>
        (4 * Φ k / (1 + (cellCentre H k) ^ (2 : ℕ))) * B t := continuous_const.mul hB
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hle
      (hgc.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    refine hmono.trans ?_
    rw [hak, hak1]
    have hEk := hE k
    have := mul_le_mul_of_nonneg_left hEk hcoef0
    refine this.trans (le_of_eq ?_)
    field_simp
  calc (∫ t in (-T)..T, g t)
      ≤ ∫ t in (-(H : ℝ) - 1 / 2)..((H : ℝ) + 1 / 2), g t := hwide
    _ = ∑ k ∈ Finset.range (2 * H + 1), ∫ t in (a k)..(a (k + 1)), g t := by
        rw [hsum, ha0, haN]
    _ ≤ ∑ k ∈ Finset.range (2 * H + 1), 4 * Φ k * E k / (1 + (cellCentre H k) ^ (2 : ℕ)) :=
        Finset.sum_le_sum hcell

/-- The centre of the `k`-th cell of half-width `ρ` covering `[-2ρN, 2ρN]`. -/
def scaledCentre (ρ : ℝ) (N k : ℕ) : ℝ := -2 * ρ * (N : ℝ) + 2 * ρ * (k : ℝ) + ρ

/-- **The cell decomposition at an arbitrary cell width.**  The mean-square estimate available for
the rapidly varying factor fixes the cell width, which need not be one; any half-width at most
`1/2` keeps the Cauchy comparison constant equal to `4`. -/
theorem cell_energy_scaled_le {T ρ : ℝ} (hT : 0 ≤ T) (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (N : ℕ) (hN : T ≤ 2 * ρ * (N : ℝ))
    {B F : ℝ → ℝ} (hB : Continuous B) (hF : Continuous F)
    (hBnn : ∀ t, 0 ≤ B t) (hFnn : ∀ t, 0 ≤ F t) (Φ E : ℕ → ℝ)
    (hΦ : ∀ k : ℕ, ∀ t : ℝ, |t - scaledCentre ρ N k| ≤ ρ → F t ≤ Φ k)
    (hE : ∀ k : ℕ,
      (∫ t in (scaledCentre ρ N k - ρ)..(scaledCentre ρ N k + ρ), B t) ≤ E k) :
    (∫ t in (-T)..T, B t * F t / (1 + t ^ (2 : ℕ)))
      ≤ ∑ k ∈ Finset.range (2 * N), 4 * Φ k * E k / (1 + (scaledCentre ρ N k) ^ (2 : ℕ)) := by
  classical
  set g : ℝ → ℝ := fun t => B t * F t / (1 + t ^ (2 : ℕ)) with hg
  have hgc : Continuous g := by
    refine (hB.mul hF).div (by continuity) fun t => ?_
    positivity
  have hgnn : ∀ t, 0 ≤ g t := fun t => by
    have h1 : (0 : ℝ) < 1 + t ^ (2 : ℕ) := by positivity
    exact div_nonneg (mul_nonneg (hBnn t) (hFnn t)) h1.le
  set a : ℕ → ℝ := fun k => -2 * ρ * (N : ℝ) + 2 * ρ * (k : ℝ) with ha
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := g) (μ := volume) (a := a) (n := 2 * N)
    (fun k _ => hgc.intervalIntegrable _ _)
  have ha0 : a 0 = -2 * ρ * (N : ℝ) := by rw [ha]; norm_num
  have haN : a (2 * N) = 2 * ρ * (N : ℝ) := by rw [ha]; push_cast; ring
  have hwide : (∫ t in (-T)..T, g t)
      ≤ ∫ t in (-2 * ρ * (N : ℝ))..(2 * ρ * (N : ℝ)), g t := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      ?_ (hgc.intervalIntegrable _ _)
    filter_upwards with t using hgnn t
  have hcell : ∀ k ∈ Finset.range (2 * N),
      (∫ t in (a k)..(a (k + 1)), g t) ≤ 4 * Φ k * E k / (1 + (scaledCentre ρ N k) ^ (2 : ℕ)) := by
    intro k _
    have hak : a k = scaledCentre ρ N k - ρ := by rw [ha, scaledCentre]; ring
    have hak1 : a (k + 1) = scaledCentre ρ N k + ρ := by
      rw [ha, scaledCentre]; push_cast; ring
    have hΦ0 : 0 ≤ Φ k := le_trans (hFnn _) (hΦ k (scaledCentre ρ N k) (by simp [hρ.le]))
    have hc0 : (0 : ℝ) < 1 + (scaledCentre ρ N k) ^ (2 : ℕ) := by positivity
    have hcoef0 : (0 : ℝ) ≤ 4 * Φ k / (1 + (scaledCentre ρ N k) ^ (2 : ℕ)) := by positivity
    have hle : a k ≤ a (k + 1) := by rw [hak, hak1]; linarith
    have hpt : ∀ t ∈ Set.Icc (a k) (a (k + 1)),
        g t ≤ (4 * Φ k / (1 + (scaledCentre ρ N k) ^ (2 : ℕ))) * B t := by
      intro t ht
      rw [hak, hak1] at ht
      have habs : |t - scaledCentre ρ N k| ≤ ρ := by
        rw [abs_le]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have habs2 : |t - scaledCentre ρ N k| ≤ 1 / 2 := le_trans habs hρ2
      have hFt : F t ≤ Φ k := hΦ k t habs
      have hcmp : 1 / (1 + t ^ (2 : ℕ)) ≤ 4 / (1 + (scaledCentre ρ N k) ^ (2 : ℕ)) :=
        inv_one_add_sq_le_cell habs2
      have ht0 : (0 : ℝ) < 1 + t ^ (2 : ℕ) := by positivity
      show B t * F t / (1 + t ^ (2 : ℕ)) ≤ _
      have hrw : B t * F t / (1 + t ^ (2 : ℕ)) = (B t * F t) * (1 / (1 + t ^ (2 : ℕ))) := by field_simp
      rw [hrw]
      have h1 : (B t * F t) * (1 / (1 + t ^ (2 : ℕ))) ≤ (B t * Φ k) * (1 / (1 + t ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFt (hBnn t)) (by positivity)
      have h2 : (B t * Φ k) * (1 / (1 + t ^ (2 : ℕ)))
          ≤ (B t * Φ k) * (4 / (1 + (scaledCentre ρ N k) ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hcmp (mul_nonneg (hBnn t) hΦ0)
      have h3 : (B t * Φ k) * (4 / (1 + (scaledCentre ρ N k) ^ (2 : ℕ)))
          = (4 * Φ k / (1 + (scaledCentre ρ N k) ^ (2 : ℕ))) * B t := by ring
      linarith [h1, h2, h3.le, h3.ge]
    have hcont2 : Continuous fun t : ℝ =>
        (4 * Φ k / (1 + (scaledCentre ρ N k) ^ (2 : ℕ))) * B t := continuous_const.mul hB
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hle
      (hgc.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    refine hmono.trans ?_
    rw [hak, hak1]
    refine (mul_le_mul_of_nonneg_left (hE k) hcoef0).trans (le_of_eq ?_)
    field_simp
  calc (∫ t in (-T)..T, g t)
      ≤ ∫ t in (-2 * ρ * (N : ℝ))..(2 * ρ * (N : ℝ)), g t := hwide
    _ = ∑ k ∈ Finset.range (2 * N), ∫ t in (a k)..(a (k + 1)), g t := by
        rw [hsum, ha0, haN]
    _ ≤ ∑ k ∈ Finset.range (2 * N), 4 * Φ k * E k / (1 + (scaledCentre ρ N k) ^ (2 : ℕ)) :=
        Finset.sum_le_sum hcell

end

end RHTower.Sieve
