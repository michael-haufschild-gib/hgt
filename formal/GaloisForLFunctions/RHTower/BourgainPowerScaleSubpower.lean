/-
# Subpower closure of Bourgain's two-thirds bootstrap

A coarse fixed-power bound and a recurrence

`b(R) ≤ Cδ R^δ b(R^(2/3))`

for every positive `δ` imply `b(R) ≪ε R^ε`.  A fixed number of
iterations suffices for each target epsilon: the accumulated recurrence
loss is at most `3δ`, while the remaining coarse exponent is multiplied by
`(2/3)^k`.
-/
import GaloisForLFunctions.RHTower.BourgainPowerScaleBootstrap
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace RHTower

noncomputable section

/-- Bourgain's multiplicative two-thirds recurrence upgrades any coarse
power bound to an arbitrary subpower bound. -/
theorem bourgain_subpower_of_twoThirds_recurrence
    (b : ℝ → ℝ) {B γ : ℝ}
    (hB : 0 < B) (hγ : 0 ≤ γ)
    (hcoarse :
      ∀ x : ℝ, 1 ≤ x →
        b x ≤ B * x ^ γ)
    (hrec :
      ∀ δ : ℝ, 0 < δ →
        ∃ C : ℝ, 0 < C ∧
          ∀ x : ℝ, 1 ≤ x →
            b x ≤ C * x ^ δ * b (x ^ (2 / 3 : ℝ))) :
    ∀ ε : ℝ, 0 < ε →
      ∃ D : ℝ, 0 < D ∧
        ∀ x : ℝ, 1 ≤ x →
          b x ≤ D * x ^ ε := by
  intro ε hε
  let δ := ε / 6
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  obtain ⟨C, hC, hstep⟩ := hrec δ hδ
  have hpowTendsto :
      Tendsto (fun k : ℕ => (2 / 3 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hthreshold : 0 < ε / (2 * (γ + 1)) := by positivity
  have heventually :
      ∀ᶠ k : ℕ in atTop,
        (2 / 3 : ℝ) ^ k < ε / (2 * (γ + 1)) :=
    (tendsto_order.1 hpowTendsto).2 _ hthreshold
  obtain ⟨k, hk⟩ := heventually.exists
  have hk0 : 0 ≤ (2 / 3 : ℝ) ^ k := by positivity
  have hkγ :
      (2 / 3 : ℝ) ^ k * γ ≤ ε / 2 := by
    have hscaled :
        (2 / 3 : ℝ) ^ k * (γ + 1) <
          (ε / (2 * (γ + 1))) * (γ + 1) := by
      exact mul_lt_mul_of_pos_right hk (by linarith)
    have hmono :
        (2 / 3 : ℝ) ^ k * γ ≤
          (2 / 3 : ℝ) ^ k * (γ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have hcancel :
        (ε / (2 * (γ + 1))) * (γ + 1) = ε / 2 := by
      field_simp
    linarith
  refine ⟨C ^ k * B, mul_pos (pow_pos hC k) hB, ?_⟩
  intro x hx
  have hiter :=
    bourgain_powerScale_iterate b hC.le (by norm_num)
      hx hstep k
  have hy :
      1 ≤ x ^ ((2 / 3 : ℝ) ^ k) :=
    Real.one_le_rpow hx hk0
  have htail :=
    hcoarse (x ^ ((2 / 3 : ℝ) ^ k)) hy
  have hpref0 :
      0 ≤ C ^ k *
        x ^ (δ *
          ∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i) := by
    positivity
  have hsum :=
    bourgain_twoThirds_geometricSum_le_three k
  have hδsum :
      δ * ∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i ≤ ε / 2 := by
    dsimp [δ]
    nlinarith
  have hexponent :
      δ * ∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i +
          (2 / 3 : ℝ) ^ k * γ ≤ ε := by
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxnonneg : 0 ≤ x := hx0.le
  have hcombine :
      x ^ (δ * ∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i) *
          x ^ ((2 / 3 : ℝ) ^ k * γ) =
        x ^
          (δ * ∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i +
            (2 / 3 : ℝ) ^ k * γ) := by
    rw [← Real.rpow_add hx0]
  calc
    b x ≤
        C ^ k *
          x ^ (δ *
            ∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i) *
          b (x ^ ((2 / 3 : ℝ) ^ k)) :=
      hiter
    _ ≤
        C ^ k *
          x ^ (δ *
            ∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i) *
          (B * (x ^ ((2 / 3 : ℝ) ^ k)) ^ γ) :=
      mul_le_mul_of_nonneg_left htail hpref0
    _ =
        (C ^ k * B) *
          x ^
            (δ * ∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i +
              (2 / 3 : ℝ) ^ k * γ) := by
      rw [← Real.rpow_mul hxnonneg]
      calc
        C ^ k *
            x ^ (δ *
              ∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i) *
            (B * x ^ ((2 / 3 : ℝ) ^ k * γ)) =
          (C ^ k * B) *
            (x ^ (δ *
                ∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i) *
              x ^ ((2 / 3 : ℝ) ^ k * γ)) := by ring
        _ = _ := by rw [hcombine]
    _ ≤ (C ^ k * B) * x ^ ε := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx hexponent)
        (mul_nonneg (pow_nonneg hC.le k) hB.le)

end

end RHTower
