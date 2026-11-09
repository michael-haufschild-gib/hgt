import GaloisForLFunctions.InfiniteRankWeilTheory.OscillatorySamplingDimension
import GaloisForLFunctions.InfiniteRankWeilTheory.AlmostEveryIsolatedTopSampling

/-!
# Dimension-zero bases that repeatedly miss an isolated top

A recurrent sub-top bound on the whole trace forces an exponentially small normalized top.
The summable lower layer has a strictly smaller exponential rate, so its contribution and any
fixed recurrence constant are absorbed by a single decay rate independent of the base.
-/

open Complex Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- Positive bases whose trace has infinitely many readings below some constant multiple
of a prescribed exponential rate. -/
def towerRecurrenceBases {ι : Type*} (ρ b : ι → ℂ) (a : ℝ) : Set ℝ :=
  {ℓ | 0 < ℓ ∧ ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
    ‖levelSum (frobTower ℓ ρ) b n‖ ≤ C * Real.exp (a * (n : ℝ) * ℓ)}

theorem towerRecurrenceBases_mono {ι : Type*} (ρ b : ι → ℂ) {a a' : ℝ} (ha : a ≤ a') :
    towerRecurrenceBases ρ b a ⊆ towerRecurrenceBases ρ b a' := by
  rintro ℓ ⟨hℓ, C, hC⟩
  refine ⟨hℓ, max C 0, hC.mono fun n hn => hn.trans ?_⟩
  calc C * Real.exp (a * (n : ℝ) * ℓ)
      ≤ max C 0 * Real.exp (a * (n : ℝ) * ℓ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (a' * (n : ℝ) * ℓ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)) hℓ.le))
          (le_max_right _ _)

/-- Recurrence below an isolated top occurs on a set of Hausdorff dimension zero. -/
theorem dimH_towerRecurrenceBases_eq_zero_of_isolatedTop {ι : Type*} (ρ b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) (F : Finset ι) {Θ Θ₂ a : ℝ}
    (hgap : Θ₂ < Θ) (hF : ∀ i ∈ F, (ρ i).re = Θ)
    (hrest : ∀ i ∉ F, (ρ i).re ≤ Θ₂)
    (hvis : ∃ j ∈ F, (∑ i ∈ F with (ρ i).im = (ρ j).im, b i) ≠ 0)
    (ha : a < Θ - 1 / 2) : dimH (towerRecurrenceBases ρ b a) = 0 := by
  let δ : ℝ := min (Θ - 1 / 2 - a) (Θ - Θ₂) / 2
  have hmin : 0 < min (Θ - 1 / 2 - a) (Θ - Θ₂) :=
    lt_min (sub_pos.mpr ha) (sub_pos.mpr hgap)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδmin : δ < min (Θ - 1 / 2 - a) (Θ - Θ₂) := by dsimp [δ]; linarith only [hmin]
  have hδa := hδmin.trans_le (min_le_left (Θ - 1 / 2 - a) (Θ - Θ₂))
  have hδgap := hδmin.trans_le (min_le_right (Θ - 1 / 2 - a) (Θ - Θ₂))
  have hsub : towerRecurrenceBases ρ b a ⊆
      exponentiallySmallSamplingBases (TrigSum.trigSum F b (fun i => (ρ i).im)) δ := by
    rintro ℓ ⟨hℓ, C, hC⟩
    let Q : ℝ := Real.exp (ℓ * (Θ - 1 / 2 - δ))
    let r : ℝ := Real.exp (ℓ * (Θ₂ - 1 / 2))
    let s : ℝ := Real.exp (a * ℓ)
    have hQ : 0 < Q := Real.exp_pos _
    have hrQ : r < Q := Real.exp_lt_exp.mpr
      (mul_lt_mul_of_pos_left (by linarith only [hδgap]) hℓ)
    have hsQ : s < Q := Real.exp_lt_exp.mpr (by
      have h := mul_lt_mul_of_pos_left
        (show a < Θ - 1 / 2 - δ by linarith only [hδa]) hℓ
      simpa only [mul_comm] using h)
    obtain ⟨htop, hlow, _⟩ := frobTower_isolatedTop hℓ hgap hF hrest
    refine ⟨hℓ, ((hC.and_eventually (eventually_two_powers_lt
      (Real.exp_pos _).le (Real.exp_pos _).le hQ hrQ hsQ (∑' i, ‖b i‖) C)).mono ?_)⟩
    intro n hn
    have hread : ‖levelSum (frobTower ℓ ρ) b n‖ ≤ C * s ^ n := by
      simpa only [s, ← Real.exp_nat_mul,
        show (n : ℝ) * (a * ℓ) = a * n * ℓ by ring] using hn.1
    have hbound := norm_top_le_norm_levelSum_add (frobTower ℓ ρ) b hb F hlow
      (fun i hi => (htop i hi).le) (Real.exp_pos _).le n
    change ‖∑ i ∈ F, b i * frobTower ℓ ρ i ^ n‖ ≤
      ‖levelSum (frobTower ℓ ρ) b n‖ + (∑' i, ‖b i‖) * r ^ n at hbound
    have htopSmall : ‖∑ i ∈ F, b i * frobTower ℓ ρ i ^ n‖ < Q ^ n := by
      linarith only [hbound, hread, hn.2]
    rw [top_sum_eq_growth_mul_trigSum ρ b F hF, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le] at htopSmall
    have heq : Q ^ n = Real.exp ((Θ - 1 / 2) * ((n : ℝ) * ℓ)) *
        Real.exp (-δ * ((n : ℝ) * ℓ)) := by
      dsimp [Q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [heq] at htopSmall
    exact (lt_of_mul_lt_mul_left htopSmall (Real.exp_pos _).le).le
  exact le_antisymm ((dimH_mono hsub).trans_eq
    (dimH_finset_oscillatory_exp_small_eq_zero F (fun i => (ρ i).im) b hvis hδ)) bot_le

/-- A single dimension-zero exceptional set works simultaneously for every rate below the top
and every recurrence constant. -/
theorem dimH_all_subtop_towerRecurrenceBases_eq_zero {ι : Type*} (ρ b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) (F : Finset ι) {Θ Θ₂ : ℝ}
    (hgap : Θ₂ < Θ) (hF : ∀ i ∈ F, (ρ i).re = Θ)
    (hrest : ∀ i ∉ F, (ρ i).re ≤ Θ₂)
    (hvis : ∃ j ∈ F, (∑ i ∈ F with (ρ i).im = (ρ j).im, b i) ≠ 0) :
    dimH {ℓ : ℝ | ∃ a : ℝ, a < Θ - 1 / 2 ∧ ℓ ∈ towerRecurrenceBases ρ b a} = 0 := by
  let a : ℕ → ℝ := fun m => Θ - 1 / 2 - 1 / ((m : ℝ) + 1)
  have hsub : {ℓ : ℝ | ∃ a : ℝ, a < Θ - 1 / 2 ∧ ℓ ∈ towerRecurrenceBases ρ b a} ⊆
      ⋃ m : ℕ, towerRecurrenceBases ρ b (a m) := by
    rintro ℓ ⟨q, hq, hℓ⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hq)
    exact mem_iUnion.mpr ⟨m, towerRecurrenceBases_mono ρ b
      (by dsimp [a]; linarith only [hm]) hℓ⟩
  have hz (m : ℕ) : dimH (towerRecurrenceBases ρ b (a m)) = 0 :=
    dimH_towerRecurrenceBases_eq_zero_of_isolatedTop ρ b hb F hgap hF hrest hvis
      (by dsimp [a]; linarith only [show 0 < 1 / ((m : ℝ) + 1) by positivity])
  apply le_antisymm ((dimH_mono hsub).trans ?_) (show (0 : ENNReal) ≤ _ from zero_le)
  rw [dimH_iUnion]
  simp only [hz, iSup_const, le_refl]

#print axioms dimH_towerRecurrenceBases_eq_zero_of_isolatedTop
#print axioms dimH_all_subtop_towerRecurrenceBases_eq_zero

end GaloisForLFunctions.InfiniteRankWeilTheory
