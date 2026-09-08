import GaloisForLFunctions.RHTower.MontgomerySpacedZeroDetection

/-!
# Block split of the Montgomery pair form

For any subset `A` of the zero window whose complement has amplitudes at most `Θ`, the real part
of the full pair form dominates the `A`-block minus the cross-term budget `64 Θ L_T Σ_{j∈A} a_j`:
the complementary block is nonnegative (Bochner) and each cross entry is bounded by the Lorentzian
weight, whose row sums are at most `8 L_T`.  This isolates the block whose mean square over a
window of scales is then estimated by Montgomery–Vaughan.
-/

open Finset

namespace RHTower

/-- Abstract block split: the `A × A` block of a Bochner-positive Hermitian array with
Lorentzian-dominated entries is controlled by the whole array up to the cross budget. -/
theorem configuration_energy_block_split {ι : Type*} [DecidableEq ι] (Z A : Finset ι)
    (hAZ : A ⊆ Z) (P : ι → ι → ℂ) (a : ι → ℝ) (w : ι → ι → ℝ) {Θ L : ℝ} (hΘ : 0 ≤ Θ)
    (ha : ∀ j, 0 ≤ a j) (hw : ∀ j k, 0 ≤ w j k) (hwsymm : ∀ j k, w j k = w k j)
    (h2 : ∀ j ∈ Z, ∀ k ∈ Z, ‖P j k‖ ≤ 4 * a j * a k * w j k)
    (h3 : ∀ R ⊆ Z, 0 ≤ (∑ j ∈ R, ∑ k ∈ R, P j k).re)
    (hR : ∀ k ∈ Z \ A, a k ≤ Θ)
    (h5 : ∀ j ∈ Z, ∑ k ∈ Z, w j k ≤ 8 * L) :
    (∑ j ∈ A, ∑ k ∈ A, P j k).re - 64 * Θ * L * ∑ j ∈ A, a j
      ≤ (∑ j ∈ Z, ∑ k ∈ Z, P j k).re := by
  classical
  set R := Z \ A with hRdef
  have hRZ : R ⊆ Z := Finset.sdiff_subset
  have hin : ∀ j, ∑ k ∈ Z, P j k = ∑ k ∈ R, P j k + ∑ k ∈ A, P j k :=
    fun j => (Finset.sum_sdiff hAZ).symm
  have hsplit : (∑ j ∈ Z, ∑ k ∈ Z, P j k)
      = ((∑ j ∈ R, ∑ k ∈ R, P j k) + ∑ j ∈ R, ∑ k ∈ A, P j k)
        + ((∑ j ∈ A, ∑ k ∈ R, P j k) + ∑ j ∈ A, ∑ k ∈ A, P j k) := by
    rw [← Finset.sum_sdiff hAZ (f := fun j => ∑ k ∈ Z, P j k)]
    simp only [hin, Finset.sum_add_distrib]
    rfl
  have hre : (∑ j ∈ Z, ∑ k ∈ Z, P j k).re
      = ((∑ j ∈ R, ∑ k ∈ R, P j k).re + (∑ j ∈ R, ∑ k ∈ A, P j k).re)
        + ((∑ j ∈ A, ∑ k ∈ R, P j k).re + (∑ j ∈ A, ∑ k ∈ A, P j k).re) := by
    rw [hsplit]; simp only [Complex.add_re]
  have hcrossbound : ∀ j ∈ A, ∑ k ∈ R, 4 * a j * a k * w j k ≤ 32 * Θ * L * a j := by
    intro j hj
    have haj := ha j
    have h4aΘ : (0 : ℝ) ≤ 4 * a j * Θ := mul_nonneg (mul_nonneg (by norm_num) haj) hΘ
    calc ∑ k ∈ R, 4 * a j * a k * w j k
        ≤ ∑ k ∈ R, 4 * a j * Θ * w j k := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hR k hk) (by linarith)) (hw j k)
      _ = 4 * a j * Θ * ∑ k ∈ R, w j k := by rw [Finset.mul_sum]
      _ ≤ 4 * a j * Θ * ∑ k ∈ Z, w j k :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hRZ (fun k _ _ => hw j k)) h4aΘ
      _ ≤ 4 * a j * Θ * (8 * L) := mul_le_mul_of_nonneg_left (h5 j (hAZ hj)) h4aΘ
      _ = 32 * Θ * L * a j := by ring
  have hAR : -(32 * Θ * L * ∑ j ∈ A, a j) ≤ (∑ j ∈ A, ∑ k ∈ R, P j k).re := by
    have hn : ‖∑ j ∈ A, ∑ k ∈ R, P j k‖ ≤ 32 * Θ * L * ∑ j ∈ A, a j := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k hk => h2 j (hAZ hj) k (hRZ hk)).trans ?_
      exact hcrossbound j hj
    have := Complex.abs_re_le_norm (∑ j ∈ A, ∑ k ∈ R, P j k)
    linarith [(abs_le.mp this).1]
  have hRA : -(32 * Θ * L * ∑ j ∈ A, a j) ≤ (∑ j ∈ R, ∑ k ∈ A, P j k).re := by
    rw [Finset.sum_comm]
    have hn : ‖∑ k ∈ A, ∑ j ∈ R, P j k‖ ≤ 32 * Θ * L * ∑ j ∈ A, a j := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun j hj => h2 j (hRZ hj) k (hAZ hk)).trans ?_
      refine le_trans (le_of_eq ?_) (hcrossbound k hk)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hwsymm j k]; ring
    have := Complex.abs_re_le_norm (∑ k ∈ A, ∑ j ∈ R, P j k)
    linarith [(abs_le.mp this).1]
  have hRR : 0 ≤ (∑ j ∈ R, ∑ k ∈ R, P j k).re := h3 R hRZ
  rw [hre]
  linarith

/-- **Block split of the Montgomery pair form at one scale.**  For `A ⊆ zeroWindow T` with all
complementary amplitudes at most `Θ`,
`Re F_A(x) − 64 Θ L_T Σ_{j∈A} a_j(x) ≤ Re F(x, T)`. -/
theorem montgomeryForm_block_split {x T : ℝ} (hx : 0 < x)
    (A : Finset XiZeroCopy) (hA : A ⊆ zeroWindow T) {Θ : ℝ} (hΘ : 0 ≤ Θ)
    (hR : ∀ k ∈ zeroWindow T \ A, zeroAmp x k ≤ Θ) :
    (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) x).re
        - 64 * Θ * windowLog T * ∑ j ∈ A, zeroAmp x j
      ≤ (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) x).re := by
  classical
  rw [montgomeryForm_eq_sum_pairEntry, montgomeryForm_eq_sum_pairEntry]
  refine configuration_energy_block_split (zeroWindow T) A hA (pairEntry x) (zeroAmp x)
    (fun j k => 1 / (3 + ((j.1 : ℂ).im - (k.1 : ℂ).im) ^ 2)) hΘ
    (zeroAmp_nonneg hx.le) (fun j k => by positivity) ?_ ?_ ?_ hR ?_
  · intro j k
    rw [show (j.1 : ℂ).im - (k.1 : ℂ).im = -((k.1 : ℂ).im - (j.1 : ℂ).im) by ring, neg_sq]
  · intro j _ k _
    exact norm_pairEntry_le hx j k
  · intro R _
    rw [← montgomeryForm_eq_sum_pairEntry]
    exact montgomeryForm_re_nonneg R _ hx fun q _ => ⟨xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q⟩
  · intro j hj
    exact sum_window_inv_three_add_sq_le hj

end RHTower
