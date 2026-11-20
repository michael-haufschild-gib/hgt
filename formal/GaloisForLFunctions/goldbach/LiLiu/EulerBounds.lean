import GaloisForLFunctions.goldbach.LiLiu.DensityEuler
import GaloisForLFunctions.RHTower.ZetaGaussianZeroSums

/-! # Size and conjugation of the Euler correction -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex GaloisForLFunctions.HTGeometry Filter
open scoped ComplexConjugate
noncomputable section

/-- Uniform in the modulus and in the height throughout a closed right half-plane. -/
theorem densityEuler_norm_bound {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (w : ℂ), a ≤ w.re → ‖densityEuler N w‖ ≤ B := by
  let m (p : Nat.Primes) := 3 * ((p : ℕ) : ℝ) ^ (-(1 + a))
  have hm : Summable m := (summable_prime_rpow_neg (show 1 < 1 + a by linarith)).mul_left 3
  refine ⟨Real.exp (∑' p, m p), Real.exp_pos _, ?_⟩
  intro N w hw
  have hprod := (hasProdLocallyUniformlyOn_densityEuler N (half_pos ha)).hasProd
    ((half_lt_self ha).trans_le hw)
  apply le_of_tendsto hprod.norm
  apply Eventually.of_forall
  intro S
  calc
    ‖∏ p ∈ S, (1 + densityIncrement N p w)‖ ≤ ∏ p ∈ S, ‖1 + densityIncrement N p w‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ S, Real.exp (m p) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro p _
      have h := norm_add_le (1 : ℂ) (densityIncrement N p w)
      rw [norm_one] at h
      exact h.trans ((add_le_add_right (norm_densityIncrement_le N p hw) 1).trans
        (by simpa only [add_comm] using Real.add_one_le_exp (m p)))
    _ = Real.exp (∑ p ∈ S, m p) := (Real.exp_sum ..).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hm.sum_le_tsum _ fun p _ => by dsimp [m]; positivity)

theorem densityIncrement_conj (N : ℕ) (p : Nat.Primes) (w : ℂ) :
    densityIncrement N p (conj w) = conj (densityIncrement N p w) := by
  unfold densityIncrement
  split_ifs
  · rw [← map_neg, map_div₀, map_sub, map_ofNat, map_natCast]
    congr 1
    simpa only [Complex.ofReal_natCast] using
      _root_.RHTower.GaussZeroSum.ofReal_cpow_conj (Nat.cast_pos.mpr p.prop.pos) (-w)
  · simp

theorem densityEuler_conj (N : ℕ) {w : ℂ} (hw : 0 < w.re) :
    densityEuler N (conj w) = conj (densityEuler N w) := by
  have h := hasProdLocallyUniformlyOn_densityEuler N (half_pos hw)
  have hp := (h.hasProd (x := w) (half_lt_self hw)).map (starRingEnd ℂ) Complex.continuous_conj
  have hc := h.hasProd (x := conj w) (half_lt_self hw)
  apply hc.unique
  apply hp.congr_fun
  intro p
  simp only [Function.comp_apply, map_add, map_one, densityIncrement_conj]

#print axioms densityEuler_norm_bound
#print axioms densityEuler_conj
end
end GaloisForLFunctions.Goldbach.LiLiu
