import GaloisForLFunctions.ArithmeticDefectRigidity.WienerCovariancesFollowTheCommonCofactorLimit

/-!
# Vanishing relative energy preserves moving Grams

Pronic Cauchy–Schwarz makes every cross pairing involving a correction of
vanishing relative energy disappear. Bilinear expansion gives exact Gram
stability for arbitrary moving rows with convergent relative energies.
-/

section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A row of vanishing relative energy pairs negligibly with any row of convergent relative energy. -/
theorem normalized_pairing_tendsto_zero_of_left_energy
    (T : ℕ → ℕ) (E : ℕ → ℝ) (hE : ∀ᶠ m in atTop, 0 < E m)
    (r f : ℕ → ℕ → ℝ) {b : ℝ}
    (hr : Tendsto (fun m => pronicNorm (T m) (r m) ^ 2 / E m) atTop (𝓝 0))
    (hf : Tendsto (fun m => pronicNorm (T m) (f m) ^ 2 / E m) atTop (𝓝 b)) :
    Tendsto (fun m => pronicPairing (T m) (r m) (f m) / E m) atTop (𝓝 0) := by
  have hr' := Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have hf' := Real.continuous_sqrt.continuousAt.tendsto.comp hf
  rw [Real.sqrt_zero] at hr'
  have hlim := hr'.mul hf'
  rw [zero_mul] at hlim
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hlim
  filter_upwards [hE] with m hm
  change |pronicPairing (T m) (r m) (f m) / E m| ≤
    Real.sqrt (pronicNorm (T m) (r m) ^ 2 / E m) *
      Real.sqrt (pronicNorm (T m) (f m) ^ 2 / E m)
  rw [abs_div, abs_of_pos hm, Real.sqrt_div (sq_nonneg _), Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (pronicNorm_nonneg _ _), Real.sqrt_sq (pronicNorm_nonneg _ _)]
  calc
    _ ≤ pronicNorm (T m) (r m) * pronicNorm (T m) (f m) / E m :=
      div_le_div_of_nonneg_right (abs_pronicPairing_le _ _ _) hm.le
    _ = _ := by
      rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hm.le]

/-- Vanishing-energy moving corrections leave every normalized Gram entry unchanged. -/
theorem normalized_moving_gram_perturbation_tendsto_zero
    (T : ℕ → ℕ) (E : ℕ → ℝ) (hE : ∀ᶠ m in atTop, 0 < E m)
    (f g r s : ℕ → ℕ → ℝ) {a b : ℝ}
    (hf : Tendsto (fun m => pronicNorm (T m) (f m) ^ 2 / E m) atTop (𝓝 a))
    (hg : Tendsto (fun m => pronicNorm (T m) (g m) ^ 2 / E m) atTop (𝓝 b))
    (hr : Tendsto (fun m => pronicNorm (T m) (r m) ^ 2 / E m) atTop (𝓝 0))
    (hs : Tendsto (fun m => pronicNorm (T m) (s m) ^ 2 / E m) atTop (𝓝 0)) :
    Tendsto (fun m =>
      (pronicPairing (T m) (fun n => f m n + r m n) (fun n => g m n + s m n) -
        pronicPairing (T m) (f m) (g m)) / E m) atTop (𝓝 0) := by
  have hfs := normalized_pairing_tendsto_zero_of_left_energy T E hE s f hs hf
  have hrg := normalized_pairing_tendsto_zero_of_left_energy T E hE r g hr hg
  have hrs := normalized_pairing_tendsto_zero_of_left_energy T E hE r s hr hs
  have hlim := (hfs.add hrg).add hrs
  simp only [add_zero] at hlim
  apply hlim.congr
  intro m
  simp only [pronicPairing, ← add_div, ← sum_add_distrib, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun n _ => by ring

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.normalized_moving_gram_perturbation_tendsto_zero
end
end
