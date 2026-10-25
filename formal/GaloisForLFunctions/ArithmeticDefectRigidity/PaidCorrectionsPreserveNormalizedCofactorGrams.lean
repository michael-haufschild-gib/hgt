import GaloisForLFunctions.ArithmeticDefectRigidity.WienerCovariancesFollowTheCommonCofactorLimit

/-!
# Paid corrections preserve normalized cofactor Grams

Cauchy–Schwarz bounds the three correction terms in a perturbed Gram entry.
Uniformly bounded correction energy vanishes after normalization by escaping energy.
-/

section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The four terms in the Gram pairing after adding two correction rows. -/
theorem pronicPairing_add_add (T : ℕ) (f g r s : ℕ → ℝ) :
    pronicPairing T (fun n => f n + r n) (fun n => g n + s n) =
      pronicPairing T f g + pronicPairing T f s +
        pronicPairing T r g + pronicPairing T r s := by
  simp only [pronicPairing, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- A paid correction changes an unnormalized Gram entry by at most a linear norm error. -/
theorem abs_pronicPairing_perturbation_le (T : ℕ) (f g r s : ℕ → ℝ) :
    |pronicPairing T (fun n => f n + r n) (fun n => g n + s n) -
      pronicPairing T f g| ≤
        pronicNorm T f * pronicNorm T s + pronicNorm T r * pronicNorm T g +
          pronicNorm T r * pronicNorm T s := by
  rw [pronicPairing_add_add]
  have heq : pronicPairing T f g + pronicPairing T f s +
      pronicPairing T r g + pronicPairing T r s - pronicPairing T f g =
      pronicPairing T f s + pronicPairing T r g + pronicPairing T r s := by ring
  rw [heq]
  have htri : |pronicPairing T f s + pronicPairing T r g + pronicPairing T r s| ≤
      |pronicPairing T f s| + |pronicPairing T r g| + |pronicPairing T r s| := by
    simpa only [Real.norm_eq_abs] using
      ((norm_add_le (pronicPairing T f s + pronicPairing T r g) (pronicPairing T r s)).trans
        (add_le_add (norm_add_le (pronicPairing T f s) (pronicPairing T r g)) le_rfl))
  exact htri.trans
    (add_le_add (add_le_add (abs_pronicPairing_le T f s)
      (abs_pronicPairing_le T r g)) (abs_pronicPairing_le T r s))

/-- Uniformly paid corrections disappear from Gram entries at every diverging energy scale. -/
theorem normalized_pronicPairing_perturbation_tendsto_zero
    (E : ℕ → ℝ) (hEpos : ∀ T, 0 < E T) (hE : Tendsto E atTop atTop)
    (f g r s : ℕ → ℝ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ T, pronicNorm T f ≤ C * Real.sqrt (E T))
    (hg : ∀ T, pronicNorm T g ≤ C * Real.sqrt (E T))
    (hr : ∀ T, pronicNorm T r ≤ D) (hs : ∀ T, pronicNorm T s ≤ D) :
    Tendsto (fun T =>
      (pronicPairing T (fun n => f n + r n) (fun n => g n + s n) -
        pronicPairing T f g) / E T) atTop (𝓝 0) := by
  have hlim₁ : Tendsto (fun T => (2 * C * D) / Real.sqrt (E T)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hE)
  have hlim₂ : Tendsto (fun T => D ^ 2 / E T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hE
  have hlim := hlim₁.add hlim₂
  rw [add_zero] at hlim
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  refine squeeze_zero (fun _ => abs_nonneg _) (fun T => ?_) hlim
  change |(_ - _) / E T| ≤ _
  rw [abs_div, abs_of_pos (hEpos T)]
  calc
    _ ≤ (pronicNorm T f * pronicNorm T s +
          pronicNorm T r * pronicNorm T g + pronicNorm T r * pronicNorm T s) / E T :=
      div_le_div_of_nonneg_right (abs_pronicPairing_perturbation_le T f g r s) (hEpos T).le
    _ ≤ (C * Real.sqrt (E T) * D + D * (C * Real.sqrt (E T)) + D * D) / E T :=
      div_le_div_of_nonneg_right
        (add_le_add
          (add_le_add (mul_le_mul (hf T) (hs T) (pronicNorm_nonneg T s) (by positivity))
            (mul_le_mul (hr T) (hg T) (pronicNorm_nonneg T g) hD))
          (mul_le_mul (hr T) (hs T) (pronicNorm_nonneg T s) hD)) (hEpos T).le
    _ = (2 * C * D) / Real.sqrt (E T) + D ^ 2 / E T := by
      have hsq := Real.sq_sqrt (hEpos T).le
      have hsqrt := (Real.sqrt_pos.mpr (hEpos T)).ne'
      field_simp [hsqrt, (hEpos T).ne']
      nlinarith only [congrArg (fun x : ℝ => C * D * x) hsq]

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.normalized_pronicPairing_perturbation_tendsto_zero
end
end


section
noncomputable section
set_option autoImplicit false
open Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The zero-energy initial horizon does not affect the paid-correction limit. -/
theorem normalized_pronicPairing_perturbation_tendsto_zero_of_nonneg
    (E : ℕ → ℝ) (hEpos : ∀ T, 0 ≤ E T) (hE : Tendsto E atTop atTop)
    (f g r s : ℕ → ℝ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ T, pronicNorm T f ≤ C * Real.sqrt (E T))
    (hg : ∀ T, pronicNorm T g ≤ C * Real.sqrt (E T))
    (hr : ∀ T, pronicNorm T r ≤ D) (hs : ∀ T, pronicNorm T s ≤ D) :
    Tendsto (fun T =>
      (pronicPairing T (fun n => f n + r n) (fun n => g n + s n) -
        pronicPairing T f g) / E T) atTop (𝓝 0) := by
  have hplus : ∀ T, 0 < E T + 1 := fun T => by linarith only [hEpos T]
  have h := normalized_pronicPairing_perturbation_tendsto_zero (fun T => E T + 1)
    hplus (tendsto_atTop_mono (fun (T : ℕ) => (by linarith only : E T ≤ E T + 1)) hE) f g r s hC hD
    (fun T => (hf T).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith only : E T ≤ E T + 1)) hC))
    (fun T => (hg T).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith only : E T ≤ E T + 1)) hC)) hr hs
  have hinv : Tendsto (fun T => 1 / E T) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hE
  have hratio : Tendsto (fun T => (E T + 1) / E T) atTop (𝓝 (1 : ℝ)) := by
    have hz : Tendsto (fun T => 1 + 1 / E T) atTop (𝓝 ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add hinv
    rw [add_zero] at hz
    apply hz.congr'
    filter_upwards [hE.eventually_gt_atTop 0] with T hT
    field_simp [hT.ne']
  have hmul := h.mul hratio
  rw [zero_mul] at hmul
  apply hmul.congr
  intro T
  rw [← mul_div_assoc, div_mul_cancel₀ _ (hplus T).ne']


end GaloisForLFunctions.ArithmeticDefectRigidity

end
end
