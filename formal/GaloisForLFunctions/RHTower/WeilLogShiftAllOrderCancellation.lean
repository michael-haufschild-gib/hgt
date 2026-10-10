import GaloisForLFunctions.RHTower.RiemannAutocorrMomentCancellation
import GaloisForLFunctions.RHTower.WeilLogShiftFiniteTailCompensation

/-!
# Arbitrary-order cancellation in consecutive logarithmic clusters

Rank-nullity supplies normalized signed coefficients. Their logarithmic
moments cancel before applying the actual autocorrelation estimate.
-/

open scoped BigOperators

namespace RHTower

theorem exists_normalized_real_moment_annihilator (r : ℕ) (h : Fin (r + 2) → ℝ) :
    ∃ c : Fin (r + 2) → ℝ, ‖c‖ = 1 ∧ ∀ p ≤ r, ∑ i, c i * h i ^ p = 0 := by
  let T : (Fin (r + 2) → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ) :=
    { toFun := fun c p => ∑ i, c i * h i ^ (p : ℕ)
      map_add' := by
        intro c d
        funext p
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        funext p
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hdim : Module.finrank ℝ (Fin (r + 1) → ℝ) <
      Module.finrank ℝ (Fin (r + 2) → ℝ) := by
    simp only [Module.finrank_fin_fun]
    omega
  obtain ⟨c, hcT, hc⟩ := (Submodule.ne_bot_iff T.ker).mp
    (LinearMap.ker_ne_bot_of_finrank_lt hdim)
  refine ⟨‖c‖⁻¹ • c, norm_smul_inv_norm (𝕜 := ℝ) hc, ?_⟩
  have hz : T c = 0 := hcT
  have hs : T (‖c‖⁻¹ • c) = 0 := by rw [map_smul, hz, smul_zero]
  intro p hp
  exact congrFun hs ⟨p, by omega⟩

/-- A cluster with `r+2` consecutive arithmetic labels has a unit coefficient
direction with sensitivity at most a constant times `n^(-(r+3))`. -/
theorem pairedLogKernel_cluster_envelope_with_moments (r : ℕ) {E : ℝ} (hE : 0 < E)
    (hcancel : ∀ (ι : Type) [Fintype ι] (c h : ι → ℝ) (H : ℝ),
      0 ≤ H → H ≤ 1 → (∀ i, 0 ≤ h i ∧ h i ≤ H) →
      (∀ p ≤ r, ∑ i, c i * h i ^ p = 0) → ∀ y : ℝ,
      |∑ i, c i * riemannAutocorr (y - h i)| ≤
        E * Real.exp (-2 * |y|) * (∑ i, |c i|) * H ^ (r + 1)) :
    ∀ n : ℕ, r + 1 ≤ n →
      ∃ c : Fin (r + 2) → ℝ, ‖c‖ = 1 ∧
        (∀ p ≤ r, ∑ i, c i *
          (Real.log ((n + (i : ℕ) : ℕ) : ℝ) - Real.log (n : ℝ)) ^ p = 0) ∧ ∀ y : ℝ,
        |∑ i, c i * pairedLogKernel y (n + (i : ℕ))| ≤
          (2 * E * ((r + 2 : ℕ) : ℝ)) * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ *
            (((r + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (r + 1) := by
  let R : ℝ := (r + 1 : ℕ)
  let M : ℝ := (r + 2 : ℕ)
  have hR : 0 < R := by dsimp [R]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  intro n hn
  let x : ℝ := n
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  have hx : 0 < x := by linarith
  have hRx : R ≤ x := by dsimp [R, x]; exact_mod_cast hn
  let h : Fin (r + 2) → ℝ := fun i => Real.log (x + (i : ℕ)) - Real.log x
  have hh (i : Fin (r + 2)) : 0 ≤ h i ∧ h i ≤ R / x := by
    have hi : (i : ℝ) ≤ R := by
      dsimp [R]
      exact_mod_cast (show (i : ℕ) ≤ r + 1 by omega)
    have hxi : 0 < x + (i : ℕ) := by positivity
    constructor
    · dsimp [h]
      exact sub_nonneg.mpr (Real.log_le_log hx (le_add_of_nonneg_right (Nat.cast_nonneg _)))
    · dsimp [h]
      rw [← Real.log_div hxi.ne' hx.ne']
      calc
        Real.log ((x + (i : ℕ)) / x) ≤ (x + (i : ℕ)) / x - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hxi hx)
        _ = (i : ℝ) / x := by field_simp; ring
        _ ≤ R / x := div_le_div_of_nonneg_right hi hx.le
  obtain ⟨c, hnorm, hm⟩ := exists_normalized_real_moment_annihilator r h
  refine ⟨c, hnorm, ?_, ?_⟩
  · intro p hp
    simpa only [h, x, Nat.cast_add] using hm p hp
  have hL : (∑ i, |c i|) ≤ M := by
    calc
      ∑ i, |c i| ≤ ∑ _i : Fin (r + 2), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Real.norm_eq_abs, hnorm] using norm_le_pi_norm c i
      _ = M := by simp [M]
  have hwidth0 : 0 ≤ R / x := (div_pos hR hx).le
  have hwidth1 : R / x ≤ 1 := (div_le_one hx).mpr hRx
  have hcenter (z : ℝ) : Real.exp (-2 * |z - Real.log x|) ≤
      Real.exp (2 * |z|) * (x ^ 2)⁻¹ := by
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    have ht : Real.log x ≤ |z| + |z - Real.log x| := by
      have ha := abs_sub (Real.log x - z) (-z)
      rw [abs_neg, abs_sub_comm (Real.log x) z] at ha
      rw [show Real.log x - z - -z = Real.log x by ring, abs_of_nonneg hlog] at ha
      linarith
    have hexp : Real.exp (2 * Real.log x) = x ^ 2 := by
      rw [show 2 * Real.log x = Real.log x + Real.log x by ring, Real.exp_add,
        Real.exp_log hx]
      ring
    calc
      Real.exp (-2 * |z - Real.log x|) ≤ Real.exp (2 * |z| - 2 * Real.log x) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = Real.exp (2 * |z|) * (x ^ 2)⁻¹ := by rw [Real.exp_sub, hexp, div_eq_mul_inv]
  intro y
  have hminus := hcancel (Fin (r + 2)) c h (R / x) hwidth0 hwidth1 hh hm (y - Real.log x)
  have hplus := hcancel (Fin (r + 2)) c h (R / x) hwidth0 hwidth1 hh hm (-y - Real.log x)
  have hp : (∑ i, c i * pairedLogKernel y (n + (i : ℕ))) =
      (∑ i, c i * riemannAutocorr ((y - Real.log x) - h i)) +
      (∑ i, c i * riemannAutocorr ((-y - Real.log x) - h i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hc : ((n + (i : ℕ) : ℕ) : ℝ) = x + (i : ℕ) := by push_cast; rfl
    dsimp [pairedLogKernel, h]
    rw [hc, show y - Real.log x - (Real.log (x + (i : ℕ)) - Real.log x) =
      y - Real.log (x + (i : ℕ)) by ring]
    rw [show -y - Real.log x - (Real.log (x + (i : ℕ)) - Real.log x) =
      -(y + Real.log (x + (i : ℕ))) by ring, WeilExcess.riemannAutocorr_neg]
    ring
  have hcminus := hcenter y
  have hcplus := hcenter (-y)
  rw [abs_neg] at hcplus
  calc
    |∑ i, c i * pairedLogKernel y (n + (i : ℕ))| ≤
        |∑ i, c i * riemannAutocorr ((y - Real.log x) - h i)| +
        |∑ i, c i * riemannAutocorr ((-y - Real.log x) - h i)| := by rw [hp]; exact abs_add_le _ _
    _ ≤ E * Real.exp (-2 * |y - Real.log x|) * (∑ i, |c i|) * (R / x) ^ (r + 1) +
        E * Real.exp (-2 * |-y - Real.log x|) * (∑ i, |c i|) * (R / x) ^ (r + 1) :=
      add_le_add hminus hplus
    _ ≤ E * (Real.exp (2 * |y|) * (x ^ 2)⁻¹) * M * (R / x) ^ (r + 1) +
        E * (Real.exp (2 * |y|) * (x ^ 2)⁻¹) * M * (R / x) ^ (r + 1) := by
      gcongr
    _ = (2 * E * M) * Real.exp (2 * |y|) * (x ^ 2)⁻¹ * (R / x) ^ (r + 1) := by ring

/-- The envelope without exposing the moment equations. -/
theorem pairedLogKernel_cluster_envelope_of_moment_bound (r : ℕ) {E : ℝ} (hE : 0 < E)
    (hcancel : ∀ (ι : Type) [Fintype ι] (c h : ι → ℝ) (H : ℝ),
      0 ≤ H → H ≤ 1 → (∀ i, 0 ≤ h i ∧ h i ≤ H) →
      (∀ p ≤ r, ∑ i, c i * h i ^ p = 0) → ∀ y : ℝ,
      |∑ i, c i * riemannAutocorr (y - h i)| ≤
        E * Real.exp (-2 * |y|) * (∑ i, |c i|) * H ^ (r + 1)) :
    ∀ n : ℕ, r + 1 ≤ n →
      ∃ c : Fin (r + 2) → ℝ, ‖c‖ = 1 ∧ ∀ y : ℝ,
        |∑ i, c i * pairedLogKernel y (n + (i : ℕ))| ≤
          (2 * E * ((r + 2 : ℕ) : ℝ)) * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ *
            (((r + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (r + 1) := by
  intro n hn
  obtain ⟨c, hc, _, hb⟩ := pairedLogKernel_cluster_envelope_with_moments r hE hcancel n hn
  exact ⟨c, hc, hb⟩

theorem exists_pairedLogKernel_allOrder_cluster_envelope (r : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, r + 1 ≤ n →
      ∃ c : Fin (r + 2) → ℝ, ‖c‖ = 1 ∧ ∀ y : ℝ,
        |∑ i, c i * pairedLogKernel y (n + (i : ℕ))| ≤
          B * Real.exp (2 * |y|) * ((n : ℝ) ^ (r + 3))⁻¹ := by
  obtain ⟨E, hE, hcancel⟩ := exists_riemannAutocorr_moment_cancellation_envelope r
  refine ⟨2 * E * ((r + 2 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) ^ (r + 1), by positivity, ?_⟩
  intro n hn
  obtain ⟨c, hc, hbound⟩ := pairedLogKernel_cluster_envelope_of_moment_bound r hE hcancel n hn
  refine ⟨c, hc, fun y => (hbound y).trans_eq ?_⟩
  rw [div_pow, div_eq_mul_inv, show r + 3 = 2 + (r + 1) by omega,
    pow_add (n : ℝ) 2 (r + 1), mul_inv_rev]
  ring

end RHTower
