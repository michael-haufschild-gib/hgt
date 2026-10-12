import GaloisForLFunctions.RHTower.PaperHeatSliceSource

/-!
# Fixed-time slice positivity and the native Newman threshold

This is an exact equivalence for the actual heat source at every nonnegative time.
The native constant is the infimum over nonnegative real-rooted heat times.
-/

namespace RHTower.PaperHeatSlice
noncomputable section
open Complex Set
open RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open scoped ComplexOrder NNReal

theorem nonnegTaylor_iff_coeff (lam : ℝ≥0) (t : ℝ) :
    NonnegTaylorAtZero (source lam t) ↔ ∀ n, 0 ≤ (coeff lam t n).re := by
  constructor
  · intro h n
    simp only [coeff, Complex.div_natCast_re]
    exact div_nonneg (Complex.nonneg_iff.mp (h.2 n)).1 (Nat.cast_nonneg _)
  · intro h
    refine ⟨differentiable_source lam t, fun n => Complex.nonneg_iff.mpr ⟨?_, ?_⟩⟩
    · have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      have hc := h n
      simp only [coeff, Complex.div_natCast_re] at hc
      simpa only [zero_mul] using (le_div_iff₀ hn).mp hc
    · exact (iteratedDeriv_im lam t n).symm

/-- Full slice positivity at this fixed heat time is exactly real-rootedness. -/
theorem forall_nonnegTaylor_iff_realRooted (lam : ℝ≥0) :
    (∀ t, NonnegTaylorAtZero (source lam t)) ↔
      ∀ z, riemannHeat lam z = 0 → z.im = 0 := by
  constructor
  · intro h z hz
    by_contra him
    obtain ⟨w, hw, hwim⟩ : ∃ w : ℂ, riemannHeat lam w = 0 ∧ 0 < w.im := by
      rcases lt_or_gt_of_ne him with hneg | hpos
      · refine ⟨starRingEnd ℂ z, ?_, by simpa using hneg⟩
        exact (riemannHeat_conj lam.property z).trans ((congrArg (starRingEnd ℂ) hz).trans (map_zero _))
      · exact ⟨z, hz, hpos⟩
    have hmono := monotoneOn_norm_riemannHeat_of_nonnegTaylorAtZero lam.property (h w.re)
    have hseg : ∀ y : ℝ, 0 ≤ y → y ≤ w.im →
        riemannHeat lam ((w.re : ℂ) + I * y) = 0 := by
      intro y hy0 hyw
      have hm := hmono hy0 hwim.le hyw
      have hw' : (w.re : ℂ) + I * (w.im : ℂ) = w := by
        apply Complex.ext <;> simp
      exact norm_le_zero_iff.mp (hm.trans_eq
        ((congrArg (fun u => ‖riemannHeat lam u‖) hw').trans
          ((congrArg norm hw).trans norm_zero)))
    let G : ℂ → ℂ := fun v => riemannHeat lam ((w.re : ℂ) + I * v)
    have hG : Differentiable ℂ G := (differentiable_riemannHeat lam.property).comp (by fun_prop)
    have hzero := entire_eq_zero_of_vanishing_on_real_interval hG
      (t₀ := w.im / 2) (r := w.im / 2) (by linarith) (fun y hy => by
        rw [abs_lt] at hy
        exact hseg y (by linarith) (by linarith))
    apply riemannHeat_zero_ne lam.property
    have h0 := hzero (-(w.re : ℂ) / I)
    change riemannHeat lam ((w.re : ℂ) + I * (-(w.re : ℂ) / I)) = 0 at h0
    rwa [show (w.re : ℂ) + I * (-(w.re : ℂ) / I) = 0 by field_simp; ring] at h0
  · intro h t
    exact nonnegTaylorAtZero_riemannHeat_slice_of_cone lam.property fun z hz => by
      rw [h z hz]
      simpa only [zero_pow two_ne_zero] using sq_nonneg (z.re - t)

theorem forall_nonnegTaylor_iff_threshold (lam : ℝ≥0) :
    (∀ t, NonnegTaylorAtZero (source lam t)) ↔ newmanConstant ≤ lam := by
  rw [forall_nonnegTaylor_iff_realRooted]
  exact ⟨fun h => (mem_realRootedTimes_iff lam.property).mp ⟨lam.property, h⟩,
    fun h => ((mem_realRootedTimes_iff lam.property).mpr h).2⟩

theorem forall_coeff_nonneg_iff_threshold (lam : ℝ≥0) :
    (∀ t n, 0 ≤ (coeff lam t n).re) ↔ newmanConstant ≤ lam := by
  rw [← forall_nonnegTaylor_iff_threshold]
  exact forall_congr' fun t => (nonnegTaylor_iff_coeff lam t).symm

theorem forall_coeff_nonneg_zero_iff_rh :
    (∀ t n, 0 ≤ (coeff 0 t n).re) ↔ RiemannHypothesis := by
  rw [forall_coeff_nonneg_iff_threshold, riemannHypothesis_iff_newmanConstant_eq_zero]
  exact ⟨fun h => le_antisymm h newmanConstant_nonneg, fun h => h.le⟩

end
end RHTower.PaperHeatSlice
