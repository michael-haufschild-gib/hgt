import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusMellinBridge
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Exact endpoint and actual Mellin domain of the PW-B Gamma/Möbius source

For `Re(z)>3/2`, the complete source divided by `sqrt(x)` tends to
`1/zeta(z-1/2)`, a nonzero coefficient. Its actual Mellin integral therefore
exists exactly when `Re(s)>-1/2`. This is a signed-source endpoint theorem,
not merely failure of an atomwise majorant. Compensating a growing coefficient
parameter to keep `z+s` fixed eventually leaves the actual integral domain.
No critical continuation, spectral occurrence or Ward balance is asserted.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

/-- The complete original source normalized by its half-density. -/
def pwGammaMobiusNormalizedSource (z : ℂ) (x : ℝ) : ℂ :=
  pwGammaMobiusTilt z x / (Real.sqrt x : ℂ)

/-- The exact damped Dirichlet coefficient of each original atom. -/
theorem pwGammaMobiusGlobalAtom_normalized (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    pwGammaMobiusGlobalAtom z n x / (Real.sqrt x : ℂ) =
      LSeries.term (fun m => ((moebius m : ℤ):ℂ)) (z-1/2) n *
        (Real.exp (-((n:ℝ)*x)) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusGlobalAtom]
  · have hnr : (0:ℝ) < n := by exact_mod_cast hn
    have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have he : Complex.exp (-z*(Real.log (n:ℝ):ℂ)) = (n:ℂ)^(-z) := by
      rw [Complex.cpow_def_of_ne_zero hnc, ← Complex.ofReal_natCast,
        ← Complex.ofReal_log hnr.le]
      congr 1
      ring
    have hp : (Real.sqrt (n:ℝ):ℂ) = (n:ℂ)^((1:ℂ)/2) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hnr.le]
      push_cast
      rfl
    rw [LSeries.term_def₀ (by simp), show -(z-1/2) = -z+1/2 by ring,
      Complex.cpow_add _ _ hnc, ← he, ← hp,
      pwGammaMobiusGlobalAtom, pwGammaRaySource_eq (mul_pos hnr hx), Real.sqrt_mul hnr.le]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne']

/-- The normalized series retains all original arithmetic coefficients. -/
theorem pwGammaMobiusNormalizedSource_eq_tsum (z : ℂ) {x : ℝ} (hx : 0 < x) :
    pwGammaMobiusNormalizedSource z x =
      ∑' n, LSeries.term (fun m => ((moebius m : ℤ):ℂ)) (z-1/2) n *
        (Real.exp (-((n:ℝ)*x)) : ℂ) := by
  rw [pwGammaMobiusNormalizedSource, pwGammaMobiusTilt_eq_global_atoms, ← tsum_div_const]
  exact tsum_congr (fun n => pwGammaMobiusGlobalAtom_normalized z n hx)

/-- Dominated convergence gives the literal right endpoint of the complete source. -/
theorem pwGammaMobiusNormalizedSource_tendsto {z : ℂ} (hz : (3/2:ℝ) < z.re) :
    Tendsto (pwGammaMobiusNormalizedSource z) (𝓝[>] (0:ℝ))
      (𝓝 ((riemannZeta (z-1/2))⁻¹)) := by
  have hzeta : 1 < (z-(1:ℂ)/2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hs := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hzeta).norm
  have ht := tendsto_tsum_of_dominated_convergence hs
    (f := fun x : ℝ => fun n : ℕ =>
      LSeries.term (fun m => ((moebius m:ℤ):ℂ)) (z-1/2) n *
        (Real.exp (-((n:ℝ)*x)) : ℂ))
    (g := fun n => LSeries.term (fun m => ((moebius m:ℤ):ℂ)) (z-1/2) n)
    (𝓕 := 𝓝[>] (0:ℝ)) ?_ ?_
  · rw [← riemannZeta_inv_eq_tsum_term hzeta] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (pwGammaMobiusNormalizedSource_eq_tsum z hx).symm
  · intro n
    have hc : Continuous (fun x : ℝ =>
        LSeries.term (fun m => ((moebius m:ℤ):ℂ)) (z-1/2) n *
          (Real.exp (-((n:ℝ)*x)) : ℂ)) := by fun_prop
    simpa using (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg n) hx.le))

/-- The endpoint coefficient is nonzero in its proved absolute region. -/
theorem pwGammaMobiusNormalizedSource_endpoint_ne_zero {z : ℂ} (hz : (3/2:ℝ) < z.re) :
    (riemannZeta (z-1/2))⁻¹ ≠ 0 := by
  apply inv_ne_zero
  apply riemannZeta_ne_zero_of_one_lt_re
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  linarith

/-- A positive endpoint norm lower bound holds on an actual right neighborhood. -/
theorem pwGammaMobiusNormalizedSource_eventual_lower {z : ℂ} (hz : (3/2:ℝ) < z.re) :
    ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ),
      ‖(riemannZeta (z-1/2))⁻¹‖/2 < ‖pwGammaMobiusNormalizedSource z x‖ := by
  have hp := norm_pos_iff.mpr (pwGammaMobiusNormalizedSource_endpoint_ne_zero hz)
  exact (pwGammaMobiusNormalizedSource_tendsto hz).norm.eventually_const_lt (by linarith)

/-- Exact norm of the actual weighted source, with its endpoint power retained. -/
theorem pwGammaMobiusMellin_norm_normalized (z s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x:ℂ)^(s-1)*pwGammaMobiusTilt z x‖ =
      x^(s.re-1/2)*‖pwGammaMobiusNormalizedSource z x‖ := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re,
    pwGammaMobiusNormalizedSource, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  rw [show s.re-(1:ℝ)/2 = (s.re-1)+1/2 by ring, Real.rpow_add hx, ← Real.sqrt_eq_rpow]
  field_simp [(Real.sqrt_pos.mpr hx).ne']

/-- The nonzero signed endpoint forces local Mellin divergence at and below the boundary. -/
theorem pwGammaMobiusTilt_not_mellinConvergent {z s : ℂ}
    (hz : (3/2:ℝ) < z.re) (hs : s.re ≤ -(1/2:ℝ)) :
    ¬ MellinConvergent (pwGammaMobiusTilt z) s := by
  intro hi
  change IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*pwGammaMobiusTilt z x) (Ioi 0) at hi
  have hp : 0 < ‖(riemannZeta (z-1/2))⁻¹‖/2 :=
    half_pos (norm_pos_iff.mpr (pwGammaMobiusNormalizedSource_endpoint_ne_zero hz))
  obtain ⟨d, hd, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (pwGammaMobiusNormalizedSource_eventual_lower hz)
  have hnorm : IntegrableOn (fun x : ℝ =>
      ‖(x:ℂ)^(s-1)*pwGammaMobiusTilt z x‖) (Ioo 0 d) := by
    exact (hi.mono_set Ioo_subset_Ioi_self).norm
  have hpow : IntegrableOn (fun x : ℝ => x^(s.re-1/2)) (Ioo 0 d) := by
    apply (hnorm.const_mul (‖(riemannZeta (z-1/2))⁻¹‖/2)⁻¹).mono' ?_ ?_
    · have hc : ContinuousOn (fun x : ℝ => x^(s.re-1/2)) (Ioo (0:ℝ) d) :=
        continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')
      exact hc.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.1.le _), pwGammaMobiusMellin_norm_normalized z s hx.1]
      have hle : ‖(riemannZeta (z-1/2))⁻¹‖/2 ≤ ‖pwGammaMobiusNormalizedSource z x‖ := (hbound hx).le
      calc
        _ = (‖(riemannZeta (z-1/2))⁻¹‖/2)⁻¹ *
            (x^(s.re-1/2)*(‖(riemannZeta (z-1/2))⁻¹‖/2)) := by rw [mul_left_comm, inv_mul_cancel₀ hp.ne', mul_one]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hx.1.le _)) (inv_nonneg.mpr hp.le)
  have hlt := (intervalIntegral.integrableOn_Ioo_rpow_iff hd).mp hpow
  linarith

/-- Sharp Mellin admission for the complete signed source when `Re(z)>3/2`. -/
theorem pwGammaMobiusTilt_mellinConvergent_iff {z : ℂ} (hz : (3/2:ℝ) < z.re) (s : ℂ) :
    MellinConvergent (pwGammaMobiusTilt z) s ↔ -(1/2:ℝ) < s.re := by
  constructor
  · intro hi
    by_contra hs
    exact pwGammaMobiusTilt_not_mellinConvergent hz (not_lt.mp hs) hi
  · intro hs
    apply pwGammaMobiusTilt_mellinConvergent hs
    simp only [Complex.add_re]
    linarith

/-- The compensating Mellin weight is unadmitted when the fixed argument lies too far left. -/
theorem pwGammaMobiusTilt_fixed_argument_not_mellinConvergent {z u : ℂ}
    (hz : (3/2:ℝ) < z.re) (hu : u.re ≤ z.re-1/2) :
    ¬ MellinConvergent (pwGammaMobiusTilt z) (u-z) := by
  apply pwGammaMobiusTilt_not_mellinConvergent hz
  simp only [Complex.sub_re]
  linarith


end
end RHTower
