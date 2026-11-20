import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CountingLargeEighthPowerGcdDeficits
import GaloisForLFunctions.RHTower.PrimePolarDirichletBackbone

/-!
# Dirichlet continuation of the signed eighth-power shortfall

The half-step asymptotic separates a simple zeta pole from an absolutely
convergent Dirichlet remainder. Deleting the proper prime powers changes
the series by a function holomorphic in a much larger half-plane.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Coefficients of the Dirichlet series for the signed shortfall. -/
abbrev eighthShortfallCoeff (b : Bool) (m : ℕ) : ℂ := (eighthReading b m:ℝ)
private def remainder (b : Bool) (m : ℕ) : ℂ := ((eighthReading b m - 1/(2*(m:ℝ)) : ℝ):ℂ)

private theorem power_majorant {f : ℕ → ℂ} {t : ℝ}
    (h : ∀ y : ℝ, t < y → ∃ A u : ℝ, u < -1 ∧ ∀ᶠ n : ℕ in atTop,
        ‖f n‖/(n:ℝ)^y ≤ A*(n:ℝ)^u) :
    LSeries.abscissaOfAbsConv f ≤ (t:EReal) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  obtain ⟨A,u,hu,hA⟩ := h y hy
  apply ((Real.summable_nat_rpow.mpr hu).mul_left A).of_norm_bounded_eventually_nat
  filter_upwards [hA,eventually_ge_atTop 1] with n hn hp
  rwa [LSeries.norm_term_eq,if_neg (Nat.ne_of_gt hp),Complex.ofReal_re]

private theorem remainder_abscissa (b : Bool) :
    LSeries.abscissaOfAbsConv (remainder b) ≤ ((-(1/3000):ℝ):EReal) := by
  apply power_majorant
  intro y hy
  obtain ⟨δ,hyδ,hδ⟩ := exists_between (by linarith only [hy] : -y < (1/3000:ℝ))
  have point : ∃ A : ℝ, 0 ≤ A ∧ ∀ {m : ℕ}, 2 ≤ m →
      |eighthReading b m - 1/(2*(m:ℝ))| ≤ A*(m:ℝ)^(-1-δ) := by
    cases b
    · exact eighth_power_gcd_deficit_half_step hδ
    · exact eighth_ordinary_prime_deficit_half_step hδ
  obtain ⟨A,_,ha⟩ := point
  refine ⟨A,-1-δ-y,by linarith only [hyδ],?_⟩
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  rw [remainder,Complex.norm_real,Real.norm_eq_abs]
  apply (div_le_div_of_nonneg_right (ha hn) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq
  rw [Real.rpow_sub (Nat.cast_pos.mpr (by omega : 0<n)) (-1-δ) y]
  ring

/-- Removing the half-shifted zeta term leaves an analytic Dirichlet
series throughout the half-plane Re s > −1/3000. -/
theorem eighth_shortfall_dirichlet_continuation (b : Bool) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | -(1/3000:ℝ) < s.re} ∧
      (∀ s : ℂ, 0 < s.re → LSeries (eighthShortfallCoeff b) s = (1/2:ℂ)*riemannZeta (s+1)+H s) ∧
      Tendsto (fun s : ℂ => s*((1/2:ℂ)*riemannZeta (s+1)+H s)) (𝓝[≠] 0) (𝓝 (1/2:ℂ)) := by
  let H := LSeries (remainder b)
  have analytic : AnalyticOnNhd ℂ H {s : ℂ | -(1/3000:ℝ)<s.re} :=
    (LSeries_analyticOnNhd _).mono (fun s hs => (remainder_abscissa b).trans_lt (by exact_mod_cast hs))
  refine ⟨H,analytic,?_,?_⟩
  · intro s hs
    let w := fun n : ℕ => (n:ℂ)^(-(1:ℂ))
    have hh : 1 < (s-(-(1:ℂ))).re := by simpa using (lt_add_of_pos_left (1:ℝ) hs)
    have hw : LSeriesSummable w s := (_root_.RHTower.lseriesSummable_cpow _ _).mpr
      (LSeriesSummable_one_iff.mpr hh)
    have hr : LSeriesSummable (remainder b) s := LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((remainder_abscissa b).trans_lt (by exact_mod_cast (by linarith only [hs] : -(1/3000:ℝ)<s.re)))
    have heq : eighthShortfallCoeff b = (1/2:ℂ) • w + remainder b := by
      funext n
      simp only [eighthShortfallCoeff,Pi.add_apply,Pi.smul_apply,smul_eq_mul,w,Complex.cpow_neg_one,remainder]
      push_cast
      simp only [one_div,mul_inv_rev]
      ring
    rw [heq,LSeries_add (hw.smul _) hr,LSeries_smul,_root_.RHTower.lseries_cpow_eq_zeta _ _ hh,sub_neg_eq_add]
  · have shift : Tendsto (fun s : ℂ => s+1) (𝓝[≠] 0) (𝓝[≠] 1) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨((continuous_id.add continuous_const).tendsto' 0 1 (by norm_num)).mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact fun he => hs (by simpa using he)
    have rz := riemannZeta_residue_one.comp shift
    have hzero := (analytic (0:ℂ) (by norm_num : -(1/3000:ℝ)<(0:ℂ).re)).continuousAt.tendsto
    have van := (show Tendsto (fun s : ℂ => s) (𝓝 0) (𝓝 0) from tendsto_id).mul hzero
    have both := (rz.const_mul (1/2:ℂ)).add (van.mono_left nhdsWithin_le_nhds)
    simp only [mul_one,zero_mul,add_zero] at both
    exact both.congr fun s => by
      change (1/2:ℂ)*((s+1-1)*riemannZeta (s+1))+s*H s=_
      ring

/-- The contribution of the proper prime powers has absolute convergence
and holomorphic dependence on s throughout Re s > −3. -/
theorem eighth_proper_power_dirichlet_correction :
    AnalyticOnNhd ℂ (LSeries (fun n => eighthShortfallCoeff true n-eighthShortfallCoeff false n)) {s : ℂ | -3 < s.re} := by
  obtain ⟨A,hA⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have bound (n : ℕ) (np : 0<n) : ‖eighthShortfallCoeff true n-eighthShortfallCoeff false n‖ ≤ |A| * Real.sqrt 2/(n:ℝ)^4 := by
    have nr : 0<(n:ℝ) := Nat.cast_pos.mpr np
    have hp := octave_gcd_product_ordinary_primes (pow_pos np 8) (n^9)
    let Q := Real.log (octaveGcdProduct (n^8) (n^9))
    let P := eighthOrdinaryPrimePrice n
    change 0 ≤ Q-P ∧ Q-P ≤ _ at hp
    have hh := (hA ((2*n^8:ℕ):ℝ)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self A) (Real.sqrt_nonneg _))
    have h := hp.2.trans (mul_le_mul_of_nonneg_left hh (by positivity))
    push_cast at h
    have sq : Real.sqrt ((n:ℝ)^8)=(n:ℝ)^4 := by
      rw [show (n:ℝ)^8=((n:ℝ)^4)^2 by ring,Real.sqrt_sq (pow_nonneg nr.le _)]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),sq] at h
    have diff : eighthShortfallCoeff true n-eighthShortfallCoeff false n = (((Q-P)/(n:ℝ)^9:ℝ):ℂ) := by
      dsimp only [eighthShortfallCoeff,eighthReading,Bool.true_eq_false,if_false,if_true,Q,P]
      push_cast
      rw [if_pos trivial]
      ring
    rw [diff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hp.1 (by positivity))]
    exact (div_le_div_of_nonneg_right h (pow_nonneg nr.le _)).trans_eq (by field_simp)
  have ab : LSeries.abscissaOfAbsConv (fun n => eighthShortfallCoeff true n-eighthShortfallCoeff false n) ≤ ((-3:ℝ):EReal) := by
    apply power_majorant
    intro y hy
    refine ⟨|A| * Real.sqrt 2,-4-y,by linarith only [hy],?_⟩
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    apply (div_le_div_of_nonneg_right (bound n hn) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq
    rw [Real.rpow_sub (Nat.cast_pos.mpr hn),Real.rpow_neg (Nat.cast_nonneg _),
      show (4:ℝ)=(4:ℕ) by norm_num,Real.rpow_natCast]
    ring
  exact (LSeries_analyticOnNhd _).mono (fun s hs => ab.trans_lt (by exact_mod_cast hs))

#print axioms eighth_shortfall_dirichlet_continuation
#print axioms eighth_proper_power_dirichlet_correction

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
