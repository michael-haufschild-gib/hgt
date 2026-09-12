import GaloisForLFunctions.RHTower.DeningerDampedOriginalGreenMellin
import GaloisForLFunctions.RHTower.ReflectedBiHeatMultiplicityTomography
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Exact zero-damping singularity of the original Green transform

The actual damped-source Euler formula forces a scalar meromorphic expression.
At each native Xi divisor point its damping pole has twice the original
multiplicity, with a nonzero coefficient determined by the original Gaussian,
prime denominator and both first surviving zeta jets. Exactly that power
normalization retains a finite nonzero limit and admits a scalar analytic germ.

This proves neither a zero-damping source vector nor fixed physical-reader
agreement. Passing all coordinate germs to the original completion remains a
separate analytic obligation. No simplicity, critical-line or norm-bound premise
is used to derive the native scalar singularity.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower

private theorem translated_analytic_unit {f : ℂ → ℂ} {r : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f r) (hm : analyticOrderAt f r = m) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      u 0 = meromorphicTrailingCoeffAt f r ∧
      ∀ᶠ a in 𝓝 (0 : ℂ), f (a + r) = a ^ m * u a := by
  obtain ⟨g, hg, hg0, hfac⟩ := hf.analyticOrderAt_eq_natCast.mp hm
  have htrail : meromorphicTrailingCoeffAt f r = g r := by
    apply hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := (m : ℤ)) hg0
    filter_upwards [hfac.filter_mono nhdsWithin_le_nhds] with z hz
    simpa only [zpow_natCast] using hz
  have hshift : AnalyticAt ℂ (fun a : ℂ => a + r) 0 :=
    analyticAt_id.add analyticAt_const
  have hcomp : AnalyticAt ℂ (fun a : ℂ => g (a + r)) 0 :=
    hg.comp_of_eq hshift (zero_add r)
  refine ⟨fun a => g (a + r), hcomp, ?_, ?_, ?_⟩
  · simpa only [zero_add] using hg0
  · simpa only [zero_add] using htrail.symm
  · have ht : Tendsto (fun a : ℂ => a + r) (𝓝 0) (𝓝 r) := by
      simpa only [zero_add] using hshift.continuousAt.tendsto
    filter_upwards [ht.eventually hfac] with a ha
    simpa only [add_sub_cancel_right, smul_eq_mul] using ha

private theorem zeta_native_order (rho : XiDivisorSupport) :
    analyticOrderAt riemannZeta (rho : ℂ) = xiSupportMultiplicity rho := by
  rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
    (xi_divisor_support_re_mem_open_unit rho), xiSupportMultiplicity_eq_analyticOrderAt_toNat]
  exact (ENat.coe_toNat (xi_orderAt_ne_top (rho : ℂ))).symm

private theorem zeta_native_analytic (rho : XiDivisorSupport) :
    AnalyticAt ℂ riemannZeta (rho : ℂ) := by
  apply GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta
  intro h
  have hlt := (xi_divisor_support_re_mem_open_unit rho).2
  rw [h] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt

private theorem native_trailingCoefficient_eq_jet {f : ℂ → ℂ} {r : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f r) (hm : analyticOrderAt f r = m) :
    meromorphicTrailingCoeffAt f r = iteratedDeriv m f r / (m.factorial : ℂ) := by
  obtain ⟨u, hu, _, huc, hfac⟩ := translated_analytic_unit hf hm
  have hfac' : (fun a : ℂ => f (a + r)) =ᶠ[𝓝 0] (fun a => a ^ m * u a) := hfac
  have hder := hfac'.iteratedDeriv_eq m
  rw [iteratedDeriv_comp_add_const] at hder
  change iteratedDeriv m f (0 + r) = _ at hder
  rw [zero_add] at hder
  have hpow : AnalyticAt ℂ (fun a : ℂ => a ^ m) 0 := analyticAt_id.pow m
  have hmul := complex_iteratedDeriv_mul_of_left_vanishing_below m hpow.contDiffAt
    hu.contDiffAt (fun j hj => by
      rw [iteratedDeriv_fun_pow_zero, if_neg (Nat.ne_of_lt hj), Nat.cast_zero])
  rw [hmul, iteratedDeriv_fun_pow_zero, if_pos rfl] at hder
  rw [← huc]
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero m)).2
  rw [hder, mul_comm]

/-- Complex damping expression forced by the proved Euler formula of the actual source.
It does not define a source at zero damping. -/
def deningerOriginalPrimeGreenDampingContinuation (p : Nat.Primes)
    (rho : XiDivisorSupport) (a : ℂ) : ℂ :=
  (deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (rho : ℂ) /
    (1 - (p : ℂ) ^ (-(rho : ℂ)))) /
    (riemannZeta (a + (rho : ℂ)) * riemannZeta (a + (1 - (rho : ℂ))))

/-- Canonical leading coefficient, retaining the original prime and both native zeta units. -/
def deningerOriginalPrimeGreenZeroDampingCoefficient (p : Nat.Primes)
    (rho : XiDivisorSupport) : ℂ :=
  (deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (rho : ℂ) /
    (1 - (p : ℂ) ^ (-(rho : ℂ)))) /
    (meromorphicTrailingCoeffAt riemannZeta (rho : ℂ) *
      meromorphicTrailingCoeffAt riemannZeta (1 - (rho : ℂ)))

private theorem original_green_gaussian_nonzero (p : Nat.Primes)
    (rho : XiDivisorSupport) :
    deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (rho : ℂ) /
      (1 - (p : ℂ) ^ (-(rho : ℂ))) ≠ 0 :=
  div_ne_zero (deningerMeyerReflectedLogGaussianSource_mellin_ne_zero (rho : ℂ))
    (deningerOriginalGreen_prime_denominator_ne_zero p
      (xi_divisor_support_re_mem_open_unit rho).1)

/-- The expression continues meromorphically throughout the complex damping plane. -/
theorem deningerOriginalPrimeGreenDampingContinuation_meromorphicOn
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    MeromorphicOn (deningerOriginalPrimeGreenDampingContinuation p rho) Set.univ := by
  intro a _
  have hshift (s : ℂ) : MeromorphicAt (fun z : ℂ => riemannZeta (z + s)) a :=
    MeromorphicAt.comp_analyticAt
      (GaloisForLFunctions.HTGeometry.meromorphicOn_riemannZeta (a + s) (Set.mem_univ _))
      (analyticAt_id.add analyticAt_const)
  exact analyticAt_const.meromorphicAt.div ((hshift (rho : ℂ)).mul (hshift (1 - (rho : ℂ))))

/-- The scalar continuation is meromorphic at zero without a source-domain premise. -/
theorem deningerOriginalPrimeGreenDampingContinuation_meromorphicAt
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    MeromorphicAt (deningerOriginalPrimeGreenDampingContinuation p rho) 0 :=
  deningerOriginalPrimeGreenDampingContinuation_meromorphicOn p rho 0 (Set.mem_univ _)

/-- Exact local unit for the zero-damping pole; every native multiplicity is retained. -/
theorem exists_deningerOriginalPrimeGreen_zeroDamping_unit
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      u 0 = deningerOriginalPrimeGreenZeroDampingCoefficient p rho ∧
      ∀ᶠ a in 𝓝[≠] (0 : ℂ),
        deningerOriginalPrimeGreenDampingContinuation p rho a =
          a ^ (-(2 * xiSupportMultiplicity rho : ℤ)) * u a := by
  obtain ⟨v, hv, hv0, hvc, hvf⟩ :=
    translated_analytic_unit (zeta_native_analytic rho) (zeta_native_order rho)
  have href : ∃ w : ℂ → ℂ, AnalyticAt ℂ w 0 ∧ w 0 ≠ 0 ∧
      w 0 = meromorphicTrailingCoeffAt riemannZeta (1 - (rho : ℂ)) ∧
      ∀ᶠ a in 𝓝 (0 : ℂ), riemannZeta (a + (1 - (rho : ℂ))) =
        a ^ xiSupportMultiplicity rho * w a := by
    simpa only [xiZeroReflectEquiv_apply, xiSupportMultiplicity_reflect] using
      translated_analytic_unit (zeta_native_analytic (xiZeroReflectEquiv rho))
        (zeta_native_order (xiZeroReflectEquiv rho))
  obtain ⟨w, hw, hw0, hwc, hwf⟩ := href
  let c : ℂ := deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (rho : ℂ) /
    (1 - (p : ℂ) ^ (-(rho : ℂ)))
  let u : ℂ → ℂ := fun a => c / (v a * w a)
  have hu : AnalyticAt ℂ u 0 := analyticAt_const.div (hv.mul hw) (mul_ne_zero hv0 hw0)
  refine ⟨u, hu, div_ne_zero (original_green_gaussian_nonzero p rho)
    (mul_ne_zero hv0 hw0), ?_, ?_⟩
  · change c / (v 0 * w 0) = _
    rw [hvc, hwc]
    rfl
  · filter_upwards [hvf.filter_mono nhdsWithin_le_nhds,
      hwf.filter_mono nhdsWithin_le_nhds] with a ha hb
    change c / (riemannZeta (a + (rho : ℂ)) * riemannZeta (a + (1 - (rho : ℂ)))) =
      a ^ (-(2 * xiSupportMultiplicity rho : ℤ)) * (c / (v a * w a))
    rw [ha, hb]
    have hp : a ^ xiSupportMultiplicity rho * v a *
        (a ^ xiSupportMultiplicity rho * w a) =
        a ^ (2 * xiSupportMultiplicity rho) * (v a * w a) := by
      rw [two_mul, pow_add]
      ring
    rw [hp, zpow_neg, show (2 * (xiSupportMultiplicity rho : ℤ)) =
      ((2 * xiSupportMultiplicity rho : ℕ) : ℤ) by simp only [Nat.cast_mul, Nat.cast_ofNat],
      zpow_natCast]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The zero-damping pole has twice the actual Xi multiplicity, without simplicity or RH. -/
theorem deningerOriginalPrimeGreenDampingContinuation_order
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    meromorphicOrderAt (deningerOriginalPrimeGreenDampingContinuation p rho) 0 =
      ((-(2 * xiSupportMultiplicity rho : ℤ)) : WithTop ℤ) := by
  obtain ⟨u, hu, hu0, _, hfac⟩ := exists_deningerOriginalPrimeGreen_zeroDamping_unit p rho
  apply (meromorphicOrderAt_eq_int_iff
    (deningerOriginalPrimeGreenDampingContinuation_meromorphicAt p rho)).2
  refine ⟨u, hu, hu0, ?_⟩
  simpa only [sub_zero, smul_eq_mul] using hfac

/-- Exact source-forced leading Laurent coefficient. -/
theorem deningerOriginalPrimeGreenDampingContinuation_trailingCoeff
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    meromorphicTrailingCoeffAt (deningerOriginalPrimeGreenDampingContinuation p rho) 0 =
      deningerOriginalPrimeGreenZeroDampingCoefficient p rho := by
  obtain ⟨u, hu, hu0, huc, hfac⟩ := exists_deningerOriginalPrimeGreen_zeroDamping_unit p rho
  rw [← huc]
  apply hu.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
    (n := -(2 * xiSupportMultiplicity rho : ℤ)) hu0
  change ∀ᶠ a in 𝓝[≠] (0 : ℂ),
    deningerOriginalPrimeGreenDampingContinuation p rho a =
      (a - 0) ^ (-(2 * xiSupportMultiplicity rho : ℤ)) • u a
  simpa only [sub_zero, smul_eq_mul] using hfac

/-- Normalization leaves a nonzero coefficient, not a vanishing boundary. -/
theorem deningerOriginalPrimeGreenZeroDampingCoefficient_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerOriginalPrimeGreenZeroDampingCoefficient p rho ≠ 0 := by
  obtain ⟨u, _, hu0, huc, _⟩ := exists_deningerOriginalPrimeGreen_zeroDamping_unit p rho
  rwa [← huc]

/-- The coefficient uses the actual first nonzero Taylor jets, including native factorials. -/
theorem deningerOriginalPrimeGreenZeroDampingCoefficient_eq_native_jets
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerOriginalPrimeGreenZeroDampingCoefficient p rho =
      (deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (rho : ℂ) /
        (1 - (p : ℂ) ^ (-(rho : ℂ)))) /
      ((iteratedDeriv (xiSupportMultiplicity rho) riemannZeta (rho : ℂ) /
          ((xiSupportMultiplicity rho).factorial : ℂ)) *
        (iteratedDeriv (xiSupportMultiplicity rho) riemannZeta (1 - (rho : ℂ)) /
          ((xiSupportMultiplicity rho).factorial : ℂ))) := by
  have href : analyticOrderAt riemannZeta (1 - (rho : ℂ)) = xiSupportMultiplicity rho := by
    simpa only [xiZeroReflectEquiv_apply, xiSupportMultiplicity_reflect] using
      zeta_native_order (xiZeroReflectEquiv rho)
  rw [deningerOriginalPrimeGreenZeroDampingCoefficient,
    native_trailingCoefficient_eq_jet (zeta_native_analytic rho) (zeta_native_order rho),
    native_trailingCoefficient_eq_jet (analyticAt_riemannZeta_one_sub_xiDivisorSupport rho) href]

/-- The forced multiplicity normalization has an exact nonzero limit. -/
theorem deningerOriginalPrimeGreenDampingContinuation_normalized_limit
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    Tendsto (fun a : ℂ => a ^ (2 * xiSupportMultiplicity rho) *
      deningerOriginalPrimeGreenDampingContinuation p rho a) (𝓝[≠] 0)
      (𝓝 (deningerOriginalPrimeGreenZeroDampingCoefficient p rho)) := by
  have hlim := (deningerOriginalPrimeGreenDampingContinuation_meromorphicAt p rho).tendsto_nhds_meromorphicTrailingCoeffAt
  have ho : (meromorphicOrderAt (deningerOriginalPrimeGreenDampingContinuation p rho) 0).untop₀ =
      -((2 * xiSupportMultiplicity rho : ℕ) : ℤ) := by
    rw [deningerOriginalPrimeGreenDampingContinuation_order]
    change -(2 * (xiSupportMultiplicity rho : ℤ)) = -((2 * xiSupportMultiplicity rho : ℕ) : ℤ)
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  change Tendsto (fun a : ℂ => (a - 0) ^
    (-(meromorphicOrderAt (deningerOriginalPrimeGreenDampingContinuation p rho) 0).untop₀) *
    deningerOriginalPrimeGreenDampingContinuation p rho a) (𝓝[≠] 0)
    (𝓝 (meromorphicTrailingCoeffAt (deningerOriginalPrimeGreenDampingContinuation p rho) 0)) at hlim
  simpa only [ho, neg_neg, zpow_natCast, sub_zero,
    deningerOriginalPrimeGreenDampingContinuation_trailingCoeff] using hlim

/-- Ordinary finite convergence is impossible for this original scalar continuation. -/
theorem deningerOriginalPrimeGreenDampingContinuation_no_finite_limit
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ¬ ∃ c : ℂ, Tendsto (deningerOriginalPrimeGreenDampingContinuation p rho)
      (𝓝[≠] 0) (𝓝 c) := by
  rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg
    (deningerOriginalPrimeGreenDampingContinuation_meromorphicAt p rho),
    deningerOriginalPrimeGreenDampingContinuation_order]
  have hm : (0 : ℤ) < xiSupportMultiplicity rho := by
    exact_mod_cast xiSupportMultiplicity_pos rho
  have hn : -(2 * (xiSupportMultiplicity rho : ℤ)) < 0 := by omega
  exact not_le.mpr (by exact_mod_cast hn)

private theorem normalized_damping_order (p : Nat.Primes) (rho : XiDivisorSupport) (k : ℕ) :
    meromorphicOrderAt (fun a : ℂ => a ^ k *
      deningerOriginalPrimeGreenDampingContinuation p rho a) 0 =
      (((k : ℤ) - 2 * xiSupportMultiplicity rho : ℤ) : WithTop ℤ) := by
  have hp : MeromorphicAt (fun a : ℂ => a ^ k) 0 := (analyticAt_id.pow k).meromorphicAt
  have ho : meromorphicOrderAt (fun a : ℂ => a ^ k) 0 = ((k : ℤ) : WithTop ℤ) := by
    have ht := meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (x := 0) (n := k)
    change meromorphicOrderAt (fun a : ℂ => (a - 0) ^ k) 0 = (k : WithTop ℤ) at ht
    simpa only [sub_zero, ← WithTop.coe_natCast] using ht
  rw [fun_meromorphicOrderAt_mul hp
    (deningerOriginalPrimeGreenDampingContinuation_meromorphicAt p rho), ho,
    deningerOriginalPrimeGreenDampingContinuation_order]
  exact (WithTop.coe_add (k : ℤ) (-(2 * xiSupportMultiplicity rho : ℤ))).symm

private theorem normalized_damping_meromorphicAt
    (p : Nat.Primes) (rho : XiDivisorSupport) (k : ℕ) :
    MeromorphicAt (fun a : ℂ => a ^ k *
      deningerOriginalPrimeGreenDampingContinuation p rho a) 0 :=
  (analyticAt_id.pow k).meromorphicAt.mul
    (deningerOriginalPrimeGreenDampingContinuation_meromorphicAt p rho)

/-- The source fixes the least possible power that admits a finite limit. -/
theorem deningerOriginalPrimeGreenDampingContinuation_finite_limit_iff
    (p : Nat.Primes) (rho : XiDivisorSupport) (k : ℕ) :
    (∃ c : ℂ, Tendsto (fun a : ℂ => a ^ k *
      deningerOriginalPrimeGreenDampingContinuation p rho a) (𝓝[≠] 0) (𝓝 c)) ↔
      2 * xiSupportMultiplicity rho ≤ k := by
  rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg
    (normalized_damping_meromorphicAt p rho k), normalized_damping_order]
  constructor
  · intro h
    have hi : (0 : ℤ) ≤ (k : ℤ) - 2 * xiSupportMultiplicity rho := by exact_mod_cast h
    omega
  · intro h
    have hi : (0 : ℤ) ≤ (k : ℤ) - 2 * xiSupportMultiplicity rho := by omega
    exact_mod_cast hi

/-- Exactly one power normalization retains a finite nonzero original coefficient. -/
theorem deningerOriginalPrimeGreenDampingContinuation_nonzero_limit_iff
    (p : Nat.Primes) (rho : XiDivisorSupport) (k : ℕ) :
    (∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun a : ℂ => a ^ k *
      deningerOriginalPrimeGreenDampingContinuation p rho a) (𝓝[≠] 0) (𝓝 c)) ↔
      k = 2 * xiSupportMultiplicity rho := by
  rw [tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
    (normalized_damping_meromorphicAt p rho k), normalized_damping_order,
    WithTop.coe_eq_zero]
  omega

/-- Agreement with the actual admitted integral; this is not a definition of a zero-damping source. -/
theorem deningerOriginalPrimeGreenDampingContinuation_eq_literal
    (a : {a : ℝ // 1 < a}) (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerOriginalPrimeGreenDampingContinuation p rho (a.val : ℂ) =
      deningerMeyerStrongLogMellin
        (deningerDampedOriginalPrimeGreen ⟨a.val, by linarith [a.property]⟩ p) (rho : ℂ) := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  rw [deningerDampedOriginalPrimeGreen_mellin _ p _ hstrip.1
      (by dsimp; linarith [a.property]) (by dsimp; linarith [a.property]),
    deningerDampedLogSource_mellin_eq _ _
      (by dsimp; linarith [a.property]) (by dsimp; linarith [a.property])]
  simp only [deningerOriginalPrimeGreenDampingContinuation, add_sub_assoc,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- The removable scalar germ fills the forced coefficient; it is not a continued source vector. -/
def deningerOriginalPrimeGreenZeroDampingRegularization (p : Nat.Primes)
    (rho : XiDivisorSupport) (a : ℂ) : ℂ :=
  if a = 0 then deningerOriginalPrimeGreenZeroDampingCoefficient p rho
  else a ^ (2 * xiSupportMultiplicity rho) *
    deningerOriginalPrimeGreenDampingContinuation p rho a

/-- The uniquely normalized scalar germ extends analytically across zero damping. -/
theorem deningerOriginalPrimeGreenZeroDampingRegularization_analyticAt
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    AnalyticAt ℂ (deningerOriginalPrimeGreenZeroDampingRegularization p rho) 0 := by
  obtain ⟨u, hu, _, huc, hfac⟩ := exists_deningerOriginalPrimeGreen_zeroDamping_unit p rho
  apply hu.congr
  filter_upwards [eventually_nhdsWithin_iff.mp hfac] with a ha
  by_cases ha0 : a = 0
  · subst a
    rw [deningerOriginalPrimeGreenZeroDampingRegularization, if_pos rfl]
    exact huc
  · rw [deningerOriginalPrimeGreenZeroDampingRegularization, if_neg ha0, ha ha0]
    have hcast : (2 * (xiSupportMultiplicity rho : ℤ)) =
        ((2 * xiSupportMultiplicity rho : ℕ) : ℤ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [hcast, zpow_neg, zpow_natCast, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ ha0), one_mul]

/-- Its value is the same nonzero coefficient fixed by the literal source formula. -/
theorem deningerOriginalPrimeGreenZeroDampingRegularization_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerOriginalPrimeGreenZeroDampingRegularization p rho 0 =
      deningerOriginalPrimeGreenZeroDampingCoefficient p rho := by
  rw [deningerOriginalPrimeGreenZeroDampingRegularization, if_pos rfl]

end RHTower
