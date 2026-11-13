import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineEnergyGap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheGammaDomainIsClosedUnderBoundedEnergyLimits

/-!
# Compactness at finite half-line energies

The full Gamma domain survives bounded-energy strong limits. Frequency
truncation and Fatou then pass a finite upper energy bound to the limit.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis WindowTowerOfSpecZ

/-- Lower semicontinuity follows from L¹ convergence and convergence of the lower-order terms. -/
theorem criticalHalfLineFullEnergy_le_of_strong_limit {R : ℝ} (hR : 0 < R)
    {U : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hU : ∀ n, CriticalHalfLineEnergyDomain (U n)) (hF : CriticalHalfLineEnergyDomain F)
    (hL1 : Tendsto (fun n => ∫ u, ‖U n u - F u‖) atTop (𝓝 0))
    (hP : Tendsto (fun n => primeSum (U n)) atTop (𝓝 (primeSum F)))
    (hC : Tendsto (fun n => coshHalfMoment (U n)) atTop (𝓝 (coshHalfMoment F)))
    (hS : Tendsto (fun n => sinhHalfMoment (U n)) atTop (𝓝 (sinhHalfMoment F)))
    {L : ℝ} (hE : Tendsto (fun n => criticalHalfLineFullEnergy R (U n)) atTop (𝓝 L)) :
    criticalHalfLineFullEnergy R F ≤ L := by
  have ha := criticalAliasCoefficient_positive hR
  let w : ℝ → ℝ := fun u => Real.exp (-(4 * u))
  have hw : Continuous w := by fun_prop
  have hsq (u x : ℝ) : (w u * x) ^ 2 = x ^ 2 * Real.exp (-(8 * u)) := by
    dsimp only [w]
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm]
    congr 2
    push_cast
    ring
  have hUw (n : ℕ) : MemLp (fun u => w u * U n u) 2 volume := by
    apply (memLp_two_iff_integrable_sq
      (hw.aestronglyMeasurable.mul (hU n).meas.aestronglyMeasurable)).mpr
    change Integrable (fun u : ℝ => (w u * U n u) ^ 2)
    simpa only [hsq] using (hU n).exponential
  have htrunc (T : ℝ) (hT : Real.exp factorialSpanGammaOffset ≤ T) :
      truncatedWeilForm F T + criticalAliasCoefficient R *
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ≤ L := by
    have hX : Tendsto (fun n => truncatedWeilForm (U n) T) atTop
        (𝓝 (truncatedWeilForm F T)) :=
      ((tendsto_lowGammaForm (fun n => (hU n).integrable) hF.integrable hL1 T).sub hP).add
        (((hC.pow 2).const_mul 2).sub ((hS.pow 2).const_mul 2))
    let b : ℕ → ℝ := fun n =>
      (criticalHalfLineFullEnergy R (U n) - truncatedWeilForm (U n) T) /
        criticalAliasCoefficient R
    let B : ℝ := (L - truncatedWeilForm F T) / criticalAliasCoefficient R
    have hb : Tendsto b atTop (𝓝 B) := (hE.sub hX).div_const _
    have hbound (n : ℕ) : (∫ u, (w u * U n u) ^ 2) ≤ b n := by
      simp_rw [hsq]
      apply (le_div_iff₀ ha).mpr
      have ht := lowGammaForm_le_archForm_of_integrable (hU n).gamma hT
      dsimp only [criticalHalfLineFullEnergy, truncatedWeilForm]
      rw [halfLineExpMass_eq_full (hU n).support]
      linarith only [ht]
    have hB : 0 ≤ B := ge_of_tendsto hb (Eventually.of_forall fun n =>
      (integral_nonneg fun u : ℝ => sq_nonneg (w u * U n u)).trans (hbound n))
    have hlim : (∫ u, (w u * F u) ^ 2) ≤ B := by
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp
        (hb.eventually (ge_mem_nhds (lt_add_of_pos_right B hε)))
      exact (weighted_sq_of_L1_limit (fun n => (hU (n + N)).integrable) hF.integrable
        (hL1.comp (tendsto_add_atTop_nat N)) hw (fun n => hUw (n + N))
        (add_nonneg hB hε.le)
        (fun n => (hbound (n + N)).trans (hN _ (by omega)))).2
    simp_rw [hsq] at hlim
    have hfin := (le_div_iff₀ ha).mp hlim
    linarith only [hfin]
  have hΓ := tendsto_lowGammaForm_atTop_of_integrable hF.gamma
  have hlim : Tendsto (fun n : ℕ => truncatedWeilForm F (n : ℝ) +
      criticalAliasCoefficient R * (∫ u, F u ^ 2 * Real.exp (-(8 * u)))) atTop
      (𝓝 (criticalHalfLineFullEnergy R F)) := by
    simpa only [criticalHalfLineFullEnergy, halfLineExpMass_eq_full hF.support,
      truncatedWeilForm] using ((hΓ.sub_const (primeSum F)).add_const
        (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2)).add_const
          (criticalAliasCoefficient R * ∫ u, F u ^ 2 * Real.exp (-(8 * u)))
  apply le_of_tendsto hlim
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (Real.exp factorialSpanGammaOffset))] with n hn
  exact htrunc n hn

/-- Normalized smooth profiles with bounded confinement and convergent energy have a full-domain limit. -/
theorem exists_domain_limit_of_smooth_energy_limit {R : ℝ} (hR : 0 < R)
    {U : ℕ → ℝ → ℝ} (hU : ∀ n, CriticalHalfLineEnergyDomain (U n))
    (hUd : ∀ n, ContDiff ℝ 2 (U n)) (hUc : ∀ n, HasCompactSupport (U n))
    (hmass : ∀ n, (∫ u, U n u ^ 2) ≤ 1)
    (hmasslim : Tendsto (fun n => ∫ u, U n u ^ 2) atTop (𝓝 1))
    {M B L : ℝ} (hM : 0 ≤ M)
    (hweight : ∀ n, (∫ u, U n u ^ 2 * Real.exp (-(8 * u))) ≤ M)
    (hEbound : ∀ n, criticalHalfLineFullEnergy R (U n) ≤ B)
    (hElim : Tendsto (fun n => criticalHalfLineFullEnergy R (U n)) atTop (𝓝 L)) :
    ∃ (F : ℝ → ℝ) (s : ℕ → ℕ), StrictMono s ∧ CriticalHalfLineEnergyDomain F ∧
      (∫ u, F u ^ 2) = 1 ∧ criticalHalfLineFullEnergy R F ≤ L ∧
      (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ≤ M ∧
      Tendsto (fun n => ∫ u, (U (s n) u - F u) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ u, ‖U (s n) u - F u‖) atTop (𝓝 0) := by
  have ha := criticalAliasCoefficient_positive hR
  have hweil (n : ℕ) : weilQuad (U n) ≤ B := by
    have h := hEbound n
    rw [criticalHalfLineFullEnergy, ← weilQuad_eq_arch_sub_prime_add_pole (hUd n) (hUc n)] at h
    have hp : 0 ≤ criticalAliasCoefficient R *
        ∫ u in Iio 0, U n u ^ 2 * Real.exp (-(8 * u)) :=
      mul_nonneg ha.le (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    linarith only [h, hp]
  obtain ⟨F, s, hs, hFm, hFi, hF2, _, hF8, hweightF, hFs, hL2, hL1, hnormlim⟩ :=
    exists_strong_negative_limit_of_bounded_weilQuad hUd hUc hmass hM hweight
      (fun n u hu => (hU n).support u (by
        have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact (hp.trans hu).le)) hweil
  have hnorm : (∫ u, F u ^ 2) = 1 :=
    tendsto_nhds_unique hnormlim (hmasslim.comp hs.tendsto_atTop)
  let J : ℝ := ∫ u : ℝ, Real.exp (-|u|)
  let C : ℝ := 2 * vonMangoldtThreeHalvesMass + 2 * J
  have hJ : 0 ≤ J := integral_nonneg fun u => (Real.exp_pos _).le
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (by norm_num) vonMangoldtThreeHalvesMass_nonneg)
    (mul_nonneg (by norm_num) hJ)
  have hsource (n : ℕ) : exponentialSourceMass (U n) ≤ 1 + M := by
    have h := (exponentialSourceMass_le_of_support (Y := 0) le_rfl
      (hU n).meas.aestronglyMeasurable (hU n).sq (hU n).exponential
      (Eventually.of_forall fun u hu => (hU n).support u hu.le)).2
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul] at h
    exact h.trans (add_le_add (hmass n) (hweight n))
  have harch (n : ℕ) : archForm (U n) ≤ B + C * (1 + M) := by
    have hp := (le_abs_self (primeSum (U n))).trans (hU n).prime_bound
    have hsin := (hU n).sinh_bound
    have hsource' := mul_le_mul_of_nonneg_left (hsource n) hC
    have he := hEbound n
    have hweight0 : 0 ≤ criticalAliasCoefficient R *
        ∫ u in Iio 0, U n u ^ 2 * Real.exp (-(8 * u)) :=
      mul_nonneg ha.le (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    dsimp only [criticalHalfLineFullEnergy] at he
    dsimp only [C, J] at hsource' ⊢
    nlinarith only [hp, hsin, hsource', he, hweight0, sq_nonneg (coshHalfMoment (U n))]
  have hΓ := integrable_gamma_of_L1_limit_bounded_archForm
    (fun n => (hU (s n)).integrable) (fun n => (hU (s n)).sq)
    (fun n => (hU (s n)).gamma) hFi hF2 hL1 (fun n => hmass (s n)) (fun n => harch (s n))
  have hDF : CriticalHalfLineEnergyDomain F := ⟨hFm, hFi, hF2, hF8, hFs, hΓ⟩
  have hsup : ∀ᶠ n in atTop, ∀ u, 1 < u → U (s n) u = 0 :=
    Eventually.of_forall fun n u hu => (hU (s n)).support u (zero_le_one.trans hu.le)
  have hd := tendsto_exponentialSourceMass_sub
    (fun n => (hUd (s n)).continuous) (fun n => hUc (s n))
    hFm.aestronglyMeasurable hF2 hF8 (fun n => hweight (s n)) hsup
    (Eventually.of_forall fun u hu => hFs u (zero_le_one.trans hu.le))
    (fun ε hε => hL2.eventually (ge_mem_nhds hε))
  obtain ⟨hP, hCos, hSin⟩ := tendsto_prime_and_pole_of_strong_limit
    (fun n => (hUd (s n)).continuous) (fun n => hUc (s n)) hDF.weighted
    (fun n => hmass (s n)) (fun n => hweight (s n)) hsup hd
  exact ⟨F, s, hs, hDF, hnorm, criticalHalfLineFullEnergy_le_of_strong_limit hR
    (fun n => hU (s n)) hDF hL1 hP hCos hSin (hElim.comp hs.tendsto_atTop),
    hweightF, hL2, hL1⟩

#print axioms criticalHalfLineFullEnergy_le_of_strong_limit
#print axioms exists_domain_limit_of_smooth_energy_limit

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
