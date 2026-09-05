import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleZeroLanding
import GaloisForLFunctions.RHTower.EulerDeletionBalancedPeriodFreedom
import GaloisForLFunctions.RHTower.EulerDeletionFullEnergyFactorization
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem

/-!
# Critical boundary of literal Euler-deletion curvature

The ordered deletion sum at exponent one is the logarithm of its modulus, obtained by
differentiating the pole-cleared source identity. The four-channel curvature consequently
has a strictly negative ordered harmonic limit. Its physical Mellin pairing agrees with the
existing absolutely admitted curvature right of half and remains nonzero at critical-line
zeros. At those same actual zeros its single-exponent source sum vanishes.

This disproves unrestricted zero-fibre annihilation of the Hermitian charge. It does not
exclude a producer genuinely restricted to the strict right-half convergence chamber.
-/

noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionCriticalCurvature

/-- The ordered deletion sum at its removable zeta pole has the exact logarithmic value. -/
theorem deletion_sum_one (q : ℕ) :
    eulerDeletionDirichletSum q 1 = (Real.log (q + 1 : ℝ) : ℂ) := by
  have hp : (q + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsum : DifferentiableAt ℂ (eulerDeletionDirichletSum q) 1 :=
    (differentiableOn_eulerDeletionDirichletSum q).differentiableAt
      (hopen.mem_nhds (by norm_num))
  have hF := ((hasDerivAt_id (1 : ℂ)).sub_const 1).mul hsum.hasDerivAt
  have hpow := (((hasDerivAt_id (1 : ℂ)).neg).const_cpow (c := (q + 1 : ℂ))
    (Or.inl hp)).const_mul (q + 1 : ℂ)
  have hG := ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub hpow).mul
    (analyticAt_zetaResidueUnit 1).differentiableAt.hasDerivAt
  have heq : (fun z : ℂ => (z - 1) * eulerDeletionDirichletSum q z) =ᶠ[𝓝 1]
      (fun z : ℂ => (1 - (q + 1 : ℂ) * (q + 1 : ℂ) ^ (-z)) * zetaResidueUnit z) := by
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℂ) ∈ {z : ℂ | 0 < z.re})]
      with z hz
    simpa [complexEulerDilationFactor] using poleCleared_eulerDeletionDirichletSum_eq q hz
  have hder := hF.unique (heq.hasDerivAt_iff.mpr hG)
  have hd : eulerDeletionDirichletSum q 1 = Complex.log (q + 1 : ℂ) := by
    simpa [Pi.sub_apply, Pi.neg_apply, id_eq, Complex.cpow_neg_one,
      zetaResidueUnit_one, ← mul_assoc, hp] using hder
  have hpcast : (((q + 1 : ℝ) : ℂ)) = (q + 1 : ℂ) := by push_cast; rfl
  rw [hd, ← hpcast]
  exact (Complex.ofReal_log (by positivity)).symm

def harmonicPrefix (p N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (blockDeletionCoefficient p n : ℝ) / n

theorem complex_prefix_one_eq (p N : ℕ) :
    eulerDeletionDirichletPrefix p N 1 = (harmonicPrefix p N : ℂ) := by
  simp only [eulerDeletionDirichletPrefix, harmonicPrefix, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp [Complex.cpow_neg_one, div_eq_mul_inv]

/-- The value is obtained along the original integer cutoffs, not by an unordered sum. -/
theorem tendsto_harmonicPrefix {p : ℕ} (hp : 0 < p) :
    Tendsto (harmonicPrefix p) atTop (𝓝 (Real.log p)) := by
  have hpred : p - 1 + 1 = p := by omega
  have h := GaloisForLFunctions.RHTower.tendsto_dirichletSum
    (eulerDeletionDirichlet_convergesAt (q := p - 1) (s := (1 : ℂ)) (by norm_num))
  change Tendsto _ _ (𝓝 (eulerDeletionDirichletSum (p - 1) 1)) at h
  rw [deletion_sum_one] at h
  have hlog : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    ring
  rw [hlog] at h
  simp_rw [dirichletPartialSum_eulerDeletion_eq_prefix, hpred,
    complex_prefix_one_eq] at h
  simpa only [Function.comp_def, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto ((Real.log p : ℝ) : ℂ)).comp h

def curvaturePrefix (p q r N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, DeletionBalancedPeriods.curvatureCoefficient p q r n / n

theorem curvaturePrefix_eq {p q r : ℕ}
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r) (N : ℕ) :
    curvaturePrefix p q r N = ((q : ℝ) - 1) *
      (harmonicPrefix (p * q) N - harmonicPrefix q N +
        (r : ℝ) * (harmonicPrefix (q * r) N - harmonicPrefix (p * q * r) N)) := by
  simp only [curvaturePrefix, harmonicPrefix, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [DeletionBalancedPeriods.curvature_coefficient_linear hpq hpr hqr]
  simp only [DeletionBalancedPeriods.coefficient]
  ring

/-- Exact ordered critical charge of the same four source channels. -/
theorem tendsto_curvaturePrefix {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r) :
    Tendsto (curvaturePrefix p q r) atTop
      (𝓝 (-((q : ℝ) - 1) * ((r : ℝ) - 1) * Real.log p)) := by
  have h := ((tendsto_harmonicPrefix (Nat.mul_pos hp hq)).sub
    (tendsto_harmonicPrefix hq)).add
      (((tendsto_harmonicPrefix (Nat.mul_pos hq hr)).sub
        (tendsto_harmonicPrefix (Nat.mul_pos (Nat.mul_pos hp hq) hr))).const_mul (r : ℝ))
  have h' := h.const_mul ((q : ℝ) - 1)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hv : ((q : ℝ) - 1) *
      (Real.log (p * q : ℕ) - Real.log q +
        (r : ℝ) * (Real.log (q * r : ℕ) - Real.log (p * q * r : ℕ))) =
          -((q : ℝ) - 1) * ((r : ℝ) - 1) * Real.log p := by
    simp only [Nat.cast_mul, Real.log_mul hpR hqR, Real.log_mul hqR hrR,
      Real.log_mul (mul_ne_zero hpR hqR) hrR]
    ring
  rw [hv] at h'
  exact h'.congr (fun N => (curvaturePrefix_eq hpq hpr hqr N).symm)

/-- Literal doubled-real-part weighting of the curvature coefficient. -/
def hermitianPrefix (p q r : ℕ) (rho : ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, DeletionBalancedPeriods.curvatureCoefficient p q r n *
    deletionDirichletWeight (2 * rho.re) n

/-- At positive integer clocks the physical pair formula requires no half-plane restriction. -/
theorem grade_pair_term {n : ℕ} (hn : 0 < n) (p q : ℕ) (s : ℂ) :
    (deletionMellinSource q s n * star (deletionFactorizationInteractionSource p q s n)).re =
      (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) ^ 2 *
        deletionDirichletWeight (2 * s.re) n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm : Complex.normSq ((n : ℂ) ^ (-s)) =
      deletionDirichletWeight (2 * s.re) n := by
    rw [Complex.normSq_eq_norm_sq]
    have h := Complex.norm_cpow_eq_rpow_re_of_pos hnR (-s)
    simp only [Complex.ofReal_natCast, Complex.neg_re] at h
    rw [h, pow_two, ← Real.rpow_add hnR]
    unfold deletionDirichletWeight
    congr 1
    ring
  rw [← hnorm]
  simp [deletionMellinSource, deletionFactorizationInteractionSource,
    deletionFactorizationInteraction, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Four literal Mellin singleton/interaction pairings on one common ordered cutoff. -/
def physicalPairPrefix (p q r : ℕ) (rho : ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((deletionMellinSource q rho n * star (deletionFactorizationInteractionSource p q rho n)).re +
      (deletionMellinSource r rho n * star (deletionFactorizationInteractionSource (p*q) r rho n)).re -
      (deletionMellinSource r rho n * star (deletionFactorizationInteractionSource q r rho n)).re -
      (deletionMellinSource (q*r) rho n * star (deletionFactorizationInteractionSource p (q*r) rho n)).re)

theorem physicalPairPrefix_eq (p q r : ℕ) (rho : ℂ) (N : ℕ) :
    physicalPairPrefix p q r rho N = hermitianPrefix p q r rho N := by
  unfold physicalPairPrefix hermitianPrefix
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [grade_pair_term hn0, grade_pair_term hn0, grade_pair_term hn0, grade_pair_term hn0]
  dsimp only [DeletionBalancedPeriods.curvatureCoefficient, DeletionBalancedPeriods.coefficient]
  ring

private theorem tendsto_gradePrefix {α : ℝ} (hα : 1 < α) (p q : ℕ) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N,
      (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) ^ 2 *
        deletionDirichletWeight α n) atTop (𝓝 (deletionFactorizationGradeCross α p q)) := by
  let f : ℕ → ℝ := fun n =>
    (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) ^ 2 *
      deletionDirichletWeight α n
  have hs : Summable f := DeletionFullEnergy.summable_selectedCoefficient hα p q
  have hv : (∑' n, f n) = deletionFactorizationGradeCross α p q := by
    unfold deletionFactorizationGradeCross
    apply tsum_congr
    intro n
    dsimp [f, deletionFactorizationInteraction]
    push_cast
    ring
  have hsum : HasSum f (deletionFactorizationGradeCross α p q) := by
    rw [← hv]
    exact hs.hasSum
  have hzero : f 0 = 0 := by
    simp [f, deletionDirichletWeight, Real.zero_rpow (by linarith : -α ≠ 0)]
  have hshift : HasSum (fun n => f (n + 1)) (deletionFactorizationGradeCross α p q) := by
    simpa [hzero] using (hasSum_nat_add_iff' 1).mpr hsum
  change Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n) atTop _
  simpa only [sum_Icc_eq_sum_range_succ] using hshift.tendsto_sum_nat

/-- Above half this ordered source is exactly the existing absolutely admitted curvature. -/
theorem tendsto_hermitianPrefix_of_half_lt {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (p q r : ℕ) :
    Tendsto (hermitianPrefix p q r rho) atTop
      (𝓝 (deletionFactorizationGradeCurvature (2 * rho.re) p q r)) := by
  have hα : 1 < 2 * rho.re := by linarith
  have h := (((tendsto_gradePrefix hα p q).add (tendsto_gradePrefix hα (p*q) r)).sub
    (tendsto_gradePrefix hα q r)).sub (tendsto_gradePrefix hα p (q*r))
  change Tendsto _ _ (𝓝 (deletionFactorizationGradeCurvature (2 * rho.re) p q r)) at h
  refine h.congr (fun N => ?_)
  simp only [hermitianPrefix, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only [DeletionBalancedPeriods.curvatureCoefficient, DeletionBalancedPeriods.coefficient]
  ring

/-- The same integer coefficient with the source exponent applied once. -/
def sourcePrefix (p q r : ℕ) (rho : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (DeletionBalancedPeriods.curvatureCoefficient p q r n : ℂ) *
    (n : ℂ) ^ (-rho)

theorem sourcePrefix_eq {p q r : ℕ}
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r)
    (rho : ℂ) (N : ℕ) :
    sourcePrefix p q r rho N = ((q : ℂ) - 1) *
      (eulerDeletionDirichletPrefix (p*q) N rho - eulerDeletionDirichletPrefix q N rho +
        (r : ℂ) * (eulerDeletionDirichletPrefix (q*r) N rho -
          eulerDeletionDirichletPrefix (p*q*r) N rho)) := by
  simp only [sourcePrefix, eulerDeletionDirichletPrefix, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [DeletionBalancedPeriods.curvature_coefficient_linear hpq hpr hqr]
  simp only [DeletionBalancedPeriods.coefficient]
  push_cast
  ring

/-- Source exponent zero-landing is valid; Hermitian regrading is a different operation. -/
theorem tendsto_sourcePrefix_zero {p q r : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r)
    {rho : ℂ} (hpos : 0 < rho.re) (hne : rho ≠ 1) (hz : riemannZeta rho = 0) :
    Tendsto (sourcePrefix p q r rho) atTop (𝓝 0) := by
  have hsingle (d : ℕ) (hd : 0 < d) :
      Tendsto (fun N => eulerDeletionDirichletPrefix d N rho) atTop (𝓝 0) := by
    have h := GaloisForLFunctions.RHTower.tendsto_dirichletSum
      (eulerDeletionDirichlet_convergesAt (q := d - 1) hpos)
    change Tendsto _ _ (𝓝 (eulerDeletionDirichletSum (d - 1) rho)) at h
    rw [eulerDeletionDirichletSum_eq_zero_of_riemannZeta_eq_zero (d - 1) hpos hne hz] at h
    simpa only [dirichletPartialSum_eulerDeletion_eq_prefix,
      Nat.sub_add_cancel (by omega : 1 ≤ d)] using h
  have h := (((hsingle (p*q) (Nat.mul_pos hp hq)).sub (hsingle q hq)).add
    (((hsingle (q*r) (Nat.mul_pos hq hr)).sub
      (hsingle (p*q*r) (Nat.mul_pos (Nat.mul_pos hp hq) hr))).const_mul (r : ℂ))).const_mul
        ((q : ℂ) - 1)
  have h' := h.congr (fun N => (sourcePrefix_eq hpq hpr hqr rho N).symm)
  simpa only [sub_self, mul_zero, add_zero] using h'

theorem hermitianPrefix_eq_critical {rho : ℂ} (hline : rho.re = 1 / 2)
    (p q r N : ℕ) : hermitianPrefix p q r rho N = curvaturePrefix p q r N := by
  simp [hermitianPrefix, curvaturePrefix, deletionDirichletWeight, hline,
    Real.rpow_neg_one, div_eq_mul_inv]

/-- The critical line itself carries a strictly negative, ordered source-curvature limit. -/
theorem criticalLine_charge_neg {rho : ℂ} (hline : rho.re = 1 / 2)
    {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r) :
    ∃ L : ℝ, L < 0 ∧ Tendsto (hermitianPrefix p q r rho) atTop (𝓝 L) := by
  refine ⟨-((q : ℝ) - 1) * ((r : ℝ) - 1) * Real.log p, ?_, ?_⟩
  · have hqR : (1 : ℝ) < q := by exact_mod_cast hq
    have hrR : (1 : ℝ) < r := by exact_mod_cast hr
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos (by linarith)) (by linarith)) hlog
  · exact (tendsto_curvaturePrefix (by omega : 0 < p) (by omega : 0 < q)
      (by omega : 0 < r) hpq hpr hqr).congr
        (fun N => (hermitianPrefix_eq_critical hline p q r N).symm)

/-- A genuine zeta zero, not a deformed-source countermodel, has nonzero critical charge. -/
theorem exists_actual_zero_with_nonzero_charge {p q r : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r) :
    ∃ rho : ℂ, riemannZeta rho = 0 ∧ rho.re = 1 / 2 ∧
      ∃ L : ℝ, L < 0 ∧ Tendsto (hermitianPrefix p q r rho) atTop (𝓝 L) := by
  obtain ⟨T₀, _, hzero⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, _, hz⟩ := hzero T₀ le_rfl
  exact ⟨linePt τ, hz, linePt_re τ,
    criticalLine_charge_neg (linePt_re τ) hp hq hr hpq hpr hqr⟩

/-- At an actual zero, the literal source closes while its actual Hermitian pair charge does not. -/
theorem exists_actual_zero_with_different_source_limits {p q r : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r) :
    ∃ (rho : ℂ) (L : ℝ), riemannZeta rho = 0 ∧ rho.re = 1 / 2 ∧ L < 0 ∧
      Tendsto (sourcePrefix p q r rho) atTop (𝓝 0) ∧
      Tendsto (physicalPairPrefix p q r rho) atTop (𝓝 L) := by
  obtain ⟨rho, hz, hline, L, hL, hlim⟩ :=
    exists_actual_zero_with_nonzero_charge hp hq hr hpq hpr hqr
  have hpos : 0 < rho.re := by rw [hline]; norm_num
  have hne : rho ≠ 1 := by
    intro heq
    rw [heq] at hline
    norm_num at hline
  refine ⟨rho, L, hz, hline, hL,
    tendsto_sourcePrefix_zero (by omega) (by omega) (by omega) hpq hpr hqr hpos hne hz, ?_⟩
  exact hlim.congr (fun N => (physicalPairPrefix_eq p q r rho N).symm)

/-- Unrestricted zero-fibre annihilation of the literal two-three-five curvature is false. -/
theorem not_global_zero_curvature_annihilation :
    ¬ ∀ rho : ℂ, 0 < rho.re → rho ≠ 1 → riemannZeta rho = 0 →
      Tendsto (hermitianPrefix 2 3 5 rho) atTop (𝓝 0) := by
  intro h
  obtain ⟨rho, hz, hline, L, hL, hlim⟩ :=
    exists_actual_zero_with_nonzero_charge (p := 2) (q := 3) (r := 5)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hpos : 0 < rho.re := by rw [hline]; norm_num
  have hne : rho ≠ 1 := by
    intro heq
    rw [heq] at hline
    norm_num at hline
  have hsame := tendsto_nhds_unique hlim (h rho hpos hne hz)
  exact (ne_of_lt hL) hsame

end RHTower.DeletionCriticalCurvature

