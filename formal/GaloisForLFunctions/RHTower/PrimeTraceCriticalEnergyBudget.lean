import GaloisForLFunctions.RHTower.GradeMonodromyInversion
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative
import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearHilbertFactor
import GaloisForLFunctions.RHTower.PrimeCharacterTailIndependence

/-!
# The prime-trace critical energy budget
-/

namespace RHTower

open Filter Complex
open scoped Topology BigOperators ENNReal NNReal

theorem tendsto_one_add_nhdsWithin :
    Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun ε : ℝ => 1 + ε) (𝓝 (0 : ℝ)) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa using hε

/-- **The grade-one prime source at the Euler pole.**  Along the real approach the source differs
from the simple pole `1/ε` by a convergent quantity. -/
theorem tendsto_primeGradeSource_sub_pole :
    Tendsto (fun ε : ℝ => primeGradeSource (1 + (ε : ℂ)) - 1 / (ε : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - xiPrimeLogHigherValuation 1)) := by
  have hpole := tendsto_LSeries_vonMangoldt_sub_pole.comp tendsto_one_add_nhdsWithin
  have htail : Tendsto (fun ε : ℝ => xiPrimeLogHigherValuation (1 + (ε : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (xiPrimeLogHigherValuation 1)) := by
    have hcont : ContinuousAt xiPrimeLogHigherValuation 1 :=
      (differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re
        (by norm_num : (1 : ℝ) / 2 < (1 : ℂ).re)).continuousAt
    have hinner : Tendsto (fun ε : ℝ => (1 : ℂ) + (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h1 : Tendsto (fun ε : ℝ => (1 : ℂ) + (ε : ℂ)) (𝓝 (0 : ℝ)) (𝓝 ((1 : ℂ) + 0)) :=
        tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)
      simpa using h1.mono_left nhdsWithin_le_nhds
    exact hcont.tendsto.comp hinner
  have hsub := hpole.sub htail
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  have hre : 1 < ((1 : ℂ) + (ε : ℂ)).re := by
    simp
    linarith
  have hcont := primeGradeSource_eq_continuation hre
  have hflux : xiPrimeLogDirichletContinuation ((1 : ℂ) + (ε : ℂ))
      = infinitePrimeFlux ((1 : ℂ) + (ε : ℂ)) - xiPrimeLogHigherValuation ((1 : ℂ) + (ε : ℂ)) := rfl
  have hLS : infinitePrimeFlux ((1 : ℂ) + (ε : ℂ))
      = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((1 : ℂ) + (ε : ℂ)) := by
    rw [infinitePrimeFlux, logDeriv_apply,
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre, neg_div]
  have hcast : (((1 + ε : ℝ)) : ℂ) = (1 : ℂ) + (ε : ℂ) := by push_cast; ring
  simp only [Function.comp_apply, hcast]
  rw [hcont, hflux, hLS]
  ring

/-- **The grade-one prime source off the Euler pole.**  At every nonzero vertical displacement on
the one-line the source has a finite limit:  zeta has no zero there. -/
theorem tendsto_primeGradeSource_shift {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun ε : ℝ => primeGradeSource (1 + (ε : ℂ) + (τ : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (xiPrimeLogDirichletContinuation (1 + (τ : ℂ) * Complex.I))) := by
  have hne1 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := by
    intro hcon
    apply hτ
    have him := congrArg Complex.im hcon
    simpa using him
  have hzeta : riemannZeta ((1 : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp
  have hdiff : DifferentiableAt ℂ xiPrimeLogDirichletContinuation
      ((1 : ℂ) + (τ : ℂ) * Complex.I) := by
    have hre : (1 : ℝ) / 2 < ((1 : ℂ) + (τ : ℂ) * Complex.I).re := by
      simp
      norm_num
    have hflux : DifferentiableAt ℂ infinitePrimeFlux ((1 : ℂ) + (τ : ℂ) * Complex.I) := by
      simpa only [infinitePrimeFlux, logDeriv_apply, neg_div] using!
        differentiableAt_neg_logDeriv_riemannZeta hne1 hzeta
    exact hflux.sub (differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re hre)
  have hinner : Tendsto (fun ε : ℝ => (1 : ℂ) + (ε : ℂ) + (τ : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℂ) + (τ : ℂ) * Complex.I)) := by
    have h1 : Tendsto (fun ε : ℝ => (1 : ℂ) + (ε : ℂ) + (τ : ℂ) * Complex.I) (𝓝 (0 : ℝ))
        (𝓝 ((1 : ℂ) + 0 + (τ : ℂ) * Complex.I)) :=
      (tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)).add tendsto_const_nhds
    simpa using h1.mono_left nhdsWithin_le_nhds
  have hcomp := hdiff.continuousAt.tendsto.comp hinner
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  have hre : 1 < ((1 : ℂ) + (ε : ℂ) + (τ : ℂ) * Complex.I).re := by
    simp
    linarith
  exact (primeGradeSource_eq_continuation hre).symm

/-! ## The divisor test energy -/

theorem conj_cis (l t : ℝ) : starRingEnd ℂ (HTGeometry.cis l t) = HTGeometry.cis (-l) t := by
  rw [HTGeometry.cis, HTGeometry.cis, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I]

theorem cis_mul_cis (l l' t : ℝ) :
    HTGeometry.cis l t * HTGeometry.cis l' t = HTGeometry.cis (l + l') t := by
  rw [HTGeometry.cis, HTGeometry.cis, HTGeometry.cis, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The unimodular divisor phase of a finite ordinate packet. -/
noncomputable def divisorPhase {J : ℕ} (m γ : Fin J → ℝ) (t : ℝ) : ℂ :=
  ∑ j, (m j : ℂ) * HTGeometry.cis (-(γ j)) t

theorem normSq_divisorPhase {J : ℕ} (m γ : Fin J → ℝ) (t : ℝ) :
    ((‖divisorPhase m γ t‖ ^ 2 : ℝ) : ℂ)
      = ∑ j, ∑ k, (m j : ℂ) * (m k : ℂ) * HTGeometry.cis (γ k - γ j) t := by
  have hnorm : ((‖divisorPhase m γ t‖ ^ 2 : ℝ) : ℂ)
      = divisorPhase m γ t * starRingEnd ℂ (divisorPhase m γ t) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    ring
  rw [hnorm, divisorPhase, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_ofReal, conj_cis, mul_mul_mul_comm, cis_mul_cis]
  congr 2
  ring

theorem natCast_cpow_neg_split (p : Nat.Primes) (σ τ : ℝ) :
    (((p : ℕ) : ℂ)) ^ (-(((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I))
      = (((((p : ℕ) : ℝ)) ^ (-σ) : ℝ) : ℂ) * HTGeometry.cis (-τ) (Real.log ((p : ℕ) : ℝ)) := by
  have hpos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hne : (((p : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast p.2.pos.ne'
  have hsplit : -(((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I)
      = (((-σ : ℝ) : ℂ)) + (((-τ : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  rw [hsplit, Complex.cpow_add _ _ hne, Complex.ofReal_cpow hpos.le,
    natCast_cpow_imaginary p.2.pos (-τ)]
  norm_num

/-- The divisor test energy of a finite ordinate packet. -/
noncomputable def divisorTestEnergy {J : ℕ} (m γ : Fin J → ℝ) (ε : ℝ) : ℝ :=
  ∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) *
    ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ ^ 2

theorem divisorTestEnergy_term_eq {J : ℕ} (m γ : Fin J → ℝ) (ε : ℝ) (p : Nat.Primes) :
    ((Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) *
        ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ ^ 2 : ℝ) : ℂ)
      = ∑ j, ∑ k, (m j : ℂ) * (m k : ℂ) *
          ((Real.log ((p : ℕ) : ℝ) : ℂ) *
            (((p : ℕ) : ℂ)) ^ (-((((1 + ε : ℝ)) : ℂ) + (((γ j - γ k : ℝ)) : ℂ) * Complex.I))) := by
  rw [Complex.ofReal_mul, Complex.ofReal_mul, normSq_divisorPhase m γ (Real.log ((p : ℕ) : ℝ))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [natCast_cpow_neg_split p (1 + ε) (γ j - γ k)]
  have hphase : HTGeometry.cis (-(γ j - γ k)) (Real.log ((p : ℕ) : ℝ))
      = HTGeometry.cis (γ k - γ j) (Real.log ((p : ℕ) : ℝ)) := by
    congr 1
    ring
  rw [hphase]
  ring

theorem norm_divisorPhase_le {J : ℕ} (m γ : Fin J → ℝ) (t : ℝ) :
    ‖divisorPhase m γ t‖ ≤ ∑ j, |m j| := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, HTGeometry.norm_cis, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem summable_divisorTestEnergyTerm {J : ℕ} (m γ : Fin J → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) *
      ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ ^ 2 := by
  have hbase : Summable fun p : Nat.Primes =>
      Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) :=
    summable_primeLogMassTerm (by linarith)
  set A := ∑ j, |m j| with hA
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hbase.mul_right (A ^ 2))
  · have h1 : (0 : ℝ) ≤ Real.log ((p : ℕ) : ℝ) :=
      Real.log_natCast_nonneg _
    positivity
  · have hnorm := norm_divisorPhase_le m γ (Real.log ((p : ℕ) : ℝ))
    have hsq : ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ ^ 2 ≤ A ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hw : (0 : ℝ) ≤ Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) := by
      have h1 : (0 : ℝ) ≤ Real.log ((p : ℕ) : ℝ) := Real.log_natCast_nonneg _
      positivity
    calc Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) *
          ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ ^ 2
        ≤ Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) * A ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hw
      _ = Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) * A ^ 2 := rfl

/-- **The divisor test energy is the ordinate-pair sum of the grade-one source.** -/
theorem divisorTestEnergy_eq {J : ℕ} (m γ : Fin J → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ((divisorTestEnergy m γ ε : ℝ) : ℂ)
      = ∑ j, ∑ k, (m j : ℂ) * (m k : ℂ) *
          primeGradeSource ((((1 + ε : ℝ)) : ℂ) + (((γ j - γ k : ℝ)) : ℂ) * Complex.I) := by
  have hsummable := summable_divisorTestEnergyTerm m γ hε
  have hterm : ∀ (j k : Fin J), Summable fun p : Nat.Primes =>
      (m j : ℂ) * (m k : ℂ) * ((Real.log ((p : ℕ) : ℝ) : ℂ) *
        (((p : ℕ) : ℂ)) ^ (-((((1 + ε : ℝ)) : ℂ) + (((γ j - γ k : ℝ)) : ℂ) * Complex.I))) := by
    intro j k
    have hre : 1 < ((((1 + ε : ℝ)) : ℂ) + (((γ j - γ k : ℝ)) : ℂ) * Complex.I).re := by
      simp
      linarith
    exact ((summable_primeGradeSourceTerm hre).mul_left _)
  have hcast : ((divisorTestEnergy m γ ε : ℝ) : ℂ)
      = ∑' p : Nat.Primes, ((Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) *
          ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ ^ 2 : ℝ) : ℂ) :=
    Complex.ofRealCLM.map_tsum hsummable
  rw [hcast, tsum_congr (divisorTestEnergy_term_eq m γ ε)]
  rw [Summable.tsum_finsetSum fun j _ => summable_sum fun k _ => hterm j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Summable.tsum_finsetSum fun k _ => hterm j k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left, primeGradeSource]

theorem tendsto_mul_primeGradeSource_pole :
    Tendsto (fun ε : ℝ => (ε : ℂ) * primeGradeSource (1 + (ε : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hg := tendsto_primeGradeSource_sub_pole
  have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using Complex.continuous_ofReal.tendsto 0
    exact h1.mono_left nhdsWithin_le_nhds
  have hprod := hε0.mul hg
  rw [zero_mul] at hprod
  have hshift := hprod.add (tendsto_const_nhds (x := (1 : ℂ)))
  rw [zero_add] at hshift
  refine hshift.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεne : (ε : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hε : (0 : ℝ) < ε))
  field_simp
  ring

theorem tendsto_mul_primeGradeSource_shift {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * primeGradeSource (1 + (ε : ℂ) + (τ : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using Complex.continuous_ofReal.tendsto 0
    exact h1.mono_left nhdsWithin_le_nhds
  have hprod := hε0.mul (tendsto_primeGradeSource_shift hτ)
  rwa [zero_mul] at hprod

/-- **The divisor test energy has residue the squared multiplicity mass.** -/
theorem tendsto_mul_divisorTestEnergy {J : ℕ} (m γ : Fin J → ℝ) (hγ : Function.Injective γ) :
    Tendsto (fun ε : ℝ => ε * divisorTestEnergy m γ ε) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ j, (m j) ^ 2)) := by
  have hpair : ∀ j k : Fin J,
      Tendsto (fun ε : ℝ => (m j : ℂ) * (m k : ℂ) * ((ε : ℂ) *
        primeGradeSource ((((1 + ε : ℝ)) : ℂ) + (((γ j - γ k : ℝ)) : ℂ) * Complex.I)))
        (𝓝[>] (0 : ℝ)) (𝓝 (if j = k then ((m j : ℂ)) ^ 2 else 0)) := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, pow_two]
      have hzero : ∀ ε : ℝ, (((1 + ε : ℝ)) : ℂ) + (((γ j - γ j : ℝ)) : ℂ) * Complex.I
          = 1 + (ε : ℂ) := by
        intro ε
        push_cast
        ring
      simp only [hzero]
      have h := tendsto_mul_primeGradeSource_pole.const_mul ((m j : ℂ) * (m j : ℂ))
      rw [mul_one] at h
      exact h
    · have hτ : γ j - γ k ≠ 0 := sub_ne_zero.mpr fun hcon => hjk (hγ hcon)
      have hshift : ∀ ε : ℝ, (((1 + ε : ℝ)) : ℂ) + (((γ j - γ k : ℝ)) : ℂ) * Complex.I
          = 1 + (ε : ℂ) + (((γ j - γ k : ℝ)) : ℂ) * Complex.I := by
        intro ε
        push_cast
        ring
      simp only [hshift, if_neg hjk]
      have := (tendsto_mul_primeGradeSource_shift hτ).const_mul ((m j : ℂ) * (m k : ℂ))
      rwa [mul_zero] at this
  have hsum : Tendsto (fun ε : ℝ => ∑ j, ∑ k, (m j : ℂ) * (m k : ℂ) * ((ε : ℂ) *
      primeGradeSource ((((1 + ε : ℝ)) : ℂ) + (((γ j - γ k : ℝ)) : ℂ) * Complex.I)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ j, ∑ k, if j = k then ((m j : ℂ)) ^ 2 else 0)) :=
    tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ => hpair j k
  have hval : (∑ j, ∑ k, if j = k then ((m j : ℂ)) ^ 2 else 0) = ∑ j, ((m j : ℂ)) ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq Finset.univ j (fun _ => ((m j : ℂ)) ^ 2)]
    simp
  rw [hval] at hsum
  have hcomplex : Tendsto (fun ε : ℝ => ((ε * divisorTestEnergy m γ ε : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ j, ((m j : ℂ)) ^ 2)) := by
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : (0 : ℝ) < ε := hε
    have hcast : ((ε * divisorTestEnergy m γ ε : ℝ) : ℂ)
        = (ε : ℂ) * ((divisorTestEnergy m γ ε : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, divisorTestEnergy_eq m γ hεpos, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hlim : (∑ j, ((m j : ℂ)) ^ 2).re = ∑ j, (m j) ^ 2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hre : Tendsto (fun ε : ℝ => ε * divisorTestEnergy m γ ε) (𝓝[>] (0 : ℝ))
      (𝓝 ((∑ j, ((m j : ℂ)) ^ 2).re)) := (Complex.continuous_re.tendsto _).comp hcomplex
  rwa [hlim] at hre

/-! ## The mixed current and the Cauchy--Schwarz budget -/

/-- The prime-trace source of a discrepancy field. -/
noncomputable def primeTraceSource (c : Nat.Primes → ℂ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, c p * (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ)) ^ (-s)

/-- The mixed prime--divisor current. -/
noncomputable def primeDivisorCurrent (c : Nat.Primes → ℂ) {J : ℕ} (m γ : Fin J → ℝ)
    (β ε : ℝ) : ℂ :=
  ∑ j, (m j : ℂ) *
    primeTraceSource c ((((β + ε : ℝ)) : ℂ) + ((γ j : ℝ) : ℂ) * Complex.I)

/-- The unnormalized critical prime-trace energy. -/
noncomputable def primeTraceEnergyReal (c : Nat.Primes → ℂ) (t : ℝ) : ℝ :=
  ∑' p : Nat.Primes, ‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-t)

theorem primeDivisorCurrent_eq_tsum (c : Nat.Primes → ℂ) {J : ℕ} (m γ : Fin J → ℝ)
    {β ε : ℝ} (hε : 0 < ε)
    (hconv : ∀ s : ℂ, β < s.re →
      Summable fun p : Nat.Primes => ‖c p * (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ)) ^ (-s)‖) :
    primeDivisorCurrent c m γ β ε
      = ∑' p : Nat.Primes, c p * (Real.log ((p : ℕ) : ℝ) : ℂ) *
          ((((((p : ℕ) : ℝ)) ^ (-(β + ε)) : ℝ)) : ℂ) *
          divisorPhase m γ (Real.log ((p : ℕ) : ℝ)) := by
  have hre : ∀ j : Fin J, β < ((((β + ε : ℝ)) : ℂ) + ((γ j : ℝ) : ℂ) * Complex.I).re := by
    intro j
    simp
    linarith
  have hsummable : ∀ j : Fin J, Summable fun p : Nat.Primes =>
      (m j : ℂ) * (c p * (Real.log ((p : ℕ) : ℝ) : ℂ) *
        (((p : ℕ) : ℂ)) ^ (-((((β + ε : ℝ)) : ℂ) + ((γ j : ℝ) : ℂ) * Complex.I))) :=
    fun j => ((Summable.of_norm (hconv _ (hre j))).mul_left _)
  rw [primeDivisorCurrent]
  have hstep : ∀ j : Fin J, (m j : ℂ) *
      primeTraceSource c ((((β + ε : ℝ)) : ℂ) + ((γ j : ℝ) : ℂ) * Complex.I)
      = ∑' p : Nat.Primes, (m j : ℂ) * (c p * (Real.log ((p : ℕ) : ℝ) : ℂ) *
        (((p : ℕ) : ℂ)) ^ (-((((β + ε : ℝ)) : ℂ) + ((γ j : ℝ) : ℂ) * Complex.I))) := by
    intro j
    rw [primeTraceSource, tsum_mul_left]
  rw [Finset.sum_congr rfl fun j _ => hstep j]
  rw [← Summable.tsum_finsetSum fun j _ => hsummable j]
  refine tsum_congr fun p => ?_
  rw [divisorPhase, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [natCast_cpow_neg_split p (β + ε) (γ j)]
  ring

theorem norm_primeDivisorCurrent_sq_le (c : Nat.Primes → ℂ) {J : ℕ} (m γ : Fin J → ℝ)
    {β ε : ℝ} (hε : 0 < ε)
    (hconv : ∀ s : ℂ, β < s.re →
      Summable fun p : Nat.Primes => ‖c p * (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ)) ^ (-s)‖)
    (hE : Summable fun p : Nat.Primes =>
      ‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(2 * (β - 1 / 2) + ε))) :
    ‖primeDivisorCurrent c m γ β ε‖ ^ 2
      ≤ primeTraceEnergyReal c (2 * (β - 1 / 2) + ε) * divisorTestEnergy m γ ε := by
  set f : Nat.Primes → ℝ := fun p =>
    ‖c p‖ * Real.sqrt (Real.log ((p : ℕ) : ℝ)) * (((p : ℕ) : ℝ)) ^ (-((β - 1 / 2) + ε / 2)) with hf
  set g : Nat.Primes → ℝ := fun p =>
    Real.sqrt (Real.log ((p : ℕ) : ℝ)) * (((p : ℕ) : ℝ)) ^ (-(1 / 2 + ε / 2)) *
      ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ with hg
  have hlogpos : ∀ p : Nat.Primes, 0 ≤ Real.log ((p : ℕ) : ℝ) := fun p =>
    Real.log_natCast_nonneg _
  have hppos : ∀ p : Nat.Primes, (0 : ℝ) < ((p : ℕ) : ℝ) := fun p => by
    exact_mod_cast p.2.pos
  have hfn : ∀ p, 0 ≤ f p := by
    intro p
    have h1 : (0 : ℝ) ≤ Real.sqrt (Real.log ((p : ℕ) : ℝ)) := Real.sqrt_nonneg _
    positivity
  have hgn : ∀ p, 0 ≤ g p := by
    intro p
    have h1 : (0 : ℝ) ≤ Real.sqrt (Real.log ((p : ℕ) : ℝ)) := Real.sqrt_nonneg _
    positivity
  have hfsq : ∀ p, f p ^ 2 = ‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) *
      (((p : ℕ) : ℝ)) ^ (-(2 * (β - 1 / 2) + ε)) := by
    intro p
    rw [hf]
    have hsq : (Real.sqrt (Real.log ((p : ℕ) : ℝ))) ^ 2 = Real.log ((p : ℕ) : ℝ) :=
      Real.sq_sqrt (hlogpos p)
    have hpow : ((((p : ℕ) : ℝ)) ^ (-((β - 1 / 2) + ε / 2))) ^ 2
        = (((p : ℕ) : ℝ)) ^ (-(2 * (β - 1 / 2) + ε)) := by
      rw [← Real.rpow_natCast ((((p : ℕ) : ℝ)) ^ (-((β - 1 / 2) + ε / 2))) 2,
        ← Real.rpow_mul (hppos p).le]
      congr 1
      push_cast
      ring
    calc (‖c p‖ * Real.sqrt (Real.log ((p : ℕ) : ℝ)) *
          (((p : ℕ) : ℝ)) ^ (-((β - 1 / 2) + ε / 2))) ^ 2
        = ‖c p‖ ^ 2 * (Real.sqrt (Real.log ((p : ℕ) : ℝ))) ^ 2 *
            ((((p : ℕ) : ℝ)) ^ (-((β - 1 / 2) + ε / 2))) ^ 2 := by ring
      _ = ‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) *
            (((p : ℕ) : ℝ)) ^ (-(2 * (β - 1 / 2) + ε)) := by rw [hsq, hpow]
  have hgsq : ∀ p, g p ^ 2 = Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) *
      ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ ^ 2 := by
    intro p
    rw [hg]
    have hsq : (Real.sqrt (Real.log ((p : ℕ) : ℝ))) ^ 2 = Real.log ((p : ℕ) : ℝ) :=
      Real.sq_sqrt (hlogpos p)
    have hpow : ((((p : ℕ) : ℝ)) ^ (-(1 / 2 + ε / 2))) ^ 2
        = (((p : ℕ) : ℝ)) ^ (-(1 + ε)) := by
      rw [← Real.rpow_natCast ((((p : ℕ) : ℝ)) ^ (-(1 / 2 + ε / 2))) 2,
        ← Real.rpow_mul (hppos p).le]
      congr 1
      push_cast
      ring
    calc (Real.sqrt (Real.log ((p : ℕ) : ℝ)) * (((p : ℕ) : ℝ)) ^ (-(1 / 2 + ε / 2)) *
          ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖) ^ 2
        = (Real.sqrt (Real.log ((p : ℕ) : ℝ))) ^ 2 *
            ((((p : ℕ) : ℝ)) ^ (-(1 / 2 + ε / 2))) ^ 2 *
            ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ ^ 2 := by ring
      _ = Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(1 + ε)) *
            ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ ^ 2 := by rw [hsq, hpow]
  have hfg : ∀ p, f p * g p = ‖c p * (Real.log ((p : ℕ) : ℝ) : ℂ) *
      ((((((p : ℕ) : ℝ)) ^ (-(β + ε)) : ℝ)) : ℂ) *
      divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ := by
    intro p
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hlogpos p),
      abs_of_nonneg (Real.rpow_nonneg (hppos p).le _)]
    have hsq : Real.sqrt (Real.log ((p : ℕ) : ℝ)) * Real.sqrt (Real.log ((p : ℕ) : ℝ))
        = Real.log ((p : ℕ) : ℝ) := Real.mul_self_sqrt (hlogpos p)
    have hpow : (((p : ℕ) : ℝ)) ^ (-((β - 1 / 2) + ε / 2)) *
        (((p : ℕ) : ℝ)) ^ (-(1 / 2 + ε / 2)) = (((p : ℕ) : ℝ)) ^ (-(β + ε)) := by
      rw [← Real.rpow_add (hppos p)]
      congr 1
      ring
    rw [hf, hg]
    calc ‖c p‖ * Real.sqrt (Real.log ((p : ℕ) : ℝ)) *
          (((p : ℕ) : ℝ)) ^ (-((β - 1 / 2) + ε / 2)) *
          (Real.sqrt (Real.log ((p : ℕ) : ℝ)) * (((p : ℕ) : ℝ)) ^ (-(1 / 2 + ε / 2)) *
            ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖)
        = ‖c p‖ * (Real.sqrt (Real.log ((p : ℕ) : ℝ)) *
            Real.sqrt (Real.log ((p : ℕ) : ℝ))) *
            ((((p : ℕ) : ℝ)) ^ (-((β - 1 / 2) + ε / 2)) *
              (((p : ℕ) : ℝ)) ^ (-(1 / 2 + ε / 2))) *
            ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ := by ring
      _ = ‖c p‖ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(β + ε)) *
            ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖ := by rw [hsq, hpow]
  have hfsummable : Summable fun p => f p ^ 2 := by
    simpa only [hfsq] using hE
  have hgsummable : Summable fun p => g p ^ 2 := by
    simpa only [hgsq] using summable_divisorTestEnergyTerm m γ hε
  have hcs := deningerTsum_mul_le_sqrt hfsummable hgsummable hfn hgn
  have hnormK : ‖primeDivisorCurrent c m γ β ε‖ ≤ ∑' p, f p * g p := by
    rw [primeDivisorCurrent_eq_tsum c m γ hε hconv]
    refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq (tsum_congr fun p => (hfg p).symm))
    have hre : β < ((((β + ε : ℝ)) : ℂ)).re := by simp; linarith
    have hbase := hconv _ hre
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
      (hbase.mul_left (∑ j, |m j|))
    have hsplit : ((((((p : ℕ) : ℝ)) ^ (-(β + ε)) : ℝ)) : ℂ)
        = (((p : ℕ) : ℂ)) ^ (-((((β + ε : ℝ)) : ℂ))) := by
      rw [Complex.ofReal_cpow (hppos p).le]
      push_cast
      ring_nf
    rw [hsplit, norm_mul]
    have hphase := norm_divisorPhase_le m γ (Real.log ((p : ℕ) : ℝ))
    calc ‖c p * (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ)) ^ (-((((β + ε : ℝ)) : ℂ)))‖ *
          ‖divisorPhase m γ (Real.log ((p : ℕ) : ℝ))‖
        ≤ ‖c p * (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ)) ^ (-((((β + ε : ℝ)) : ℂ)))‖ *
            (∑ j, |m j|) := mul_le_mul_of_nonneg_left hphase (norm_nonneg _)
      _ = (∑ j, |m j|) *
            ‖c p * (Real.log ((p : ℕ) : ℝ) : ℂ) *
              (((p : ℕ) : ℂ)) ^ (-((((β + ε : ℝ)) : ℂ)))‖ := by ring
  have hEeq : ∑' p, f p ^ 2 = primeTraceEnergyReal c (2 * (β - 1 / 2) + ε) := by
    rw [primeTraceEnergyReal]
    exact tsum_congr hfsq
  have hBeq : ∑' p, g p ^ 2 = divisorTestEnergy m γ ε := by
    rw [divisorTestEnergy]
    exact tsum_congr hgsq
  rw [hEeq, hBeq] at hcs
  have hchain := le_trans hnormK hcs
  have hEnn : 0 ≤ primeTraceEnergyReal c (2 * (β - 1 / 2) + ε) := by
    rw [← hEeq]
    exact tsum_nonneg fun p => sq_nonneg _
  have hBnn : 0 ≤ divisorTestEnergy m γ ε := by
    rw [← hBeq]
    exact tsum_nonneg fun p => sq_nonneg _
  calc ‖primeDivisorCurrent c m γ β ε‖ ^ 2
      ≤ (Real.sqrt (primeTraceEnergyReal c (2 * (β - 1 / 2) + ε)) *
          Real.sqrt (divisorTestEnergy m γ ε)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hchain 2
    _ = primeTraceEnergyReal c (2 * (β - 1 / 2) + ε) * divisorTestEnergy m γ ε := by
        rw [mul_pow, Real.sq_sqrt hEnn, Real.sq_sqrt hBnn]

/-! ## The critical energy budget -/

/-- **Prime-trace critical energy bounds the off-line divisor budget.**  If the prime-trace source
has residue `-m_j` at each of finitely many distinct ordinates on the abscissa `β`, then the
unnormalized critical energy has residue at least the squared multiplicity mass.  A divergent
energy satisfies the bound vacuously, which is the hypothesis-free reading of the summability
premise. -/
theorem primeTraceCriticalEnergyBudget (c : Nat.Primes → ℂ) {J : ℕ} (m γ : Fin J → ℝ)
    {β : ℝ} (hγ : Function.Injective γ)
    (hconv : ∀ s : ℂ, β < s.re →
      Summable fun p : Nat.Primes => ‖c p * (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ)) ^ (-s)‖)
    (hres : ∀ j : Fin J, Tendsto (fun ε : ℝ => (ε : ℂ) *
      primeTraceSource c ((((β + ε : ℝ)) : ℂ) + ((γ j : ℝ) : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(m j : ℂ))))
    (hM : 0 < ∑ j, (m j) ^ 2) :
    ∀ r : ℝ, r < ∑ j, (m j) ^ 2 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (Summable fun p : Nat.Primes =>
        ‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(2 * (β - 1 / 2) + ε))) →
        r ≤ ε * primeTraceEnergyReal c (2 * (β - 1 / 2) + ε) := by
  intro r hr
  set M : ℝ := ∑ j, (m j) ^ 2 with hMdef
  have hcur : Tendsto (fun ε : ℝ => (ε : ℂ) * primeDivisorCurrent c m γ β ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (-((M : ℝ) : ℂ))) := by
    have hsum : Tendsto (fun ε : ℝ => ∑ j, (m j : ℂ) * ((ε : ℂ) *
        primeTraceSource c ((((β + ε : ℝ)) : ℂ) + ((γ j : ℝ) : ℂ) * Complex.I)))
        (𝓝[>] (0 : ℝ)) (𝓝 (∑ j, (m j : ℂ) * (-(m j : ℂ)))) :=
      tendsto_finsetSum _ fun j _ => (hres j).const_mul _
    have hval : (∑ j, (m j : ℂ) * (-(m j : ℂ))) = -((M : ℝ) : ℂ) := by
      rw [hMdef]
      push_cast
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hval] at hsum
    refine hsum.congr fun ε => ?_
    rw [primeDivisorCurrent, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hnormK : Tendsto (fun ε : ℝ => ε * ‖primeDivisorCurrent c m γ β ε‖)
      (𝓝[>] (0 : ℝ)) (𝓝 M) := by
    have hn := (continuous_norm.tendsto _).comp hcur
    have hval : ‖(-((M : ℝ) : ℂ))‖ = M := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
    rw [hval] at hn
    refine hn.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : (0 : ℝ) < ε := hε
    simp only [Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hεpos]
  have hB := tendsto_mul_divisorTestEnergy m γ hγ
  rw [← hMdef] at hB
  have hquot : Tendsto (fun ε : ℝ =>
      (ε * ‖primeDivisorCurrent c m γ β ε‖) ^ 2 / (ε * divisorTestEnergy m γ ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (M ^ 2 / M)) := (hnormK.pow 2).div hB hM.ne'
  have hMM : M ^ 2 / M = M := by
    field_simp
  rw [hMM] at hquot
  have hgt : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      r < (ε * ‖primeDivisorCurrent c m γ β ε‖) ^ 2 / (ε * divisorTestEnergy m γ ε) :=
    hquot.eventually (eventually_gt_nhds hr)
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε * divisorTestEnergy m γ ε :=
    hB.eventually (eventually_gt_nhds hM)
  filter_upwards [hgt, hpos, self_mem_nhdsWithin] with ε hgtε hposε hε hsum
  have hεpos : (0 : ℝ) < ε := hε
  have hcs := norm_primeDivisorCurrent_sq_le c m γ hεpos hconv hsum
  have hkey : (ε * ‖primeDivisorCurrent c m γ β ε‖) ^ 2
      ≤ (ε * primeTraceEnergyReal c (2 * (β - 1 / 2) + ε)) * (ε * divisorTestEnergy m γ ε) := by
    calc (ε * ‖primeDivisorCurrent c m γ β ε‖) ^ 2
        = ε ^ 2 * ‖primeDivisorCurrent c m γ β ε‖ ^ 2 := by ring
      _ ≤ ε ^ 2 * (primeTraceEnergyReal c (2 * (β - 1 / 2) + ε) * divisorTestEnergy m γ ε) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (ε * primeTraceEnergyReal c (2 * (β - 1 / 2) + ε)) * (ε * divisorTestEnergy m γ ε) := by
          ring
  have hdiv : (ε * ‖primeDivisorCurrent c m γ β ε‖) ^ 2 / (ε * divisorTestEnergy m γ ε)
      ≤ ε * primeTraceEnergyReal c (2 * (β - 1 / 2) + ε) :=
    (div_le_iff₀ hposε).mpr hkey
  linarith

/-- The unnormalized critical prime-trace energy as an extended nonnegative real:  a divergent
energy is `⊤`. -/
noncomputable def primeTraceEnergy (c : Nat.Primes → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∑' p : Nat.Primes,
    ENNReal.ofReal (‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-t))

theorem primeTraceEnergy_nonneg_term (c : Nat.Primes → ℂ) (t : ℝ) (p : Nat.Primes) :
    0 ≤ ‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-t) := by
  have h1 : (0 : ℝ) ≤ Real.log ((p : ℕ) : ℝ) := Real.log_natCast_nonneg _
  positivity

theorem primeTraceEnergy_eq_top_of_not_summable (c : Nat.Primes → ℂ) (t : ℝ)
    (h : ¬ Summable fun p : Nat.Primes =>
      ‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-t)) :
    primeTraceEnergy c t = ⊤ := by
  by_contra hne
  apply h
  have hcoe : ∀ p : Nat.Primes,
      ENNReal.ofReal (‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-t))
        = ((‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) *
            (((p : ℕ) : ℝ)) ^ (-t)).toNNReal : ℝ≥0∞) := fun p => rfl
  have hnn : (∑' p : Nat.Primes,
      (((‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-t)).toNNReal : ℝ≥0)
        : ℝ≥0∞)) ≠ ⊤ := by
    rw [← tsum_congr hcoe]
    exact hne
  have hsum := ENNReal.tsum_coe_ne_top_iff_summable.mp hnn
  have hreal := NNReal.summable_coe.mpr hsum
  refine hreal.congr fun p => ?_
  exact Real.coe_toNNReal _ (primeTraceEnergy_nonneg_term c t p)

/-- **The critical energy budget, hypothesis-free in the energy.**  With a divergent energy read
as `⊤`, the residue of the unnormalized critical energy is at least the squared multiplicity
mass. -/
theorem primeTraceCriticalEnergyBudget_extended (c : Nat.Primes → ℂ) {J : ℕ} (m γ : Fin J → ℝ)
    {β : ℝ} (hγ : Function.Injective γ)
    (hconv : ∀ s : ℂ, β < s.re →
      Summable fun p : Nat.Primes => ‖c p * (Real.log ((p : ℕ) : ℝ) : ℂ) * (((p : ℕ) : ℂ)) ^ (-s)‖)
    (hres : ∀ j : Fin J, Tendsto (fun ε : ℝ => (ε : ℂ) *
      primeTraceSource c ((((β + ε : ℝ)) : ℂ) + ((γ j : ℝ) : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(m j : ℂ))))
    (hM : 0 < ∑ j, (m j) ^ 2) :
    ∀ r : ℝ, r < ∑ j, (m j) ^ 2 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal r ≤ ENNReal.ofReal ε * primeTraceEnergy c (2 * (β - 1 / 2) + ε) := by
  intro r hr
  filter_upwards [primeTraceCriticalEnergyBudget c m γ hγ hconv hres hM r hr,
    self_mem_nhdsWithin] with ε hbound hε
  have hεpos : (0 : ℝ) < ε := hε
  by_cases hsum : Summable fun p : Nat.Primes =>
      ‖c p‖ ^ 2 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)) ^ (-(2 * (β - 1 / 2) + ε))
  · have henergy : primeTraceEnergy c (2 * (β - 1 / 2) + ε)
        = ENNReal.ofReal (primeTraceEnergyReal c (2 * (β - 1 / 2) + ε)) := by
      rw [primeTraceEnergy, primeTraceEnergyReal,
        ENNReal.ofReal_tsum_of_nonneg
          (fun p => primeTraceEnergy_nonneg_term c (2 * (β - 1 / 2) + ε) p) hsum]
    rw [henergy, ← ENNReal.ofReal_mul hεpos.le]
    exact ENNReal.ofReal_le_ofReal (hbound hsum)
  · rw [primeTraceEnergy_eq_top_of_not_summable c _ hsum,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hεpos).ne']
    exact le_top

end RHTower
