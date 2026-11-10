import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ExponentialPrimePhase
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeLogarithmRenormalization

/-!
# The first moving branch of exponentially damped Liouville phases

Separating the first phase term exposes a shifted prime logarithm.
Its singularity at `s=1-t` has exponent `iπ`; the remaining factor
is analytic and nonzero for sufficiently small positive `t`.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The analytic exponent left after removing the first moving branch. -/
def exponentialPhaseBranchExponent (t : ℝ) (s : ℂ) : ℂ :=
  -(Real.pi : ℂ) * I * primeLogRegularPart (s + (t : ℂ)) +
    exponentialPhasePrimeRemainder t s + hullRem s (twist (exponentialPhaseGauge t)) -
      hullRem s (twist 0)

/-- The nonvanishing factor accompanying the first moving branch. -/
def exponentialPhaseBranchUnit (t : ℝ) (s : ℂ) : ℂ :=
  zetaResidueFactor s * Complex.exp (exponentialPhaseBranchExponent t s)


private theorem prime_decay_eq (p : Nat.Primes) (s : ℂ) :
    Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) = (p : ℂ) ^ (-s) := by
  simpa only [primeFrequency, neg_mul] using prime_cexp_decay p s

private theorem summable_exponentialPhase_prime_terms {t : ℝ} {s : ℂ}
    (hs : 1 < s.re + t) :
    Summable (fun p : Nat.Primes => (twist (exponentialPhaseGauge t) p - 1) *
      (p : ℂ) ^ (-s)) := by
  apply Summable.of_norm
  convert exponentialPhase_prime_summability hs using 1
  funext p
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]

/-- The canonical logarithm is the sum of its first-prime part and higher-power remainders. -/
theorem jointExponent_exponentialPhase_eq {t : ℝ} {s : ℂ}
    (hs : 1 < s.re + t) (hhalf : 1 / 2 < s.re) :
    jointDeformationExponent exponentialPrimePhase ((t : ℂ), s) =
      deformationExponent (exponentialPhaseGauge t) s := by
  have hp := summable_exponentialPhase_prime_terms hs
  have hx := summable_localRem (s := s) (norm_twist_prime (exponentialPhaseGauge t)) hhalf
  have h0 := summable_localRem (s := s) (norm_twist_prime 0) hhalf
  rw [jointDeformationExponent, deformationExponent, deformationPrimeSum, hullRem, hullRem,
    ← hp.tsum_add hx, ← (hp.add hx).tsum_sub h0]
  apply tsum_congr
  intro p
  simp only [jointEulerChange, prime_cexp_decay, exponentialPrimePhase_eq_twist,
    localRem, eulerVar, powCoeff, twist_trivial, mul_one]
  rw [mul_comm ((p : ℂ) ^ (-s)) (twist (exponentialPhaseGauge t) p)]
  ring

/-- The sole first shifted prime logarithm has coefficient `-iπ`. -/
theorem deformationPrimeSum_exponentialPhase_split {t : ℝ} (ht : 0 ≤ t) {s : ℂ}
    (hs : 1 < s.re + t) :
    deformationPrimeSum (exponentialPhaseGauge t) s =
      -(Real.pi : ℂ) * I * coronaPrimeZeta (s + (t : ℂ)) +
        exponentialPhasePrimeRemainder t s := by
  have hst : 1 < (s + (t : ℂ)).re := by simpa only [Complex.add_re, Complex.ofReal_re] using hs
  have hf := (summable_coronaPrimeEigenvalue hst).mul_left (-(Real.pi : ℂ) * I)
  have hr := summable_exponentialPhasePrimeRemainder ht (s := s)
    (by linarith only [hs, ht])
  rw [deformationPrimeSum, exponentialPhasePrimeRemainder, coronaPrimeZeta,
    ← tsum_mul_left, ← hf.tsum_add hr]
  apply tsum_congr
  intro p
  rw [← exponentialPrimePhase_eq_twist]
  simp only [coronaPrimeEigenvalue]
  rw [← prime_decay_eq p s, ← prime_decay_eq p (s + (t : ℂ))]
  rw [show -(s + (t : ℂ)) * (Real.log (p : ℝ) : ℂ) =
    -(t : ℂ) * (Real.log (p : ℝ) : ℂ) + -s * (Real.log (p : ℝ) : ℂ) by ring,
    Complex.exp_add]
  ring

/-- The branch exponent is analytic at its moving singularity. -/
theorem analyticAt_exponentialPhaseBranchExponent {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    AnalyticAt ℂ (exponentialPhaseBranchExponent t) (1 - (t : ℂ)) := by
  have hreg : AnalyticAt ℂ primeLogRegularPart ((1 - (t : ℂ)) + (t : ℂ)) := by
    simpa only [sub_add_cancel] using analyticAt_primeLogRegularPart_one
  have hshift : AnalyticAt ℂ (fun s : ℂ => s + (t : ℂ)) (1 - (t : ℂ)) :=
    analyticAt_id.add analyticAt_const
  have hhalf : (1 : ℂ) - (t : ℂ) ∈ PrimeTorusTheory.rightHalf := by
    change 1 / 2 < (1 : ℂ).re - (t : ℂ).re
    simp only [Complex.one_re, Complex.ofReal_re]
    linarith only [ht2]
  have hr := analyticOnNhd_exponentialPhasePrimeRemainder ht.le (1 - (t : ℂ))
    (by change 1 < (1 : ℂ).re - (t : ℂ).re + 2 * t
        simp only [Complex.one_re, Complex.ofReal_re]
        linarith only [ht])
  exact (((analyticAt_const.mul (hreg.comp (f := fun z : ℂ => z + (t : ℂ)) hshift)).add hr).add
    (analyticOnNhd_hullRem (norm_twist_prime (exponentialPhaseGauge t)) _ hhalf)).sub
      (analyticOnNhd_hullRem (norm_twist_prime 0) _ hhalf)

theorem analyticAt_exponentialPhaseBranchUnit {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    AnalyticAt ℂ (exponentialPhaseBranchUnit t) (1 - (t : ℂ)) :=
  (differentiable_zetaResidueFactor.analyticAt _).mul
    (analyticAt_exponentialPhaseBranchExponent ht ht2).cexp


/-- One spectral radius works for the exact moving-branch factorization. -/
theorem exponentialPhase_moving_branch_factorization :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 ≤ t → ∀ s : ℂ,
      ‖s - (1 - (t : ℂ))‖ < r → 1 < s.re + t → 1 / 2 < s.re →
        jointGaugeRegularization exponentialPrimePhase ((t : ℂ), s) =
          exponentialPhaseBranchUnit t s *
            Complex.exp ((Real.pi : ℂ) * I * Complex.log (s - (1 - (t : ℂ)))) := by
  obtain ⟨r, hr, _, hprime⟩ := exists_primeLogRegularPart_germ
  refine ⟨r, hr, ?_⟩
  intro t ht s hsr hs hhalf
  have harg : s + (t : ℂ) - 1 = s - (1 - (t : ℂ)) := by ring
  have hball : s + (t : ℂ) ∈ ball 1 r := by
    simpa only [mem_ball, dist_eq_norm, harg] using hsr
  have hp := hprime (s + (t : ℂ)) hball
    (by simpa only [Complex.add_re, Complex.ofReal_re] using hs)
  have hH : deformationExponent (exponentialPhaseGauge t) s =
      exponentialPhaseBranchExponent t s +
        (Real.pi : ℂ) * I * Complex.log (s - (1 - (t : ℂ))) := by
    rw [deformationExponent, deformationPrimeSum_exponentialPhase_split ht hs,
      exponentialPhaseBranchExponent]
    rw [harg] at hp
    linear_combination -(Real.pi : ℂ) * I * hp
  rw [jointGaugeRegularization, jointExponent_exponentialPhase_eq hs hhalf, hH,
    Complex.exp_add, exponentialPhaseBranchUnit]
  ring


/-- For small positive parameters the branch factor is an analytic unit. -/
theorem exponentialPhase_moving_branch_unit :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 < t → t < T →
      AnalyticAt ℂ (exponentialPhaseBranchUnit t) (1 - (t : ℂ)) ∧
        exponentialPhaseBranchUnit t (1 - (t : ℂ)) ≠ 0 := by
  have hZ : ∀ᶠ s in 𝓝 (1 : ℂ), zetaResidueFactor s ≠ 0 :=
    (differentiable_zetaResidueFactor.continuous.continuousAt).eventually_ne
      (by rw [zetaResidueFactor_one]; exact one_ne_zero)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hZ
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num), ?_⟩
  intro t ht htT
  have htε : t < ε := lt_of_lt_of_le htT (min_le_left _ _)
  have ht2 : t < 1 / 2 := lt_of_lt_of_le htT (min_le_right _ _)
  refine ⟨analyticAt_exponentialPhaseBranchUnit ht ht2, ?_⟩
  have hdist : dist (1 - (t : ℂ)) 1 < ε := by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    exact htε
  exact mul_ne_zero (hb hdist) (Complex.exp_ne_zero _)


private def branchApproach (b : ℝ) (n : ℕ) : ℝ := Real.exp (-(2 * (n : ℝ)) - b)

private theorem tendsto_branchApproach (b : ℝ) :
    Tendsto (branchApproach b) atTop (𝓝[>] (0 : ℝ)) := by
  have hn : Tendsto (fun n : ℕ => -(2 * (n : ℝ))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      tendsto_natCast_atTop_atTop)
  have he := (Real.tendsto_exp_atBot.comp hn).mul_const (Real.exp (-b))
  have hzero : Tendsto (branchApproach b) atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun n : ℕ => Real.exp (-(2 * (n : ℝ)) - b)) atTop (𝓝 (0 : ℝ))
    simpa only [branchApproach, Function.comp_apply, sub_eq_add_neg, Real.exp_add, zero_mul] using he
  refine tendsto_nhdsWithin_iff.mpr ⟨hzero, ?_⟩
  exact Eventually.of_forall (fun n => Real.exp_pos _)

private theorem exp_log_branchApproach (b : ℝ) (n : ℕ) :
    Complex.exp ((Real.pi : ℂ) * I * Complex.log ((branchApproach b n : ℝ) : ℂ)) =
      Complex.exp (-(Real.pi : ℂ) * I * (b : ℂ)) := by
  rw [branchApproach, ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  have hex : (Real.pi : ℂ) * I * ((-(2 * (n : ℝ)) - b : ℝ) : ℂ) =
      (n : ℂ) * (-(2 * (Real.pi : ℂ) * I)) + (-(Real.pi : ℂ) * I * (b : ℂ)) := by
    push_cast
    ring
  rw [hex, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg,
    Complex.exp_two_pi_mul_I, inv_one, one_pow, one_mul]

/-- A nonzero continuous factor cannot remove the logarithmic phase oscillation. -/
theorem oscillatoryLogBranch_no_continuous_extension {c : ℂ} {A F : ℂ → ℂ}
    (hA : ContinuousAt A c) (hA0 : A c ≠ 0) (hF : ContinuousAt F c)
    (he : ∀ᶠ x : ℝ in 𝓝[>] 0, F (c + (x : ℂ)) =
      A (c + (x : ℂ)) * Complex.exp ((Real.pi : ℂ) * I * Complex.log (x : ℂ))) : False := by
  have hvalue (b : ℝ) : F c = A c * Complex.exp (-(Real.pi : ℂ) * I * (b : ℂ)) := by
    have ht := tendsto_branchApproach b
    have hc : Tendsto (fun n : ℕ => c + ((branchApproach b n : ℝ) : ℂ)) atTop (𝓝 c) := by
      have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp
        (ht.mono_right nhdsWithin_le_nhds)
      simpa only [Function.comp_apply, Complex.ofReal_zero, add_zero] using tendsto_const_nhds.add hcast
    have hleft : Tendsto (fun n => F (c + ((branchApproach b n : ℝ) : ℂ))) atTop (𝓝 (F c)) :=
      hF.tendsto.comp hc
    have hright := (hA.tendsto.comp hc).mul_const
      (Complex.exp (-(Real.pi : ℂ) * I * (b : ℂ)))
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [ht.eventually he] with n hn
    simp only [Function.comp_apply, hn, exp_log_branchApproach]
  have h0 := hvalue 0
  have h1 := hvalue 1
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
  simp only [Complex.ofReal_one, mul_one, neg_mul, Complex.exp_neg_pi_mul_I, mul_neg_one] at h1
  have hz : A c = 0 := by linear_combination (h1 - h0) / 2
  exact hA0 hz

/-- The first moving branch has no continuous extension from its right. -/
theorem exponentialPhase_moving_branch_no_continuous_extension :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 < t → t < T →
      ¬ ∃ F : ℂ → ℂ, ContinuousAt F (1 - (t : ℂ)) ∧
        ∀ᶠ x : ℝ in 𝓝[>] 0,
          F (1 - (t : ℂ) + (x : ℂ)) =
            jointGaugeRegularization exponentialPrimePhase ((t : ℂ), 1 - (t : ℂ) + (x : ℂ)) := by
  obtain ⟨T, hT, hunit⟩ := exponentialPhase_moving_branch_unit
  obtain ⟨r, hr, hfac⟩ := exponentialPhase_moving_branch_factorization
  refine ⟨min T (1 / 2), lt_min hT (by norm_num), ?_⟩
  intro t ht htT
  have htT' : t < T := lt_of_lt_of_le htT (min_le_left _ _)
  have ht2 : t < 1 / 2 := lt_of_lt_of_le htT (min_le_right _ _)
  obtain ⟨ha, hne⟩ := hunit t ht htT'
  rintro ⟨F, hF, he⟩
  apply oscillatoryLogBranch_no_continuous_extension ha.continuousAt hne hF
  filter_upwards [he, self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hr)] with x hx hx0 hxr
  change 0 < x at hx0
  rw [hx, hfac t ht.le]
  · simp only [add_sub_cancel_left]
  · rw [add_sub_cancel_left, norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    exact hxr
  · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [hx0]
  · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [hx0, ht2]


private theorem analyticAt_exponentialPhase_spectral_regularization {t : ℝ} {s : ℂ}
    (hh : 1 / 2 < s.re) (hs : 1 < s.re + t) :
    AnalyticAt ℂ (fun z => zetaResidueFactor z *
      Complex.exp (deformationExponent (exponentialPhaseGauge t) z)) s := by
  have hmax : max (1 / 2) (1 - t) < s.re :=
    max_lt hh (by linarith only [hs])
  obtain ⟨σ, hσ, hσs⟩ := exists_between hmax
  have hσhalf : 1 / 2 < σ := (le_max_left _ _).trans_lt hσ
  have hσt : 1 < σ + t := by
    have h := (le_max_right (1 / 2) (1 - t)).trans_lt hσ
    linarith only [h]
  have hH := (exists_isozeric hσhalf.le (exponentialPhase_prime_summability hσt)).1 s hσs
  exact (differentiable_zetaResidueFactor.analyticAt s).mul hH.cexp

/-- Even real Euler agreement excludes an actual joint endpoint regularization. -/
theorem exponentialPhase_no_joint_endpoint_regularization :
    ¬ ∃ U : ℂ × ℂ → ℂ, AnalyticAt ℂ U (0, 1) ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᶠ σ : ℝ in 𝓝[>] 1,
        U ((t : ℂ), (σ : ℂ)) =
          ((σ : ℂ) - 1) * gaugeFibre (exponentialPhaseGauge t) (σ : ℂ) := by
  rintro ⟨U, hU, hagree⟩
  obtain ⟨R, hR, hUa⟩ := hU.exists_ball_analyticOnNhd
  obtain ⟨T, hT, hno⟩ := exponentialPhase_moving_branch_no_continuous_extension
  have hmin : 0 < min T (min R (1 / 2)) := lt_min hT (lt_min hR (by norm_num))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < min T (min R (1 / 2)) :=
    nhdsWithin_le_nhds (gt_mem_nhds hmin)
  obtain ⟨t, ht, ha, htmax⟩ := (hpos.and (hagree.and hsmall)).exists
  have htT : t < T := lt_of_lt_of_le htmax (min_le_left _ _)
  have htR : t < R := lt_of_lt_of_le htmax ((min_le_right _ _).trans (min_le_left _ _))
  have ht2 : t < 1 / 2 := lt_of_lt_of_le htmax ((min_le_right _ _).trans (min_le_right _ _))
  let F : ℂ → ℂ := fun s => U ((t : ℂ), s)
  let K : ℂ → ℂ := fun s => zetaResidueFactor s *
    Complex.exp (deformationExponent (exponentialPhaseGauge t) s)
  have hFa : AnalyticOnNhd ℂ F (ball 1 R) := by
    intro s hs
    have hq : ((t : ℂ), s) ∈ ball ((0 : ℂ), (1 : ℂ)) R := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨?_, hs⟩
      simpa only [dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos ht] using htR
    exact (hUa _ hq).comp (g := U) (f := fun z : ℂ => ((t : ℂ), z))
      (analyticAt_const.prod analyticAt_id)
  let D : Set ℂ := (ball 1 R ∩ {s | 1 - t < s.re}) ∩ {s | 1 / 2 < s.re}
  have hKa : AnalyticOnNhd ℂ K D := by
    intro s hs
    have hst : 1 - t < s.re := hs.1.2
    exact analyticAt_exponentialPhase_spectral_regularization hs.2 (by linarith only [hst])
  have hFKa : AnalyticOnNhd ℂ F D := hFa.mono (fun s hs => hs.1.1)
  have hD : IsPreconnected D :=
    (((convex_ball (1 : ℂ) R).inter (convex_halfSpace_re_gt (1 - t))).inter
      (convex_halfSpace_re_gt (1 / 2))).isPreconnected
  have h1D : (1 : ℂ) ∈ D := by
    exact ⟨⟨mem_ball_self hR, by change 1 - t < 1; linarith only [ht]⟩, by norm_num⟩
  have he : ∀ᶠ σ : ℝ in 𝓝[>] 1, F (σ : ℂ) = K (σ : ℂ) := by
    filter_upwards [ha, self_mem_nhdsWithin] with σ hσ hσ1
    change 1 < σ at hσ1
    have hse : 1 < (σ : ℂ).re := hσ1
    have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne'
    dsimp [F, K]
    rw [hσ, gaugeFibre_eq_zeta_mul_exp _ hse, zetaResidueFactor_of_ne hs1]
    ring
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [Complex.ofReal_one] using
        (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact fun h => (ne_of_gt hσ) (Complex.ofReal_eq_one.mp h)
  have hid := hFKa.eqOn_of_preconnected_of_frequently_eq hKa hD h1D
    (hmap.frequently he.frequently)
  apply hno t ht htT
  have hs0 : 1 - (t : ℂ) ∈ ball 1 R := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    exact htR
  refine ⟨F, (hFa _ hs0).continuousAt, ?_⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds ht)] with x hx hxt
  change 0 < x at hx
  have hpoint : 1 - (t : ℂ) + (x : ℂ) ∈ D := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, dist_eq_norm]
      have heq : 1 - (t : ℂ) + (x : ℂ) - 1 = ((x - t : ℝ) : ℂ) := by push_cast; ring
      rw [heq, norm_real, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hxt)]
      linarith only [hx, htR]
    · simp only [mem_setOf_eq, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith only [hx]
    · simp only [mem_setOf_eq, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith only [hx, ht2]
  rw [hid hpoint, jointGaugeRegularization,
    jointExponent_exponentialPhase_eq (by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith only [hx]) hpoint.2]

#print axioms exponentialPhase_moving_branch_factorization
#print axioms exponentialPhase_moving_branch_unit
#print axioms exponentialPhase_moving_branch_no_continuous_extension
#print axioms exponentialPhase_no_joint_endpoint_regularization

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
