import GaloisForLFunctions.EllipticThetaLogGlobalAnalytic
import GaloisForLFunctions.JacobiThetaParallelogramCharge
import GaloisForLFunctions.MeromorphicNormalizedRemovable
import GaloisForLFunctions.MeromorphicOrderLocalPeriod

/-!
# Constraint comparison with analytic Jacobi theta

The constructed theta-product logarithmic kernel and mathlib's analytic Jacobi-theta logarithmic
derivative obey the same additive constraints. Their difference is therefore periodic in both
`1` and `τ` on the common regular locus. The remaining comparison theorem is reduced to a divisor
statement: once this discrepancy is shown to have no poles, compact ellipticity makes it constant,
and every translated defect agrees without any normalization constant.
-/

open Complex Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-- Discrepancy between the constructed product boundary and the analytic theta logarithmic
derivative in the aligned additive coordinate. -/
def ellipticThetaLogComparison (τ z : ℂ) : ℂ :=
  ellipticThetaAdditiveLogKernel τ z - thetaLogDeriv z τ

/-- The constructed-versus-analytic discrepancy is globally meromorphic. -/
theorem meromorphicOn_ellipticThetaLogComparison {τ : ℂ} (hτ : 0 < τ.im) :
    MeromorphicOn (ellipticThetaLogComparison τ) Set.univ := by
  intro z _
  have hconstructed := meromorphicOn_ellipticThetaAdditiveLogKernel hτ z (Set.mem_univ z)
  have hanalytic : MeromorphicAt (thetaLogDeriv · τ) z := by
    exact ((jacobiTheta₂'_analyticOnNhd_fst τ hτ) z (Set.mem_univ z)).meromorphicAt.div
      ((jacobiTheta₂_analyticOnNhd_fst τ hτ) z (Set.mem_univ z)).meromorphicAt
  exact hconstructed.sub hanalytic

/-- The comparison discrepancy is period-one. -/
theorem ellipticThetaLogComparison_add_one (τ z : ℂ) :
    ellipticThetaLogComparison τ (z + 1) = ellipticThetaLogComparison τ z := by
  rw [ellipticThetaLogComparison, ellipticThetaLogComparison,
    ellipticThetaAdditiveLogKernel_add_one, thetaLogDeriv_add_one]

/-- On the common regular locus, the two identical quasiperiod increments cancel, so the
comparison discrepancy is `τ`-periodic. -/
theorem ellipticThetaLogComparison_add_tau
    {τ z : ℂ} (hτ : 0 < τ.im) (hcoord : ellipticThetaCoordinate τ z ≠ 1)
    (htheta : jacobiTheta₂ z τ ≠ 0) :
    ellipticThetaLogComparison τ (z + τ) = ellipticThetaLogComparison τ z := by
  have hconstructed := ellipticThetaAdditiveLogKernel_add_tau_sub hτ hcoord
  have hanalytic := thetaLogDeriv_add_tau htheta
  rw [ellipticThetaLogComparison, ellipticThetaLogComparison, hanalytic]
  linear_combination hconstructed

/-- The constructed and analytic theta logarithmic kernels have the same normalized principal
part at the odd half-period; their comparison discrepancy has vanishing residue there. -/
theorem tendsto_ellipticThetaLogComparison_normalized_halfPeriod
    {τ : ℂ} (hτ : 0 < τ.im) :
    Tendsto
      (fun z : ℂ => (z - thetaHalfPeriod τ) * ellipticThetaLogComparison τ z)
      (𝓝[≠] thetaHalfPeriod τ) (𝓝 0) := by
  have hconstructed := tendsto_ellipticThetaAdditiveLogKernel_normalized_halfPeriod hτ
  have hanalytic : Tendsto
      (fun z : ℂ => (z - thetaHalfPeriod τ) * thetaLogDeriv z τ)
      (𝓝[≠] thetaHalfPeriod τ) (𝓝 1) := by
    simpa [thetaLogDeriv] using tendsto_thetaLogDeriv_normalized_halfPeriod hτ
  simpa [ellipticThetaLogComparison, mul_sub] using hconstructed.sub hanalytic

/-- The comparison discrepancy has no pole at the distinguished odd half-period. -/
theorem meromorphicOrderAt_ellipticThetaLogComparison_halfPeriod_nonneg
    {τ : ℂ} (hτ : 0 < τ.im) :
    0 ≤ meromorphicOrderAt (ellipticThetaLogComparison τ) (thetaHalfPeriod τ) := by
  apply meromorphicOrderAt_nonneg_of_tendsto_mul_sub_zero
  · exact meromorphicOn_ellipticThetaLogComparison hτ _ (Set.mem_univ _)
  · exact tendsto_ellipticThetaLogComparison_normalized_halfPeriod hτ

/-- Near every odd-half-period lattice point, the comparison discrepancy is `τ`-periodic on the
punctured neighborhood. Both regularity side conditions follow from the nonzero derivatives of
theta and of the exponential coordinate. -/
theorem ellipticThetaLogComparison_eventually_add_tau_eq_lattice
    {τ : ℂ} (hτ : 0 < τ.im) (m n : ℤ) :
    let p := thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ
    ∀ᶠ z in 𝓝[≠] p,
      ellipticThetaLogComparison τ (z + τ) = ellipticThetaLogComparison τ z := by
  let p := thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ
  have htheta0 : jacobiTheta₂ p τ = 0 :=
    jacobiTheta₂_thetaHalfPeriod_add_lattice_eq_zero τ m n
  have hthetaPrime : jacobiTheta₂' p τ ≠ 0 :=
    jacobiTheta₂'_thetaHalfPeriod_add_lattice_ne_zero hτ m n
  have hthetaDeriv : HasDerivAt (jacobiTheta₂ · τ) (jacobiTheta₂' p τ) p :=
    hasDerivAt_jacobiTheta₂_fst p hτ
  have hthetaMap := hthetaDeriv.tendsto_nhdsNE hthetaPrime
  have htheta : ∀ᶠ z in 𝓝[≠] p, jacobiTheta₂ z τ ≠ 0 := by
    simpa only [htheta0, Set.mem_singleton_iff] using
      hthetaMap.eventually self_mem_nhdsWithin
  have hcoordDeriv := hasDerivAt_ellipticThetaCoordinate τ p
  have hcoordValue : ellipticThetaCoordinate τ p ≠ 0 :=
    ellipticThetaCoordinate_ne_zero τ p
  have hcoordDerivNe :
      (2 * Real.pi * I * ellipticThetaCoordinate τ p : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (mod_cast Real.pi_ne_zero)) I_ne_zero) hcoordValue
  have hcoordMap := hcoordDeriv.tendsto_nhdsNE hcoordDerivNe
  have hcoord : ∀ᶠ z in 𝓝[≠] p, ellipticThetaCoordinate τ z ≠ 1 := by
    by_cases hp1 : ellipticThetaCoordinate τ p = 1
    · simpa only [hp1, Set.mem_singleton_iff] using
        hcoordMap.eventually self_mem_nhdsWithin
    · exact (hcoordDeriv.continuousAt.eventually_ne hp1).filter_mono inf_le_left
  filter_upwards [htheta, hcoord] with z hztheta hzcoord
  exact ellipticThetaLogComparison_add_tau hτ hzcoord hztheta

/-- Meromorphic order of the comparison discrepancy is invariant under one `τ`-step at every
odd-half-period lattice point. -/
theorem meromorphicOrderAt_ellipticThetaLogComparison_add_tau_lattice
    {τ : ℂ} (hτ : 0 < τ.im) (m n : ℤ) :
    let p := thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ
    meromorphicOrderAt (ellipticThetaLogComparison τ) (p + τ) =
      meromorphicOrderAt (ellipticThetaLogComparison τ) p := by
  apply meromorphicOrderAt_add_eq_of_eventually_periodic
  exact ellipticThetaLogComparison_eventually_add_tau_eq_lattice hτ m n

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Meromorphic order of the comparison discrepancy is constant along the full integer
`τ`-orbit of the distinguished odd half-period. -/
theorem meromorphicOrderAt_ellipticThetaLogComparison_tau_int
    {τ : ℂ} (hτ : 0 < τ.im) (n : ℤ) :
    meromorphicOrderAt (ellipticThetaLogComparison τ)
        (thetaHalfPeriod τ + (n : ℂ) * τ) =
      meromorphicOrderAt (ellipticThetaLogComparison τ) (thetaHalfPeriod τ) := by
  let O : ℤ → WithTop ℤ := fun k =>
    meromorphicOrderAt (ellipticThetaLogComparison τ)
      (thetaHalfPeriod τ + (k : ℂ) * τ)
  have hstep (k : ℤ) : O (k + 1) = O k := by
    dsimp [O]
    have h := meromorphicOrderAt_ellipticThetaLogComparison_add_tau_lattice
      hτ 0 k
    rw [show thetaHalfPeriod τ + (((k + 1 : ℤ) : ℂ)) * τ =
        (thetaHalfPeriod τ + (0 : ℂ) + (k : ℂ) * τ) + τ by
          push_cast
          ring]
    rw [show thetaHalfPeriod τ + (k : ℂ) * τ =
        thetaHalfPeriod τ + (0 : ℂ) + (k : ℂ) * τ by ring]
    simpa only [Int.cast_zero] using h
  change O n = meromorphicOrderAt (ellipticThetaLogComparison τ) (thetaHalfPeriod τ)
  induction n using Int.induction_on with
  | zero => simp [O]
  | succ i ih =>
      exact (hstep (i : ℤ)).trans ih
  | pred i ih =>
      have hs := hstep (-((i : ℤ)) - 1)
      have hind : (-((i : ℤ)) - 1) + 1 = -((i : ℤ)) := by omega
      rw [hind] at hs
      exact hs.symm.trans ih

/-- The constructed-versus-analytic theta discrepancy has no pole at any odd-half-period
lattice point. Thus cancellation of the distinguished principal part propagates across the
entire theta divisor without a product formula for the analytic kernel. -/
theorem meromorphicOrderAt_ellipticThetaLogComparison_lattice_nonneg
    {τ : ℂ} (hτ : 0 < τ.im) (m n : ℤ) :
    0 ≤ meromorphicOrderAt (ellipticThetaLogComparison τ)
      (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) := by
  have hperOne : Function.Periodic (ellipticThetaLogComparison τ) 1 :=
    ellipticThetaLogComparison_add_one τ
  have hperM : Function.Periodic (ellipticThetaLogComparison τ) (m : ℂ) := by
    simpa using hperOne.int_mul m
  have horderM := meromorphicOrderAt_add_period
    (ellipticThetaLogComparison τ) (m : ℂ)
      (thetaHalfPeriod τ + (n : ℂ) * τ) hperM
  rw [show thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ =
      (thetaHalfPeriod τ + (n : ℂ) * τ) + (m : ℂ) by ring]
  rw [horderM, meromorphicOrderAt_ellipticThetaLogComparison_tau_int hτ n]
  exact meromorphicOrderAt_ellipticThetaLogComparison_halfPeriod_nonneg hτ

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- The constructed additive theta logarithmic kernel is analytic exactly where the analytic
Jacobi theta denominator is nonzero. The exact divisor-coordinate bridge converts theta
nonvanishing into avoidance of the full multiplicative nome orbit. -/
theorem analyticAt_ellipticThetaAdditiveLogKernel_of_jacobiTheta₂_ne
    {τ z : ℂ} (hτ : 0 < τ.im) (hz : jacobiTheta₂ z τ ≠ 0) :
    AnalyticAt ℂ (ellipticThetaAdditiveLogKernel τ) z := by
  have hfree : ∀ N : ℤ, ellipticThetaCoordinate τ z ≠ ellipticNome τ ^ N := by
    intro N hN
    apply hz
    exact (ellipticThetaCoordinate_mem_nomeOrbit_iff_jacobiTheta₂_zero hτ).mp ⟨N, hN⟩
  have hkernel := analyticAt_ellipticThetaLogKernel_of_nomeOrbitFree
    (ellipticNome_ne_zero τ) (norm_ellipticNome_lt_one hτ)
      (ellipticThetaCoordinate_ne_zero τ z) hfree
  have hcomp := hkernel.comp (analyticAt_ellipticThetaCoordinate τ z)
  have hc : AnalyticAt ℂ (fun _ : ℂ => (2 * Real.pi * I : ℂ)) z := analyticAt_const
  simpa [ellipticThetaAdditiveLogKernel, Function.comp_def] using hc.mul hcomp

/-- Away from the theta divisor, both logarithmic kernels are analytic, hence so is their
comparison discrepancy. -/
theorem analyticAt_ellipticThetaLogComparison_of_jacobiTheta₂_ne
    {τ z : ℂ} (hτ : 0 < τ.im) (hz : jacobiTheta₂ z τ ≠ 0) :
    AnalyticAt ℂ (ellipticThetaLogComparison τ) z := by
  have hconstructed :=
    analyticAt_ellipticThetaAdditiveLogKernel_of_jacobiTheta₂_ne hτ hz
  have hnum := (jacobiTheta₂'_analyticOnNhd_fst τ hτ) z (Set.mem_univ z)
  have hden := (jacobiTheta₂_analyticOnNhd_fst τ hτ) z (Set.mem_univ z)
  have hanalytic : AnalyticAt ℂ (thetaLogDeriv · τ) z := by
    simpa [thetaLogDeriv] using hnum.div hden hz
  exact hconstructed.sub hanalytic

/-- The constructed-versus-analytic theta discrepancy has no poles anywhere. On the theta divisor
this follows by lattice transport of the cancelled principal part; off the divisor it follows from
global analyticity of both kernels. -/
theorem meromorphicOrderAt_ellipticThetaLogComparison_nonneg
    {τ z : ℂ} (hτ : 0 < τ.im) :
    0 ≤ meromorphicOrderAt (ellipticThetaLogComparison τ) z := by
  by_cases hz : jacobiTheta₂ z τ = 0
  · rw [jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ] at hz
    obtain ⟨m, n, rfl⟩ := hz
    exact meromorphicOrderAt_ellipticThetaLogComparison_lattice_nonneg hτ m n
  · exact (analyticAt_ellipticThetaLogComparison_of_jacobiTheta₂_ne
      hτ hz).meromorphicOrderAt_nonneg

end

end GaloisForLFunctions
