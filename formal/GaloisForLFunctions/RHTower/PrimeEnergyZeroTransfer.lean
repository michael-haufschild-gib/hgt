import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import GaloisForLFunctions.RHTower.FinitePrimeBoundaryTransfer
import Mathlib.Analysis.Complex.TaylorSeries

open Complex Metric Set Filter Topology

namespace RHTower

/-- The canonical degree-`< n` Cauchy--Taylor approximant to `XiC` at the origin.
This definition is source-side: it uses the Cauchy power series of the entire function, not its
zero divisor. -/
noncomputable def xiCTaylorApprox (n : ℕ) (z : ℂ) : ℂ :=
  (cauchyPowerSeries XiC 0 1).partialSum n z

/-- The canonical Taylor approximants converge locally uniformly to `XiC` on the whole plane. -/
theorem xiCTaylorApprox_tendstoLocallyUniformly :
    TendstoLocallyUniformly xiCTaylorApprox XiC atTop := by
  have hpow := (analyticOnNhd_univ_iff_differentiable.mp XiC_analytic).hasFPowerSeriesOnBall
    0 (R := 1) (by norm_num)
  have hconv := hpow.tendstoLocallyUniformlyOn'
  rw [Metric.eball_top] at hconv
  rw [← tendstoLocallyUniformlyOn_univ]
  simpa only [xiCTaylorApprox, sub_zero] using! hconv

/-- Every canonical Taylor approximant is entire. -/
theorem xiCTaylorApprox_differentiable (n : ℕ) : Differentiable ℂ (xiCTaylorApprox n) := by
  unfold xiCTaylorApprox FormalMultilinearSeries.partialSum
  apply Differentiable.fun_sum
  intro k hk
  exact fun z => (HasFDerivAt.multilinear_comp (f := cauchyPowerSeries XiC 0 1 k)
    (fun _ => hasFDerivAt_id z)).differentiableAt

/-- The finite-prime logarithmic pinning theorem along an arbitrary cofinal cutoff sequence. -/
theorem tendsto_horizontalDisplacement_zero_of_cofinal_energy_div_log_sq_tendsto_zero
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (epsilon : ℕ → ℝ)
    (henergy : Tendsto
      (fun j : ℕ => primeClockCutoffEnergy (cutoff j) (epsilon j) /
        Real.log (cutoff j) ^ (2 : ℕ))
      atTop (𝓝 0)) :
    Tendsto epsilon atTop (𝓝 0) := by
  have hratio := tendsto_primeClockSusceptibility_div_log_sq.comp hcutoff
  have hratioLower : ∀ᶠ j : ℕ in atTop,
      (1 / 4 : ℝ) ≤ primeClockSusceptibility (cutoff j) / Real.log (cutoff j) ^ (2 : ℕ) := by
    filter_upwards [(tendsto_order.1 hratio).1 (1 / 4 : ℝ) (by norm_num)] with j hj
    exact hj.le
  have hcutoffTwo : ∀ᶠ j : ℕ in atTop, 2 ≤ cutoff j :=
    hcutoff.eventually (eventually_ge_atTop 2)
  have hsqBound : ∀ᶠ j : ℕ in atTop,
      epsilon j ^ (2 : ℕ) ≤
        primeClockCutoffEnergy (cutoff j) (epsilon j) / Real.log (cutoff j) ^ (2 : ℕ) := by
    filter_upwards [hratioLower, hcutoffTwo] with j hratioJ hN
    exact horizontalDisplacement_sq_le_energy_div_log_sq (cutoff j) (epsilon j) hN hratioJ
  have hsq : Tendsto (fun j : ℕ => epsilon j ^ (2 : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun j => sq_nonneg (epsilon j)
    · exact hsqBound
    · exact henergy
  have habs : Tendsto (fun j : ℕ => |epsilon j|) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsq.sqrt
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using habs

/-- Locally uniform entire approximants whose zero fibres have locally uniform sub-log-square
finite-prime reflected energy force the Riemann hypothesis. Only zeros in each fixed compact ball
are controlled; no condition is imposed on spurious approximant zeros escaping to infinity. -/
theorem riemannHypothesis_of_XiC_locally_uniform_cofinalLocalPrimeEnergy_approximants
    {Fn : ℕ → ℂ → ℂ} {cutoff : ℕ → ℕ}
    (hcutoff : Tendsto cutoff atTop atTop)
    (hconv : TendstoLocallyUniformly Fn XiC atTop)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hzeroEnergyLocal : ∀ R : ℝ, ∃ E : ℕ → ℝ,
      Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) R, Fn n z = 0 →
        primeClockCutoffEnergy (cutoff n) z.im / Real.log (cutoff n) ^ (2 : ℕ) ≤ E n) :
    RiemannHypothesis := by
  classical
  have hXiCZeroReal : ∀ z : ℂ, XiC z = 0 → z.im = 0 := by
    intro z hz
    by_contra hzim
    have hnotEventuallyZero : ¬ ∀ᶠ w in 𝓝 z, XiC w = 0 := by
      intro hev
      have hall := XiC_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z) hev (Set.mem_univ 0)
      exact XiC_zero_ne hall
    have hpunct : ∀ᶠ w in 𝓝[≠] z, XiC w ≠ 0 :=
      (XiC_analytic z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
        hnotEventuallyZero
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
    let r : ℝ := min (|z.im| / 4) (δ / 2)
    have hr : 0 < r := lt_min (div_pos (abs_pos.mpr hzim) (by norm_num)) (half_pos hδ)
    have hrIm : r ≤ |z.im| / 4 := min_le_left _ _
    have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ)
    have hsphere : ∀ w ∈ sphere z r, XiC w ≠ 0 := by
      intro w hw
      apply hδsub
      refine ⟨?_, ?_⟩
      · exact Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hrδ)
      · exact Set.mem_compl_singleton_iff.mpr (Metric.ne_of_mem_sphere hw hr.ne')
    have hlocal : ∀ᶠ n in atTop, ∃ w ∈ closedBall z r, Fn n w = 0 :=
      eventually_exists_zero_closedBall_of_tendstoLocallyUniformly hconv
        (fun w => (XiC_analytic w (Set.mem_univ w)).differentiableAt) hFn hr hz hsphere
    let P : ℕ → Prop := fun n => ∃ w ∈ closedBall z r, Fn n w = 0
    let w : ℕ → ℂ := fun n => if hn : P n then Classical.choose hn else 0
    have hwSpec : ∀ᶠ n in atTop, w n ∈ closedBall z r ∧ Fn n (w n) = 0 := by
      filter_upwards [hlocal] with n hn
      have hchoose := Classical.choose_spec hn
      simpa only [w, P, dif_pos hn] using hchoose
    obtain ⟨E, hE, hzeroEnergy⟩ := hzeroEnergyLocal (dist z 0 + r)
    have henergyNonneg : ∀ n : ℕ,
        0 ≤ primeClockCutoffEnergy (cutoff n) (w n).im / Real.log (cutoff n) ^ (2 : ℕ) := by
      intro n
      exact div_nonneg (primeClockCutoffEnergy_nonneg (cutoff n) (w n).im) (sq_nonneg _)
    have henergyLe : ∀ᶠ n in atTop,
        primeClockCutoffEnergy (cutoff n) (w n).im / Real.log (cutoff n) ^ (2 : ℕ) ≤ E n := by
      filter_upwards [hwSpec, hzeroEnergy] with n hwn hbound
      apply hbound (w n)
      · rw [Metric.mem_closedBall]
        calc
          dist (w n) 0 ≤ dist (w n) z + dist z 0 := dist_triangle _ _ _
          _ ≤ r + dist z 0 := add_le_add (Metric.mem_closedBall.mp hwn.1) le_rfl
          _ = dist z 0 + r := add_comm _ _
      · exact hwn.2
    have henergyTendsto : Tendsto
        (fun n : ℕ => primeClockCutoffEnergy (cutoff n) (w n).im /
          Real.log (cutoff n) ^ (2 : ℕ))
        atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall henergyNonneg) henergyLe hE
    have hwIm : Tendsto (fun n : ℕ => (w n).im) atTop (𝓝 0) :=
      tendsto_horizontalDisplacement_zero_of_cofinal_energy_div_log_sq_tendsto_zero
        cutoff hcutoff (fun n => (w n).im) henergyTendsto
    have hsmall : ∀ᶠ n in atTop, |(w n).im| < r := by
      have hmetric := (Metric.tendsto_atTop.mp hwIm) r hr
      simpa [Real.dist_eq] using hmetric
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hwSpec
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hsmall
    let n := max N₁ N₂
    have hwn := hN₁ n (le_max_left _ _)
    have hwnSmall := hN₂ n (le_max_right _ _)
    have himdiff : |(w n).im - z.im| ≤ r := by
      calc
        |(w n).im - z.im| = |((w n) - z).im| := by simp
        _ ≤ ‖(w n) - z‖ := Complex.abs_im_le_norm _
        _ = dist (w n) z := by rw [dist_eq_norm]
        _ ≤ r := Metric.mem_closedBall.mp hwn.1
    have hzle : |z.im| ≤ |(w n).im - z.im| + |(w n).im| := by
      calc
        |z.im| = |(z.im - (w n).im) + (w n).im| := by congr 1; ring
        _ ≤ |z.im - (w n).im| + |(w n).im| := abs_add_le _ _
        _ = |(w n).im - z.im| + |(w n).im| := by rw [abs_sub_comm]
    nlinarith [abs_pos.mpr hzim]
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have him : z.im = 0 := hXiCZeroReal z hXiC
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  have hre : ρ.re = 1 / 2 := by linarith [him, hzIm]
  exact (ne_of_gt (mem_rightHalf.mp hρ)) hre

/-- The index-cutoff specialization of the cofinal compact-local transfer theorem. -/
theorem riemannHypothesis_of_XiC_locally_uniform_localPrimeEnergy_approximants
    {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformly Fn XiC atTop)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hzeroEnergyLocal : ∀ R : ℝ, ∃ E : ℕ → ℝ,
      Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) R, Fn n z = 0 →
        primeClockCutoffEnergy n z.im / Real.log n ^ (2 : ℕ) ≤ E n) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_XiC_locally_uniform_cofinalLocalPrimeEnergy_approximants
    (cutoff := fun n => n) tendsto_id hconv hFn hzeroEnergyLocal

/-- Uniform zero-fibre energy is a convenient stronger interface to the compact-local theorem. -/
theorem riemannHypothesis_of_XiC_locally_uniform_primeEnergy_approximants
    {Fn : ℕ → ℂ → ℂ} {E : ℕ → ℝ}
    (hconv : TendstoLocallyUniformly Fn XiC atTop)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hE : Tendsto E atTop (𝓝 0))
    (hzeroEnergy : ∀ᶠ n in atTop, ∀ z, Fn n z = 0 →
      primeClockCutoffEnergy n z.im / Real.log n ^ (2 : ℕ) ≤ E n) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_XiC_locally_uniform_localPrimeEnergy_approximants hconv hFn
  intro R
  refine ⟨E, hE, ?_⟩
  filter_upwards [hzeroEnergy] with n hn
  exact fun z _ hz => hn z hz

/-- **Canonical local Taylor-prime-energy chain to RH.** It is enough to control zeros of the
source-defined Cauchy--Taylor partial sums in every fixed compact ball. Escaping section zeros are
irrelevant. -/
theorem riemannHypothesis_of_xiCTaylorApprox_localPrimeEnergy
    (hzeroEnergyLocal : ∀ R : ℝ, ∃ E : ℕ → ℝ,
      Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) R, xiCTaylorApprox n z = 0 →
        primeClockCutoffEnergy n z.im / Real.log n ^ (2 : ℕ) ≤ E n) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_XiC_locally_uniform_localPrimeEnergy_approximants
    xiCTaylorApprox_tendstoLocallyUniformly
    (Eventually.of_forall xiCTaylorApprox_differentiable) hzeroEnergyLocal

/-- **Canonical Taylor-prime-energy chain to RH.** It is enough to bound the reflected finite-prime
energy uniformly on the complete zero fibres of the source-defined Cauchy--Taylor partial sums of
`XiC`. No separate approximation or holomorphy assumptions remain. -/
theorem riemannHypothesis_of_xiCTaylorApprox_primeEnergy
    {E : ℕ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hzeroEnergy : ∀ᶠ n in atTop, ∀ z, xiCTaylorApprox n z = 0 →
      primeClockCutoffEnergy n z.im / Real.log n ^ (2 : ℕ) ≤ E n) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_XiC_locally_uniform_primeEnergy_approximants
    xiCTaylorApprox_tendstoLocallyUniformly
    (Eventually.of_forall xiCTaylorApprox_differentiable) hE hzeroEnergy

end RHTower
