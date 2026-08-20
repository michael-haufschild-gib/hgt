import GaloisForLFunctions.RHTower.GradeMonodromyInversion
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.XiPrimeLogHigherValuationHalfPlane
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.HTGeometry.ZeroDivisorCount
import GaloisForLFunctions.HTGeometry.LogDerivUniformLimit
import Mathlib

/-!
# Prime-zeta monodromy and the escape of the divisor charge

The compact prime boundary layer carries only endpoint jets; the zeta divisor sits in the
prime-zeta monodromy, which escapes every fixed boundary chart.  This module assembles that
statement from the corpus:

* `primeBoundary_moebius_inversion` — the derivative form of `P(s) = ∑_n μ(n)/n log ζ(ns)`;
* `primeBoundary_monodromy_charge` — at every zeta zero right of the critical line the continued
  prime-log current has a simple pole whose residue is the multiplicity, i.e. `P` has a
  logarithmic branch point of quantized charge `m_ρ`;
* `tendsto_boundaryChart_escape` — in the boundary coordinate `z = L(s-1)` that branch point runs
  to infinity at speed `log N`;
* `circleIntegral_logDeriv_archFactor_eq_zero` — the archimedean completion factor is holomorphic
  and nonvanishing on the open strip, so the Gamma/theta weld has zero monodromy;
* `riemannHypothesis_iff_no_primeBoundary_charge` — the terminal restatement: RH is exactly the
  absence of quantized prime-boundary charge in the right half of the critical strip;
* `circleIntegral_deriv_of_entire_eq_zero` and `no_zero_of_tendstoUniformlyOn_zeroFree` — the two
  zero-charge obstructions: entire cumulants carry no charge, and a locally uniform limit of
  zero-free entire functions cannot acquire a zero.
-/

set_option maxHeartbeats 1600000

open Filter Topology Set MeasureTheory ArithmeticFunction

namespace RHTower

noncomputable section

/-! ## The continued prime-log current is the derivative of the prime zeta function -/

/-- `P'(s) = -∑_p (log p) p^{-s}` on the half-plane of absolute convergence: the prime zeta
derivative is minus the grade-one prime source. -/
theorem deriv_coronaPrimeZeta_eq_neg_primeGradeSource {s : ℂ} (hs : 1 < s.re) :
    deriv coronaPrimeZeta s = -primeGradeSource s := by
  have h := tsum_neg_deriv_coronaPrimeZeta hs
  rw [primeGradeSource]
  have hterm : ∀ p : Nat.Primes,
      (Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue s p
        = (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) := by
    intro p
    rw [coronaPrimeEigenvalue]
  rw [tsum_congr hterm] at h
  linear_combination -h

/-- **`(21)`: the Möbius inversion of the prime-log current**, restated for the card: the
grade-one prime source is the Möbius transform of the von Mangoldt current along the dilation
ray, which is the derivative form of `P(s) = ∑_n μ(n)/n · log ζ(ns)`. -/
theorem primeBoundary_moebius_inversion {s : ℂ} (hs : 1 < s.re) :
    -deriv coronaPrimeZeta s
      = ∑' r : ℕ+, (moebius (r : ℕ) : ℂ)
          * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (((r : ℕ) : ℂ) * s) := by
  rw [deriv_coronaPrimeZeta_eq_neg_primeGradeSource hs, neg_neg]
  exact primeGradeSource_eq_tsum_moebius_lSeries hs

/-- **`(22)`: the quantized monodromy charge.**  At every zeta zero to the right of the critical
line, the continued prime-log current has a simple pole whose residue is exactly the zero's
multiplicity; equivalently the continued prime zeta function has a logarithmic branch point of
charge `m_ρ` there. -/
theorem primeBoundary_monodromy_charge {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ => (s - rho) * (-xiPrimeLogDirichletContinuation s))
        (𝓝[≠] rho) (𝓝 (m : ℂ)) := by
  obtain ⟨m, hm, hres⟩ := primeGradeMonodromy_zero_residue hrho hzeta
  refine ⟨m, hm, ?_⟩
  have h := hres.neg
  rw [neg_neg] at h
  refine h.congr fun s => ?_
  ring

/-- **`(24)`: the divisor charge escapes every compact boundary chart.**  In the boundary
coordinate `z = L(s-1)` the branch point attached to a zeta zero `ρ ≠ 1` runs off to infinity at
speed `log N`. -/
theorem tendsto_boundaryChart_escape {rho : ℂ} (hrho : rho ≠ 1) :
    Tendsto (fun N : ℕ => ‖(Real.log (N : ℝ) : ℂ) * (rho - 1)‖) atTop atTop := by
  have hne : 0 < ‖rho - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero_of_ne hrho
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun N : ℕ => Real.log (N : ℝ) * ‖rho - 1‖) atTop atTop :=
    hlog.atTop_mul_const hne
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogpos : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogpos]

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set Metric

/-! ## The archimedean weld carries no divisor charge -/

theorem analyticAt_archFactor_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ archFactor s := by
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hGa : AnalyticAt ℂ Complex.Gammaℝ s := Gammaℝ_analyticAt hG
  have hpoly : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / 2) s :=
    (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div analyticAt_const
      (by norm_num)
  have hfun : archFactor = fun z : ℂ => z * (z - 1) / 2 * Complex.Gammaℝ z := rfl
  rw [hfun]
  exact hpoly.mul hGa

theorem archFactor_ne_zero_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    archFactor s ≠ 0 := by
  refine archFactor_ne_zero ?_ ?_ (Complex.Gammaℝ_ne_zero_of_re_pos h0)
  · intro h
    rw [h] at h0
    simp at h0
  · intro h
    rw [h] at h1
    simp at h1

/-- **`(26)`: the archimedean completion factor has zero monodromy.**  It is holomorphic and
nonvanishing on the open critical strip, so the contour integral of its logarithmic derivative
around any small circle inside the strip vanishes: the Gamma/theta weld can renormalize the
endpoint jet but cannot create, cancel or move divisor charge. -/
theorem circleIntegral_logDeriv_archFactor_eq_zero {rho : ℂ} {r : ℝ} (hr : 0 < r)
    (hstrip : ∀ s ∈ closedBall rho r, 0 < s.re ∧ s.re < 1) :
    (∮ s in C(rho, r), logDeriv archFactor s) = 0 := by
  have hkey : ∀ s ∈ closedBall rho r,
      AnalyticAt ℂ archFactor s ∧ archFactor s ≠ 0 := by
    intro s hs
    obtain ⟨h0, h1⟩ := hstrip s hs
    exact ⟨analyticAt_archFactor_of_re_pos h0, archFactor_ne_zero_of_mem_strip h0 h1⟩
  have hcont : ContinuousOn (logDeriv archFactor) (closedBall rho r) := by
    intro s hs
    obtain ⟨hA, hne⟩ := hkey s hs
    have hd : ContinuousAt (deriv archFactor) s := hA.deriv.continuousAt
    have hf : ContinuousAt archFactor s := hA.continuousAt
    have : ContinuousAt (fun z : ℂ => deriv archFactor z / archFactor z) s := hd.div hf hne
    exact this.continuousWithinAt
  have hdiff : ∀ z ∈ ball rho r \ (∅ : Set ℂ), DifferentiableAt ℂ (logDeriv archFactor) z := by
    intro z hz
    obtain ⟨hA, hne⟩ := hkey z (ball_subset_closedBall hz.1)
    have hd : DifferentiableAt ℂ (deriv archFactor) z := hA.deriv.differentiableAt
    have hf : DifferentiableAt ℂ archFactor z := hA.differentiableAt
    exact hd.div hf hne
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    (Set.countable_empty) hcont hdiff

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set Metric

/-! ## The terminal RH restatement and the two zero-charge obstructions -/

theorem tendsto_primeBoundary_residue_zero_of_zeta_ne_zero {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (h1 : rho ≠ 1) (hzeta : riemannZeta rho ≠ 0) :
    Tendsto (fun s : ℂ => (s - rho) * (-xiPrimeLogDirichletContinuation s)) (𝓝[≠] rho) (𝓝 0) := by
  have hlog : DifferentiableAt ℂ (fun s : ℂ => -logDeriv riemannZeta s) rho := by
    have h := differentiableAt_neg_logDeriv_riemannZeta h1 hzeta
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with z
    rw [logDeriv, Pi.div_apply, neg_div]
  have hhigh : DifferentiableAt ℂ xiPrimeLogHigherValuation rho :=
    differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re hrho
  have hfun : (fun s : ℂ => -xiPrimeLogDirichletContinuation s)
      = fun s : ℂ => -(-logDeriv riemannZeta s) + xiPrimeLogHigherValuation s := by
    funext s
    rw [xiPrimeLogDirichletContinuation, infinitePrimeFlux]
    ring
  have hcont : ContinuousAt (fun s : ℂ => -xiPrimeLogDirichletContinuation s) rho := by
    rw [hfun]
    exact (hlog.neg.continuousAt).add hhigh.continuousAt
  have hlim : Tendsto (fun s : ℂ => -xiPrimeLogDirichletContinuation s) (𝓝[≠] rho)
      (𝓝 (-xiPrimeLogDirichletContinuation rho)) := hcont.continuousWithinAt.tendsto
  have hlin := tendsto_sub_self_punctured_zero rho
  simpa using hlin.mul hlim

/-- **`(27)`: the terminal RH restatement.**  The Riemann hypothesis is exactly the statement that
the continued prime-log current carries no quantized charge in the right half of the critical
strip — equivalently that the prime zeta function has no zero-generated branch point there. -/
theorem riemannHypothesis_iff_no_primeBoundary_charge :
    RiemannHypothesis ↔ ∀ rho : ℂ, 1 / 2 < rho.re → rho.re < 1 →
      ¬ ∃ m : ℕ, 1 ≤ m ∧
        Tendsto (fun s : ℂ => (s - rho) * (-xiPrimeLogDirichletContinuation s))
          (𝓝[≠] rho) (𝓝 (m : ℂ)) := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  constructor
  · intro h rho hlo hhi ⟨m, hm, hlim⟩
    have hne : riemannZeta rho ≠ 0 := h rho hlo hhi
    have h1 : rho ≠ 1 := by
      intro hEq
      rw [hEq] at hhi
      simp at hhi
    have hzero := tendsto_primeBoundary_residue_zero_of_zeta_ne_zero hlo h1 hne
    have huniq : (m : ℂ) = 0 := tendsto_nhds_unique hlim hzero
    have : (m : ℝ) = 0 := by exact_mod_cast congrArg Complex.re huniq
    have hm0 : m = 0 := by exact_mod_cast this
    omega
  · intro h rho hlo hhi hzero
    exact h rho hlo hhi (primeBoundary_monodromy_charge hlo hzero)

/-- **Zero-charge obstruction 1.**  Every finite cumulant is entire, so its monodromy vanishes:
contour integration of a globally defined derivative gives zero, and quantized charge cannot
nucleate through locally uniform convergence of regular finite fields. -/
theorem circleIntegral_deriv_of_entire_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ)
    {r : ℝ} (hr : 0 ≤ r) :
    (∮ z in C(c, r), deriv f z) = 0 := by
  have hd : Differentiable ℂ (deriv f) := GaloisForLFunctions.HTGeometry.differentiable_deriv_of_differentiable hf
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
    hd.continuous.continuousOn (fun z _ => hd.differentiableAt)

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set Metric

/-- **Zero-charge obstruction 2 (Hurwitz).**  A locally uniform limit of zero-free entire
functions has no zero inside a circle on which the limit is nonvanishing: raw finite Euler
exponentials, even multiplied by nonvanishing gauges, cannot converge locally uniformly to a
function with a zero. -/
theorem no_zero_of_tendstoUniformlyOn_zeroFree {α : Type*} {p : Filter α} [p.NeBot]
    {F : α → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ a, Differentiable ℂ (F a)) (hFne : ∀ a z, F a z ≠ 0)
    (hf : Differentiable ℂ f) {c : ℂ} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (huniform : TendstoUniformlyOn F f p (closedBall c R))
    (hfne : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∀ z ∈ ball c r, f z ≠ 0 := by
  classical
  have hzeroInt : ∀ a, (∮ z in C(c, r), logDeriv (F a) z) = 0 := by
    intro a
    have hderiv : Differentiable ℂ (deriv (F a)) :=
      GaloisForLFunctions.HTGeometry.differentiable_deriv_of_differentiable (hF a)
    have hd : Differentiable ℂ (logDeriv (F a)) := by
      intro z
      exact (hderiv z).div ((hF a) z) (hFne a z)
    exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      hd.continuous.continuousOn (fun z _ => hd.differentiableAt)
  have hlim := GaloisForLFunctions.HTGeometry.tendsto_circleIntegral_logDeriv hF hf hr hrR huniform hfne
  have hI : (∮ z in C(c, r), logDeriv f z) = 0 := by
    have hconst : Tendsto (fun a : α => (∮ z in C(c, r), logDeriv (F a) z)) p (𝓝 (0 : ℂ)) := by
      simp only [hzeroInt]
      exact tendsto_const_nhds
    exact (tendsto_nhds_unique hlim hconst)
  obtain ⟨Z, hZball, hZmem, hZint⟩ :=
    GaloisForLFunctions.HTGeometry.exists_zeroSet_circleIntegral_logDeriv hr hrR isOpen_univ
      (Set.subset_univ _) hf.differentiableOn hfne
  rw [hI] at hZint
  have hsum : ∑ rho ∈ Z, (GaloisForLFunctions.HTGeometry.zeroMult f rho : ℂ) = 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have htwopi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have hprod : (2 * (Real.pi : ℂ) * Complex.I)
        * ∑ rho ∈ Z, (GaloisForLFunctions.HTGeometry.zeroMult f rho : ℂ) = 0 := hZint.symm
    exact (mul_eq_zero.mp hprod).resolve_left htwopi
  intro z hz hfz
  have hzZ : z ∈ Z := (hZmem z hz).mp hfz
  have hmultpos : 1 ≤ GaloisForLFunctions.HTGeometry.zeroMult f z := by
    have hana : AnalyticAt ℂ f z := hf.analyticAt z
    have hord0 : analyticOrderAt f z ≠ 0 := hana.analyticOrderAt_ne_zero.mpr hfz
    have hordtop : analyticOrderAt f z ≠ ⊤ := by
      intro htop
      have hev : ∀ᶠ w in 𝓝 z, f w = 0 := analyticOrderAt_eq_top.mp htop
      have hall : ∀ w : ℂ, f w = 0 := by
        have hana' : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
        have := hana'.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (isPreconnected_univ) (Set.mem_univ z) hev
        intro w
        exact this (Set.mem_univ w)
      have hspoint : c + (r : ℂ) ∈ sphere c r := by
        rw [mem_sphere, dist_eq_norm]
        simp [Complex.norm_real, abs_of_pos hr]
      exact hfne _ hspoint (hall _)
    have : GaloisForLFunctions.HTGeometry.zeroMult f z ≠ 0 := by
      rw [GaloisForLFunctions.HTGeometry.zeroMult]
      intro h
      rcases ENat.toNat_eq_zero.mp h with h0 | htop
      · exact hord0 h0
      · exact hordtop htop
    omega
  have hnonneg : ∀ rho ∈ Z, (0 : ℝ) ≤ (GaloisForLFunctions.HTGeometry.zeroMult f rho : ℝ) := by
    intro rho _
    positivity
  have hre : ∑ rho ∈ Z, (GaloisForLFunctions.HTGeometry.zeroMult f rho : ℝ) = 0 := by
    have := congrArg Complex.re hsum
    simpa using this
  have hzterm : (GaloisForLFunctions.HTGeometry.zeroMult f z : ℝ) ≤ 0 := by
    have hle := Finset.single_le_sum hnonneg hzZ
    linarith [hre, hle]
  have : (1 : ℝ) ≤ (GaloisForLFunctions.HTGeometry.zeroMult f z : ℝ) := by exact_mod_cast hmultpos
  linarith

end

end RHTower
