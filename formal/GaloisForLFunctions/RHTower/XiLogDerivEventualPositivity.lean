import GaloisForLFunctions.RHTower.LindelofCosineFiniteDefectDepth
import GaloisForLFunctions.RHTower.XiLogDerivReLocality
import GaloisForLFunctions.RHTower.XiLogDerivReCriterion
import GaloisForLFunctions.RHTower.XiDeck

/-!
# Eventual Hadamard positivity is "zeros approach the line"

RH is equivalent to `Re (ξ'/ξ)(s) ≥ 0` on the whole half-plane `Re s > ½`
(`riemannHypothesis_iff_re_logDeriv_xi_nonneg`).  Its large-height form is

`EventualHadamardPositivity`: for every `σ > ½` there is `T` with `Re (ξ'/ξ)(s) ≥ 0` whenever
`Re s ≥ σ` and `|Im s| ≥ T`.

**Theorem** (`eventualHadamardPositivity_iff_zerosApproachLine`).  Eventual Hadamard positivity
holds if and only if the zeros of `ξ` approach the critical line: for every `h > 0` only finitely
many zeros satisfy `β < ½ − h`.

* Zeros approaching the line give positivity: a zero obstructs at `s` only inside the disc
  `(β − ½)² ≥ (σ − ½)² + (t − γ)²` (`re_logDeriv_xi_nonneg_of_disk_bound`).  Zeros with
  `|β − ½| ≤ (σ − ½)/2` never obstruct, and the finitely many others have bounded ordinate, so they
  are at distance `≥ 1 > ½` from `s` once `|Im s|` is large.
* Positivity gives zeros approaching the line: near a zero `ρ₀` of order `m`,
  `(ξ'/ξ)(ρ₀ − ε) = −m/ε + O(1)` (`exists_re_logDeriv_xi_neg_near_zero`), so a zero with
  `Re ρ₀ > σ` and `|Im ρ₀| ≥ T` violates positivity; deep zeros on the left are reflected to the
  right by `ρ ↦ 1 − ρ`.

With `zerosApproachLine_iff_lindelof_and_cosShiftXi_finite_nonreal`, the three large-height
receivers coincide: eventual Hadamard positivity, finitely many defects of every cosine level
together with LH, and zeros approaching the line.  Each implies LH and a zero-free half-plane.
-/

open Complex Metric Filter Topology

namespace RHTower.BacklundConverse

open RHTower.LindelofSparse RHTower.CosineSparseCluster RHTower.DeBruijn RHTower.CosineDefectBudget

noncomputable section

/-- Large-height Hadamard positivity of the completed logarithmic derivative. -/
def EventualHadamardPositivity : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → ∃ T : ℝ, ∀ s : ℂ, σ ≤ s.re → T ≤ |s.im| → 0 ≤ (logDeriv xi s).re

/-- Near a zero the logarithmic derivative is the pole `m/(z − ρ₀)` plus an analytic remainder. -/
theorem logDeriv_xi_eq_pole_add {ρ₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hgan : AnalyticOnNhd ℂ g (ball ρ₀ R)) (hg0 : ∀ z ∈ ball ρ₀ R, g z ≠ 0)
    (hfact : ∀ z ∈ ball ρ₀ R, xi z = (z - ρ₀) ^ (analyticOrderAt xi ρ₀).toNat * g z)
    {z : ℂ} (hz : z ∈ ball ρ₀ R) (hzne : z ≠ ρ₀) :
    logDeriv xi z = ((analyticOrderAt xi ρ₀).toNat : ℂ) / (z - ρ₀) + logDeriv g z := by
  set m := (analyticOrderAt xi ρ₀).toNat with hm
  have hsub : z - ρ₀ ≠ 0 := sub_ne_zero.mpr hzne
  have hpow : (z - ρ₀) ^ m ≠ 0 := pow_ne_zero _ hsub
  have hgz : g z ≠ 0 := hg0 z hz
  have hev : xi =ᶠ[𝓝 z] fun w : ℂ => (w - ρ₀) ^ m * g w :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw => hfact w hw
  have hdpow : DifferentiableAt ℂ (fun w : ℂ => (w - ρ₀) ^ m) z := by fun_prop
  have hdg : DifferentiableAt ℂ g z := (hgan z hz).differentiableAt
  have hlog : logDeriv xi z = logDeriv (fun w : ℂ => (w - ρ₀) ^ m * g w) z := by
    rw [logDeriv, logDeriv, Pi.div_apply, Pi.div_apply, hev.deriv_eq, hfact z hz]
  rw [hlog, logDeriv_mul z hpow hgz hdpow hdg]
  congr 1
  have hderiv : HasDerivAt (fun w : ℂ => (w - ρ₀) ^ m) ((m : ℂ) * (z - ρ₀) ^ (m - 1)) z := by
    have h := ((hasDerivAt_id z).sub_const ρ₀).pow m
    simpa using! h
  rw [logDeriv, Pi.div_apply, hderiv.deriv]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]; simp
  · have e : (z - ρ₀) ^ m = (z - ρ₀) ^ (m - 1) * (z - ρ₀) := by
      rw [← pow_succ, Nat.sub_add_cancel hpos]
    rw [e]
    field_simp

/-- **The pole drives `Re (ξ'/ξ)` to `−∞` just left of a zero.** -/
theorem exists_re_logDeriv_xi_neg_near_zero {ρ₀ : ℂ} (h0 : xi ρ₀ = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ (logDeriv xi (ρ₀ - ε)).re < 0 := by
  obtain ⟨R, hR, g, hgan, hg0, hfact⟩ := xi_peel_ball ρ₀
  set m := (analyticOrderAt xi ρ₀).toNat with hm
  have hmpos : 0 < m := by
    by_contra hcon
    have hzero : m = 0 := by omega
    have hval := hfact ρ₀ (mem_ball_self hR)
    rw [hzero, pow_zero, one_mul] at hval
    exact hg0 ρ₀ (mem_ball_self hR) (by rw [← hval, h0])
  have hcont : ContinuousAt (logDeriv g) ρ₀ := by
    have hd1 : ContinuousAt (deriv g) ρ₀ := ((hgan ρ₀ (mem_ball_self hR)).deriv).continuousAt
    have hd2 : ContinuousAt g ρ₀ := (hgan ρ₀ (mem_ball_self hR)).continuousAt
    unfold logDeriv
    exact ContinuousAt.div hd1 hd2 (hg0 ρ₀ (mem_ball_self hR))
  obtain ⟨r, hr, hr'⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  set K : ℝ := ‖logDeriv g ρ₀‖ + 1 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hmpos
  set ε : ℝ := min (min (R / 2) (r / 2)) (min (δ / 2) (m / (2 * K))) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεR : ε < R := by
    have : ε ≤ R / 2 := (min_le_left _ _).trans (min_le_left _ _); linarith
  have hεr : ε < r := by
    have : ε ≤ r / 2 := (min_le_left _ _).trans (min_le_right _ _); linarith
  have hεδ : ε < δ := by
    have : ε ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _); linarith
  have hεK : ε * K < m := by
    have : ε ≤ m / (2 * K) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : ε * K ≤ m / (2 * K) * K := mul_le_mul_of_nonneg_right this hK0.le
    have h3 : m / (2 * K) * K = m / 2 := by field_simp
    linarith
  refine ⟨ε, hε0, hεδ, ?_⟩
  set z : ℂ := ρ₀ - ε with hz
  have hzsub : z - ρ₀ = -(ε : ℂ) := by rw [hz]; ring
  have hdist : dist z ρ₀ = ε := by
    rw [dist_eq_norm, hzsub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
  have hzb : z ∈ ball ρ₀ R := by rw [mem_ball, hdist]; exact hεR
  have hzne : z ≠ ρ₀ := by
    intro h; rw [h, dist_self] at hdist; linarith
  rw [logDeriv_xi_eq_pole_add hgan hg0 hfact hzb hzne, Complex.add_re, hzsub]
  have hpole : ((m : ℂ) / -(ε : ℂ)).re = -(m / ε) := by
    rw [show ((m : ℂ) / -(ε : ℂ)) = ((-(m / ε) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [← hm, hpole]
  have hg : (logDeriv g z).re < K := by
    have h1 : dist (logDeriv g z) (logDeriv g ρ₀) < 1 := hr' (by rw [hdist]; exact hεr)
    have h2 : (logDeriv g z).re ≤ ‖logDeriv g z‖ := Complex.re_le_norm _
    have h3 : ‖logDeriv g z‖ ≤ ‖logDeriv g ρ₀‖ + dist (logDeriv g z) (logDeriv g ρ₀) := by
      rw [dist_eq_norm]
      calc ‖logDeriv g z‖ = ‖logDeriv g ρ₀ + (logDeriv g z - logDeriv g ρ₀)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [hK]; linarith
  have hmε : K < m / ε := by rw [lt_div_iff₀ hε0]; linarith
  linarith

/-- **Zeros approaching the line give eventual Hadamard positivity.** -/
theorem eventualHadamardPositivity_of_zerosApproachLine (hZ : ZerosApproachLine) :
    EventualHadamardPositivity := by
  intro σ hσ
  set h : ℝ := (σ - 1 / 2) / 2 with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  obtain ⟨M, hM⟩ := ((finite_abs_im_gt_of_zerosApproachLine hZ hh0).image
    fun q => |((q.1 : ℂ)).im|).bddAbove
  refine ⟨M + 1, fun s hs hT => ?_⟩
  by_cases hxi : xi s = 0
  · rw [logDeriv_xi_eq_zero_of_xi_eq_zero hxi, Complex.zero_re]
  refine re_logDeriv_xi_nonneg_of_disk_bound (by linarith) hxi fun q => ?_
  have hspec := abs_spectral_im_lt_half q
  rw [spectral_im_eq] at hspec
  have hhalf : (((q.1 : ℂ)).re - 1 / 2) ^ 2 < 1 / 4 := by
    have : |((q.1 : ℂ)).re - 1 / 2| < 1 / 2 := by rw [abs_sub_comm]; exact hspec
    nlinarith [abs_nonneg (((q.1 : ℂ)).re - 1 / 2), sq_abs (((q.1 : ℂ)).re - 1 / 2)]
  by_cases hq : h < |(xiSpectralPoint q).im|
  · -- a deep zero: its ordinate is bounded, so it is far from `s`
    have hγ : |((q.1 : ℂ)).im| ≤ M := hM ⟨q, hq, rfl⟩
    have hfar : 1 ≤ |s.im - ((q.1 : ℂ)).im| := by
      have := abs_sub_abs_le_abs_sub s.im ((q.1 : ℂ)).im
      linarith
    have h1 : 1 ≤ (s.im - ((q.1 : ℂ)).im) ^ 2 := by
      nlinarith [sq_abs (s.im - ((q.1 : ℂ)).im)]
    nlinarith [sq_nonneg (s.re - 1 / 2)]
  · -- a shallow zero never obstructs
    rw [not_lt, spectral_im_eq, abs_sub_comm] at hq
    have h1 : (((q.1 : ℂ)).re - 1 / 2) ^ 2 ≤ h ^ 2 := by
      nlinarith [sq_abs (((q.1 : ℂ)).re - 1 / 2), abs_nonneg (((q.1 : ℂ)).re - 1 / 2)]
    have h2 : h ^ 2 < (s.re - 1 / 2) ^ 2 := by
      have : h < s.re - 1 / 2 := by rw [hh]; linarith
      nlinarith
    nlinarith [sq_nonneg (s.im - ((q.1 : ℂ)).im)]

/-- **Eventual Hadamard positivity forces the zeros to approach the line.** -/
theorem zerosApproachLine_of_eventualHadamardPositivity (hE : EventualHadamardPositivity) :
    ZerosApproachLine := by
  intro h hh
  obtain ⟨T, hT⟩ := hE (1 / 2 + h / 2) (by linarith)
  -- deep zeros have ordinate below `T`
  have hbound : ∀ q ∈ deepCopies h, |((q.1 : ℂ)).im| < T := by
    intro q hq
    have hq' : h < (xiSpectralPoint q).im := hq
    rw [spectral_im_eq] at hq'
    by_contra hge
    rw [not_lt] at hge
    -- the reflected zero `1 − ρ` lies right of `½ + h`
    set ρ₁ : ℂ := 1 - (q.1 : ℂ) with hρ₁
    have hz : xi ρ₁ = 0 := by rw [hρ₁, xi_one_sub]; exact xi_xiZeroCopy_eq_zero q
    obtain ⟨ε, hε0, hεδ, hneg⟩ := exists_re_logDeriv_xi_neg_near_zero hz (δ := h / 2) (by linarith)
    have hre : 1 / 2 + h / 2 ≤ (ρ₁ - ε).re := by
      rw [hρ₁]; simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]; linarith
    have him : T ≤ |(ρ₁ - ε).im| := by
      rw [hρ₁]
      simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, zero_sub, abs_neg]
      exact hge
    linarith [hT _ hre him]
  refine (xiZeroBall (⌈|T| + 1⌉₊)).finite_toSet.subset fun q hq => ?_
  simp only [Finset.mem_coe, mem_xiZeroBall]
  have h1 := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
  have h2 := abs_spectral_im_lt_half q
  have h3 : |T| + 1 ≤ (⌈|T| + 1⌉₊ : ℝ) := Nat.le_ceil _
  have h4 : |(xiSpectralPoint q).re| < |T| := by
    rw [spectral_re_eq]; exact (hbound q hq).trans_le (le_abs_self T)
  linarith

/-- **Eventual Hadamard positivity is exactly "zeros approach the line".** -/
theorem eventualHadamardPositivity_iff_zerosApproachLine :
    EventualHadamardPositivity ↔ ZerosApproachLine :=
  ⟨zerosApproachLine_of_eventualHadamardPositivity, eventualHadamardPositivity_of_zerosApproachLine⟩

/-- **Eventual Hadamard positivity implies LH.** -/
theorem lindelofCriticalLine_of_eventualHadamardPositivity (hE : EventualHadamardPositivity) :
    LindelofCriticalLine :=
  lindelofCriticalLine_of_zerosApproachLine (zerosApproachLine_of_eventualHadamardPositivity hE)

end

end RHTower.BacklundConverse
