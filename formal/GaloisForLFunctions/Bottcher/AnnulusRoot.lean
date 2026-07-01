/-
# Analytic logarithm and dyadic roots on a round annulus (single-circle winding criterion)

The band-tower construction of the deep radicand (`ExtendedNonSquare.q62_disconnected_of_towerData`'s
supply) iterates square roots of analytic nonvanishing functions on round annuli.  Root existence on
an annulus is governed by one number: the winding `∮ d log g` along a single core circle.  This file
proves the two bricks:

* `exists_log_on_annulus` — winding `0` along one core circle ⟹ analytic logarithm on the annulus;
* `exists_pow_root_on_annulus` — winding `2πi·(2^k·m)` ⟹ analytic nonvanishing `2^k`-th root
  (reduce to winding `0` by dividing the monomial `w^{2^k·m}`, then `w^m · exp(L/2^k)`).

No `π₁` computation and no all-loops hypothesis: the strip `{log r < Re ξ < log R}` (convex, hence
simply connected) carries a branch by `HolomorphicBranch`; the `+2πi`-periodicity defect is a
`2πiℤ`-valued continuous function on the connected strip, hence constant, and equals the core
winding by the vertical-segment FTC; winding `0` descends the branch through `exp`.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.AnalyticRoot
import GaloisForLFunctions.Bottcher.HolomorphicBranch
import GaloisForLFunctions.Bottcher.CylinderUnivalence

open Complex Set Filter

namespace Bottcher

/-- The open round annulus `{r < ‖w‖ < R}`. -/
def annulusSet (r R : ℝ) : Set ℂ := {w : ℂ | r < ‖w‖ ∧ ‖w‖ < R}

/-- The full vertical strip `{log r < Re ξ < log R}` covering the annulus through `exp`. -/
def stripSet (r R : ℝ) : Set ℂ := {ξ : ℂ | Real.log r < ξ.re ∧ ξ.re < Real.log R}

theorem isOpen_annulusSet (r R : ℝ) : IsOpen (annulusSet r R) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem isOpen_stripSet (r R : ℝ) : IsOpen (stripSet r R) :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

theorem convex_stripSet (r R : ℝ) : Convex ℝ (stripSet r R) :=
  (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)

theorem stripSet_nonempty {r R : ℝ} (hr : 0 < r) (hrR : r < R) : (stripSet r R).Nonempty := by
  have hlog := Real.log_lt_log hr hrR
  refine ⟨(((Real.log r + Real.log R) / 2 : ℝ) : ℂ), ?_, ?_⟩
  · show Real.log r < (((Real.log r + Real.log R) / 2 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]; linarith
  · show (((Real.log r + Real.log R) / 2 : ℝ) : ℂ).re < Real.log R
    rw [Complex.ofReal_re]; linarith

/-- The full vertical strip is simply connected (convex, hence contractible). -/
theorem isSimplyConnected_stripSet {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    IsSimplyConnected (stripSet r R) := by
  haveI : ContractibleSpace (stripSet r R) :=
    (convex_stripSet r R).contractibleSpace (stripSet_nonempty hr hrR)
  exact SimplyConnectedSpace.ofContractible _

/-- Membership transport: `exp` maps the strip into the annulus. -/
theorem exp_mem_annulusSet {r R : ℝ} (hr : 0 < r) (hrR : r < R) {ξ : ℂ}
    (hξ : ξ ∈ stripSet r R) : Complex.exp ξ ∈ annulusSet r R := by
  have hR : 0 < R := lt_trans hr hrR
  constructor
  · rw [Complex.norm_exp]
    calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
      _ < Real.exp ξ.re := Real.exp_lt_exp.mpr hξ.1
  · rw [Complex.norm_exp]
    calc Real.exp ξ.re < Real.exp (Real.log R) := Real.exp_lt_exp.mpr hξ.2
      _ = R := Real.exp_log hR

/-- Membership transport: the principal `log` maps the annulus into the strip. -/
theorem log_mem_stripSet {r R : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ annulusSet r R) :
    Complex.log w ∈ stripSet r R := by
  have hwpos : 0 < ‖w‖ := lt_trans hr hw.1
  constructor
  · rw [Complex.log_re]; exact Real.log_lt_log hr hw.1
  · rw [Complex.log_re]; exact Real.log_lt_log hwpos hw.2

theorem annulus_mem_ne_zero {r R : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ annulusSet r R) :
    w ≠ 0 := by
  intro h0
  subst h0
  have : r < (0:ℝ) := by simpa using hw.1
  linarith

/-- Purely imaginary shifts keep the strip. -/
theorem stripSet_add_im {r R : ℝ} {ξ z : ℂ} (hξ : ξ ∈ stripSet r R) (hz : z.re = 0) :
    ξ + z ∈ stripSet r R := by
  have hre : (ξ + z).re = ξ.re := by rw [Complex.add_re, hz, add_zero]
  exact ⟨by rw [hre]; exact hξ.1, by rw [hre]; exact hξ.2⟩

/-- `exp (log ρ + θ·I) = circleMap 0 ρ θ` for real `ρ > 0`. -/
theorem exp_vertical_eq_circleMap {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    Complex.exp (((Real.log ρ : ℝ) : ℂ) + (θ : ℂ) * Complex.I) = circleMap 0 ρ θ := by
  rw [Complex.exp_add, circleMap]
  rw [← Complex.ofReal_exp, Real.exp_log hρ]
  ring_nf

/-- **Analytic logarithm on a round annulus, from vanishing core winding.** If `g` is analytic and
nonvanishing on `{r < ‖w‖ < R}` and its logarithmic winding along ONE core circle of radius
`ρ ∈ (r, R)` vanishes, then `g = exp L` for an analytic `L` on the whole annulus.  Strip descent:
the convex strip carries a log branch; the `+2πi` defect is `2πiℤ`-valued continuous on the
connected strip, hence constant, and the vertical-segment FTC identifies it with the core winding. -/
theorem exists_log_on_annulus {r R ρ : ℝ} (hr : 0 < r) (hρ1 : r < ρ) (hρ2 : ρ < R)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (annulusSet r R))
    (hgne : ∀ w ∈ annulusSet r R, g w ≠ 0)
    (hwind : (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv g (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) = 0) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (annulusSet r R) ∧
      ∀ w ∈ annulusSet r R, Complex.exp (L w) = g w := by
  have hrR : r < R := lt_trans hρ1 hρ2
  have hρ0 : 0 < ρ := lt_trans hr hρ1
  set S := stripSet r R with hSdef
  set A := annulusSet r R with hAdef
  set h : ℂ → ℂ := fun ξ => g (Complex.exp ξ) with hhdef
  have hexpan : AnalyticOnNhd ℂ Complex.exp univ :=
    Complex.differentiable_exp.differentiableOn.analyticOnNhd isOpen_univ
  have hhan : AnalyticOnNhd ℂ h S := fun ξ hξ =>
    (hg _ (exp_mem_annulusSet hr hrR hξ)).comp (hexpan ξ (mem_univ ξ))
  have hhne : ∀ ξ ∈ S, h ξ ≠ 0 := fun ξ hξ => hgne _ (exp_mem_annulusSet hr hrR hξ)
  obtain ⟨L₀, hL₀d, hL₀e⟩ := exists_differentiableOn_exp_eq
    (isSimplyConnected_stripSet hr hrR) (isOpen_stripSet r R)
    (fun ξ hξ => ((hhan ξ hξ).differentiableAt).differentiableWithinAt)
    (by rintro ⟨ξ, hξ, h0⟩; exact hhne ξ hξ h0)
  have hL₀an : AnalyticOnNhd ℂ L₀ S := hL₀d.analyticOnNhd (isOpen_stripSet r R)
  have hL₀exp : ∀ ξ ∈ S, Complex.exp (L₀ ξ) = h ξ := fun ξ hξ => hL₀e hξ
  -- L₀' = logDeriv h on the strip
  have hL₀deriv : ∀ ξ ∈ S, deriv L₀ ξ = logDeriv h ξ := by
    intro ξ hξ
    have hev : h =ᶠ[nhds ξ] (fun ζ => Complex.exp (L₀ ζ)) := by
      filter_upwards [(isOpen_stripSet r R).mem_nhds hξ] with ζ hζ
      exact (hL₀exp ζ hζ).symm
    have hL₀at : HasDerivAt L₀ (deriv L₀ ξ) ξ := (hL₀an ξ hξ).differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun ζ => Complex.exp (L₀ ζ))
        (Complex.exp (L₀ ξ) * deriv L₀ ξ) ξ :=
      (Complex.hasStrictDerivAt_exp (L₀ ξ)).hasDerivAt.comp ξ hL₀at
    have hh' : HasDerivAt h (Complex.exp (L₀ ξ) * deriv L₀ ξ) ξ :=
      hcomp.congr_of_eventuallyEq hev
    rw [logDeriv_apply, hh'.deriv, hL₀exp ξ hξ]
    field_simp [hhne ξ hξ]
  -- vertical-segment FTC at the base radius
  set ξ₀ : ℂ := ((Real.log ρ : ℝ) : ℂ) with hξ₀def
  have hξ₀S : ξ₀ ∈ S := by
    constructor
    · show Real.log r < ξ₀.re
      rw [hξ₀def, Complex.ofReal_re]; exact Real.log_lt_log hr hρ1
    · show ξ₀.re < Real.log R
      rw [hξ₀def, Complex.ofReal_re]; exact Real.log_lt_log hρ0 hρ2
  have hvertS : ∀ θ : ℝ, ξ₀ + (θ : ℂ) * Complex.I ∈ S := fun θ =>
    stripSet_add_im hξ₀S (by simp)
  set v : ℝ → ℂ := fun θ => L₀ (ξ₀ + (θ : ℂ) * Complex.I) with hvdef
  have hpath : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => ξ₀ + (t : ℂ) * Complex.I) Complex.I θ := by
    intro θ
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ := by
      simpa using (hasDerivAt_id θ).ofReal_comp
    simpa using (h1.mul_const Complex.I).const_add ξ₀
  have hvderiv : ∀ θ : ℝ,
      HasDerivAt v (logDeriv h (ξ₀ + (θ:ℂ) * Complex.I) * Complex.I) θ := by
    intro θ
    have hL := (hL₀an _ (hvertS θ)).differentiableAt.hasDerivAt
    have hc := hL.comp θ (hpath θ)
    rwa [hL₀deriv _ (hvertS θ)] at hc
  have hlogcont : ContinuousOn (logDeriv h) S := by
    have h1 : ContinuousOn (deriv h) S := (hhan.deriv).continuousOn
    have h2 : ContinuousOn (fun ξ => deriv h ξ / h ξ) S :=
      h1.div hhan.continuousOn (fun ξ hξ => hhne ξ hξ)
    intro ξ hξ
    exact (h2 ξ hξ).congr (fun ζ _ => by rw [logDeriv_apply]) (by rw [logDeriv_apply])
  have hpc : Continuous (fun θ : ℝ => ξ₀ + (θ:ℂ) * Complex.I) := by fun_prop
  have hintcont : Continuous
      (fun θ : ℝ => logDeriv h (ξ₀ + (θ:ℂ) * Complex.I) * Complex.I) :=
    ((hlogcont.comp_continuous hpc hvertS)).mul continuous_const
  have hFTC : (∫ θ in (0:ℝ)..(2 * Real.pi),
      logDeriv h (ξ₀ + (θ:ℂ) * Complex.I) * Complex.I) = v (2 * Real.pi) - v 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => hvderiv θ) (hintcont.intervalIntegrable _ _)
  have hmatch : ∀ θ : ℝ, logDeriv h (ξ₀ + (θ:ℂ) * Complex.I) * Complex.I
      = logDeriv g (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I) := by
    intro θ
    have hξθ := hvertS θ
    have hcm : Complex.exp (ξ₀ + (θ:ℂ) * Complex.I) = circleMap 0 ρ θ :=
      exp_vertical_eq_circleMap hρ0 θ
    have hgd : DifferentiableAt ℂ g (Complex.exp (ξ₀ + (θ:ℂ) * Complex.I)) :=
      (hg _ (exp_mem_annulusSet hr hrR hξθ)).differentiableAt
    have hcomp : logDeriv h (ξ₀ + (θ:ℂ) * Complex.I)
        = logDeriv g (Complex.exp (ξ₀ + (θ:ℂ) * Complex.I))
          * deriv Complex.exp (ξ₀ + (θ:ℂ) * Complex.I) :=
      logDeriv_comp hgd Complex.differentiable_exp.differentiableAt
    rw [hcomp, Complex.deriv_exp, hcm]
    ring
  have hdefect0 : v (2 * Real.pi) - v 0 = 0 := by
    rw [← hFTC, intervalIntegral.integral_congr (fun θ _ => hmatch θ)]
    exact hwind
  -- the +2πi defect is 2πiℤ-valued, continuous, zero at ξ₀ ⟹ zero on the strip
  set D : ℂ → ℂ := fun ξ => L₀ (ξ + 2 * (Real.pi : ℂ) * Complex.I) - L₀ ξ with hDdef
  have him2π : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by simp
  have hshiftS : ∀ ξ ∈ S, ξ + 2 * (Real.pi : ℂ) * Complex.I ∈ S := fun ξ hξ =>
    stripSet_add_im hξ him2π
  have hDval : ∀ ξ ∈ S, ∃ n : ℤ, D ξ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    intro ξ hξ
    have hper : Complex.exp (ξ + 2 * (Real.pi : ℂ) * Complex.I) = Complex.exp ξ := by
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    have hexpD : Complex.exp (D ξ) = 1 := by
      rw [hDdef]
      show Complex.exp (L₀ (ξ + 2 * (Real.pi:ℂ) * Complex.I) - L₀ ξ) = 1
      rw [Complex.exp_sub, hL₀exp _ (hshiftS ξ hξ), hL₀exp ξ hξ]
      show g (Complex.exp (ξ + 2 * (Real.pi:ℂ) * Complex.I)) / g (Complex.exp ξ) = 1
      rw [hper, div_self (hhne ξ hξ)]
    exact Complex.exp_eq_one_iff.mp hexpD
  have hDcont : ContinuousOn D S := by
    have hsc : Continuous (fun ξ : ℂ => ξ + 2 * (Real.pi : ℂ) * Complex.I) := by fun_prop
    have h1 : ContinuousOn (fun ξ => L₀ (ξ + 2 * (Real.pi : ℂ) * Complex.I)) S :=
      hL₀an.continuousOn.comp hsc.continuousOn hshiftS
    exact h1.sub hL₀an.continuousOn
  have hDξ₀ : D ξ₀ = 0 := by
    have hv2 : v (2 * Real.pi) = L₀ (ξ₀ + 2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hvdef]; push_cast; ring_nf
    have hv0 : v 0 = L₀ ξ₀ := by rw [hvdef]; push_cast; ring_nf
    have := hdefect0
    rw [hv2, hv0] at this
    exact this
  have hDzero : ∀ ξ ∈ S, D ξ = 0 := by
    have hgap : ∀ ξ ∈ S, ∀ ζ ∈ S, ‖D ξ - D ζ‖ < 2 * Real.pi → D ξ = D ζ := by
      intro ξ hξ ζ hζ hlt
      obtain ⟨n, hn⟩ := hDval ξ hξ
      obtain ⟨p, hp⟩ := hDval ζ hζ
      rw [hn, hp, ← sub_mul] at hlt
      rw [hn, hp]
      have h2π : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
        simp [abs_of_pos Real.pi_pos]
      rw [norm_mul, h2π] at hlt
      have hnp : n = p := by
        by_contra hne
        have hcast : ((n:ℂ) - p) = ((n - p : ℤ) : ℂ) := by push_cast; ring
        have hnz : (n - p : ℤ) ≠ 0 := sub_ne_zero.mpr hne
        have h1 : (1 : ℝ) ≤ ‖((n:ℂ) - p)‖ := by
          rw [hcast, Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs hnz
        nlinarith [Real.pi_pos]
      rw [hnp]
    set E : Set ℂ := {ξ | ξ ∈ S ∧ D ξ = 0} with hEdef
    set F : Set ℂ := {ξ | ξ ∈ S ∧ D ξ ≠ 0} with hFdef
    have hnearD : ∀ ξ ∈ S, ∀ᶠ ζ in nhds ξ, ζ ∈ S ∧ ‖D ζ - D ξ‖ < 2 * Real.pi := by
      intro ξ hξS
      have h1 : ∀ᶠ ζ in nhds ξ, ζ ∈ S := (isOpen_stripSet r R).mem_nhds hξS
      have hc : ContinuousAt D ξ :=
        hDcont.continuousAt ((isOpen_stripSet r R).mem_nhds hξS)
      have h2 := hc.eventually (Metric.ball_mem_nhds (D ξ)
        (by positivity : (0:ℝ) < 2 * Real.pi))
      filter_upwards [h1, h2] with ζ h1' h2'
      refine ⟨h1', ?_⟩
      rw [← dist_eq_norm]
      exact h2'
    have hopenE : IsOpen E := by
      rw [isOpen_iff_mem_nhds]
      rintro ξ ⟨hξS, hξD⟩
      filter_upwards [hnearD ξ hξS] with ζ hζ
      exact ⟨hζ.1, by rw [hgap ζ hζ.1 ξ hξS hζ.2, hξD]⟩
    have hopenF : IsOpen F := by
      rw [isOpen_iff_mem_nhds]
      rintro ξ ⟨hξS, hξD⟩
      filter_upwards [hnearD ξ hξS] with ζ hζ
      exact ⟨hζ.1, by rw [hgap ζ hζ.1 ξ hξS hζ.2]; exact hξD⟩
    intro ξ hξ
    by_contra hcon
    have hpre : IsPreconnected S := (convex_stripSet r R).isPreconnected
    have hcover : S ⊆ E ∪ F := by
      intro ζ hζ
      by_cases hD : D ζ = 0
      · exact Or.inl ⟨hζ, hD⟩
      · exact Or.inr ⟨hζ, hD⟩
    obtain ⟨ζ, _, ⟨_, hζ0⟩, ⟨_, hζne⟩⟩ := hpre E F hopenE hopenF hcover
      ⟨ξ₀, hξ₀S, hξ₀S, hDξ₀⟩ ⟨ξ, hξ, hξ, hcon⟩
    exact hζne hζ0
  -- periodicity for all integer multiples of 2πi
  have hstep : ∀ ξ ∈ S, L₀ (ξ + 2 * (Real.pi:ℂ) * Complex.I) = L₀ ξ := by
    intro ξ hξ
    have := hDzero ξ hξ
    rw [hDdef] at this
    exact sub_eq_zero.mp this
  have hperZ : ∀ ξ ∈ S, ∀ k : ℤ,
      L₀ (ξ + (k : ℂ) * (2 * (Real.pi:ℂ) * Complex.I)) = L₀ ξ := by
    intro ξ hξ k
    have hmem : ∀ j : ℤ, ξ + (j : ℂ) * (2 * (Real.pi:ℂ) * Complex.I) ∈ S := fun j =>
      stripSet_add_im hξ (by simp)
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
        have harg : ξ + ((n : ℤ) + 1 : ℂ) * (2 * (Real.pi:ℂ) * Complex.I)
            = (ξ + ((n : ℤ) : ℂ) * (2 * (Real.pi:ℂ) * Complex.I))
              + 2 * (Real.pi:ℂ) * Complex.I := by push_cast; ring
        rw [show (((n : ℤ) + 1 : ℤ) : ℂ) = ((n : ℤ) : ℂ) + 1 by push_cast; ring, harg,
          hstep _ (hmem n)]
        exact ih
    | pred n ih =>
        have hs := hstep _ (hmem (-(n : ℤ) - 1))
        have harg : ξ + ((-(n : ℤ) - 1 : ℤ) : ℂ) * (2 * (Real.pi:ℂ) * Complex.I)
            + 2 * (Real.pi:ℂ) * Complex.I
            = ξ + ((-(n : ℤ) : ℤ) : ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by
          push_cast; ring
        rw [harg] at hs
        rw [← hs]
        exact ih
  -- descend through exp via the principal log
  refine ⟨fun w => L₀ (Complex.log w), ?_, ?_⟩
  · intro w₀ hw₀
    have hw₀ne : w₀ ≠ 0 := annulus_mem_ne_zero hr hw₀
    set ξw := Complex.log w₀ with hξwdef
    have hξwS : ξw ∈ S := log_mem_stripSet hr hw₀
    have hlogdiff : DifferentiableOn ℂ Complex.log Complex.slitPlane := fun z hz =>
      (Complex.differentiableAt_log hz).differentiableWithinAt
    have hlogan : AnalyticOnNhd ℂ Complex.log Complex.slitPlane :=
      hlogdiff.analyticOnNhd Complex.isOpen_slitPlane
    set ℓ : ℂ → ℂ := fun w => ξw + Complex.log (w / w₀) with hℓdef
    have hℓw₀ : ℓ w₀ = ξw := by
      rw [hℓdef]; simp [div_self hw₀ne]
    have hℓan : AnalyticAt ℂ ℓ w₀ := by
      have hdiv : AnalyticAt ℂ (fun w : ℂ => w / w₀) w₀ :=
        (analyticAt_id).div analyticAt_const hw₀ne
      have hmem1 : w₀ / w₀ ∈ Complex.slitPlane := by
        rw [div_self hw₀ne]; exact Complex.one_mem_slitPlane
      have hcomp : AnalyticAt ℂ (Complex.log ∘ (fun w : ℂ => w / w₀)) w₀ :=
        AnalyticAt.comp (g := Complex.log) (f := fun w : ℂ => w / w₀)
          (hlogan _ hmem1) hdiv
      exact (analyticAt_const).add hcomp
    have hℓcont : ContinuousAt ℓ w₀ := hℓan.continuousAt
    have hev : (fun w => L₀ (Complex.log w)) =ᶠ[nhds w₀] fun w => L₀ (ℓ w) := by
      have h1 : ∀ᶠ w in nhds w₀, w ∈ A := (isOpen_annulusSet r R).mem_nhds hw₀
      have h2 : ∀ᶠ w in nhds w₀, ℓ w ∈ S := by
        have : S ∈ nhds (ℓ w₀) := by
          rw [hℓw₀]; exact (isOpen_stripSet r R).mem_nhds hξwS
        exact hℓcont.eventually_mem this
      filter_upwards [h1, h2] with w hwA hwℓ
      have hwne : w ≠ 0 := annulus_mem_ne_zero hr hwA
      have hlogS : Complex.log w ∈ S := log_mem_stripSet hr hwA
      have hexpeq : Complex.exp (Complex.log w) = Complex.exp (ℓ w) := by
        rw [Complex.exp_log hwne, hℓdef]
        show w = Complex.exp (ξw + Complex.log (w / w₀))
        rw [Complex.exp_add, hξwdef, Complex.exp_log hw₀ne,
          Complex.exp_log (div_ne_zero hwne hw₀ne)]
        field_simp
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexpeq
      rw [hn]
      exact hperZ _ hwℓ n
    have hLℓ : AnalyticAt ℂ (fun w => L₀ (ℓ w)) w₀ := by
      have := (hL₀an _ (by rw [← hℓw₀] at hξwS; exact hξwS)).comp hℓan
      exact this
    exact hLℓ.congr hev.symm
  · intro w hw
    have hwne : w ≠ 0 := annulus_mem_ne_zero hr hw
    rw [hL₀exp _ (log_mem_stripSet hr hw)]
    show g (Complex.exp (Complex.log w)) = g w
    rw [Complex.exp_log hwne]

/-- The core winding of the monomial `w ^ n` is `n · 2πi`. -/
theorem winding_zpow_circle {ρ : ℝ} (hρ : 0 < ρ) (n : ℤ) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
      logDeriv (fun w : ℂ => w ^ n) (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
    = (n : ℂ) * (2 * Real.pi * Complex.I) := by
  have hne : ∀ θ : ℝ, circleMap 0 ρ θ ≠ 0 := fun θ => circleMap_ne_center (ne_of_gt hρ)
  have hcongr : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      logDeriv (fun w : ℂ => w ^ n) (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)
        = (n : ℂ) * Complex.I := by
    intro θ _
    rw [logDeriv_zpow]
    field_simp [hne θ]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const]
  rw [sub_zero, Complex.real_smul]
  push_cast
  ring

/-- **Analytic `2^k`-th root on a round annulus, from dyadically divisible core winding.** If the
core winding of `g` is `2πi·(2^k·m)`, then `g` has an analytic nonvanishing `2^k`-th root on the
whole annulus: divide out the monomial `w^{2^k·m}` (winding `0` remains), take the annulus
logarithm, and set `s = w^m · exp(L/2^k)`. -/
theorem exists_pow_root_on_annulus {r R ρ : ℝ} (hr : 0 < r) (hρ1 : r < ρ) (hρ2 : ρ < R)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (annulusSet r R))
    (hgne : ∀ w ∈ annulusSet r R, g w ≠ 0) (k : ℕ) (m : ℤ)
    (hwind : (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv g (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I))
      = ((2 ^ k * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (annulusSet r R) ∧
      (∀ w ∈ annulusSet r R, s w ^ (2 ^ k) = g w) ∧
      (∀ w ∈ annulusSet r R, s w ≠ 0) := by
  have hρ0 : 0 < ρ := lt_trans hr hρ1
  have hcmA : ∀ θ : ℝ, circleMap 0 ρ θ ∈ annulusSet r R := by
    intro θ
    have hnorm : ‖circleMap 0 ρ θ‖ = ρ := by
      simp [circleMap, Complex.norm_exp, abs_of_pos hρ0]
    exact ⟨by rw [hnorm]; exact hρ1, by rw [hnorm]; exact hρ2⟩
  set n : ℤ := 2 ^ k * m with hndef
  set p : ℂ → ℂ := fun w => w ^ (-n) with hpdef
  have hp_an : AnalyticOnNhd ℂ p (annulusSet r R) := by
    have hdiff : DifferentiableOn ℂ p (annulusSet r R) := fun w hw =>
      (differentiableAt_zpow.mpr (Or.inl (annulus_mem_ne_zero hr hw))).differentiableWithinAt
    exact hdiff.analyticOnNhd (isOpen_annulusSet r R)
  have hp_ne : ∀ w ∈ annulusSet r R, p w ≠ 0 := fun w hw =>
    zpow_ne_zero _ (annulus_mem_ne_zero hr hw)
  set gm : ℂ → ℂ := fun w => g w * p w with hgmdef
  have hgm_an : AnalyticOnNhd ℂ gm (annulusSet r R) := hg.mul hp_an
  have hgm_ne : ∀ w ∈ annulusSet r R, gm w ≠ 0 := fun w hw =>
    mul_ne_zero (hgne w hw) (hp_ne w hw)
  -- winding of gm vanishes
  have hgmwind : (∫ θ in (0:ℝ)..(2 * Real.pi),
      logDeriv gm (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) = 0 := by
    have hsplit : ∀ θ : ℝ,
        logDeriv gm (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)
        = logDeriv g (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)
          + logDeriv p (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I) := by
      intro θ
      have hmul : logDeriv gm (circleMap 0 ρ θ)
          = logDeriv g (circleMap 0 ρ θ) + logDeriv p (circleMap 0 ρ θ) := by
        rw [hgmdef]
        exact logDeriv_mul _ (hgne _ (hcmA θ)) (hp_ne _ (hcmA θ))
          ((hg _ (hcmA θ)).differentiableAt) ((hp_an _ (hcmA θ)).differentiableAt)
      rw [hmul]; ring
    have hcont1 : Continuous (fun θ : ℝ =>
        logDeriv g (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) := by
      have hld : ContinuousOn (logDeriv g) (annulusSet r R) := by
        have h2 : ContinuousOn (fun w => deriv g w / g w) (annulusSet r R) :=
          (hg.deriv).continuousOn.div hg.continuousOn (fun w hw => hgne w hw)
        intro w hw
        exact (h2 w hw).congr (fun ζ _ => by rw [logDeriv_apply]) (by rw [logDeriv_apply])
      exact ((hld.comp_continuous (continuous_circleMap 0 ρ) hcmA)).mul
        ((continuous_circleMap 0 ρ).mul continuous_const)
    have hcont2 : Continuous (fun θ : ℝ =>
        logDeriv p (circleMap 0 ρ θ) * (circleMap 0 ρ θ * Complex.I)) := by
      have hld : ContinuousOn (logDeriv p) (annulusSet r R) := by
        have h2 : ContinuousOn (fun w => deriv p w / p w) (annulusSet r R) :=
          (hp_an.deriv).continuousOn.div hp_an.continuousOn (fun w hw => hp_ne w hw)
        intro w hw
        exact (h2 w hw).congr (fun ζ _ => by rw [logDeriv_apply]) (by rw [logDeriv_apply])
      exact ((hld.comp_continuous (continuous_circleMap 0 ρ) hcmA)).mul
        ((continuous_circleMap 0 ρ).mul continuous_const)
    rw [intervalIntegral.integral_congr (fun θ _ => hsplit θ),
      intervalIntegral.integral_add (hcont1.intervalIntegrable _ _)
        (hcont2.intervalIntegrable _ _)]
    rw [hwind, winding_zpow_circle hρ0 (-n)]
    push_cast
    ring
  obtain ⟨L, hLan, hLexp⟩ := exists_log_on_annulus hr hρ1 hρ2 hgm_an hgm_ne hgmwind
  have h2k : ((2 ^ k : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero k two_ne_zero)
  refine ⟨fun w => w ^ m * Complex.exp (L w / ((2 ^ k : ℕ) : ℂ)), ?_, ?_, ?_⟩
  · intro w hw
    have hzm : AnalyticAt ℂ (fun w : ℂ => w ^ m) w := by
      have hdiff : DifferentiableOn ℂ (fun w : ℂ => w ^ m) (annulusSet r R) := fun ζ hζ =>
        (differentiableAt_zpow.mpr (Or.inl (annulus_mem_ne_zero hr hζ))).differentiableWithinAt
      exact hdiff.analyticOnNhd (isOpen_annulusSet r R) w hw
    exact hzm.mul (((hLan w hw).div analyticAt_const h2k).cexp)
  · intro w hw
    have hwne : w ≠ 0 := annulus_mem_ne_zero hr hw
    rw [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ h2k, hLexp w hw]
    rw [hgmdef]
    show (w ^ m) ^ (2 ^ k) * (g w * p w) = g w
    rw [hpdef]
    show (w ^ m) ^ (2 ^ k) * (g w * w ^ (-n)) = g w
    rw [← zpow_natCast (w ^ m) (2 ^ k), ← zpow_mul]
    rw [show m * ((2 ^ k : ℕ) : ℤ) = n from by rw [hndef]; push_cast; ring]
    calc w ^ n * (g w * w ^ (-n)) = g w * (w ^ n * w ^ (-n)) := by ring
      _ = g w := by rw [← zpow_add₀ hwne]; simp
  · intro w hw
    exact mul_ne_zero (zpow_ne_zero _ (annulus_mem_ne_zero hr hw)) (Complex.exp_ne_zero _)

end Bottcher
