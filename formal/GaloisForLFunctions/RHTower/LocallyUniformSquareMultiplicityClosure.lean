import GaloisForLFunctions.HTGeometry.LocallyUniformZeroCountTransfer
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantMultiplicityEventually

/-!
# Locally uniform square limits retain even local multiplicity

Pointwise multiplicity parity is not invariant under an arbitrary continuous deformation of
holomorphic functions.  There is, however, a precise closedness statement useful for proposed
square-approximation mechanisms: a locally uniform limit of global holomorphic squares has even
zero count on every isolating disc, hence even multiplicity at every isolated zero.

This result is purely a receiver theorem.  It does not produce square approximants to `riemannXi`
or an analytic square root on `rightHalf`.
-/

open Complex Metric Set Filter Topology

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The normalized argument-principle count of a global holomorphic power is multiplied by the
power. -/
theorem zeroSumBall_pow {g : ℂ → ℂ} (hg : Differentiable ℂ g) (c : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (n : ℕ) :
    zeroSumBall (fun z => g z ^ n) c r = (n : ℂ) * zeroSumBall g c r := by
  rw [zeroSumBall, zeroSumBall]
  rw [circleIntegral.integral_congr hr fun z _ => logDeriv_fun_pow (hg z) n]
  rw [circleIntegral.integral_const_mul]
  ring

/-- A locally uniform limit of global holomorphic squares has an even total zero count inside
every circle on which the limit is nonvanishing. -/
theorem exists_even_zeroSumBall_of_tendstoLocallyUniformly_squares
    {α : Type*} {p : Filter α} [NeBot p]
    {G F : α → ℂ → ℂ} {f : ℂ → ℂ}
    (hG : ∀ a, Differentiable ℂ (G a))
    (hF : ∀ a, F a = fun z => G a z ^ 2)
    (hf : Differentiable ℂ f)
    (huniform : TendstoLocallyUniformly F f p)
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hne : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∃ N : ℕ, zeroSumBall f c r = ((2 * N : ℕ) : ℂ) := by
  have hFd : ∀ a, Differentiable ℂ (F a) := by
    intro a
    rw [hF a]
    exact (hG a).pow 2
  have hstable : ∀ᶠ a in p, zeroSumBall (F a) c r = zeroSumBall f c r :=
    eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hFd hf huniform hr hrR hne
  have hconv : TendstoUniformlyOn F f p (closedBall c R) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall c R)).mp
      huniform.tendstoLocallyUniformlyOn
  have hFboundary : ∀ᶠ a in p, ∀ z ∈ sphere c r, F a z ≠ 0 :=
    eventually_forall_ne_zero_on_sphere_of_tendstoUniformlyOn hr hrR
      hf.continuous.continuousOn hne hconv
  have hGboundary : ∀ᶠ a in p, ∀ z ∈ sphere c r, G a z ≠ 0 := by
    filter_upwards [hFboundary] with a ha
    intro z hz hzero
    apply ha z hz
    rw [hF a]
    change G a z ^ 2 = 0
    rw [hzero]
    norm_num
  obtain ⟨a, hstablea, hGboundarya⟩ := (hstable.and hGboundary).exists
  obtain ⟨N, hN⟩ := exists_nat_zeroSumBall hr hrR isOpen_univ (by simp)
    (hG a).differentiableOn hGboundarya
  refine ⟨N, ?_⟩
  rw [← hstablea, hF a, zeroSumBall_pow (hG a) c hr.le 2, hN]
  push_cast
  ring

/-- In particular, an isolated zero of a locally uniform limit of global holomorphic squares has
even analytic order. -/
theorem even_analyticOrderAt_of_tendstoLocallyUniformly_squares
    {α : Type*} {p : Filter α} [NeBot p]
    {G F : α → ℂ → ℂ} {f : ℂ → ℂ}
    (hG : ∀ a, Differentiable ℂ (G a))
    (hF : ∀ a, F a = fun z => G a z ^ 2)
    (hf : Differentiable ℂ f)
    (huniform : TendstoLocallyUniformly F f p)
    {c : ℂ} {d : ℕ} (hord : analyticOrderAt f c = (d : ℕ∞))
    {r R R' : ℝ} (hr : 0 < r) (hrR : r < R) (hrR' : r < R')
    (hne : ∀ z ∈ ball c R', z ≠ c → f z ≠ 0) :
    Even d := by
  have hboundary : ∀ z ∈ sphere c r, f z ≠ 0 := by
    intro z hz
    have hdist : dist z c = r := mem_sphere.mp hz
    apply hne z (by rw [mem_ball, hdist]; exact hrR')
    intro hzc
    rw [hzc, dist_self] at hdist
    exact hr.ne hdist
  obtain ⟨N, hN⟩ := exists_even_zeroSumBall_of_tendstoLocallyUniformly_squares
    hG hF hf huniform hr hrR hboundary
  have hcount : zeroSumBall f c r = (d : ℂ) := by
    have hlocal := circleIntegral_logDeriv_eq_analyticOrder_local hf hord hne hr hrR'
    rw [zeroSumBall]
    rw [show logDeriv f = fun z => deriv f z / f z by
      funext z
      exact logDeriv_apply f z]
    rw [hlocal]
    field_simp [twoPiI_ne_zero]
  have hcast : (d : ℂ) = ((2 * N : ℕ) : ℂ) := hcount.symm.trans hN
  have hd : d = 2 * N := by exact_mod_cast hcast
  refine ⟨N, ?_⟩
  omega

/-! ## Domain-local form -/

/-- Compact-open convergence on an open domain preserves the full zero count on any contained
closed disc whose inner circle is zero-free for the limit. -/
theorem eventually_zeroSumBall_eq_of_tendstoLocallyUniformlyOn
    {α : Type*} {p : Filter α} [NeBot p]
    {U : Set ℂ} (hU : IsOpen U)
    {F : α → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ a, DifferentiableOn ℂ (F a) U)
    (hf : DifferentiableOn ℂ f U)
    (huniform : TendstoLocallyUniformlyOn F f p U)
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hsub : closedBall c R ⊆ U)
    (hne : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∀ᶠ a in p, zeroSumBall (F a) c r = zeroSumBall f c r := by
  obtain ⟨ε, hε, hstable⟩ := exists_eps_zeroSumBall_eq hr hrR hU hsub hf hne
  have hconv : TendstoUniformlyOn F f p (closedBall c R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp
      huniform (closedBall c R) hsub (isCompact_closedBall c R)
  have hclose : ∀ᶠ a in p, ∀ z ∈ closedBall c R, ‖F a z - f z‖ ≤ ε := by
    have hlt := (Metric.tendstoUniformlyOn_iff.mp hconv) ε hε
    filter_upwards [hlt] with a ha
    intro z hz
    have := ha z hz
    simpa only [dist_eq_norm, norm_sub_rev] using this.le
  filter_upwards [hclose] with a ha
  exact (hstable (F a) (hF a) ha).2

/-- On a circle contained in an open differentiability domain, the normalized zero count of a
power is multiplied by its exponent. -/
theorem zeroSumBall_pow_of_differentiableOn
    {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (c : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hsphere : sphere c r ⊆ U) (n : ℕ) :
    zeroSumBall (fun z => g z ^ n) c r = (n : ℂ) * zeroSumBall g c r := by
  rw [zeroSumBall, zeroSumBall]
  rw [circleIntegral.integral_congr hr fun z hz =>
    logDeriv_fun_pow ((hg z (hsphere hz)).differentiableAt (hU.mem_nhds (hsphere hz))) n]
  rw [circleIntegral.integral_const_mul]
  ring

/-- A locally uniform limit of squares holomorphic on one open domain has even total zero count
inside every compactly contained circle that is zero-free for the limit. -/
theorem exists_even_zeroSumBall_of_tendstoLocallyUniformlyOn_squares
    {α : Type*} {p : Filter α} [NeBot p]
    {U : Set ℂ} (hU : IsOpen U)
    {G F : α → ℂ → ℂ} {f : ℂ → ℂ}
    (hG : ∀ a, DifferentiableOn ℂ (G a) U)
    (hF : ∀ a, F a = fun z => G a z ^ 2)
    (hf : DifferentiableOn ℂ f U)
    (huniform : TendstoLocallyUniformlyOn F f p U)
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hsub : closedBall c R ⊆ U)
    (hne : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∃ N : ℕ, zeroSumBall f c r = ((2 * N : ℕ) : ℂ) := by
  have hFd : ∀ a, DifferentiableOn ℂ (F a) U := by
    intro a
    rw [hF a]
    exact (hG a).pow 2
  have hstable : ∀ᶠ a in p, zeroSumBall (F a) c r = zeroSumBall f c r :=
    eventually_zeroSumBall_eq_of_tendstoLocallyUniformlyOn
      hU hFd hf huniform hr hrR hsub hne
  have hconv : TendstoUniformlyOn F f p (closedBall c R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp
      huniform (closedBall c R) hsub (isCompact_closedBall c R)
  have hFboundary : ∀ᶠ a in p, ∀ z ∈ sphere c r, F a z ≠ 0 :=
    eventually_forall_ne_zero_on_sphere_of_tendstoUniformlyOn hr hrR
      ((hf.mono (fun z hz => hsub (by
        rw [mem_closedBall, mem_sphere.mp hz]
        exact hrR.le))).continuousOn) hne hconv
  have hGboundary : ∀ᶠ a in p, ∀ z ∈ sphere c r, G a z ≠ 0 := by
    filter_upwards [hFboundary] with a ha
    intro z hz hzero
    apply ha z hz
    rw [hF a]
    change G a z ^ 2 = 0
    rw [hzero]
    norm_num
  obtain ⟨a, hstablea, hGboundarya⟩ := (hstable.and hGboundary).exists
  obtain ⟨N, hN⟩ := exists_nat_zeroSumBall hr hrR hU hsub (hG a) hGboundarya
  refine ⟨N, ?_⟩
  rw [← hstablea, hF a,
    zeroSumBall_pow_of_differentiableOn hU (hG a) c hr.le
      (fun z hz => hsub (by
        rw [mem_closedBall, mem_sphere.mp hz]
        exact hrR.le)) 2,
    hN]
  push_cast
  ring

/-- Argument-principle count of one isolated zero in an arbitrary open analytic domain equals its
local analytic order. -/
theorem zeroSumBall_eq_analyticOrderAt_of_isolated_on
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) {c : ℂ} (hcU : c ∈ U)
    {d : ℕ} (hord : analyticOrderAt f c = (d : ℕ∞))
    {r R R' : ℝ} (hr : 0 < r) (hrR : r < R) (hrR' : r < R')
    (hsub : closedBall c R ⊆ U)
    (hne : ∀ z ∈ ball c R', z ≠ c → f z ≠ 0) :
    zeroSumBall f c r = (d : ℂ) := by
  have hboundary : ∀ z ∈ sphere c r, f z ≠ 0 := by
    intro z hz
    have hdist : dist z c = r := mem_sphere.mp hz
    apply hne z (by rw [mem_ball, hdist]; exact hrR')
    intro hzc
    rw [hzc, dist_self] at hdist
    exact hr.ne hdist
  obtain ⟨Z, hZball, hZzero, hsum⟩ :=
    exists_zeroSet_zeroSumBall hr hrR hU hsub hf.differentiableOn hboundary
  rw [hsum]
  have hZeq : ∀ z ∈ Z, z = c := by
    intro z hz
    by_contra hzc
    exact hne z (by
      rw [mem_ball]
      exact lt_trans (mem_ball.mp (hZball z hz)) hrR') hzc
      ((hZzero z (hZball z hz)).mpr hz)
  by_cases hcZ : c ∈ Z
  · rw [Finset.sum_eq_single c]
    · simp [zeroMult, hord]
    · intro b hb hbc
      exact (hbc (hZeq b hb)).elim
    · exact fun hcnot => (hcnot hcZ).elim
  · have hZempty : Z = ∅ := by
      ext z
      constructor
      · intro hz
        exact (hcZ (by simpa [hZeq z hz] using hz)).elim
      · simp
    rw [hZempty]
    simp only [Finset.sum_empty]
    by_contra hd
    have hdne : d ≠ 0 := by
      intro hd0
      apply hd
      rw [hd0]
      norm_num
    have hordne : analyticOrderAt f c ≠ 0 := by
      rw [hord]
      simpa using hdne
    have hczero : f c = 0 := by
      by_contra hfne
      exact hordne ((hf c hcU).analyticOrderAt_eq_zero.mpr hfne)
    exact hcZ ((hZzero c (mem_ball_self hr)).mp hczero)

/-- Every isolated zero of a locally uniform limit of squares holomorphic on one open domain has
even analytic order. -/
theorem even_analyticOrderAt_of_tendstoLocallyUniformlyOn_squares
    {α : Type*} {p : Filter α} [NeBot p]
    {U : Set ℂ} (hU : IsOpen U)
    {G F : α → ℂ → ℂ} {f : ℂ → ℂ}
    (hG : ∀ a, AnalyticOnNhd ℂ (G a) U)
    (hF : ∀ a, F a = fun z => G a z ^ 2)
    (hf : AnalyticOnNhd ℂ f U)
    (huniform : TendstoLocallyUniformlyOn F f p U)
    {c : ℂ} (hcU : c ∈ U) {d : ℕ}
    (hord : analyticOrderAt f c = (d : ℕ∞))
    {r R R' : ℝ} (hr : 0 < r) (hrR : r < R) (hrR' : r < R')
    (hsub : closedBall c R ⊆ U)
    (hne : ∀ z ∈ ball c R', z ≠ c → f z ≠ 0) :
    Even d := by
  have hboundary : ∀ z ∈ sphere c r, f z ≠ 0 := by
    intro z hz
    have hdist : dist z c = r := mem_sphere.mp hz
    apply hne z (by rw [mem_ball, hdist]; exact hrR')
    intro hzc
    rw [hzc, dist_self] at hdist
    exact hr.ne hdist
  obtain ⟨N, hN⟩ :=
    exists_even_zeroSumBall_of_tendstoLocallyUniformlyOn_squares
      hU (fun a => (hG a).differentiableOn) hF hf.differentiableOn huniform
      hr hrR hsub hboundary
  have hcount : zeroSumBall f c r = (d : ℂ) :=
    zeroSumBall_eq_analyticOrderAt_of_isolated_on
      hU hf hcU hord hr hrR hrR' hsub hne
  have hcast : (d : ℂ) = ((2 * N : ℕ) : ℂ) := hcount.symm.trans hN
  have hd : d = 2 * N := by exact_mod_cast hcast
  refine ⟨N, ?_⟩
  omega

/-- Every finite local order of a compact-open limit of holomorphic squares is even.  Openness of
the domain and isolated-zero theory supply the nested discs required by the argument principle. -/
theorem even_analyticOrderAt_of_tendstoLocallyUniformlyOn_squares_of_order
    {α : Type*} {p : Filter α} [NeBot p]
    {U : Set ℂ} (hU : IsOpen U)
    {G F : α → ℂ → ℂ} {f : ℂ → ℂ}
    (hG : ∀ a, AnalyticOnNhd ℂ (G a) U)
    (hF : ∀ a, F a = fun z => G a z ^ 2)
    (hf : AnalyticOnNhd ℂ f U)
    (huniform : TendstoLocallyUniformlyOn F f p U)
    {c : ℂ} (hcU : c ∈ U) {d : ℕ}
    (hord : analyticOrderAt f c = (d : ℕ∞)) :
    Even d := by
  have hpunct : ∀ᶠ z in 𝓝[≠] c, f z ≠ 0 := by
    rcases (hf c hcU).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · have htop : analyticOrderAt f c = ⊤ := analyticOrderAt_eq_top.mpr hzero
      rw [hord] at htop
      exact (ENat.coe_ne_top d htop).elim
    · exact hne
  have hpunct' : ∀ᶠ z in 𝓝 c, z ∈ ({c} : Set ℂ)ᶜ → f z ≠ 0 :=
    eventually_nhdsWithin_iff.mp hpunct
  obtain ⟨εi, hεi, hi⟩ := Metric.eventually_nhds_iff.mp hpunct'
  obtain ⟨εU, hεU, hUball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hcU)
  let δ := min εi εU
  have hδ : 0 < δ := lt_min hεi hεU
  let R := δ / 2
  let r := δ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r, R]; linarith
  have hRδ : R < δ := by dsimp [R]; linarith
  have hsub : closedBall c R ⊆ U := by
    intro z hz
    apply hUball
    exact lt_of_le_of_lt (mem_closedBall.mp hz) (hRδ.trans_le (min_le_right _ _))
  have hne : ∀ z ∈ ball c R, z ≠ c → f z ≠ 0 := by
    intro z hz hzc
    apply hi
    · exact (mem_ball.mp hz).trans (hRδ.trans_le (min_le_left _ _))
    · simpa using hzc
  exact even_analyticOrderAt_of_tendstoLocallyUniformlyOn_squares
    hU hG hF hf huniform hcU hord hr hrR hrR hsub hne

end GaloisForLFunctions.RHTower
