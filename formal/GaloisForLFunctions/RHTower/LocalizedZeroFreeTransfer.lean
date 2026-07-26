import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer

/-!
# Zero transfer needs only local zero-freeness, not global real-rootedness

The zero-transfer connector of this development asks for entire approximants **all** of whose zeros
are real.  That is a global condition, and by the Laguerre–Pólya characterisation it is equivalent to
the hypothesis itself, so the whole difficulty sits in producing one such family.

The condition can be localized.  Hurwitz's existence mechanism is a statement about one ball: if the
limit vanishes at `z`, the approximants must eventually vanish near `z`.  Contrapositively, an
approximating family that is zero-free on a **single** closed ball already forces the limit to be
nonzero at its centre — and nothing is required of its zeros anywhere else.

> **To prove the hypothesis it suffices to produce, for each off-critical point separately, a
> sequence of entire functions converging locally uniformly to `XiC` and zero-free on some ball
> around that point.  The sequences may differ from point to point and need not be real-rooted
> anywhere.**

This is strictly weaker than the global criterion: a real-rooted family is zero-free on every ball
centred off the real axis, but a family zero-free near one point need not be real-rooted at all.  It
converts a single global construction into a family of independent local ones, each of which may use
whatever structure is available near its own point.

This file formalizes the local transfer and the resulting localized criterion.
-/

open Complex Metric Set Filter Topology

namespace RHTower

/-- **Local zero-freeness transfer.**  If the approximants are eventually zero-free on a closed ball
and converge locally uniformly to a nonzero entire limit, the limit does not vanish at the centre. -/
theorem ne_zero_of_eventually_zeroFree_closedBall
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformly Fn F atTop)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    {a z : ℂ} {R : ℝ} (hR : 0 < R) (ha : F a ≠ 0)
    (hfree : ∀ᶠ n in atTop, ∀ w ∈ closedBall z R, Fn n w ≠ 0) :
    F z ≠ 0 := by
  intro hz
  have hnotEventuallyZero : ¬ ∀ᶠ w in 𝓝 z, F w = 0 := by
    intro hev
    have hall := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hev (Set.mem_univ a)
    exact ha hall
  have hpunct : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 :=
    (hF z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      hnotEventuallyZero
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  let r : ℝ := min R (δ / 2)
  have hr : 0 < r := lt_min hR (half_pos hδ)
  have hrR : r ≤ R := min_le_left _ _
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ)
  have hsphere : ∀ w ∈ sphere z r, F w ≠ 0 := by
    intro w hw
    apply hδsub
    exact ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hrδ),
      Set.mem_compl_singleton_iff.mpr (Metric.ne_of_mem_sphere hw hr.ne')⟩
  have hlocal := eventually_exists_zero_closedBall_of_tendstoLocallyUniformly
    hconv (fun w => (hF w (Set.mem_univ w)).differentiableAt) hFn hr hz hsphere
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlocal
  obtain ⟨M, hM⟩ := eventually_atTop.1 hfree
  obtain ⟨w, hwball, hwzero⟩ := hN (max N M) (le_max_left _ _)
  have hwR : w ∈ closedBall z R :=
    Metric.closedBall_subset_closedBall hrR hwball
  exact hM (max N M) (le_max_right _ _) w hwR hwzero

/-- **The localized criterion.**  If every point off the real axis admits its own locally uniform
approximating family that is zero-free near it, the Riemann hypothesis follows. -/
theorem riemannHypothesis_of_pointwise_zeroFree_approximants
    (hloc : ∀ z : ℂ, z.im ≠ 0 → ∃ (Fn : ℕ → ℂ → ℂ) (R : ℝ), 0 < R ∧
      TendstoLocallyUniformly Fn XiC atTop ∧
      (∀ᶠ n in atTop, Differentiable ℂ (Fn n)) ∧
      (∀ᶠ n in atTop, ∀ w ∈ closedBall z R, Fn n w ≠ 0)) :
    RiemannHypothesis := by
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
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  have hne : z.im ≠ 0 := by
    rw [hzIm]
    have := mem_rightHalf.mp hρ
    intro h
    exact (ne_of_gt this) (by linarith)
  obtain ⟨Fn, R, hR, hconv, hFn, hfree⟩ := hloc z hne
  exact ne_zero_of_eventually_zeroFree_closedBall hconv XiC_analytic hFn hR
    XiC_zero_ne hfree hXiC

/-- The localized criterion is implied by the global one: a real-rooted family is zero-free on every
ball centred off the real axis. -/
theorem pointwise_from_real_rooted
    {Fn : ℕ → ℂ → ℂ} {z : ℂ} (hz : z.im ≠ 0)
    (hreal : ∀ᶠ n in atTop, ∀ w, Fn n w = 0 → w.im = 0) :
    ∀ᶠ n in atTop, ∀ w ∈ closedBall z (|z.im| / 2), Fn n w ≠ 0 := by
  filter_upwards [hreal] with n hn w hw hwzero
  have him : w.im = 0 := hn w hwzero
  have hdist : dist w z ≤ |z.im| / 2 := Metric.mem_closedBall.mp hw
  have : |z.im| ≤ dist w z := by
    have h := Complex.abs_im_le_norm (w - z)
    rw [Complex.dist_eq]
    simpa [him] using h
  have habs : 0 < |z.im| := abs_pos.mpr hz
  linarith

end RHTower
