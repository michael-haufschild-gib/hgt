import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoalescingReflection
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The singularly normalized resolvent is normal on the lower half-plane

The meromorphic-inner reflection law makes the singularly normalized resolvent odd under
conjugation-reflection, so on the lower half-plane it is the conjugate-reflection of its
upper-half-plane restriction:

`R(z) = -conj (R (conj z))`.

Conjugation is an isometric involution of the plane exchanging the two half-planes, and
`conj ∘ f ∘ conj` is holomorphic exactly where `f` is.  Every locally uniform statement therefore
transports: the pointwise bound, holomorphy, and the extraction of a locally uniform limit on a
closed ball.  The quadratic factor is again harmless, because it only multiplies by the squared
distance to the origin, which is bounded on a ball.
-/

open Complex Filter Topology Set ComplexConjugate

noncomputable section

namespace RHTower

/-- The reflected value: on the lower half-plane the resolvent is minus the conjugate of its
value at the conjugate point. -/
theorem suzukiCoalescingResolvent_conj_reflect {θ : ℂ → ℂ} {c : ℝ} {z : ℂ}
    (hθ : θ z * (starRingEnd ℂ) (θ ((starRingEnd ℂ) z)) = 1)
    (hne : 1 + θ ((starRingEnd ℂ) z) ≠ 0) :
    suzukiCoalescingResolvent θ c z
      = -(starRingEnd ℂ) (suzukiCoalescingResolvent θ c ((starRingEnd ℂ) z)) := by
  have hθ' : θ ((starRingEnd ℂ) ((starRingEnd ℂ) z)) * (starRingEnd ℂ) (θ ((starRingEnd ℂ) z))
      = 1 := by
    rwa [Complex.conj_conj]
  have h := suzukiCoalescingResolvent_reflection (θ := θ) (c := c)
    (z := (starRingEnd ℂ) z) hθ' hne
  rw [Complex.conj_conj] at h
  have h2 := congrArg (starRingEnd ℂ) h
  rw [Complex.conj_conj, map_neg] at h2
  exact h2

/-- The resolvent has the same modulus at conjugate points. -/
theorem norm_suzukiCoalescingResolvent_conj {θ : ℂ → ℂ} {c : ℝ} {z : ℂ}
    (hθ : θ z * (starRingEnd ℂ) (θ ((starRingEnd ℂ) z)) = 1)
    (hne : 1 + θ ((starRingEnd ℂ) z) ≠ 0) :
    ‖suzukiCoalescingResolvent θ c z‖
      = ‖suzukiCoalescingResolvent θ c ((starRingEnd ℂ) z)‖ := by
  rw [suzukiCoalescingResolvent_conj_reflect hθ hne, norm_neg, RCLike.norm_conj]

/-- **Local boundedness on the lower half-plane.**  The defect bound proved on the upper
half-plane transports through the reflection law. -/
theorem norm_suzukiCoalescingResolvent_le_of_conj {θ : ℂ → ℂ} {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    {z : ℂ}
    (hθ : θ z * (starRingEnd ℂ) (θ ((starRingEnd ℂ) z)) = 1)
    (hne : 1 + θ ((starRingEnd ℂ) z) ≠ 0)
    (hdefect : ‖1 - θ ((starRingEnd ℂ) z)‖ ≤ c * A)
    (hsmall : c * A ≤ 1) :
    ‖suzukiCoalescingResolvent θ c z‖ ≤ A := by
  rw [norm_suzukiCoalescingResolvent_conj hθ hne]
  exact norm_suzukiCoalescingResolvent_le hc hA hdefect hsmall

/-- On the lower half-plane the resolvent agrees with minus the conjugate-reflection of itself. -/
theorem suzukiCoalescingResolvent_eqOn_lower {θ : ℂ → ℂ} {c : ℝ}
    (hθ : ∀ z : ℂ, z.im < 0 → θ z * (starRingEnd ℂ) (θ ((starRingEnd ℂ) z)) = 1)
    (hne : ∀ z : ℂ, z.im < 0 → 1 + θ ((starRingEnd ℂ) z) ≠ 0) :
    EqOn (suzukiCoalescingResolvent θ c)
      (fun z => -((starRingEnd ℂ) ∘ suzukiCoalescingResolvent θ c ∘ (starRingEnd ℂ)) z)
      {z : ℂ | z.im < 0} := by
  intro z hz
  simpa [Function.comp] using
    suzukiCoalescingResolvent_conj_reflect (θ := θ) (c := c) (z := z) (hθ z hz) (hne z hz)

/-- **Holomorphy on the lower half-plane.**  Conjugate-reflection preserves holomorphy, so the
upper-half-plane differentiability statement transports. -/
theorem differentiableOn_suzukiCoalescingResolvent_lower {θ : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hθdiff : DifferentiableOn ℂ θ {z : ℂ | 0 < z.im})
    (hθlt : ∀ z : ℂ, 0 < z.im → ‖θ z‖ < 1)
    (hθ : ∀ z : ℂ, z.im < 0 → θ z * (starRingEnd ℂ) (θ ((starRingEnd ℂ) z)) = 1)
    (hne : ∀ z : ℂ, z.im < 0 → 1 + θ ((starRingEnd ℂ) z) ≠ 0) :
    DifferentiableOn ℂ (suzukiCoalescingResolvent θ c) {z : ℂ | z.im < 0} := by
  have hopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hupper := differentiableOn_suzukiCoalescingResolvent hc hθdiff hθlt
  have hstep : ∀ z : ℂ, z.im < 0 →
      DifferentiableAt ℂ
        (fun w => -((starRingEnd ℂ) ∘ suzukiCoalescingResolvent θ c ∘ (starRingEnd ℂ)) w) z := by
    intro z hz
    have hconj : (0 : ℝ) < ((starRingEnd ℂ) z).im := by
      simpa using hz
    have hmem : ((starRingEnd ℂ) z) ∈ {w : ℂ | 0 < w.im} := hconj
    have hupperAt : DifferentiableAt ℂ (suzukiCoalescingResolvent θ c) ((starRingEnd ℂ) z) :=
      (hupper _ hmem).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hmem)
    exact
      (differentiableAt_conj_conj_iff (f := suzukiCoalescingResolvent θ c) (x := z)).2
        hupperAt |>.neg
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (hstep z hz).congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds hz] with w hw using
    (suzukiCoalescingResolvent_eqOn_lower (c := c) hθ hne hw)

/-- Conjugation transports a locally uniform limit from a ball in the upper half-plane to the
reflected ball in the lower half-plane. -/
theorem tendstoUniformlyOn_conj_reflect {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {q : ℂ} {r : ℝ}
    (h : TendstoUniformlyOn F g Filter.atTop (Metric.closedBall ((starRingEnd ℂ) q) r)) :
    TendstoUniformlyOn (fun k z => -(starRingEnd ℂ) (F k ((starRingEnd ℂ) z)))
      (fun z => -(starRingEnd ℂ) (g ((starRingEnd ℂ) z))) Filter.atTop
      (Metric.closedBall q r) := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with k hk z hz
  have hzmem : (starRingEnd ℂ) z ∈ Metric.closedBall ((starRingEnd ℂ) q) r := by
    rw [Metric.mem_closedBall, Complex.dist_conj_conj]
    exact Metric.mem_closedBall.mp hz
  have := hk _ hzmem
  rwa [dist_neg_neg, Complex.dist_conj_conj]

/-- **Theorem C on the lower half-plane.**  The quadratic anchor gap makes the singularly
normalized resolvents a normal family on every ball contained in the lower half-plane. -/
theorem exists_suzukiCoalescingResolvent_montel_subseq_lower
    {θ : ℕ → ℂ → ℂ} {c κ : ℕ → ℝ} {C R r : ℝ} {q : ℂ}
    (hC : 0 ≤ C) (hR0 : 0 < R) (hRq : R < -q.im)
    (hr0 : 0 < r) (hrR : r < R / 2)
    (hc : ∀ n, 0 < c n) (hc1 : ∀ n, c n ≤ 1)
    (hθdiff : ∀ n, DifferentiableOn ℂ (θ n) {z : ℂ | 0 < z.im})
    (hθlt : ∀ n z, 0 < z.im → ‖θ n z‖ < 1)
    (hθanchor : ∀ n, θ n ((c n : ℂ) * I) = 0)
    (hκderiv : ∀ n,
      2 * (c n : ℂ) * I * deriv (θ n) ((c n : ℂ) * I) = (κ n : ℂ))
    (hκ0 : ∀ n, 0 ≤ κ n) (hκ1 : ∀ n, κ n < 1)
    (hκgap : ∀ n, 1 - κ n ≤ C * (c n) ^ (2 : ℕ))
    (hsmall : ∀ n,
      c n * ((2 + C * (‖q‖ + R + 1) ^ (2 : ℕ)) / (-q.im - R)) ≤ 1)
    (hθrefl : ∀ n, ∀ z : ℂ, z.im < 0 →
      θ n z * (starRingEnd ℂ) (θ n ((starRingEnd ℂ) z)) = 1)
    (hθne : ∀ n, ∀ z : ℂ, z.im < 0 → 1 + θ n ((starRingEnd ℂ) z) ≠ 0) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoUniformlyOn
        (fun k => suzukiCoalescingResolvent (θ (φ k)) (c (φ k)))
        g Filter.atTop (Metric.closedBall q r) ∧
      DifferentiableOn ℂ g (Metric.ball q r) := by
  have hqnorm : ‖(starRingEnd ℂ) q‖ = ‖q‖ := RCLike.norm_conj q
  have hqim : ((starRingEnd ℂ) q).im = -q.im := by simp
  obtain ⟨φ, g, hφ, huni, hgdiff⟩ :=
    exists_suzukiCoalescingResolvent_montel_subseq (θ := θ) (c := c) (κ := κ) (C := C)
      (R := R) (r := r) (q := (starRingEnd ℂ) q) hC hR0 (by rw [hqim]; exact hRq) hr0 hrR
      hc hc1 hθdiff hθlt hθanchor hκderiv hκ0 hκ1 hκgap
      (by simpa [hqnorm, hqim] using hsmall)
  refine ⟨φ, fun z => -(starRingEnd ℂ) (g ((starRingEnd ℂ) z)), hφ, ?_, ?_⟩
  · have htr := tendstoUniformlyOn_conj_reflect (q := q) (r := r) huni
    refine htr.congr ?_
    filter_upwards with k
    intro z hz
    have hzim : z.im < 0 := by
      have hd : dist z q ≤ r := Metric.mem_closedBall.mp hz
      have h1 : |z.im - q.im| ≤ r := by
        calc |z.im - q.im| = |(z - q).im| := by simp
          _ ≤ ‖z - q‖ := Complex.abs_im_le_norm _
          _ ≤ r := by simpa [dist_eq_norm] using hd
      have h2 : z.im - q.im ≤ r := le_trans (le_abs_self _) h1
      have : q.im < -R := by linarith
      linarith
    exact (suzukiCoalescingResolvent_conj_reflect (θ := θ (φ k)) (c := c (φ k)) (z := z)
      (hθrefl (φ k) z hzim) (hθne (φ k) z hzim)).symm
  · have hball : ∀ z ∈ Metric.ball q r, (starRingEnd ℂ) z ∈ Metric.ball ((starRingEnd ℂ) q) r := by
      intro z hz
      rw [Metric.mem_ball, Complex.dist_conj_conj]
      exact Metric.mem_ball.mp hz
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hgAt : DifferentiableAt ℂ g ((starRingEnd ℂ) z) :=
      (hgdiff _ (hball z hz)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (hball z hz))
    exact ((differentiableAt_conj_conj_iff (f := g) (x := z)).2 hgAt).neg

end RHTower
