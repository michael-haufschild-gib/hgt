import GaloisForLFunctions.ConstituentTheoryOfTheZeros.PrimeCutoffMultipliers
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.PoissonExtensionOfHolomorphicFamilies
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.BoundedDirichletTwists

/-!
# Disc contraction of a bounded prime-torus family

Replacing every prime beyond a fixed cutoff by one disc parameter contracts a
bounded Dirichlet series to its smooth part. Poisson averaging constructs the
bounded continuation. Its Cauchy representation propagates from the half-plane
of absolute convergence and gives holomorphy in the disc parameter.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry _root_.RHTower

noncomputable section
namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

/-- The absolutely convergent series after simultaneous prime damping. -/
def primeCutoffSeries (a : ℕ → ℂ) (N : ℕ) (s w : ℂ) : ℂ :=
  LSeries (fun n => a n * primeCutoffMultiplier N w n) s

theorem primeCutoffSeries_eq_tsum (a : ℕ → ℂ) (N : ℕ) (s w : ℂ) :
    primeCutoffSeries a N s w =
      ∑' n, primeCutoffMultiplier N w n * LSeries.term a s n := by
  simp only [primeCutoffSeries, LSeries, term_primeCutoffMultiplier]

/-- Absolute Dirichlet convergence supplies a holomorphic continuous disc trace. -/
theorem diffContOnCl_primeCutoffSeries {a : ℕ → ℂ} {s : ℂ}
    (hs : LSeriesSummable a s) (N : ℕ) :
    DiffContOnCl ℂ (primeCutoffSeries a N s) (ball (0 : ℂ) 1) := by
  have hterm (n : ℕ) : Differentiable ℂ
      (fun w => primeCutoffMultiplier N w n * LSeries.term a s n) :=
    (differentiable_primeCutoffMultiplier N n).mul_const _
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) 1) :
      ‖primeCutoffMultiplier N w n * LSeries.term a s n‖ ≤ ‖LSeries.term a s n‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (norm_primeCutoffMultiplier_le_one N n (by simpa only [mem_closedBall, dist_zero_right] using hw))
  have heq : primeCutoffSeries a N s =
      fun w => ∑' n, primeCutoffMultiplier N w n * LSeries.term a s n := by
    funext w
    exact primeCutoffSeries_eq_tsum a N s w
  rw [heq]
  constructor
  · intro w hw
    obtain ⟨R, hR, hRB⟩ := Metric.isOpen_iff.mp isOpen_ball w hw
    have hd := differentiableAt_tsum_of_cauchy_dominated hR
      (fun n => (hterm n).differentiableOn)
      (fun n z hz => hbound n z (ball_subset_closedBall (hRB hz))) hs.norm
    exact hd.differentiableWithinAt
  · rw [closure_ball (0 : ℂ) one_ne_zero]
    exact continuousOn_tsum (fun n => (hterm n).continuous.continuousOn) hs.norm hbound

/-- Circle parameters agree with the corresponding unitary prime twists. -/
theorem primeCutoffSeries_circle (a : ℕ → ℂ) (N : ℕ) (s : ℂ) (w : Circle) :
    primeCutoffSeries a N s (w : ℂ) =
      LSeries (fun n => a n * primePhaseTwist (retainedPrimePhase N w) n) s := by
  unfold primeCutoffSeries LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp only [hn, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      primeCutoffMultiplier_circle N w hn]

/-- The central fibre is the exact projection onto smooth coefficient indices. -/
theorem primeCutoffSeries_zero (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    primeCutoffSeries a N s 0 = LSeries (fun n => if n ∈ Nat.smoothNumbers N then a n else 0) s := by
  unfold primeCutoffSeries
  congr 1
  funext n
  rw [primeCutoffMultiplier_zero]
  split_ifs <;> simp only [mul_one, mul_zero]

/-- A bounded prime-torus lift admits simultaneous damping of all omitted primes,
with its original bound and its exact Dirichlet coefficients. -/
theorem exists_primeCutoff_family
    {a : ℕ → ℂ} {x u₀ M : ℝ} {G : (Nat.Primes → Circle) → ℂ → ℂ}
    (hsum : LSeriesSummable a (u₀ : ℂ))
    (hG : ∀ ω, DifferentiableOn ℂ (G ω) {s : ℂ | x < s.re})
    (hM : ∀ ω s, x < s.re → ‖G ω s‖ ≤ M)
    (hGL : ∀ ω s, u₀ < s.re → G ω s = LSeries (fun n => a n * primePhaseTwist ω n) s)
    (hGc : ContinuousOn (fun q : (Nat.Primes → Circle) × ℂ => G q.1 q.2)
      (univ ×ˢ {s : ℂ | x < s.re})) (N : ℕ) :
    ∃ H : ℂ → ℂ → ℂ,
      ContinuousOn (Function.uncurry H) ({s : ℂ | x < s.re} ×ˢ closedBall 0 1) ∧
      (∀ w ∈ closedBall (0 : ℂ) 1, DifferentiableOn ℂ (fun s => H s w) {s : ℂ | x < s.re}) ∧
      (∀ s, x < s.re → DifferentiableOn ℂ (H s) (ball 0 1)) ∧
      (∀ s, x < s.re → ∀ w ∈ closedBall (0 : ℂ) 1, ‖H s w‖ ≤ M) ∧
      (∀ s, u₀ < s.re → ∀ w ∈ closedBall (0 : ℂ) 1, H s w = primeCutoffSeries a N s w) ∧
      (∀ s (w : Circle), H s w = G (retainedPrimePhase N w) s) := by
  let U := {s : ℂ | x < s.re}
  let B : ℂ → Circle → ℂ := fun s w => G (retainedPrimePhase N w) s
  let H : ℂ → ℂ → ℂ := fun s w => circlePoissonExtension (B s) w
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hBc : ContinuousOn (Function.uncurry B) (U ×ˢ univ) := by
    exact hGc.comp
      (((continuous_retainedPrimePhase N).comp continuous_snd).prodMk continuous_fst).continuousOn
      (fun q hq => ⟨mem_univ _, hq.1⟩)
  have hb (s : ℂ) (hs : s ∈ U) : Continuous (B s) := by
    rw [← continuousOn_univ]
    exact hBc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun w _ => ⟨hs, mem_univ w⟩)
  have hBs (w : Circle) : DifferentiableOn ℂ (fun s => B s w) U :=
    hG (retainedPrimePhase N w)
  have hBM (s : ℂ) (hs : s ∈ U) (w : Circle) : ‖B s w‖ ≤ M :=
    hM (retainedPrimePhase N w) s hs
  have htrace (s : ℂ) (hs : u₀ < s.re) : B s = fun w : Circle => primeCutoffSeries a N s w := by
    funext w
    dsimp only [B]
    rw [hGL _ s hs, primeCutoffSeries_circle]
  have hsd (s : ℂ) (hs : u₀ < s.re) :
      DiffContOnCl ℂ (primeCutoffSeries a N s) (ball (0 : ℂ) 1) :=
    diffContOnCl_primeCutoffSeries (hsum.of_re_le_re (by simpa only [Complex.ofReal_re] using hs.le)) N
  have hfar (s : ℂ) (hs : u₀ < s.re) (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) 1) :
      H s w = primeCutoffSeries a N s w := by
    dsimp only [H]
    rw [htrace s hs]
    exact circlePoissonExtension_eq_of_diffContOnCl (hsd s hs) hw
  have hHs (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) 1) :
      DifferentiableOn ℂ (fun s => H s w) U :=
    differentiableOn_circlePoissonExtension_parameter hU hb hBs hBM hw
  have hPC (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) :
      EqOn (fun s => H s w) (fun s => circleL1CauchyTransform (B s) w) U := by
    apply eqOn_halfPlane_of_eq_far_right (u := u₀)
      (hHs w (ball_subset_closedBall hw))
      (differentiableOn_circleCauchyTransform_parameter hU hb hBs hBM hw)
    intro s hs
    rw [hfar s hs w (ball_subset_closedBall hw), htrace s hs,
      circleL1CauchyTransform_eq_of_diffContOnCl (hsd s hs) hw]
  refine ⟨H, continuousOn_circlePoissonExtension_family hBc, hHs, ?_, ?_, hfar, ?_⟩
  · intro s hs w hw
    have hc := differentiableOn_circleL1CauchyTransform
      ((hb s hs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) w hw
    exact hc.congr (fun z hz => hPC z hz hs) (hPC w hw hs)
  · intro s hs w hw
    exact norm_circlePoissonExtension_le (hb s hs) (hBM s hs) hw
  · intro s w
    exact circlePoissonExtension_coe (B s) w

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
