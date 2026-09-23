/-
# `u₀ ⟂` every Kummer layer: the dyadic roots of the window branch

The assembly functor (`u0_window_independence_of_transcendental_engine`) applied to the whole
dyadic root tower of the window branch: for `‖b‖ > 2+√2` and every `k`,

  `phiBRoot k b z := exp(2^{-(k+1)}·(log b + log(1 + z²/b) + tail(z² + b)))`

is a `2^k`-th root of `phiB b` (`phiBRoot 0 = phiB`), analytic on the whole window disk, with

* transcendence over `ℂ(z)` inherited UP the root tower — a relation for the root powers down to
  a relation for `phiB` itself (`IsIntegral.pow`), against `phiB_transcendental`;
* the (φ-generic) natural-boundary window engine.

Conclusion: `u0_phiBRoot_independence` — `u₀` is algebraically independent over `ℂ(z)` of EVERY
Kummer layer of the window branch, for every `‖b‖ > 2+√2`.  This is the window-side analog of
the tower certificate's radicand clause (`aExt` with `restrict = φ^{2^k}`): the whole radical
tower above the window branch is `u₀`-free, unconditionally, at the sharp threshold.
-/
import GaloisForLFunctions.U0.U0PhiLargeCapstone

open Complex Filter Topology Metric Set Polynomial Bottcher
open U0 U0NaturalBoundary U0WindowNormalization U0PhiFourFarCarrier U0PhiFourDescent
open U0MeroCarrier U0PhiLargeWindow U0PhiLargeCarrier U0PhiLargeDescent U0PhiLargeCapstone

namespace U0PhiKummerLayers

/-- The `2^k`-th root layer of the window branch. -/
noncomputable def phiBRoot (k : ℕ) (b z : ℂ) : ℂ :=
  Complex.exp (((2 : ℂ) ^ (k + 1))⁻¹ * (Complex.log b + Complex.log (1 + z ^ (2 : ℕ) / b)
    + ∑' j, bottcherLogTerm b (quadratic b z) j))

theorem phiBRoot_ne_zero (k : ℕ) (b z : ℂ) : phiBRoot k b z ≠ 0 := Complex.exp_ne_zero _

theorem phiBRoot_zero (b z : ℂ) : phiBRoot 0 b z = phiB b z := by
  unfold phiBRoot phiB
  norm_num

/-- The root relation: `phiBRoot k ^ (2^k) = phiB` — pointwise on all of `ℂ`. -/
theorem phiBRoot_pow (k : ℕ) (b z : ℂ) : phiBRoot k b z ^ (2 ^ k) = phiB b z := by
  unfold phiBRoot phiB
  rw [← Complex.exp_nat_mul]
  congr 1
  have h2 : ((2 : ℂ) ^ (k + 1)) ≠ 0 := by
    apply pow_ne_zero
    norm_num
  push_cast
  rw [pow_succ] at h2 ⊢
  field_simp

/-- Every root layer is analytic on the whole window disk. -/
theorem phiBRoot_analytic {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (k : ℕ) :
    AnalyticOnNhd ℂ (phiBRoot k b) (ball (0 : ℂ) (rB b)) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hqd : DifferentiableAt ℂ (quadratic b) z := by
    have : (quadratic b) = fun v => v ^ (2 : ℕ) + b := by
      funext v; exact quadratic_apply b v
    rw [this]
    exact ((differentiable_pow 2).add_const b).differentiableAt
  have hratio : DifferentiableAt ℂ (fun v => Complex.log (1 + v ^ (2 : ℕ) / b)) z := by
    have hin : DifferentiableAt ℂ (fun v : ℂ => 1 + v ^ (2 : ℕ) / b) z := by
      have : DifferentiableAt ℂ (fun v : ℂ => v ^ (2 : ℕ) / b) z :=
        (differentiableAt_pow 2).div_const b
      exact (differentiableAt_const (1 : ℂ)).add this
    exact hin.clog (ratio_mem_slitPlane hb hz)
  have htail : DifferentiableAt ℂ (fun v => ∑' j, bottcherLogTerm b (quadratic b v) j) z := by
    have hT : DifferentiableAt ℂ (fun w => ∑' j, bottcherLogTerm b w j) (quadratic b z) :=
      (tail_differentiableOn_B (norm_gt_two hb)).differentiableAt
        ((isOpen_farB b).mem_nhds (quadB_mem_farB hb hz))
    exact hT.comp z hqd
  have hsum : DifferentiableAt ℂ (fun v => Complex.log b + Complex.log (1 + v ^ (2 : ℕ) / b)
      + ∑' j, bottcherLogTerm b (quadratic b v) j) z :=
    ((differentiableAt_const _).add hratio).add htail
  exact (hsum.const_mul _).cexp

/-- The root layer as an analytic germ on the sharp annulus. -/
noncomputable def phiBRootAn (k : ℕ) (b : ℂ) (hb : 2 + Real.sqrt 2 < ‖b‖) :
    analyticSubring (annWB b) :=
  ⟨Germ.coeRingHom (𝓟 (annWB b)) (phiBRoot k b),
    ⟨phiBRoot k b, (phiBRoot_analytic hb k).mono annWB_subset_ball, rfl⟩⟩

/-- **Every Kummer layer is transcendental over `ℂ(z)`** — a relation for the root descends to a
relation for its `2^k`-th power `phiB`, against `phiB_transcendental`. -/
theorem phiBRoot_transcendental {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (k : ℕ) :
    letI := isDomain_analyticSubring (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
      (annWB_nonempty hb)
    letI : Algebra (RatFunc ℂ) (meroField (annWB b)) :=
      (ratfuncToMero (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb) (annWB_nonempty hb)
        (annWB_infinite hb)).toAlgebra
    Transcendental (RatFunc ℂ)
      (algebraMap (analyticSubring (annWB b)) (meroField (annWB b)) (phiBRootAn k b hb)) := by
  letI := isDomain_analyticSubring (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
    (annWB_nonempty hb)
  letI : Algebra (RatFunc ℂ) (meroField (annWB b)) :=
    (ratfuncToMero (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb) (annWB_nonempty hb)
      (annWB_infinite hb)).toAlgebra
  intro halg
  have hpow : (phiBRootAn k b hb) ^ (2 ^ k) = phiBAn b hb := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    show ((↑(phiBRoot k b) : Germ (𝓟 (annWB b)) ℂ)) ^ (2 ^ k)
      = (↑(phiB b) : Germ (𝓟 (annWB b)) ℂ)
    rw [← Germ.coe_pow, Germ.coe_eq]
    apply Filter.eventually_principal.mpr
    intro z _
    exact phiBRoot_pow k b z
  have halg2 : IsAlgebraic (RatFunc ℂ)
      (algebraMap (analyticSubring (annWB b)) (meroField (annWB b)) (phiBAn b hb)) := by
    rw [← hpow, map_pow]
    exact ((isAlgebraic_iff_isIntegral.mp halg).pow _).isAlgebraic
  exact phiB_transcendental hb halg2

/-- **`u₀ ⟂ phiBRoot k b` — every Kummer layer, every `‖b‖ > 2+√2`, unconditionally.** -/
theorem u0_phiBRoot_independence {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (k : ℕ) :
    letI := isDomain_analyticSubring (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
      (annWB_nonempty hb)
    letI : Algebra (RatFunc ℂ) (meroField (annWB b)) :=
      (ratfuncToMero (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb) (annWB_nonempty hb)
        (annWB_infinite hb)).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring (annWB b)) (meroField (annWB b)) (phiBRootAn k b hb))
      (algebraMap (analyticSubring (annWB b)) (meroField (annWB b))
        (u0AnSub annWB_subset_Ext)) := by
  letI := isDomain_analyticSubring (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
    (annWB_nonempty hb)
  letI : Algebra (RatFunc ℂ) (meroField (annWB b)) :=
    (ratfuncToMero (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb) (annWB_nonempty hb)
      (annWB_infinite hb)).toAlgebra
  refine u0_window_independence_of_transcendental_engine (isOpen_annWB b)
    (isPreconnected_annWB hb) (annWB_nonempty hb) (annWB_infinite hb) annWB_subset_Ext
    (phiBRoot k b) (phiBRootAn k b hb) rfl
    (phiBRoot_transcendental hb k) ?_
  intro P' j₀ hj₀ hnd hrel
  refine u0_windowed_no_relation_nondegenerate isOpen_ball
    ((convex_ball (0 : ℂ) (rB b)).isPreconnected)
    (isPreconnected_annulus_of_one_lt (one_lt_rB hb))
    (phiBRoot_analytic hb k) (z₁ := 1) ?_ ?_ P' hj₀ hnd (isOpen_annWB b) (annWB_nonempty hb)
    (fun z hz => hz) hrel
  · show (1 : ℂ) ∈ Metric.ball (0 : ℂ) (rB b)
    simp only [Metric.mem_ball, dist_zero_right, norm_one]
    exact one_lt_rB hb
  · simp

end U0PhiKummerLayers
