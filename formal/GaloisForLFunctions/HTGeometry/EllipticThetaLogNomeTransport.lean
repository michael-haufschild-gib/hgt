import GaloisForLFunctions.HTGeometry.EllipticThetaLogFundamentalAnnulus

/-!
# Meromorphic transport under the nome

The intrinsic quasiperiod equation transports meromorphicity bidirectionally under `x ↦ q*x`.
The proof works even at the exceptional point `x = 1`: the functional identity is used only on the
punctured-neighborhood filter, exactly the equivalence relation defining `MeromorphicAt`.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions

noncomputable section

theorem meromorphicAt_ellipticThetaLogKernel_mul_nome_iff {q x : ℂ}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    MeromorphicAt (ellipticThetaLogKernel q) (q * x) ↔
      MeromorphicAt (ellipticThetaLogKernel q) x := by
  let T := ellipticThetaLogKernel q
  let g : ℂ → ℂ := fun y => q * y
  have hg : AnalyticAt ℂ g x := analyticAt_const.mul analyticAt_id
  have hg' : deriv g x ≠ 0 := by
    have hd : HasDerivAt g q x := by
      simpa [g] using (hasDerivAt_id x).const_mul q
    simpa [hd.deriv] using hq0
  have hcomp : MeromorphicAt (T ∘ g) x ↔ MeromorphicAt T (q * x) := by
    simpa [T, g] using meromorphicAt_comp_iff_of_deriv_ne_zero hg hg'
  have hy0 : ∀ᶠ y in 𝓝[≠] x, y ≠ 0 := by
    by_cases hx0 : x = 0
    · subst x
      exact self_mem_nhdsWithin
    · exact (continuousAt_id.eventually_ne hx0).filter_mono inf_le_left
  have hy1 : ∀ᶠ y in 𝓝[≠] x, y ≠ 1 := by
    by_cases hx1 : x = 1
    · subst x
      exact self_mem_nhdsWithin
    · exact (continuousAt_id.eventually_ne hx1).filter_mono inf_le_left
  have heq : (T ∘ g) =ᶠ[𝓝[≠] x] (fun y => T y - 1) := by
    filter_upwards [hy0, hy1] with y hy0 hy1
    have h := ellipticThetaLogKernel_mul_q_sub hq0 hy0 hy1 hq
    dsimp [T, g, Function.comp_def]
    linear_combination h
  constructor
  · intro hqx
    have hc : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) x := analyticAt_const.meromorphicAt
    have hcompM : MeromorphicAt (T ∘ g) x := hcomp.mpr hqx
    have hsub : MeromorphicAt (fun y => T y - 1) x := hcompM.congr heq
    have hadd := hsub.add hc
    apply hadd.congr
    filter_upwards with y
    simp [T]
  · intro hx
    have hc : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) x := analyticAt_const.meromorphicAt
    have hsub : MeromorphicAt (fun y => T y - 1) x := hx.sub hc
    have hcompM : MeromorphicAt (T ∘ g) x := hsub.congr heq.symm
    exact hcomp.mp hcompM

/-- Meromorphicity is invariant under every nonnegative nome power. -/
theorem meromorphicAt_ellipticThetaLogKernel_pow_mul_iff
    {q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : ℕ) :
    MeromorphicAt (ellipticThetaLogKernel q) (q ^ n * x) ↔
      MeromorphicAt (ellipticThetaLogKernel q) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        MeromorphicAt (ellipticThetaLogKernel q) (q ^ (n + 1) * x) ↔
            MeromorphicAt (ellipticThetaLogKernel q) (q ^ n * x) := by
          convert meromorphicAt_ellipticThetaLogKernel_mul_nome_iff
            (q := q) (x := q ^ n * x) hq0 hq using 1
          all_goals ring
        _ ↔ MeromorphicAt (ellipticThetaLogKernel q) x := ih

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Analyticity of the theta logarithmic kernel transports bidirectionally under one nome step
away from the multiplicative divisor. Unlike meromorphic transport, full-neighborhood analyticity
requires the source point to avoid `0` and `1`. -/
theorem analyticAt_ellipticThetaLogKernel_mul_nome_iff {q x : ℂ}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    AnalyticAt ℂ (ellipticThetaLogKernel q) (q * x) ↔
      AnalyticAt ℂ (ellipticThetaLogKernel q) x := by
  let T := ellipticThetaLogKernel q
  let g : ℂ → ℂ := fun y => q * y
  have hg : AnalyticAt ℂ g x := analyticAt_const.mul analyticAt_id
  have hg' : deriv g x ≠ 0 := by
    have hd : HasDerivAt g q x := by
      simpa [g] using (hasDerivAt_id x).const_mul q
    simpa [hd.deriv] using hq0
  have hcomp : AnalyticAt ℂ (T ∘ g) x ↔ AnalyticAt ℂ T (q * x) := by
    simpa [T, g] using analyticAt_comp_iff_of_deriv_ne_zero hg hg'
  have hy0 : ∀ᶠ y in 𝓝 x, y ≠ 0 := continuousAt_id.eventually_ne hx0
  have hy1 : ∀ᶠ y in 𝓝 x, y ≠ 1 := continuousAt_id.eventually_ne hx1
  have heq : (T ∘ g) =ᶠ[𝓝 x] (fun y => T y - 1) := by
    filter_upwards [hy0, hy1] with y hy0 hy1
    have h := ellipticThetaLogKernel_mul_q_sub hq0 hy0 hy1 hq
    dsimp [T, g, Function.comp_def]
    linear_combination h
  constructor
  · intro hqx
    have hc : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) x := analyticAt_const
    have hcompA : AnalyticAt ℂ (T ∘ g) x := hcomp.mpr hqx
    have hsub : AnalyticAt ℂ (fun y => T y - 1) x := hcompA.congr heq
    have hadd := hsub.add hc
    apply hadd.congr
    filter_upwards with y
    simp [T]
  · intro hx
    have hc : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) x := analyticAt_const
    have hsub : AnalyticAt ℂ (fun y => T y - 1) x := hx.sub hc
    have hcompA : AnalyticAt ℂ (T ∘ g) x := hsub.congr heq.symm
    exact hcomp.mp hcompA

/-- Analyticity transports across a nonnegative nome power provided every intermediate point avoids
the divisor point `1`. -/
theorem analyticAt_ellipticThetaLogKernel_pow_mul_iff
    {q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hx0 : x ≠ 0) (n : ℕ)
    (havoid : ∀ k < n, q ^ k * x ≠ 1) :
    AnalyticAt ℂ (ellipticThetaLogKernel q) (q ^ n * x) ↔
      AnalyticAt ℂ (ellipticThetaLogKernel q) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hxn0 : q ^ n * x ≠ 0 := mul_ne_zero (pow_ne_zero _ hq0) hx0
      have hxn1 : q ^ n * x ≠ 1 := havoid n (Nat.lt_succ_self n)
      have hstep := analyticAt_ellipticThetaLogKernel_mul_nome_iff hq0 hq hxn0 hxn1
      have hprev : ∀ k < n, q ^ k * x ≠ 1 := fun k hk =>
        havoid k (hk.trans (Nat.lt_succ_self n))
      calc
        AnalyticAt ℂ (ellipticThetaLogKernel q) (q ^ (n + 1) * x) ↔
            AnalyticAt ℂ (ellipticThetaLogKernel q) (q ^ n * x) := by
          rw [show q ^ (n + 1) * x = q * (q ^ n * x) by
            rw [pow_succ]
            ring]
          exact hstep
        _ ↔ AnalyticAt ℂ (ellipticThetaLogKernel q) x := ih hprev

end

end GaloisForLFunctions
