import GaloisForLFunctions.EllipticThetaLogFundamentalAnnulus

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
