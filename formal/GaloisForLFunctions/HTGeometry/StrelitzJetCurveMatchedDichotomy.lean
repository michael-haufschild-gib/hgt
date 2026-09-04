import GaloisForLFunctions.HTGeometry.StrelitzJetCurveEdgeLimit

/-!
# Exhaustive matched-edge dichotomy for Strelitz jet curves

The nonzero numerical branch now carries more than an abstract edge-root witness: after two cofinal
extractions its normalized roots converge to that exact nonzero edge root.  Recurrent exact-zero
roots remain the exhaustive alternative and force the observed second jet to zero.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- Complete matched Newton-edge data for one nonzero numerical Strelitz branch. -/
def HasStrelitzJetCurveMatchedNewtonEdgeLimit
    (S : MvPolynomial (Fin 2) ℂ) (u root : ℕ → ℂ) : Prop :=
  ∃ i ∈ (strelitzJetCurvePolynomial S).support,
    ∃ j ∈ (strelitzJetCurvePolynomial S).support, i ≠ j ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k)) atTop
          (nhds (strelitzJetCurveNewtonSlope S i j)) ∧
        (∀ k ∈ (strelitzJetCurvePolynomial S).support,
          strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) k ≤
            strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) i) ∧
        ∃ c : ℂ, c ≠ 0 ∧
          (strelitzJetCurveNewtonEdgePolynomial S
            (strelitzJetCurveNewtonSlope S i j)
            (strelitzJetCurveNewtonWeight S
              (strelitzJetCurveNewtonSlope S i j) i)).IsRoot c ∧
          ∃ τ : ℕ → ℕ, StrictMono τ ∧
            Tendsto (fun m => strelitzJetCurveNormalizedRoot u root
              (strelitzJetCurveNewtonSlope S i j) (ns (τ m))) atTop (nhds c)

/-- Every exact numerical root sequence either converges after Newton normalization to an exact nonzero edge root, or has a cofinal exact-zero branch forcing the observed jet to zero. -/
theorem strelitzJetCurve_matchedNewtonEdge_or_zeroBranch
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {ν : ℕ → ℕ} {u v root : ℕ → ℂ} (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ))
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0)) :
    HasStrelitzJetCurveMatchedNewtonEdgeLimit S u root ∨
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        (∀ k, root (ns k) = 0) ∧
        Tendsto (fun k => ‖v (ns k)‖) atTop (nhds 0) := by
  have huTop : Tendsto (fun n => ‖u n‖) atTop atTop :=
    tendsto_norm_atTop_of_nat_tendsto_atTop_of_strelitzRelativeError hνTop hu
  rcases eventually_ne_or_exists_strictMono_eq_zero root with hne | ⟨ns, hns, hzero⟩
  · left
    obtain ⟨i, hi, j, hj, hij, ns, hns, hslope, hmax⟩ :=
      exists_strelitzJetCurveNewtonSlope_tendsto_subsequence hS huTop hroot hne
    obtain ⟨c, hc, hcEdge, τ, hτ, hcLim⟩ :=
      exists_strelitzJetCurveNormalizedRoot_tendsto_edgeRoot_subsequence
        hns hνTop hu hroot hne hslope hi hmax
    exact ⟨i, hi, j, hj, hij, ns, hns, hslope, hmax, c, hc, hcEdge, τ, hτ, hcLim⟩
  · right
    exact ⟨ns, hns, hzero,
      tendsto_norm_zero_of_root_eq_zero_subsequence hns hclose hzero⟩

end

end GaloisForLFunctions.HTGeometry

