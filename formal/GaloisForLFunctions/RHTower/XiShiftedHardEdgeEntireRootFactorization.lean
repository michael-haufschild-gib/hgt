import GaloisForLFunctions.RHTower.XiShiftedHardEdgeLocallyUniformL2Source
import GaloisForLFunctions.HTGeometry.AnalyticRootFactor

/-!
# Entire root factorization of the Route-U hard-edge limit

The squared-angular approximants are rational, with their only possible pole at `-aₙ²`.  As the
hard-edge mass tends to infinity, these poles escape every fixed complex neighbourhood.  Thus a
locally uniform limit is entire even though no individual approximant is entire on all of `ℂ`.

Unit `L²` normalization then prevents the entire limit from vanishing identically.  Every physical
root consequently has positive finite analytic order, its full power divides globally, and the
resulting factorization feeds directly into the literal compact Route-U source.  No continuity,
entireness, nondegeneracy, multiplicity, or quotient hypothesis is added at the capstone.
-/

open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Squared-variable angular approximant used by the Route-U hard-edge normal-family limit. -/
def routeUHardEdgeSquaredAngularApprox (a : ℝ) (p : Polynomial ℝ) (u : ℂ) : ℂ :=
  evalRealPolynomial (routeUHardEdgeAngularPoly a p)
    ((((a : ℂ) ^ 2) - u) / (((a : ℂ) ^ 2) + u))

/-- A squared-angular approximant is analytic away from its single possible pole `-a²`. -/
theorem analyticAt_routeUHardEdgeSquaredAngularApprox {a : ℝ} (p : Polynomial ℝ) {u : ℂ}
    (hden : (a : ℂ) ^ 2 + u ≠ 0) :
    AnalyticAt ℂ (routeUHardEdgeSquaredAngularApprox a p) u := by
  have hquot : AnalyticAt ℂ
      (fun v : ℂ => (((a : ℂ) ^ 2) - v) / (((a : ℂ) ^ 2) + v)) u := by
    exact (analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.add analyticAt_id) hden
  let P : Polynomial ℂ :=
    (routeUHardEdgeAngularPoly a p).map (algebraMap ℝ ℂ)
  have hpoly : AnalyticAt ℂ (fun z : ℂ => P.eval z)
      ((((a : ℂ) ^ 2) - u) / (((a : ℂ) ^ 2) + u)) :=
    (P.differentiable.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
  exact AnalyticAt.comp
    (f := fun v : ℂ => (((a : ℂ) ^ 2) - v) / (((a : ℂ) ^ 2) + v)) hpoly hquot

/-- **Escaping poles force an entire limit.**  If `aₙ → ∞`, then on every fixed unit ball the
possible poles `-aₙ²` are eventually absent.  The locally uniform limit is therefore entire by
eventual holomorphy; no termwise global-entireness assumption is needed. -/
theorem analyticOnNhd_routeUHardEdge_angularLocallyUniformLimit
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ}
    (ha : ∀ n, 0 < a n) (haT : Tendsto a atTop atTop)
    {F : ℂ → ℂ}
    (hFlocal : TendstoLocallyUniformly
      (fun n => routeUHardEdgeSquaredAngularApprox (a n) (p n)) F atTop) :
    AnalyticOnNhd ℂ F Set.univ := by
  intro z _hz
  let M : ℝ := max 1 (‖z‖ + 1)
  have hlarge : ∀ᶠ n in atTop, M + 1 ≤ a n := (tendsto_atTop.1 haT) (M + 1)
  have hdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (routeUHardEdgeSquaredAngularApprox (a n) (p n))
        (Metric.ball z 1) := by
    filter_upwards [hlarge] with n hn
    intro u hu
    have hMlt : M < a n := lt_of_lt_of_le (lt_add_one M) hn
    have ha1 : 1 < a n := (le_max_left _ _).trans_lt hMlt
    have haz : ‖z‖ + 1 < a n := (le_max_right _ _).trans_lt hMlt
    have huNorm : ‖u‖ < ‖z‖ + 1 := by
      calc
        ‖u‖ = ‖(u - z) + z‖ := by ring_nf
        _ ≤ ‖u - z‖ + ‖z‖ := norm_add_le _ _
        _ < 1 + ‖z‖ := by
          gcongr
          simpa [dist_eq_norm] using hu
        _ = ‖z‖ + 1 := by ring
    have hnormlt : ‖u‖ < (a n) ^ 2 := by
      have haa : a n < (a n) ^ 2 := by nlinarith [ha1]
      exact huNorm.trans (haz.trans haa)
    have hden : ((a n : ℂ) ^ 2) + u ≠ 0 := by
      intro hzero
      have hueq : u = -((a n : ℂ) ^ 2) := by linear_combination hzero
      have hunorm : ‖u‖ = (a n) ^ 2 := by
        rw [hueq, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (ha n)]
      rw [hunorm] at hnormlt
      exact (lt_irrefl _) hnormlt
    exact (analyticAt_routeUHardEdgeSquaredAngularApprox (p n) hden).differentiableAt
      |>.differentiableWithinAt
  have hdiffF : DifferentiableOn ℂ F (Metric.ball z 1) :=
    (hFlocal.tendstoLocallyUniformlyOn.mono (Set.subset_univ _)).differentiableOn
      hdiff Metric.isOpen_ball
  exact (hdiffF.analyticOnNhd Metric.isOpen_ball) z (Metric.mem_ball_self zero_lt_one)

/-- Strong convergence of unit-normalized hard-edge packets preserves norm exactly. -/
theorem norm_routeUHardEdge_strongLimit_eq_one
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    (hnorm : ∀ k : ℕ,
      (∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ 2) = 1)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) atTop (𝓝 L)) :
    ‖L‖ = 1 := by
  have hnorm1 : ∀ k : ℕ,
      ‖(memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))‖ = 1 := by
    intro k
    have hsq :
        ‖(memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
          (routeUHardEdgeRationalTest (a k) (p k))‖ ^ 2 =
          ∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ 2 :=
      norm_toLp_sq _
    rw [hnorm k] at hsq
    nlinarith [norm_nonneg
      ((memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k)))]
  have htend := hL.norm
  have hconst :
      (fun k : ℕ =>
        ‖(memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
          (routeUHardEdgeRationalTest (a k) (p k))‖) = fun _ => (1 : ℝ) := by
    funext k
    exact hnorm1 k
  rw [hconst] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

/-- The locally uniform angular limit cannot vanish identically: its physical representative is
the complexification of a unit-norm strong `L²` limit. -/
theorem exists_ne_zero_routeUHardEdge_angularLocallyUniformLimit
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    (haT : Tendsto a atTop atTop)
    (hnorm : ∀ k : ℕ,
      (∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ 2) = 1)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) atTop (𝓝 L))
    {F : ℂ → ℂ}
    (hFlocal : TendstoLocallyUniformly
      (fun n u => evalRealPolynomial (routeUHardEdgeAngularPoly (a n) (p n))
        ((((a n : ℂ) ^ 2) - u) / (((a n : ℂ) ^ 2) + u))) F atTop) :
    ∃ z : ℂ, F z ≠ 0 := by
  obtain ⟨hf2, hrep⟩ :=
    exists_memLp_routeUHardEdge_angularLocallyUniformLimit_toLp_eq ha haT hL hFlocal
  have hLnorm : ‖L‖ = 1 := norm_routeUHardEdge_strongLimit_eq_one ha hnorm hL
  by_contra hnone
  push Not at hnone
  have hzero : hf2.toLp (fun x : ℝ => F ((x : ℂ) ^ 2)) = 0 := by
    exact MemLp.toLp_congr hf2 MemLp.zero
      (Filter.Eventually.of_forall fun x => hnone ((x : ℂ) ^ 2))
  have hofzero : ofRealLp L = 0 := hrep.symm.trans hzero
  have hnormzero := congrArg norm hofzero
  rw [norm_ofRealLp, hLnorm, norm_zero] at hnormzero
  norm_num at hnormzero

/-- Every physical root of the locally uniform Route-U limit has an automatically supplied global
entire quotient at its exact positive multiplicity. -/
theorem exists_positive_entireRootFactor_routeUHardEdge_angularLocallyUniformLimit
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    (haT : Tendsto a atTop atTop)
    (hnorm : ∀ k : ℕ,
      (∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ 2) = 1)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) atTop (𝓝 L))
    {F : ℂ → ℂ}
    (hFlocal : TendstoLocallyUniformly
      (fun n u => evalRealPolynomial (routeUHardEdgeAngularPoly (a n) (p n))
        ((((a n : ℂ) ^ 2) - u) / (((a n : ℂ) ^ 2) + u))) F atTop)
    {r : ℝ} (hroot : F ((r : ℂ) ^ 2) = 0) :
    ∃ (m : ℕ) (H : ℂ → ℂ), 0 < m ∧ AnalyticOnNhd ℂ H Set.univ ∧
      H ((r : ℂ) ^ 2) ≠ 0 ∧
      ∀ u : ℂ, F u = (u - (r : ℂ) ^ 2) ^ m * H u := by
  have hFlocal' : TendstoLocallyUniformly
      (fun n => routeUHardEdgeSquaredAngularApprox (a n) (p n)) F atTop := by
    convert hFlocal using 1
    rfl
  have hFanalytic : AnalyticOnNhd ℂ F Set.univ :=
    analyticOnNhd_routeUHardEdge_angularLocallyUniformLimit ha haT hFlocal'
  have hFnonzero : ∃ z : ℂ, F z ≠ 0 :=
    exists_ne_zero_routeUHardEdge_angularLocallyUniformLimit ha haT hnorm hL hFlocal
  exact exists_positive_pow_factor_of_entire_root hFanalytic hroot hFnonzero

/-- **Route-U root-factor capstone.**  A root of the actual locally uniform, strongly convergent,
unit-normalized hard-edge packet limit automatically produces its exact positive multiplicity,
global entire quotient, literal compact source, and multiplicity-preserving Fourier factorization.
No factorization or regularity of the limit is assumed. -/
theorem routeUHardEdge_angularLocallyUniformLimit_root_has_literal_compact_factorization
    {C : ℝ} (hC : 0 < C)
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ} {N : ℕ → ℕ} {b : ℕ → ℕ → ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    (haT : Tendsto a atTop atTop)
    (hb : ∀ k : ℕ, routeUHardEdgeAngularPoly (a k) (p k)
      = ∑ j ∈ Finset.range (N k + 1),
        Polynomial.C (b k j) * Polynomial.Chebyshev.T ℝ (j : ℤ))
    (hNC : ∀ k : ℕ, ((N k : ℕ) : ℝ) ≤ C * a k)
    (hnorm : ∀ k : ℕ,
      (∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ 2) = 1)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) atTop (𝓝 L))
    {F : ℂ → ℂ}
    (hFlocal : TendstoLocallyUniformly
      (fun n u => evalRealPolynomial (routeUHardEdgeAngularPoly (a n) (p n))
        ((((a n : ℂ) ^ 2) - u) / (((a n : ℂ) ^ 2) + u))) F atTop)
    {r : ℝ} (hroot : F ((r : ℂ) ^ 2) = 0) :
    ∃ (m : ℕ) (H : ℂ → ℂ) (q : ℝ → ℂ) (G : ℝ → ℂ),
      0 < m ∧ AnalyticOnNhd ℂ H Set.univ ∧ H ((r : ℂ) ^ 2) ≠ 0 ∧
      (∀ u : ℂ, F u = (u - (r : ℂ) ^ 2) ^ m * H u) ∧
      Integrable q ∧ MemLp q 2 volume ∧ Continuous G ∧
      (∀ x : ℝ, x ≤ -(C / Real.pi) ∨ C / Real.pi ≤ x → q x = 0) ∧
      (∀ w : ℝ, routeURealFourier q w =
        (((w ^ 2 - (2 * Real.pi * r) ^ 2 : ℝ) : ℂ) ^ m) * G (w ^ 2)) := by
  obtain ⟨m, H, hm, hHanalytic, hHroot, hfactor⟩ :=
    exists_positive_entireRootFactor_routeUHardEdge_angularLocallyUniformLimit
      ha haT hnorm hL hFlocal hroot
  have hFlocal' : TendstoLocallyUniformly
      (fun n => routeUHardEdgeSquaredAngularApprox (a n) (p n)) F atTop := by
    convert hFlocal using 1
    rfl
  have hFanalytic : AnalyticOnNhd ℂ F Set.univ :=
    analyticOnNhd_routeUHardEdge_angularLocallyUniformLimit ha haT hFlocal'
  obtain ⟨q, G, hq1, hq2, hG, hsupp, hfourier⟩ :=
    routeUHardEdge_angularLocallyUniformLimit_has_literal_compact_factorization
      hC ha haT hb hNC hnorm hL hFlocal hFanalytic.continuous
        hHanalytic.continuous hfactor
  exact ⟨m, H, q, G, hm, hHanalytic, hHroot, hfactor,
    hq1, hq2, hG, hsupp, hfourier⟩

end RHTower
