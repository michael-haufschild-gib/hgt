import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelForcedCriticalWallResidue

/-!
# The full positive critical divisor of the natural Wold Abel germ

Every holomorphic continuation of the literal natural Wold Abel germ inherits the exact nonzero
radial residue at every positive-height critical-line zeta zero.  Hardy's theorem then rules out
every continuation whose exceptional radial singular heights form a finite set.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A continuation has finite radial singular support when it has a finite right-radial boundary
value at every positive wall height outside one finite exceptional set. -/
def WoldNatAbelFiniteRadialSingularSupport (F : ℂ → ℂ) : Prop :=
  ∃ S : Finset ℝ, ∀ tau : ℝ, 0 < tau → tau ∉ S →
    ∃ L : ℂ, Tendsto (fun x : ℝ => F ((linePt tau - 1) + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 L)

/-- **Full critical-divisor inheritance.**  At every positive-height critical-line zeta zero, every
holomorphic continuation of the literal natural Wold Abel germ has the canonical negative-integer
radial residue. -/
theorem woldNatAbelContinuation_forced_residue_at_criticalLine_zero
    {rho : ℂ} (hrhoRe : rho.re = 1 / 2) (hrhoIm : 0 < rho.im)
    (hzeta : riemannZeta rho = 0)
    {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (xiHeatCassiniWoldResidualODESector 1))
    (hEq : Set.EqOn F (fun s : ℂ => abelDirichlet woldNatDifferenceCoeff s)
      {s : ℂ | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re}) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun x : ℝ =>
        (x : ℂ) * F ((rho - 1) + (x : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (-(m : ℂ))) := by
  let s0 : ℂ := rho - 1
  have hs0re : s0.re = -(1 / 2 : ℝ) := by
    dsimp only [s0]
    simp only [Complex.sub_re, Complex.one_re, hrhoRe]
    norm_num
  have hs0im : s0.im = rho.im := by
    dsimp only [s0]
    simp
  obtain ⟨m, hm, hpole⟩ :=
    xiHeatCassiniWoldCriticalLaplaceContinuation_zero_residue hrhoRe hzeta
  refine ⟨m, hm, ?_⟩
  have hsectorEq :=
    xiHeatCassiniWoldZetaClearedContinuation_eq_mul_naturalAbel_on_sector hF hEq
  have hpathS0 : Tendsto (fun x : ℝ => s0 + (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 s0) := by
    have hcont : ContinuousAt (fun x : ℝ => s0 + (x : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpathS0Punct : Tendsto (fun x : ℝ => s0 + (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝[≠] s0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hpathS0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    have hx0 : (x : ℂ) = 0 := by linear_combination heq
    exact hx.ne' (ofReal_eq_zero.mp hx0)
  have hpolePath0 := hpole.comp hpathS0Punct
  have hpolePath : Tendsto (fun x : ℝ =>
      (x : ℂ) * xiHeatCassiniWoldCriticalLaplaceContinuation
        (s0 + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(m : ℂ))) := by
    convert hpolePath0 using 1
    funext x
    simp only [Function.comp_apply, s0]
    congr 1
    ring
  have hpathRho : Tendsto (fun x : ℝ => rho + (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 rho) := by
    have hcont : ContinuousAt (fun x : ℝ => rho + (x : ℂ)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpathRhoPunct : Tendsto (fun x : ℝ => rho + (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝[≠] rho) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hpathRho, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    have hx0 : (x : ℂ) = 0 := by linear_combination heq
    exact hx.ne' (ofReal_eq_zero.mp hx0)
  have hzetaOff : ∀ᶠ z in 𝓝[≠] rho, riemannZeta z ≠ 0 :=
    eventually_riemannZeta_ne_zero_nhdsNE (by rw [hrhoRe]; norm_num)
      (by rw [hrhoRe]; norm_num)
  have hzetaPath : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      riemannZeta (rho + (x : ℂ)) ≠ 0 :=
    hpathRhoPunct.eventually hzetaOff
  have heq : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      xiHeatCassiniWoldCriticalLaplaceContinuation (s0 + (x : ℂ)) =
        F (s0 + (x : ℂ)) +
          integerLogMeshContinuation (s0 + (x : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin, hzetaPath] with x hx hzetaX
    change 0 < x at hx
    let z : ℂ := s0 + (x : ℂ)
    have hzarg : riemannZeta (z + 1) ≠ 0 := by
      rw [show z + 1 = rho + (x : ℂ) by
        dsimp only [z, s0]
        ring]
      exact hzetaX
    have hzmem : z ∈ xiHeatCassiniWoldResidualODESector 1 := by
      change -(1 / 2 : ℝ) < z.re ∧ 0 < (1 : ℝ) * z.im
      dsimp only [z]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im,
        Complex.ofReal_im, add_zero, one_mul, hs0re, hs0im]
      exact ⟨by linarith, hrhoIm⟩
    have hclearedAbel := hsectorEq hzmem
    have hclearedCritical :=
      xiHeatCassiniWoldZetaClearedContinuation_eq_mul_critical hzarg
    apply mul_left_cancel₀ hzarg
    exact hclearedCritical.symm.trans hclearedAbel
  have hsumPole : Tendsto (fun x : ℝ =>
      (x : ℂ) * (F (s0 + (x : ℂ)) +
        integerLogMeshContinuation (s0 + (x : ℂ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(m : ℂ))) := by
    apply hpolePath.congr'
    exact heq.mono fun x hx => by
      change (x : ℂ) * xiHeatCassiniWoldCriticalLaplaceContinuation
          (s0 + (x : ℂ)) =
        (x : ℂ) * (F (s0 + (x : ℂ)) +
          integerLogMeshContinuation (s0 + (x : ℂ)))
      rw [hx]
  have hs00 : s0 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [hs0im] at him
    simp at him
    linarith
  have hmeshAt := differentiableAt_integerLogMeshContinuation
    (s := s0) (by rw [hs0re]; norm_num) hs00
  have hmesh : Tendsto
      (fun x : ℝ => integerLogMeshContinuation (s0 + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (integerLogMeshContinuation s0)) :=
    hmeshAt.continuousAt.tendsto.comp hpathS0
  have hxzero : Tendsto (fun x : ℝ => (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmeshZero : Tendsto (fun x : ℝ =>
      (x : ℂ) * integerLogMeshContinuation (s0 + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using hxzero.mul hmesh
  have hsub := hsumPole.sub hmeshZero
  change Tendsto (fun x : ℝ => (x : ℂ) * F (s0 + (x : ℂ)))
    (𝓝[>] (0 : ℝ)) (𝓝 (-(m : ℂ)))
  convert hsub using 1
  · funext x
    ring
  · simp

/-- **Finite-singularity T2 no-go.**  No holomorphic continuation of the literal natural Wold Abel
germ can have only finitely many exceptional radial singular heights. -/
theorem not_woldNatAbelFiniteRadialSingularSupport
    {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (xiHeatCassiniWoldResidualODESector 1))
    (hEq : Set.EqOn F (fun s : ℂ => abelDirichlet woldNatDifferenceCoeff s)
      {s : ℂ | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re}) :
    ¬ WoldNatAbelFiniteRadialSingularSupport F := by
  rintro ⟨S, hS⟩
  obtain ⟨T0, hT0, hHardy⟩ := exists_riemannZeta_line_zero_dyadic
  let T : ℝ := T0 + (∑ u ∈ S, |u|) + 1
  have hsum0 : 0 ≤ ∑ u ∈ S, |u| :=
    Finset.sum_nonneg fun u _ => abs_nonneg u
  have hT0T : T0 ≤ T := by
    dsimp only [T]
    linarith
  obtain ⟨tau, htauIcc, hzeta⟩ := hHardy T hT0T
  have hTpos : 0 < T := lt_of_lt_of_le hT0 hT0T
  have htau : 0 < tau := lt_of_lt_of_le hTpos htauIcc.1
  have htauNot : tau ∉ S := by
    intro htauS
    have habs : |tau| ≤ ∑ u ∈ S, |u| :=
      Finset.single_le_sum (fun u _ => abs_nonneg u) htauS
    have htauLe : tau ≤ ∑ u ∈ S, |u| :=
      (le_abs_self tau).trans habs
    dsimp only [T] at htauIcc
    have hTtau : T0 + (∑ u ∈ S, |u|) + 1 ≤ tau := htauIcc.1
    linarith
  obtain ⟨L, hlim⟩ := hS tau htau htauNot
  have hrhoRe : (linePt tau).re = 1 / 2 := by simp [linePt]
  have hrhoIm : 0 < (linePt tau).im := by simpa [linePt] using htau
  obtain ⟨m, hm, hres⟩ :=
    woldNatAbelContinuation_forced_residue_at_criticalLine_zero
      hrhoRe hrhoIm hzeta hF hEq
  have hxzero : Tendsto (fun x : ℝ => (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun x : ℝ =>
      (x : ℂ) * F ((linePt tau - 1) + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using hxzero.mul hlim
  have hmzero : -(m : ℂ) = 0 := tendsto_nhds_unique hres hzero
  have hmzero' : (m : ℂ) = 0 := neg_eq_zero.mp hmzero
  have : m = 0 := by exact_mod_cast hmzero'
  omega

end

end RHTower
