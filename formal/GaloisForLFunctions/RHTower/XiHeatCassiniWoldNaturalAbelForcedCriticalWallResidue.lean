import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergyHalfNoGo

/-!
# T2 natural Abel continuations have a forced critical-wall residue

The literal natural Wold Abel germ is unconditional on `Re s > 0`.  This module proves that every
holomorphic continuation of that germ to the upper translated critical sector inherits the same
nonzero negative-integer residue at one unconditional Hardy critical-line zero.  Thus regular
continuation is impossible independently of any square-energy mechanism used to produce it.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- The integer logarithmic mesh is holomorphic throughout the upper translated critical sector. -/
theorem analyticOnNhd_integerLogMeshContinuation_residualODESector :
    AnalyticOnNhd ℂ integerLogMeshContinuation
      (xiHeatCassiniWoldResidualODESector 1) := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_xiHeatCassiniWoldResidualODESector 1)
  intro s hs
  change -(1 / 2 : ℝ) < s.re ∧ 0 < (1 : ℝ) * s.im at hs
  simp only [one_mul] at hs
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    simp at hs
  exact (differentiableAt_integerLogMeshContinuation (by linarith) hs0).differentiableWithinAt

/-- On the safe half-plane, the literal natural Abel germ plus the continued integer mesh is the
ordered Wold current.  No square-energy assumption is used. -/
theorem woldNatAbel_add_mesh_eq_woldLaplaceCurrent_safe
    {F : ℂ → ℂ}
    (hEq : Set.EqOn F (fun s : ℂ => abelDirichlet woldNatDifferenceCoeff s)
      {s : ℂ | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re})
    {s : ℂ} (hsU : s ∈ xiHeatCassiniWoldResidualODESector 1) (hs : 0 < s.re) :
    F s + integerLogMeshContinuation s = xiHeatCassiniWoldLaplaceCurrent s := by
  have hF := hEq ⟨hsU, hs⟩
  have hAbel := abelDirichlet_woldNatDifferenceCoeff_eq_wold_sub_mesh hs
  rw [hF, integerLogMeshContinuation_eq_current hs]
  linear_combination hAbel

/-- Zeta-clearing and the identity theorem force any holomorphic continuation of the natural Abel
germ to coincide with the canonical cleared Wold continuation on the whole upper sector. -/
theorem xiHeatCassiniWoldZetaClearedContinuation_eq_mul_naturalAbel_on_sector
    {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (xiHeatCassiniWoldResidualODESector 1))
    (hEq : Set.EqOn F (fun s : ℂ => abelDirichlet woldNatDifferenceCoeff s)
      {s : ℂ | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re}) :
    Set.EqOn xiHeatCassiniWoldZetaClearedContinuation
      (fun s : ℂ => riemannZeta (s + 1) *
        (F s + integerLogMeshContinuation s))
      (xiHeatCassiniWoldResidualODESector 1) := by
  have hL := analyticOnNhd_xiHeatCassiniWoldZetaClearedContinuation
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => F s + integerLogMeshContinuation s)
      (xiHeatCassiniWoldResidualODESector 1) :=
    hF.add analyticOnNhd_integerLogMeshContinuation_residualODESector
  have hR : AnalyticOnNhd ℂ
      (fun s : ℂ => riemannZeta (s + 1) *
        (F s + integerLogMeshContinuation s))
      (xiHeatCassiniWoldResidualODESector 1) :=
    (analyticOnNhd_riemannZeta_add_one_residualODESector 1).mul hG
  let q : ℂ := 1 + Complex.I
  have hq : q ∈ xiHeatCassiniWoldResidualODESector 1 := by
    change -(1 / 2 : ℝ) < q.re ∧ 0 < (1 : ℝ) * q.im
    constructor <;> norm_num [q]
  have hevent : xiHeatCassiniWoldZetaClearedContinuation =ᶠ[𝓝 q]
      (fun s : ℂ => riemannZeta (s + 1) *
        (F s + integerLogMeshContinuation s)) := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hqpos : 0 < q.re := by simp [q]
    filter_upwards [hopen.mem_nhds hqpos,
      (isOpen_xiHeatCassiniWoldResidualODESector 1).mem_nhds hq] with s hs hsU
    have hz : riemannZeta (s + 1) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simp
      linarith
    rw [xiHeatCassiniWoldZetaClearedContinuation_eq_mul_critical hz,
      xiHeatCassiniWoldCriticalLaplaceContinuation_eq (by linarith),
      xiHeatCassiniWoldLaplaceContinuation_eq hs,
      woldNatAbel_add_mesh_eq_woldLaplaceCurrent_safe hEq hsU hs]
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR
    (isPreconnected_xiHeatCassiniWoldResidualODESector 1) hq hevent

/-- **Universal T2 critical-wall residue.**  One unconditional Hardy zero supplies a wall point and
a positive multiplicity, independent of the proposed continuation, at which every holomorphic
continuation of the literal natural Wold Abel germ has radial residue `-m`. -/
theorem exists_woldNatAbelContinuation_forced_criticalWall_residue :
    ∃ (s0 : ℂ) (m : ℕ),
      s0.re = -(1 / 2 : ℝ) ∧ 0 < s0.im ∧ 1 ≤ m ∧
      ∀ (F : ℂ → ℂ),
        AnalyticOnNhd ℂ F (xiHeatCassiniWoldResidualODESector 1) →
        Set.EqOn F (fun s : ℂ => abelDirichlet woldNatDifferenceCoeff s)
          {s : ℂ | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re} →
        Tendsto (fun x : ℝ => (x : ℂ) * F (s0 + (x : ℂ)))
          (𝓝[>] (0 : ℝ)) (𝓝 (-(m : ℂ))) := by
  obtain ⟨T0, hT0, hHardy⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨tau, htauIcc, hzeta⟩ := hHardy T0 le_rfl
  have htau : 0 < tau := lt_of_lt_of_le hT0 htauIcc.1
  let rho : ℂ := linePt tau
  have hrhoRe : rho.re = 1 / 2 := by
    simp [rho, linePt]
  have hrhoIm : rho.im = tau := by
    simp [rho, linePt]
  let s0 : ℂ := rho - 1
  have hs0re : s0.re = -(1 / 2 : ℝ) := by
    dsimp only [s0]
    simp only [Complex.sub_re, Complex.one_re, hrhoRe]
    norm_num
  have hs0im : s0.im = tau := by
    dsimp only [s0]
    simp only [Complex.sub_im, Complex.one_im, sub_zero, hrhoIm]
  obtain ⟨m, hm, hpole⟩ :=
    xiHeatCassiniWoldCriticalLaplaceContinuation_zero_residue hrhoRe hzeta
  refine ⟨s0, m, hs0re, ?_, hm, ?_⟩
  · rw [hs0im]
    exact htau
  intro F hF hEq
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
      exact ⟨by linarith, htau⟩
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
  convert hsub using 1
  · funext x
    ring
  · simp

/-- No holomorphic continuation of the literal natural Abel germ can have a finite right-radial
boundary value at the universal Hardy wall point.  This is the regular-continuation branch kill. -/
theorem exists_woldNatAbelContinuation_no_finite_criticalWall_limit :
    ∃ (s0 : ℂ) (m : ℕ),
      s0.re = -(1 / 2 : ℝ) ∧ 0 < s0.im ∧ 1 ≤ m ∧
      ∀ (F : ℂ → ℂ),
        AnalyticOnNhd ℂ F (xiHeatCassiniWoldResidualODESector 1) →
        Set.EqOn F (fun s : ℂ => abelDirichlet woldNatDifferenceCoeff s)
          {s : ℂ | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re} →
        ∀ L : ℂ, ¬ Tendsto (fun x : ℝ => F (s0 + (x : ℂ)))
          (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  obtain ⟨s0, m, hs0re, hs0im, hm, hres⟩ :=
    exists_woldNatAbelContinuation_forced_criticalWall_residue
  refine ⟨s0, m, hs0re, hs0im, hm, ?_⟩
  intro F hF hEq L hlim
  have hxzero : Tendsto (fun x : ℝ => (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun x : ℝ => (x : ℂ) * F (s0 + (x : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using hxzero.mul hlim
  have hmzero : -(m : ℂ) = 0 :=
    tendsto_nhds_unique (hres F hF hEq) hzero
  have hmzero' : (m : ℂ) = 0 := neg_eq_zero.mp hmzero
  have : m = 0 := by exact_mod_cast hmzero'
  omega

end

end RHTower
