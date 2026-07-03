/-
# Maximum principle for harmonic functions

mathlib has the harmonic mean-value property (`HarmonicOnNhd.circleAverage_eq`) and the harmonic
conjugate on a ball (`HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`), but not the maximum principle.
This file supplies it, as the first of the three ingredients of the Dirichlet-problem / harmonic
Schwarz reflection development needed to discharge the Kellogg–Warschawski boundary-extension
hypothesis `hu` of `BottcherArcExtension.lean`.

The proof reads the harmonic maximum principle off the **holomorphic** maximum-modulus principle: near
any point `u = Re F` for an analytic `F` (`exists_analyticOnNhd_ball_re_eq`), so `exp F` is analytic
with `‖exp F‖ = exp u`; an interior maximum of `u` is an interior maximum of `‖exp F‖`, which forces
`exp F` locally constant (`eqOn_of_isPreconnected_of_isMaxOn_norm`), hence `u` locally constant.  The
local-constancy set is clopen in the preconnected domain.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.AbsMax

open Complex Set Filter Topology InnerProductSpace

namespace Bottcher

/-- **Maximum principle for harmonic functions.** A real harmonic function on a preconnected open
set that attains a maximum at an interior point is constant.  Proof: locally `u = Re F` for an
analytic `F`, so `exp F` is analytic with `‖exp F‖ = exp u`; an interior max of `u` is an interior
max of `‖exp F‖`, forcing `exp F` locally constant (holomorphic maximum modulus), hence `u` locally
constant.  The local-constancy set is clopen in the preconnected `U`. -/
theorem harmonic_eqOn_const_of_isMaxOn
    {u : ℂ → ℝ} {U : Set ℂ} {c : ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hu : HarmonicOnNhd u U)
    (hc : c ∈ U) (hmax : IsMaxOn u U c) :
    Set.EqOn u (fun _ => u c) U := by
  classical
  have hucont : ContinuousOn u U := hu.contDiffOn.continuousOn
  set M : ℝ := u c with hMdef
  set S : Set ℂ := {z | z ∈ U ∧ u z = M} with hSdef
  have hcS : c ∈ S := ⟨hc, rfl⟩
  -- S is open in ℂ
  have hSopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro z₀ hz₀
    obtain ⟨hz₀U, hz₀M⟩ := hz₀
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo z₀ hz₀U
    obtain ⟨F, hFan, hFre⟩ := (hu.mono hball).exists_analyticOnNhd_ball_re_eq
    set g : ℂ → ℂ := fun w => Complex.exp (F w) with hgdef
    have hgdiff : DifferentiableOn ℂ g (Metric.ball z₀ ε) := hFan.differentiableOn.cexp
    have hgnorm : ∀ w ∈ Metric.ball z₀ ε, ‖g w‖ = Real.exp (u w) := fun w hw => by
      have hre : (F w).re = u w := hFre hw
      rw [hgdef, Complex.norm_exp, hre]
    have hgmax : IsMaxOn (norm ∘ g) (Metric.ball z₀ ε) z₀ := by
      intro w hw
      show ‖g w‖ ≤ ‖g z₀‖
      rw [hgnorm w hw, hgnorm z₀ (Metric.mem_ball_self hε)]
      apply Real.exp_le_exp.mpr
      rw [hz₀M]; exact hmax (hball hw)
    have hgconst : Set.EqOn g (fun _ => g z₀) (Metric.ball z₀ ε) :=
      eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball z₀ ε).isPreconnected Metric.isOpen_ball
        hgdiff (Metric.mem_ball_self hε) hgmax
    refine ⟨Metric.ball z₀ ε, fun w hw => ⟨hball hw, ?_⟩, Metric.isOpen_ball, Metric.mem_ball_self hε⟩
    have h1 : Real.exp (u w) = Real.exp (u z₀) := by
      rw [← hgnorm w hw, ← hgnorm z₀ (Metric.mem_ball_self hε), hgconst hw]
    exact (Real.exp_eq_exp.mp h1).trans hz₀M
  -- U ∖ S is open in U: extract W with u⁻¹{M}ᶜ ∩ U = W ∩ U
  obtain ⟨W, hWo, hW⟩ := continuousOn_iff'.mp hucont {M}ᶜ isOpen_compl_singleton
  -- IsPreconnected forces U ⊆ S
  intro z hzU
  by_contra hne
  have hzW : z ∈ W ∩ U := by
    rw [← hW]; exact ⟨by simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]; exact hne, hzU⟩
  have hcover : U ⊆ S ∪ W := by
    intro y hyU
    by_cases hyM : u y = M
    · exact Or.inl ⟨hyU, hyM⟩
    · have : y ∈ W ∩ U := by
        rw [← hW]; exact ⟨by simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]; exact hyM, hyU⟩
      exact Or.inr this.1
  have hSU : (U ∩ S).Nonempty := ⟨c, hc, hcS⟩
  have hWU : (U ∩ W).Nonempty := ⟨z, hzU, hzW.1⟩
  obtain ⟨y, hyU, hyS, hyW⟩ := hUc S W hSopen hWo hcover hSU hWU
  -- y ∈ S ∩ W: u y = M (from S) but y ∈ W∩U = u⁻¹{M}ᶜ (u y ≠ M) — contradiction
  have : y ∈ W ∩ U := ⟨hyW, hyU⟩
  rw [← hW] at this
  exact this.1 hyS.2

end Bottcher
