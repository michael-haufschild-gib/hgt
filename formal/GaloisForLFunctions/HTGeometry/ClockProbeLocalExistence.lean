import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import GaloisForLFunctions.HTGeometry.ClockProbeConditionAudit

/-!
# Local existence of clock probes for an arbitrary smooth potential

The determination results so far realized the no-common-zero condition only for particular
potentials — constant, Riccati, or induced by a chosen nonvanishing function. This file removes that
restriction in one dimension: for **every** `C¹` potential and every event there is a genuine local
solution of `u'' + Vu = 0` equal to `1` at that event.

The construction autonomises the second-order equation as the first-order field
`(x, u, v) ↦ (1, v, -(V x)·u)` on `ℝ³`, applies the Picard–Lindelöf existence theorem for `C¹`
vector fields, and identifies the first component with `a + t` by the mean value theorem. The
resulting probe solves the equation on an open interval around the event, which is the region form
the determination theory consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- Autonomised first-order field of the second-order equation `u'' + Vu = 0`. -/
noncomputable def waveField (V : ℝ → ℝ) : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
  fun p => (1, p.2.2, -(V p.1) * p.2.1)

theorem contDiff_waveField {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) :
    ContDiff ℝ 1 (waveField V) := by
  refine ContDiff.prodMk contDiff_const (ContDiff.prodMk ?_ ?_)
  · exact contDiff_snd.comp contDiff_snd
  · exact ((hV.comp contDiff_fst).neg).mul (contDiff_fst.comp contDiff_snd)

/-- First component of a curve in `ℝ³`. -/
noncomputable def projOne : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

/-- Second component of a curve in `ℝ³`. -/
noncomputable def projTwo : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Third component of a curve in `ℝ³`. -/
noncomputable def projThree : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

@[simp] theorem projOne_apply (p : ℝ × ℝ × ℝ) : projOne p = p.1 := rfl
@[simp] theorem projTwo_apply (p : ℝ × ℝ × ℝ) : projTwo p = p.2.1 := rfl
@[simp] theorem projThree_apply (p : ℝ × ℝ × ℝ) : projThree p = p.2.2 := rfl

/-- **Local probe existence.** For every `C¹` potential and every event there is a solution of
`u'' + Vu = 0` on an open interval around the event, taking the value one there. -/
theorem exists_localProbe {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (a : ℝ) :
    ∃ (u : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ u a = 1 ∧
      SolvesPotentialWaveOn secondDeriv V u (Ioo (a - ε) (a + ε)) := by
  obtain ⟨α, hα0, ε, hε, hode⟩ :=
    (contDiff_waveField hV).contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (x₀ := ((a, 1, 0) : ℝ × ℝ × ℝ)) 0
  have hIoo : ∀ t : ℝ, t ∈ Ioo (-ε) ε → t ∈ Ioo (0 - ε) (0 + ε) := by
    intro t ht
    simpa using ht
  -- componentwise equations
  have hcomp1 : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s => (α s).1) 1 t := by
    intro t ht
    exact projOne.hasFDerivAt.comp_hasDerivAt t (hode t (hIoo t ht))
  have hcomp2 : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s => (α s).2.1) ((α t).2.2) t := by
    intro t ht
    exact projTwo.hasFDerivAt.comp_hasDerivAt t (hode t (hIoo t ht))
  have hcomp3 : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s => (α s).2.2) (-(V ((α t).1)) * (α t).2.1) t := by
    intro t ht
    exact projThree.hasFDerivAt.comp_hasDerivAt t (hode t (hIoo t ht))
  -- the first component is affine
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> linarith
  have haffine : ∀ t ∈ Ioo (-ε) ε, (α t).1 = a + t := by
    have hg : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s => (α s).1 - s) 0 t := by
      intro t ht
      have hsub := (hcomp1 t ht).sub (hasDerivAt_id t)
      have hval : (1 : ℝ) - 1 = 0 := by ring
      rw [hval] at hsub
      exact hsub
    have hdiff : DifferentiableOn ℝ (fun s => (α s).1 - s) (Ioo (-ε) ε) :=
      fun t ht => ((hg t ht).differentiableAt).differentiableWithinAt
    have hfd : EqOn (fderiv ℝ fun s => (α s).1 - s) 0 (Ioo (-ε) ε) := by
      intro t ht
      have := (hg t ht).hasFDerivAt.fderiv
      simpa using this
    intro t ht
    have hconst := isOpen_Ioo.is_const_of_fderiv_eq_zero isPreconnected_Ioo hdiff hfd ht hzero
    have hconst' : (α t).1 - t = (α 0).1 - 0 := hconst
    have h0 : (α 0).1 - 0 = a := by rw [hα0]; simp
    rw [h0] at hconst'
    linarith [hconst']
  -- the probe
  refine ⟨fun x => (α (x - a)).2.1, ε, hε, ?_, ?_⟩
  · simp [hα0]
  · intro x hx
    have hxa : x - a ∈ Ioo (-ε) ε := by
      obtain ⟨h1, h2⟩ := hx
      constructor <;> linarith
    have hshift : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z - a) 1 y := by
      intro y
      simpa using (hasDerivAt_id y).sub_const a
    -- first derivative of the probe near x
    have hu' : ∀ y ∈ Ioo (a - ε) (a + ε),
        HasDerivAt (fun z => (α (z - a)).2.1) ((α (y - a)).2.2) y := by
      intro y hy
      have hya : y - a ∈ Ioo (-ε) ε := by
        obtain ⟨h1, h2⟩ := hy
        constructor <;> linarith
      have hcomp := (hcomp2 (y - a) hya).comp y (hshift y)
      rw [mul_one] at hcomp
      exact hcomp
    have hderivEq : Set.EqOn (deriv fun z => (α (z - a)).2.1)
        (fun y => (α (y - a)).2.2) (Ioo (a - ε) (a + ε)) := by
      intro y hy
      exact (hu' y hy).deriv
    have hmem : Ioo (a - ε) (a + ε) ∈ nhds x := isOpen_Ioo.mem_nhds hx
    have hev : (deriv fun z => (α (z - a)).2.1) =ᶠ[nhds x] fun y => (α (y - a)).2.2 :=
      Filter.eventuallyEq_of_mem hmem hderivEq
    have hsecond : HasDerivAt (fun y => (α (y - a)).2.2)
        (-(V ((α (x - a)).1)) * (α (x - a)).2.1) x := by
      have hcomp := (hcomp3 (x - a) hxa).comp x (hshift x)
      rw [mul_one] at hcomp
      exact hcomp
    have hfinal : HasDerivAt (deriv fun z => (α (z - a)).2.1)
        (-(V ((α (x - a)).1)) * (α (x - a)).2.1) x :=
      (hev.hasDerivAt_iff).2 hsecond
    rw [SolvesPotentialWaveAt, secondDeriv, hfinal.deriv, haffine (x - a) hxa]
    have hxx : a + (x - a) = x := by ring
    rw [hxx]
    ring

/-- **Every `C¹` potential has a shared-probe determination on an interval.** Any potential solved
by the same probe on that interval agrees with `V` there. -/
theorem potential_eqOn_of_contDiff {V other : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (a : ℝ) :
    ∃ (u : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ u a = 1 ∧
      (SolvesPotentialWaveOn secondDeriv other u (Ioo (a - ε) (a + ε)) →
        other a = V a) := by
  obtain ⟨u, ε, hε, hua, hsolve⟩ := exists_localProbe hV a
  refine ⟨u, ε, hε, hua, fun hother => ?_⟩
  have hmem : a ∈ Ioo (a - ε) (a + ε) := by constructor <;> linarith
  refine potential_eq_of_solvesPotentialWaveAt (hother a hmem) (hsolve a hmem) ?_
  rw [hua]
  exact one_ne_zero

/-! ## The local nondegeneracy condition never fails

The audit of the global condition `NoCommonZero` showed it is two-sided: for a degenerate wave
operator it fails, and determination fails with it. For the second-derivative operator with a `C¹`
potential the local form of the condition is unconditional. -/

/-- **Local nondegeneracy, unconditionally.** At every event of the line some solution of
`u'' + Vu = 0` on a neighbourhood of that event is nonzero there. -/
theorem exists_localProbe_ne_zero {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (a : ℝ) :
    ∃ (u : ℝ → ℝ) (ε : ℝ), 0 < ε ∧
      SolvesPotentialWaveOn secondDeriv V u (Ioo (a - ε) (a + ε)) ∧ u a ≠ 0 := by
  obtain ⟨u, ε, hε, hua, hsolve⟩ := exists_localProbe hV a
  exact ⟨u, ε, hε, hsolve, by rw [hua]; exact one_ne_zero⟩

/-- **Unconditional one-dimensional determination.** A `C¹` potential is pinned by its local
solutions: any competitor solving them on their own intervals equals it everywhere. No
nondegeneracy hypothesis is assumed — local existence supplies it. -/
theorem eq_of_solvesOn_localSolutions {V other : ℝ → ℝ} (hV : ContDiff ℝ 1 V)
    (hother : ∀ (a : ℝ) (u : ℝ → ℝ) (ε : ℝ), 0 < ε →
      SolvesPotentialWaveOn secondDeriv V u (Ioo (a - ε) (a + ε)) →
      SolvesPotentialWaveOn secondDeriv other u (Ioo (a - ε) (a + ε))) :
    other = V := by
  funext a
  obtain ⟨u, ε, hε, hsolve, hua⟩ := exists_localProbe_ne_zero hV a
  have hmem : a ∈ Ioo (a - ε) (a + ε) := by constructor <;> linarith
  exact potential_eq_of_solvesPotentialWaveAt
    (hother a u ε hε hsolve a hmem) (hsolve a hmem) hua

/-- **The conformal scale of a two-species pair is reconstructed unconditionally.** With both
species governed by `C¹` potentials on the line, any competing pair solving the same local
solutions yields the same reconstructed scale. -/
theorem reconstructedScale_eq_of_solvesOn_localSolutions
    {potential₁ potential₂ other₁ other₂ : ℝ → ℝ} {massSq₁ massSq₂ : ℝ}
    (h₁ : ContDiff ℝ 1 potential₁) (h₂ : ContDiff ℝ 1 potential₂)
    (hother₁ : ∀ (a : ℝ) (u : ℝ → ℝ) (ε : ℝ), 0 < ε →
      SolvesPotentialWaveOn secondDeriv potential₁ u (Ioo (a - ε) (a + ε)) →
      SolvesPotentialWaveOn secondDeriv other₁ u (Ioo (a - ε) (a + ε)))
    (hother₂ : ∀ (a : ℝ) (u : ℝ → ℝ) (ε : ℝ), 0 < ε →
      SolvesPotentialWaveOn secondDeriv potential₂ u (Ioo (a - ε) (a + ε)) →
      SolvesPotentialWaveOn secondDeriv other₂ u (Ioo (a - ε) (a + ε))) :
    reconstructedScale other₁ other₂ massSq₁ massSq₂ =
      reconstructedScale potential₁ potential₂ massSq₁ massSq₂ := by
  rw [eq_of_solvesOn_localSolutions h₁ hother₁, eq_of_solvesOn_localSolutions h₂ hother₂]

end GaloisForLFunctions.HTGeometry
