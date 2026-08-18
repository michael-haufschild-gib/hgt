import GaloisForLFunctions.HTGeometry.StripTranslateCurve
import GaloisForLFunctions.HTGeometry.BohrHullGroup
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.MetricSpace.Completion

/-!
# Points of the strip carrier are holomorphic

A uniform limit of vertical translates of a holomorphic function is holomorphic in the interior of
the substrip: the translates are holomorphic there and uniform convergence on the closed substrip is
in particular locally uniform inside it.

Every point of the phase carrier of the translate curve is such a limit — the carrier is a
completion of the line under the substrip sup-distance, so each point is the limit of a sequence of
translates, and evaluation is continuous.  Hence each carrier point *is* a holomorphic function on
the open substrip, which is the analytic transfer eq. (19) needs: the carrier is not merely a
compact group, it is a compact family of holomorphic functions.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : ℂ → E} {σ R r : ℝ}

/-- **Uniform limits of vertical translates are holomorphic inside the substrip.** -/
theorem differentiableOn_of_tendstoUniformlyOn (hr : r < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) {g : ℂ → E} {τ : ℕ → ℝ}
    (hconv : TendstoUniformlyOn (fun n z => F (z + (τ n : ℂ) * Complex.I)) g atTop
      (closedStrip σ r)) :
    DifferentiableOn ℂ g (verticalStrip σ r) := by
  have hsub : verticalStrip σ r ⊆ closedStrip σ r := by
    intro z hz
    show |z.re - σ| ≤ r
    exact le_of_lt hz
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun z => F (z + (τ n : ℂ) * Complex.I))
      (verticalStrip σ r) := by
    intro n z hz
    have hzs : z + (τ n : ℂ) * Complex.I ∈ verticalStrip σ R := by
      have hmem : z + (τ n : ℂ) * Complex.I ∈ closedStrip σ r :=
        mem_closedStrip_add_I σ r z (hsub hz) (τ n)
      exact closedStrip_subset_verticalStrip hr hmem
    have hd : DifferentiableAt ℂ (fun w : ℂ => F (w + (τ n : ℂ) * Complex.I)) z := by
      exact (hF.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds hzs)).comp z
        ((differentiable_id.add_const _) z)
    exact hd.differentiableWithinAt
  refine (hconv.mono hsub).tendstoLocallyUniformlyOn.differentiableOn ?_ (isOpen_verticalStrip σ r)
  exact Filter.Eventually.of_forall hdiff

omit [NormedSpace ℂ E] in
/-- **Every point of the strip carrier is a uniform limit of vertical translates.** -/
theorem exists_translate_seq_of_hull
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ E)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    (x : BohrHull Gb) :
    ∃ (g : ℂ → E) (τ : ℕ → ℝ),
      TendstoUniformlyOn (fun n z => F (z + (τ n : ℂ) * Complex.I)) g atTop (closedStrip σ r) ∧
        ∀ z : closedStrip σ r, g (z : ℂ) = bohrEval Gb x z := by
  classical
  -- a sequence of translates converging to `x`
  have hdense : x ∈ closure (Set.range (bohrIota Gb)) := (denseRange_bohrIota Gb) x
  rw [mem_closure_iff_seq_limit] at hdense
  obtain ⟨u, hu, hulim⟩ := hdense
  choose τ hτ using hu
  -- the evaluations converge in the substrip sup-norm space
  have heval : Tendsto (fun n => bohrEval Gb (u n)) atTop (nhds (bohrEval Gb x)) :=
    (UniformSpace.Completion.continuous_extension.tendsto x).comp hulim
  have hGval : ∀ n, bohrEval Gb (u n) = Gb (τ n) := by
    intro n
    rw [← hτ n, bohrEval_bohrIota]
  have hconv : Tendsto (fun n => Gb (τ n)) atTop (nhds (bohrEval Gb x)) := by
    refine heval.congr fun n => ?_
    rw [hGval n]
  -- uniform convergence on the substrip
  set g : ℂ → E := fun z => if h : z ∈ closedStrip σ r then (bohrEval Gb x) ⟨z, h⟩ else 0 with hgdef
  have hgval : ∀ z : closedStrip σ r, g (z : ℂ) = bohrEval Gb x z := by
    intro z
    rw [hgdef]
    simp only [dif_pos z.2]
  have huniform : TendstoUniformlyOn (fun n z => F (z + (τ n : ℂ) * Complex.I)) g atTop
      (closedStrip σ r) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have hrw : (fun n (z : closedStrip σ r) => F ((z : ℂ) + (τ n : ℂ) * Complex.I))
        = fun n (z : closedStrip σ r) => Gb (τ n) z := by
      funext n z
      rw [hGb (τ n) z]
    rw [hrw]
    have hgc : (g ∘ Subtype.val : closedStrip σ r → E) = fun z => (bohrEval Gb x) z := by
      funext z
      exact hgval z
    rw [hgc]
    exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  exact ⟨g, τ, huniform, hgval⟩

/-- **Every point of the strip carrier is a holomorphic function on the open substrip.** -/
theorem exists_holomorphic_of_hull (hr : r < R) (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ E)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    (x : BohrHull Gb) :
    ∃ g : ℂ → E, DifferentiableOn ℂ g (verticalStrip σ r) ∧
      ∀ z : closedStrip σ r, g (z : ℂ) = bohrEval Gb x z := by
  obtain ⟨g, τ, huniform, hgval⟩ := exists_translate_seq_of_hull hGb x
  exact ⟨g, differentiableOn_of_tendstoUniformlyOn hr hF huniform, hgval⟩

end GaloisForLFunctions
