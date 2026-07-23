import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Basiswise boundary Pick rigidity

An operator-valued Pick family cannot hide loss in off-diagonal directions when every vector of
a Hilbert basis becomes lossless at one boundary node.  Pick Cauchy--Schwarz forces the fixed
interior operator to fix every basis vector through its adjoint, hence to be the identity.

No dimension, finite-rank, compactness, or trace-class hypothesis is used.
-/

open Filter Topology
open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

variable {E ι α : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Diagonal normalized loss for an operator at scalar Pick node `q`. -/
def operatorPickDiagonal (T : E →L[ℝ] E) (q : ℝ) (u : E) : ℝ :=
  (‖u‖ ^ 2 - ‖T u‖ ^ 2) / (1 - q ^ 2)

/-- Cross normalized loss for two operators at scalar Pick nodes `q,r`. -/
def operatorPickCross
    (S T : E →L[ℝ] E) (q r : ℝ) (u v : E) : ℝ :=
  (inner ℝ u v - inner ℝ (S u) (T v)) / (1 - q * r)

/-- **Basiswise boundary-charge law.**  Suppose a moving operator family converges strongly to
the identity on every vector of a Hilbert basis, while its normalized diagonal loss on every
basis vector tends to zero.  If the operator-valued Pick Cauchy--Schwarz inequality holds
eventually between a fixed interior operator and the moving boundary family, then the fixed
operator is the identity.

This is dimension-free: `ι` may be infinite and `E` need not be separable or finite-dimensional.
-/
theorem continuousLinearMap_eq_id_of_basiswise_boundaryPick
    {l : Filter α} [l.NeBot] (b : HilbertBasis ι ℝ E)
    (S : E →L[ℝ] E) (q₀ : ℝ) (T : α → E →L[ℝ] E) (q : α → ℝ)
    (hq : Tendsto q l (𝓝 1)) (hq₀ : q₀ ≠ 1)
    (hT : ∀ i, Tendsto (fun a => T a (b i)) l (𝓝 (b i)))
    (hdiag : ∀ i,
      Tendsto (fun a => operatorPickDiagonal (T a) (q a) (b i)) l (𝓝 0))
    (hpick : ∀ᶠ a in l, ∀ u v,
      operatorPickCross S (T a) q₀ (q a) u v ^ 2 ≤
        operatorPickDiagonal S q₀ u * operatorPickDiagonal (T a) (q a) v) :
    S = ContinuousLinearMap.id ℝ E := by
  have hfix : ∀ i, S.adjoint (b i) = b i := by
    intro i
    let h : E := b i - S.adjoint (b i)
    have hnum : Tendsto
        (fun a => inner ℝ h (b i) - inner ℝ (S h) (T a (b i))) l
        (𝓝 (‖h‖ ^ 2)) := by
      have htinner : Tendsto (fun a => inner ℝ (S h) (T a (b i))) l
          (𝓝 (inner ℝ (S h) (b i))) :=
        tendsto_const_nhds.inner (hT i)
      have hsub : Tendsto
          (fun a : α => inner ℝ h (b i) - inner ℝ (S h) (T a (b i))) l
          (𝓝 (inner ℝ h (b i) - inner ℝ (S h) (b i))) :=
        tendsto_const_nhds.sub htinner
      have hval : inner ℝ h (b i) - inner ℝ (S h) (b i) = ‖h‖ ^ 2 := by
        rw [← ContinuousLinearMap.adjoint_inner_right, ← inner_sub_right]
        change inner ℝ h h = ‖h‖ ^ 2
        exact real_inner_self_eq_norm_sq h
      simpa only [hval] using hsub
    have hden : Tendsto (fun a => 1 - q₀ * q a) l (𝓝 (1 - q₀)) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hq)
    have hden_ne : 1 - q₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hq₀)
    have hcross : Tendsto
        (fun a => operatorPickCross S (T a) q₀ (q a) h (b i)) l
        (𝓝 (‖h‖ ^ 2 / (1 - q₀))) := by
      simpa [operatorPickCross] using hnum.div hden hden_ne
    have hrhs : Tendsto
        (fun a => operatorPickDiagonal S q₀ h *
          operatorPickDiagonal (T a) (q a) (b i)) l (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (hdiag i)
    have hsqzero : Tendsto
        (fun a => operatorPickCross S (T a) q₀ (q a) h (b i) ^ 2) l (𝓝 0) := by
      apply squeeze_zero' (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (hpick.mono fun _ ha => ha h (b i)) hrhs
    have hsqlim : Tendsto
        (fun a => operatorPickCross S (T a) q₀ (q a) h (b i) ^ 2) l
        (𝓝 ((‖h‖ ^ 2 / (1 - q₀)) ^ 2)) := hcross.pow 2
    have heq : (‖h‖ ^ 2 / (1 - q₀)) ^ 2 = 0 :=
      tendsto_nhds_unique hsqlim hsqzero
    have hquot : ‖h‖ ^ 2 / (1 - q₀) = 0 := sq_eq_zero_iff.mp heq
    have hh : h = 0 := by
      have : ‖h‖ ^ 2 = 0 := (div_eq_zero_iff).mp hquot |>.resolve_right hden_ne
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)
    exact (sub_eq_zero.mp hh).symm
  have hadj : S.adjoint = ContinuousLinearMap.id ℝ E := by
    refine ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) ?_
    rintro x ⟨i, rfl⟩
    simpa using hfix i
  have := congrArg ContinuousLinearMap.adjoint hadj
  simpa using this

end

end HTGeometry
