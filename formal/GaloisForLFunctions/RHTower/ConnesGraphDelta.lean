import GaloisForLFunctions.RHTower.ConnesLinearFourier
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Connes' graph delta-section and the transversality condition

Formalization of the coordinate-free core of Appendix III of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068,

together with §IV (5)-(7).

Appendix III recalls, following Guillemin-Sternberg, the distribution-theoretic trace of a flow.
Three statements carry the whole computation.

* App. III (25) - the `δ`-section supported on the graph of a map evaluates as
  `∫ δ(y - f(x)) ξ(y) dy = ξ(f(x))`; formalized as integration against the Dirac measure at
  `f x`, i.e. as the pushforward of the diagonal.
* App. III (31)-(34) - the transversality of the diagonal to the graph of the flow, *"every element
  of `T_x M` is of the form `(F_t)_* X - X + μ v_x`"*, holds exactly when `1 - P` is invertible,
  where `P` is the Poincaré return map induced on the transverse space `N_x = T_x / ℝ v_x`.
* §IV (5)-(7), App. III (49)-(50) - at a zero of the vector field the symbol of the `δ`-section is
  the scalar `|1 - (F_t)_*|^{-1}`; formalized as the linear change of variables
  `∫ φ((1 - A) x) dx = |det (1 - A)|^{-1} ∫ φ`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory

/-! ### The delta section on a graph -/

/-- **Appendix III (25).**  The `δ`-section supported on the graph of `f` with its canonical symbol
evaluates a test function at `f x`. -/
theorem connes_graph_delta_apply {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : X → X) (ξ : X → E) (x : X) :
    ∫ y, ξ y ∂(Measure.dirac (f x)) = ξ (f x) :=
  integral_dirac ξ (f x)

/-! ### The transversality condition -/

section Transversality

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The line `ℝ v` spanned by the value of the vector field. -/
def connesFlowLine (v : V) : Submodule ℝ V := Submodule.span ℝ {v}

theorem connesFlowLine_le_comap {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v) :
    connesFlowLine v ≤ (connesFlowLine v).comap A := by
  rw [connesFlowLine, Submodule.span_le]
  rintro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  simp [hA, Submodule.mem_span_singleton_self]

/-- **Appendix III (33).**  The Poincaré return map: the map induced by `(F_t)_*` on the transverse
space `N_x = T_x / ℝ v_x`. -/
def connesReturnMap {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v) :
    (V ⧸ connesFlowLine v) →ₗ[ℝ] (V ⧸ connesFlowLine v) :=
  (connesFlowLine v).mapQ (connesFlowLine v) A (connesFlowLine_le_comap hA)

theorem connesReturnMap_mk {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v) (x : V) :
    connesReturnMap hA (Submodule.Quotient.mk x) = Submodule.Quotient.mk (A x) := rfl

/-- **Appendix III (31) ⟺ (34).**  The transversality condition `φ ⋔ Z` — *every element of
`T_x M` is of the form `(F_t)_* X - X + μ v_x`* — holds exactly when `1 - P` is surjective on the
transverse space, `P` the Poincaré return map. -/
theorem connes_transversality_iff {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v) :
    (∀ X : V, ∃ (Y : V) (μ : ℝ), X = A Y - Y + μ • v)
      ↔ Function.Surjective
          (⇑((LinearMap.id : (V ⧸ connesFlowLine v) →ₗ[ℝ] (V ⧸ connesFlowLine v))
              - connesReturnMap hA)) := by
  constructor
  · intro h q
    obtain ⟨X, rfl⟩ := Submodule.Quotient.mk_surjective (connesFlowLine v) q
    obtain ⟨Y, μ, hXY⟩ := h (-X)
    refine ⟨Submodule.Quotient.mk Y, ?_⟩
    have hmem : μ • v ∈ connesFlowLine v :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have hkey : (Submodule.Quotient.mk (p := connesFlowLine v) (-X))
        = Submodule.Quotient.mk (A Y - Y) := by
      rw [hXY]
      exact (Submodule.Quotient.eq _).mpr (by simpa using hmem)
    simp only [LinearMap.sub_apply, LinearMap.id_apply, connesReturnMap_mk]
    rw [← Submodule.Quotient.mk_sub]
    have hneg : (Submodule.Quotient.mk (p := connesFlowLine v) (Y - A Y))
        = -Submodule.Quotient.mk (A Y - Y) := by
      rw [← Submodule.Quotient.mk_neg]
      congr 1
      abel
    rw [hneg, ← hkey, Submodule.Quotient.mk_neg, neg_neg]
  · intro h X
    obtain ⟨q, hq⟩ := h (-Submodule.Quotient.mk X)
    obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective (connesFlowLine v) q
    simp only [LinearMap.sub_apply, LinearMap.id_apply, connesReturnMap_mk] at hq
    rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_neg] at hq
    have hmem0 := (Submodule.Quotient.eq (connesFlowLine v)).mp hq
    have hmem : X - (A Y - Y) ∈ connesFlowLine v := by
      have hEq : X - (A Y - Y) = Y - A Y - -X := by abel
      rw [hEq]
      exact hmem0
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨Y, μ, ?_⟩
    rw [hμ]
    abel

end Transversality

/-! ### The symbol at a zero of the vector field -/

/-- **§IV (5)-(7) / Appendix III (49)-(50).**  At a zero of the vector field the transversality
condition reads `1 - (F_t)_*` invertible and the symbol of the `δ`-section is the scalar
`|1 - (F_t)_*|^{-1} = |det (1 - A)|^{-1}`: the Jacobian of the change of variables
`x ↦ (1 - A) x` used to compute `∫ δ(x - A x) dx`. -/
theorem connes_symbol_at_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {A : E →ₗ[ℝ] E}
    (hA : LinearMap.det ((LinearMap.id : E →ₗ[ℝ] E) - A) ≠ 0) {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : E → G} (hg : AEStronglyMeasurable g μ) :
    ∫ x, g (((LinearMap.id : E →ₗ[ℝ] E) - A) x) ∂μ
      = |LinearMap.det ((LinearMap.id : E →ₗ[ℝ] E) - A)|⁻¹ • ∫ u, g u ∂μ :=
  integral_comp_linearMap_addHaar μ hA hg

end

end GaloisForLFunctions.RHTower
