import GaloisForLFunctions.HTGeometry.DivergenceCompactSupport

/-!
# Divergence of a field on `Fin n → ℝ`, all dimensions

`GaloisForLFunctions.HTGeometry.divergence` is stated for `Fin (n+1) → ℝ`, because mathlib's box
divergence theorem needs at least one coordinate.  Degree theory wants a statement uniform in the
dimension, including the degenerate zero-dimensional case where the divergence is an empty sum.
This file records that uniform version and the regularity facts the later mollifier arguments use.
-/

open MeasureTheory Finset Set

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ}

/-- The divergence of a vector field on `Fin n → ℝ`. -/
noncomputable def fieldDivergence (V : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  ∑ j, fderiv ℝ V x (Pi.single j 1) j

theorem fderiv_eq_zero_of_notMem_tsupport {V : (Fin n → ℝ) → (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∉ tsupport V) : fderiv ℝ V x = 0 := by
  have h : V =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  rw [h.fderiv_eq]
  simp

theorem fieldDivergence_eq_zero_of_notMem_tsupport {V : (Fin n → ℝ) → (Fin n → ℝ)}
    {x : Fin n → ℝ} (hx : x ∉ tsupport V) : fieldDivergence V x = 0 := by
  simp [fieldDivergence, fderiv_eq_zero_of_notMem_tsupport hx]

theorem continuous_fieldDivergence {V : (Fin n → ℝ) → (Fin n → ℝ)} (hV : ContDiff ℝ 1 V) :
    Continuous (fieldDivergence V) := by
  have hcont' : Continuous (fderiv ℝ V) := hV.continuous_fderiv (by simp)
  refine continuous_finsetSum _ fun j _ => ?_
  exact (continuous_apply j).comp (hcont'.clm_apply continuous_const)

theorem hasCompactSupport_fieldDivergence {V : (Fin n → ℝ) → (Fin n → ℝ)}
    (hsupp : HasCompactSupport V) : HasCompactSupport (fieldDivergence V) :=
  HasCompactSupport.intro hsupp.isCompact fun _ hx =>
    fieldDivergence_eq_zero_of_notMem_tsupport hx

/-- **The integral of a compactly supported divergence vanishes**, in every dimension. -/
theorem integral_fieldDivergence_eq_zero {V : (Fin n → ℝ) → (Fin n → ℝ)}
    (hV : ContDiff ℝ 1 V) (hsupp : HasCompactSupport V) :
    ∫ x, fieldDivergence V x = 0 := by
  cases n with
  | zero => simp [fieldDivergence]
  | succ m =>
    exact integral_divergence_eq_zero_of_hasCompactSupport V (fderiv ℝ V)
      (fun x => (hV.differentiable (by simp) x).hasFDerivAt)
      (continuous_fieldDivergence hV) hsupp

end GaloisForLFunctions.HTGeometry.PoincareHopf
