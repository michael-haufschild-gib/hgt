import GaloisForLFunctions.BiScaleUncertainty.DivisorCellConstraints
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Exact closure of arithmetic trace gradients

The closure is the concrete prefix-conservation space. Its orthogonal
complement consists exactly of square-summable currents constant on active
edges. No spectral gap or closed-range premise enters this identification.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def divisorGradient (d : ℕ) (D : Set ℕ) : DivisorGridData d D →L[ℝ] TraceData :=
  traceGradient ∘L (divisorGridDataSpace d D).subtypeL

theorem divisorGradient_apply (d : ℕ) (D : Set ℕ) (v : DivisorGridData d D) :
    divisorGradient d D v = traceGradient v.1 := rfl

theorem divisorGradient_orthogonal_iff (d : ℕ) (D : Set ℕ) (w : TraceData) :
    w ∈ (divisorGradient d D).rangeᗮ ↔
      ∀ k, divisorGridActive d D k → w k = w (k+1) := by
  classical
  constructor
  · intro hw k hk
    have hv : lp.single 2 k (1 : ℝ) ∈ divisorGridDataSpace d D := by
      rw [mem_divisorGridDataSpace_iff]
      intro j hj
      have hjk : j ≠ k := by intro h; subst j; exact hj hk
      simp [lp.single_apply, Pi.single_eq_of_ne hjk]
    have he := (Submodule.mem_orthogonal _ _).mp hw _
      (LinearMap.mem_range.mpr ⟨⟨_, hv⟩, rfl⟩)
    change ⟪traceGradient (lp.single 2 k (1 : ℝ)), w⟫ = 0 at he
    simpa only [traceGradient_single, inner_sub_left, lp.inner_single_left,
      Real.inner_apply, one_mul, sub_eq_zero] using he
  · intro hw
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨v, rfl⟩
    have hs := (innerSL ℝ w).hasSum
      (traceGradient.hasSum (lp.hasSum_single (by norm_num) v.1))
    have hz (k : ℕ) : ⟪w, traceGradient (lp.single 2 k (v.1 k))⟫ = 0 := by
      rw [traceGradient_single, inner_sub_right, lp.inner_single_right,
        lp.inner_single_right, Real.inner_apply, Real.inner_apply]
      by_cases hk : divisorGridActive d D k
      · rw [hw k hk, sub_self]
      · rw [divisorGridData_off d D v hk]; simp
    simp only [innerSL_apply_apply, hz] at hs
    have he : ⟪w, traceGradient v.1⟫ = 0 := by simpa using hs.tsum_eq.symm
    change ⟪traceGradient v.1, w⟫ = 0
    rw [real_inner_comm]
    exact he

theorem divisorGradient_closure_le (d : ℕ) (D : Set ℕ) :
    (divisorGradient d D).range.topologicalClosure ≤ divisorCellSpace d D := by
  apply Submodule.topologicalClosure_minimal
  · rintro _ ⟨v, rfl⟩
    exact divisorGradient_mem d D v
  · exact isClosed_divisorCellSpace d D

/-- The entire completion is identified, including unbounded-run families. -/
theorem divisorGradient_closure (d : ℕ) (D : Set ℕ) :
    (divisorGradient d D).range.topologicalClosure = divisorCellSpace d D := by
  apply le_antisymm (divisorGradient_closure_le d D)
  intro w hw
  let M := (divisorGradient d D).range.topologicalClosure
  letI : CompleteSpace M := (divisorGradient d D).range.isClosed_topologicalClosure.completeSpace_coe
  obtain ⟨m, hm, hz⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := M) w
  have hzm : w-m ∈ divisorCellSpace d D :=
    (divisorCellSpace d D).sub_mem hw (divisorGradient_closure_le d D hm)
  have hza : ∀ k, divisorGridActive d D k → (w-m) k = (w-m) (k+1) := by
    apply (divisorGradient_orthogonal_iff d D (w-m)).mp
    simpa only [M, Submodule.orthogonal_closure] using hz
  have he := divisorCell_eq_zero_of_adjacent d D (w-m) hzm hza
  rw [sub_eq_zero.mp he]
  exact hm

theorem divisorCell_orthogonal_iff (d : ℕ) (D : Set ℕ) (w : TraceData) :
    w ∈ (divisorCellSpace d D)ᗮ ↔
      ∀ k, divisorGridActive d D k → w k = w (k+1) := by
  rw [← divisorGradient_closure, Submodule.orthogonal_closure]
  exact divisorGradient_orthogonal_iff d D w

theorem divisorCell_orthogonal_component (d : ℕ) (D : Set ℕ)
    (w : (divisorCellSpace d D)ᗮ) (a b : ℕ) (h : DivisorFiniteComponent d D a b)
    (i : ℕ) (hi : a+i < b) : w.1 (a+i) = w.1 a := by
  have ha := (divisorCell_orthogonal_iff d D w.1).mp w.2
  induction i with
  | zero => simp
  | succ i ih =>
      have he := ha (a+i) (h.2.2.2 (a+i) (by omega) (by omega))
      rw [show a+(i+1) = (a+i)+1 by omega, ← he]
      exact ih (by omega)

theorem divisorCell_orthogonal_tail_zero (d : ℕ) (D : Set ℕ)
    (w : (divisorCellSpace d D)ᗮ) (a : ℕ)
    (h : ∀ n, divisorGridActive d D (a+n)) : ∀ n, w.1 (a+n) = 0 := by
  have ha := (divisorCell_orthogonal_iff d D w.1).mp w.2
  have hc (n : ℕ) : w.1 (a+n) = w.1 a := by
    induction n with
    | zero => simp
    | succ n ih => rw [show a+(n+1) = (a+n)+1 by omega, ← ha (a+n) (h n), ih]
  have hz := traceData_tail_constant_zero w.1 a (w.1 a) hc
  intro n
  rw [hc, hz]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
