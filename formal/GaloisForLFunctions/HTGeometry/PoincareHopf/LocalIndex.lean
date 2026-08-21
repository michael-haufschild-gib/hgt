import GaloisForLFunctions.HTGeometry.PoincareHopf.DegreeLinear

/-!
# The index of a vector field at an isolated zero

If `v` has no zero other than `p` on a closed ball around `p`, the degree of `v` on the open ball at
the value `0` is independent of the radius, by excision.  That common value is the index of `v` at
`p`.

At a nondegenerate zero the index is the sign of the determinant of the linearization: the affine
homotopy from `v` to `z ↦ (Dv p) (z - p)` misses `0` on a small sphere, because the linearization is
bounded below there while the remainder is `o` of the radius.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {v : (Fin n → ℝ) → (Fin n → ℝ)} {p : Fin n → ℝ} {ε : ℝ}

/-- `ε` isolates a zero of `v` at `p`. -/
def IsolatingRadius (v : (Fin n → ℝ) → (Fin n → ℝ)) (p : Fin n → ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ x ∈ Metric.closedBall p ε, x ≠ p → v x ≠ 0

theorem IsolatingRadius.mono (h : IsolatingRadius v p ε) {ε' : ℝ} (hpos : 0 < ε')
    (hle : ε' ≤ ε) : IsolatingRadius v p ε' :=
  ⟨hpos, fun x hx hxp => h.2 x (Metric.closedBall_subset_closedBall hle hx) hxp⟩

open scoped Classical in
/-- The index of `v` at an isolated zero `p`. -/
noncomputable def index (v : (Fin n → ℝ) → (Fin n → ℝ)) (p : Fin n → ℝ) : ℝ :=
  if h : ∃ ε, IsolatingRadius v p ε then degree v (Metric.ball p (Classical.choose h)) 0 else 0

theorem degree_ball_eq_of_le (hv : ContDiff ℝ 2 v) (h : IsolatingRadius v p ε)
    {ε' : ℝ} (hpos : 0 < ε') (hle : ε' ≤ ε) :
    degree v (Metric.ball p ε) 0 = degree v (Metric.ball p ε') 0 := by
  refine degree_eq_of_subset hv Metric.isOpen_ball Metric.isBounded_ball Metric.isOpen_ball
    (Metric.ball_subset_ball hle) ?_
  intro x hx
  have hclos : x ∈ Metric.closedBall p ε := Metric.closure_ball_subset_closedBall hx.1
  have hne : x ≠ p := fun hxp => hx.2 (by rw [hxp]; exact Metric.mem_ball_self hpos)
  exact h.2 x hclos hne

/-- The index is the degree on any isolating ball. -/
theorem index_eq_degree (hv : ContDiff ℝ 2 v) (h : IsolatingRadius v p ε) :
    index v p = degree v (Metric.ball p ε) 0 := by
  classical
  have hex : ∃ ε, IsolatingRadius v p ε := ⟨ε, h⟩
  have hch : IsolatingRadius v p (Classical.choose hex) := Classical.choose_spec hex
  have hrpos : 0 < min ε (Classical.choose hex) := lt_min h.1 hch.1
  rw [index, dif_pos hex,
    degree_ball_eq_of_le hv hch hrpos (min_le_right _ _),
    degree_ball_eq_of_le hv h hrpos (min_le_left _ _)]

/-- A continuous linear self-map of `ℝⁿ` acts as its Jacobian matrix. -/
theorem clm_eq_mulVec (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (w : Fin n → ℝ) :
    L w = (Matrix.of fun a b => L (Pi.single b 1) a) *ᵥ w := by
  funext a
  rw [clm_apply_eq_sum L w]
  simp only [Matrix.mulVec, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem fderiv_eq_matVec (v : (Fin n → ℝ) → (Fin n → ℝ)) (x w : Fin n → ℝ) :
    fderiv ℝ v x w = matVec (jac v x) w := by
  rw [matVec_apply]
  exact clm_eq_mulVec (fderiv ℝ v x) w

theorem frontier_ball_norm {x : Fin n → ℝ} (hx : x ∈ frontier (Metric.ball p ε)) :
    ‖x - p‖ = ε := by
  rw [Metric.isOpen_ball.frontier_eq] at hx
  have h1 : dist x p ≤ ε := Metric.closure_ball_subset_closedBall hx.1
  have h2 : ¬ dist x p < ε := fun h => hx.2 (Metric.mem_ball.mpr h)
  rw [← dist_eq_norm]
  linarith [not_lt.mp h2]

/-- An invertible matrix is bounded below, and near a nondegenerate zero the field is dominated by
its linearization. -/
theorem exists_isolating_of_nondegenerate (hv : ContDiff ℝ 2 v) (hp : v p = 0)
    (hdet : (jac v p).det ≠ 0) :
    ∃ c > 0, ∃ ε > 0, IsolatingRadius v p ε ∧
      (∀ w : Fin n → ℝ, c * ‖w‖ ≤ ‖matVec (jac v p) w‖) ∧
      (∀ x ∈ Metric.closedBall p ε,
        ‖v x - matVec (jac v p) (x - p)‖ ≤ c / 2 * ‖x - p‖) := by
  classical
  set A := jac v p with hA
  haveI : Invertible A := A.invertibleOfIsUnitDet (Ne.isUnit hdet)
  set E : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    LinearEquiv.toContinuousLinearEquiv (Matrix.toLinearEquiv' A inferInstance) with hE
  have hEapp : ∀ w : Fin n → ℝ, E w = matVec A w := fun w => rfl
  set M := ‖(E.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ with hM
  have hMnn : 0 ≤ M := norm_nonneg _
  set c := (M + 1)⁻¹ with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hlow : ∀ w : Fin n → ℝ, c * ‖w‖ ≤ ‖matVec A w‖ := by
    intro w
    have h1 : ‖w‖ ≤ M * ‖matVec A w‖ := by
      have h0 := (E.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).le_opNorm (E w)
      have hsym : (E.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (E w) = w := by simp
      rw [hsym, hEapp w] at h0
      rw [hM]
      exact h0
    rw [hc, inv_mul_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (matVec A w)]
  have hdiff : HasFDerivAt v (fderiv ℝ v p) p := (hv.differentiable (by simp) p).hasFDerivAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp (hdiff.isLittleO.def
    (c := c / 2) (by positivity))
  refine ⟨c, hcpos, δ / 2, by linarith, ?_, hlow, ?_⟩
  · refine ⟨by linarith, fun x hx hxp hv0 => ?_⟩
    have hxb : x ∈ Metric.ball p δ := by
      rw [Metric.mem_closedBall] at hx
      rw [Metric.mem_ball]
      linarith
    have h := hδ x hxb
    rw [hp, sub_zero, fderiv_eq_matVec v p (x - p), ← hA, hv0, zero_sub, norm_neg] at h
    have hn : 0 < ‖x - p‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hxp
    have h1 : c * ‖x - p‖ ≤ ‖matVec A (x - p)‖ := hlow _
    nlinarith
  · intro x hx
    have hxb : x ∈ Metric.ball p δ := by
      rw [Metric.mem_closedBall] at hx
      rw [Metric.mem_ball]
      linarith
    have h := hδ x hxb
    rw [hp, sub_zero, fderiv_eq_matVec v p (x - p), ← hA] at h
    exact h

/-- **The index at a nondegenerate zero is the sign of the determinant of the linearization.** -/
theorem index_eq_sign_det (hv : ContDiff ℝ 2 v) (hp : v p = 0) (hdet : (jac v p).det ≠ 0) :
    index v p = if 0 < (jac v p).det then 1 else -1 := by
  classical
  obtain ⟨c, hcpos, ε, hεpos, hisol, hlow, hest⟩ :=
    exists_isolating_of_nondegenerate hv hp hdet
  set A := jac v p with hA
  set L : (Fin n → ℝ) → (Fin n → ℝ) := fun z => matVec A (z - p) with hL
  have hLcd : ContDiff ℝ 2 L := (matVec A).contDiff.comp (contDiff_id.sub contDiff_const)
  set ρ := c * ε / 6 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hfront : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier (Metric.ball p ε),
      ρ + ρ < ‖linPath v L t x - 0‖ := by
    intro t ht x hx
    have hnx : ‖x - p‖ = ε := frontier_ball_norm hx
    have h1 : c * ε ≤ ‖matVec A (x - p)‖ := by rw [← hnx]; exact hlow _
    have hxb : x ∈ Metric.closedBall p ε := by
      rw [Metric.mem_closedBall, dist_eq_norm, hnx]
    have h2 : ‖v x - matVec A (x - p)‖ ≤ c / 2 * ε := by
      have h := hest x hxb
      rwa [hnx] at h
    have hrepr : linPath v L t x = matVec A (x - p) + (1 - t) • (v x - matVec A (x - p)) := by
      simp only [linPath, hL]
      module
    have h3 : ‖(1 - t) • (v x - matVec A (x - p))‖ ≤ c / 2 * ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      nlinarith [norm_nonneg (v x - matVec A (x - p)), ht.1, ht.2]
    have h5 : ‖matVec A (x - p)‖
        ≤ ‖matVec A (x - p) + (1 - t) • (v x - matVec A (x - p))‖
          + ‖(1 - t) • (v x - matVec A (x - p))‖ := by
      have h := norm_sub_le (matVec A (x - p) + (1 - t) • (v x - matVec A (x - p)))
        ((1 - t) • (v x - matVec A (x - p)))
      simpa using h
    rw [sub_zero, hrepr, hρ]
    nlinarith
  have hdeg : degree v (Metric.ball p ε) 0 = degree L (Metric.ball p ε) 0 :=
    degree_eq_of_linPath hv hLcd Metric.isOpen_ball Metric.isBounded_ball hρpos hfront
  rw [index_eq_degree hv hisol, hdeg, hL]
  exact degree_matVec_affine A hdet p Metric.isOpen_ball Metric.isBounded_ball
    (Metric.mem_ball_self hεpos)

end GaloisForLFunctions.HTGeometry.PoincareHopf
