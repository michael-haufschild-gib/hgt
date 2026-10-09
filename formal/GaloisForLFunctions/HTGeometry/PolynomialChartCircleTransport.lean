import GaloisForLFunctions.HTGeometry.PolynomialRootLoopTransport
import GaloisForLFunctions.HTGeometry.CircleRootPaths

open Polynomial Set Topology Metric
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- A quadratic power chart gives two explicitly exchanged sheets of the actual circle transport. -/
theorem quadratic_chart_circle_exchange {n : ℕ} (v : Parameter n) (c : ℂ)
    (e : OpenPartialHomeomorph ℂ ℂ) (r : ℝ) (hr : 0 < r)
    (hinside : closedBall (0 : ℂ) r ⊆ e.target)
    (hpow : ∀ z ∈ e.source, (additivePolynomial v).eval z = c + (e z) ^ 2)
    (havoid : ∀ t j, positiveCirclePath c (r ^ 2) t ≠ valuesWithConstant v j) :
    ∃ x y : RootFiber v (c + (r ^ 2 : ℝ)), x ≠ y ∧
      rootLoopTransport v (positiveCirclePath c (r ^ 2)) havoid x = y ∧
      rootLoopTransport v (positiveCirclePath c (r ^ 2)) havoid y = x ∧
      ∀ z : RootFiber v (c + (r ^ 2 : ℝ)), (z : ℂ) ∈ e.source → z = x ∨ z = y := by
  have hp : ∀ t : I, quadraticRootHalfCircle r t ∈ e.target := by
    intro t
    apply hinside
    simp only [mem_closedBall, dist_zero_right, norm_quadraticRootHalfCircle, abs_of_pos hr]
    exact le_rfl
  have hm : ∀ t : I, -(quadraticRootHalfCircle r t) ∈ e.target := by
    intro t
    apply hinside
    simp only [mem_closedBall, dist_zero_right, norm_neg, norm_quadraticRootHalfCircle,
      abs_of_pos hr]
    exact le_rfl
  let up : C(I, ℂ) := ⟨fun t => e.symm (quadraticRootHalfCircle r t),
    e.continuousOn_symm.comp_continuous (quadraticRootHalfCircle r).continuous hp⟩
  let um : C(I, ℂ) := ⟨fun t => e.symm (-(quadraticRootHalfCircle r t)),
    e.continuousOn_symm.comp_continuous (quadraticRootHalfCircle r).continuous.neg hm⟩
  have hup : ∀ t, (additivePolynomial v).eval (up t) = positiveCirclePath c (r ^ 2) t := by
    intro t
    change (additivePolynomial v).eval (e.symm (quadraticRootHalfCircle r t)) = _
    rw [hpow _ (e.map_target (hp t)), e.right_inv (hp t), quadraticRootHalfCircle_sq]
    simp only [positiveCirclePath_apply, circleMap, zero_add]
  have hum : ∀ t, (additivePolynomial v).eval (um t) = positiveCirclePath c (r ^ 2) t := by
    intro t
    change (additivePolynomial v).eval (e.symm (-(quadraticRootHalfCircle r t))) = _
    rw [hpow _ (e.map_target (hm t)), e.right_inv (hm t), neg_sq, quadraticRootHalfCircle_sq]
    simp only [positiveCirclePath_apply, circleMap, zero_add]
  let x : RootFiber v (c + (r ^ 2 : ℝ)) :=
    ⟨up 0, (hup 0).trans (positiveCirclePath c (r ^ 2)).source⟩
  let y : RootFiber v (c + (r ^ 2 : ℝ)) :=
    ⟨um 0, (hum 0).trans (positiveCirclePath c (r ^ 2)).source⟩
  have hxp : e (up 0) = (r : ℂ) := by
    change e (e.symm (quadraticRootHalfCircle r 0)) = _
    rw [e.right_inv (hp 0), quadraticRootHalfCircle_zero]
  have hym : e (um 0) = -(r : ℂ) := by
    change e (e.symm (-(quadraticRootHalfCircle r 0))) = _
    rw [e.right_inv (hm 0), quadraticRootHalfCircle_zero]
  have hxy : x ≠ y := by
    intro heq
    have he : (r : ℂ) = -(r : ℂ) :=
      hxp.symm.trans ((congrArg e (congrArg Subtype.val heq)).trans hym)
    have hre := congrArg Complex.re he
    simp only [Complex.neg_re, Complex.ofReal_re] at hre
    linarith
  refine ⟨x, y, hxy, ?_, ?_, ?_⟩
  · apply Subtype.ext
    have h := rootLoopTransport_val_eq_of_section v (positiveCirclePath c (r ^ 2)) havoid x up rfl hup
    simpa only [y, um, up, ContinuousMap.coe_mk, quadraticRootHalfCircle_one,
      quadraticRootHalfCircle_zero] using h
  · apply Subtype.ext
    have h := rootLoopTransport_val_eq_of_section v (positiveCirclePath c (r ^ 2)) havoid y um rfl hum
    simpa only [x, um, up, ContinuousMap.coe_mk, quadraticRootHalfCircle_one,
      quadraticRootHalfCircle_zero, neg_neg] using h
  · intro z hz
    have hs : (e z) ^ 2 = (r : ℂ) ^ 2 := by
      apply add_left_cancel (a := c)
      simpa only [Complex.ofReal_pow] using (hpow z hz).symm.trans z.property
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
    · left
      apply Subtype.ext
      change (z : ℂ) = up 0
      calc
        (z : ℂ) = e.symm (e z) := (e.left_inv hz).symm
        _ = e.symm (r : ℂ) := congrArg e.symm hs
        _ = up 0 := by simp [up]
    · right
      apply Subtype.ext
      change (z : ℂ) = um 0
      calc
        (z : ℂ) = e.symm (e z) := (e.left_inv hz).symm
        _ = e.symm (-(r : ℂ)) := congrArg e.symm hs
        _ = um 0 := by simp [um]

/-- A linear power chart gives a closed lift, hence a fixed actual sheet. -/
theorem linear_chart_circle_fixed {n : ℕ} (v : Parameter n) (c : ℂ)
    (e : OpenPartialHomeomorph ℂ ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hinside : closedBall (0 : ℂ) R ⊆ e.target)
    (hpow : ∀ z ∈ e.source, (additivePolynomial v).eval z = c + e z)
    (havoid : ∀ t j, positiveCirclePath c R t ≠ valuesWithConstant v j)
    (z : RootFiber v (c + R)) (hz : (z : ℂ) ∈ e.source) :
    rootLoopTransport v (positiveCirclePath c R) havoid z = z := by
  have ht : ∀ t : I, positiveCirclePath 0 R t ∈ e.target := by
    intro t
    apply hinside
    exact circleMap_mem_closedBall _ hR _
  let u : C(I, ℂ) := ⟨fun t => e.symm (positiveCirclePath 0 R t),
    e.continuousOn_symm.comp_continuous (positiveCirclePath 0 R).continuous ht⟩
  have hu : ∀ t, (additivePolynomial v).eval (u t) = positiveCirclePath c R t := by
    intro t
    change (additivePolynomial v).eval (e.symm (positiveCirclePath 0 R t)) = _
    rw [hpow _ (e.map_target (ht t)), e.right_inv (ht t)]
    simp only [positiveCirclePath_apply, circleMap, zero_add]
  have hez : e z = (R : ℂ) := add_left_cancel ((hpow z hz).symm.trans z.property)
  have hu0 : u 0 = z := by
    change e.symm (positiveCirclePath 0 R 0) = z
    rw [(positiveCirclePath 0 R).source, zero_add]
    exact (congrArg e.symm hez.symm).trans (e.left_inv hz)
  have hu1 : u 1 = z := by
    change e.symm (positiveCirclePath 0 R 1) = z
    rw [(positiveCirclePath 0 R).target, zero_add]
    exact (congrArg e.symm hez.symm).trans (e.left_inv hz)
  apply Subtype.ext
  exact (rootLoopTransport_val_eq_of_section v (positiveCirclePath c R) havoid z u hu0 hu).trans hu1

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
