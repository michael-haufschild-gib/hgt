import GaloisForLFunctions.HTGeometry.PolydiscCauchyFormula

/-!
# The Cauchy integral formula on a polydisc, locally

The Cauchy integral formula on a polydisc needs the function only on the polydisc, not on the whole
space: a function holomorphic on `polydiscSet c R` is reproduced by the product Cauchy kernel over
the distinguished boundary of every strictly smaller polydisc.  The induction is the one for entire
functions — the torus integral becomes an iterated circle integral, the remaining kernel factors out
of the innermost one, and the one-variable Cauchy formula finishes the step — carried out with the
domain hypotheses tracked: the distinguished boundary of the smaller polydisc lies inside the
larger, so every slice is holomorphic on a neighbourhood of the closed disc it is integrated over.

* `GaloisForLFunctions.HTGeometry.polydiscSet` : the open polydisc as a set.
* `GaloisForLFunctions.HTGeometry.polydiscCauchyFormula_of_differentiableOn` : the formula.
-/

open MeasureTheory Complex Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

section PolydiscSet

variable {n : ℕ}

/-- The open polydisc as a set. -/
def polydiscSet (c : Fin n → ℂ) (R : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ i, z i ∈ Metric.ball (c i) (R i)}

theorem mem_polydiscSet {c : Fin n → ℂ} {R : Fin n → ℝ} {z : Fin n → ℂ} :
    z ∈ polydiscSet c R ↔ ∀ i, z i ∈ Metric.ball (c i) (R i) := Iff.rfl

theorem isOpen_polydiscSet (c : Fin n → ℂ) (R : Fin n → ℝ) : IsOpen (polydiscSet c R) := by
  have h : polydiscSet c R =
      ⋂ i : Fin n, (fun z : Fin n → ℂ => z i) ⁻¹' Metric.ball (c i) (R i) := by
    ext z
    simp [polydiscSet, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun i => Metric.isOpen_ball.preimage (continuous_apply i)

/-- The distinguished boundary of a smaller polydisc lies inside the larger one. -/
theorem torusMap_mem_polydiscSet {c : Fin n → ℂ} {R R' : Fin n → ℝ}
    (hR' : ∀ i, 0 ≤ R' i) (hlt : ∀ i, R' i < R i) (θ : Fin n → ℝ) :
    torusMap c R' θ ∈ polydiscSet c R := by
  intro i
  have h : ‖torusMap c R' θ i - c i‖ = |R' i| := by simp [torusMap]
  refine Metric.mem_ball.mpr ?_
  rw [Complex.dist_eq, h, abs_of_nonneg (hR' i)]
  exact hlt i

end PolydiscSet

section Cons

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Prepending a variable first coordinate to a fixed tail is holomorphic. -/
theorem differentiable_consMapLeft (y : Fin m → ℂ) :
    Differentiable ℂ (fun x : ℂ => (Fin.cons x y : Fin (m + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simp only [Fin.cons_zero]
    exact differentiable_id
  · intro j
    simp only [Fin.cons_succ]
    exact differentiable_const (y j)

/-- Prepending a fixed first coordinate to a variable tail is holomorphic. -/
theorem differentiable_consMapRight (x : ℂ) :
    Differentiable ℂ (fun y : Fin m → ℂ => (Fin.cons x y : Fin (m + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simp only [Fin.cons_zero]
    exact differentiable_const x
  · intro j
    simp only [Fin.cons_succ]
    exact (differentiable_pi.1 differentiable_id) j

/-- Prepending a first coordinate of the right size lands in the polydisc. -/
theorem cons_mem_polydiscSet {c : Fin (m + 1) → ℂ} {R : Fin (m + 1) → ℝ} {x : ℂ}
    (hx : x ∈ Metric.ball (c 0) (R 0)) {y : Fin m → ℂ}
    (hy : y ∈ polydiscSet (c ∘ Fin.succ) (R ∘ Fin.succ)) :
    (Fin.cons x y : Fin (m + 1) → ℂ) ∈ polydiscSet c R := by
  intro i
  refine Fin.cases ?_ ?_ i
  · rwa [Fin.cons_zero]
  · intro j
    rw [Fin.cons_succ]
    exact hy j

/-- Fixing the first coordinate inside its disc leaves a function holomorphic on the tail
polydisc. -/
theorem differentiableOn_cons_right {f : (Fin (m + 1) → ℂ) → E} {c : Fin (m + 1) → ℂ}
    {R : Fin (m + 1) → ℝ} (hf : DifferentiableOn ℂ f (polydiscSet c R)) {x : ℂ}
    (hx : x ∈ Metric.ball (c 0) (R 0)) :
    DifferentiableOn ℂ (fun y : Fin m → ℂ => f (Fin.cons x y))
      (polydiscSet (c ∘ Fin.succ) (R ∘ Fin.succ)) :=
  hf.comp (differentiable_consMapRight x).differentiableOn fun _ hy => cons_mem_polydiscSet hx hy

/-- Fixing the tail inside its polydisc leaves a function holomorphic on the first disc. -/
theorem differentiableOn_cons_left {f : (Fin (m + 1) → ℂ) → E} {c : Fin (m + 1) → ℂ}
    {R : Fin (m + 1) → ℝ} (hf : DifferentiableOn ℂ f (polydiscSet c R)) {y : Fin m → ℂ}
    (hy : y ∈ polydiscSet (c ∘ Fin.succ) (R ∘ Fin.succ)) :
    DifferentiableOn ℂ (fun x : ℂ => f (Fin.cons x y)) (Metric.ball (c 0) (R 0)) :=
  hf.comp (differentiable_consMapLeft y).differentiableOn fun _ hx => cons_mem_polydiscSet hx hy

end Cons

section LocalFormula

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **The Cauchy integral formula on a polydisc, from holomorphy on that polydisc alone.**  A
function holomorphic on `polydiscSet c R` is reproduced by the product Cauchy kernel over the
distinguished boundary of every strictly smaller polydisc. -/
theorem polydiscCauchyFormula_of_differentiableOn :
    ∀ (n : ℕ) (f : (Fin n → ℂ) → E) (c : Fin n → ℂ) (R R' : Fin n → ℝ),
      DifferentiableOn ℂ f (polydiscSet c R) → (∀ i, 0 ≤ R' i) → (∀ i, R' i < R i) →
      ∀ z : Fin n → ℂ, (∀ i, z i ∈ Metric.ball (c i) (R' i)) →
        (∯ ζ in T(c, R'), (∏ i, (ζ i - z i)⁻¹) • f ζ) =
          ((2 * Real.pi * Complex.I) ^ n : ℂ) • f z := by
  intro n
  induction n with
  | zero =>
      intro f c _ _ _ _ _ z _
      rw [torusIntegral_dim0]
      have hcz : c = z := Subsingleton.elim c z
      rw [hcz]
      simp
  | succ m ih =>
      intro f c R R' hf hR'0 hlt z hz
      have hne : ∀ (θ : Fin (m + 1) → ℝ) (i : Fin (m + 1)),
          torusMap c R' θ i - z i ≠ 0 :=
        torusMap_sub_ne_zero hz
      have hmap : Continuous fun θ : Fin (m + 1) → ℝ => torusMap c R' θ :=
        continuous_torusMap c R'
      have hfcont : Continuous fun θ : Fin (m + 1) → ℝ => f (torusMap c R' θ) :=
        hf.continuousOn.comp_continuous hmap (torusMap_mem_polydiscSet hR'0 hlt)
      have hcontint : Continuous fun θ : Fin (m + 1) → ℝ =>
          (∏ i, (torusMap c R' θ i - z i)⁻¹) • f (torusMap c R' θ) := by
        refine Continuous.smul ?_ hfcont
        refine continuous_finsetProd _ fun i _ => ?_
        exact (((continuous_apply i).comp hmap).sub continuous_const).inv₀ fun θ => hne θ i
      have hint : TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) • f ζ) c R' :=
        torusIntegrable_of_continuous hcontint
      have hz' : ∀ i : Fin m, (z ∘ Fin.succ) i ∈
          Metric.ball ((c ∘ Fin.succ) i) ((R' ∘ Fin.succ) i) := fun i => hz i.succ
      have hzsub : (z ∘ Fin.succ) ∈ polydiscSet (c ∘ Fin.succ) (R ∘ Fin.succ) := fun i =>
        Metric.ball_subset_ball (le_of_lt (hlt i.succ)) (hz i.succ)
      have hz0 : z 0 ∈ Metric.ball (c 0) (R 0) :=
        Metric.ball_subset_ball (le_of_lt (hlt 0)) (hz 0)
      have hinner : ∀ x ∈ Metric.sphere (c 0) (R' 0),
          (∯ y in T(c ∘ Fin.succ, R' ∘ Fin.succ),
              (∏ i, ((Fin.cons x y : Fin (m + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y)) =
            (x - z 0)⁻¹ •
              (((2 * Real.pi * Complex.I) ^ m : ℂ) • f (Fin.cons x (z ∘ Fin.succ))) := by
        intro x hx
        have hxball : x ∈ Metric.ball (c 0) (R 0) := by
          rw [Metric.mem_sphere] at hx
          exact Metric.mem_ball.mpr (by rw [hx]; exact hlt 0)
        have hfun : (fun y : Fin m → ℂ =>
              (∏ i, ((Fin.cons x y : Fin (m + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y)) =
            fun y : Fin m → ℂ => (x - z 0)⁻¹ •
              ((∏ i : Fin m, (y i - (z ∘ Fin.succ) i)⁻¹) • f (Fin.cons x y)) := by
          funext y
          rw [Fin.prod_univ_succ, Fin.cons_zero, mul_smul]
          congr 2
        rw [hfun, torusIntegral_smul,
          ih (fun y : Fin m → ℂ => f (Fin.cons x y)) (c ∘ Fin.succ) (R ∘ Fin.succ) (R' ∘ Fin.succ)
            (differentiableOn_cons_right hf hxball) (fun i => hR'0 i.succ)
            (fun i => hlt i.succ) (z ∘ Fin.succ) hz']
      rw [torusIntegral_succ hint]
      rw [circleIntegral.integral_congr (hR'0 0) hinner]
      have hswap : ∀ x : ℂ, (x - z 0)⁻¹ •
          (((2 * Real.pi * Complex.I) ^ m : ℂ) • f (Fin.cons x (z ∘ Fin.succ))) =
          ((2 * Real.pi * Complex.I) ^ m : ℂ) •
            ((x - z 0)⁻¹ • f (Fin.cons x (z ∘ Fin.succ))) := fun x => smul_comm _ _ _
      simp only [hswap]
      have hslice : DiffContOnCl ℂ (fun x : ℂ => f (Fin.cons x (z ∘ Fin.succ)))
          (Metric.ball (c 0) (R' 0)) := by
        refine DifferentiableOn.diffContOnCl ?_
        refine (differentiableOn_cons_left hf hzsub).mono ?_
        exact Metric.closure_ball_subset_closedBall.trans
          (Metric.closedBall_subset_ball (hlt 0))
      rw [circleIntegral.integral_smul,
        DiffContOnCl.circleIntegral_sub_inv_smul hslice (hz 0)]
      have hcons : (Fin.cons (z 0) (z ∘ Fin.succ) : Fin (m + 1) → ℂ) = z := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rw [Fin.cons_zero]
        · intro j
          rw [Fin.cons_succ]
          rfl
      rw [hcons, smul_smul, ← pow_succ]

end LocalFormula

end GaloisForLFunctions.HTGeometry
