import Mathlib.MeasureTheory.Integral.TorusIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Cauchy integral formula on a polydisc

A holomorphic function of several complex variables is reproduced on a polydisc by the integral of
its values on the distinguished boundary against the product Cauchy kernel.  The formula follows
from the one-variable formula applied in each coordinate in turn, through the recurrence that writes
an integral over a torus as an iterated circle integral.

* `torusIntegrable_of_continuous` : a continuous integrand is torus integrable.
* `polydiscCauchyFormula` : the Cauchy integral formula on a polydisc.
-/

open MeasureTheory Complex Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

section TorusIntegrable

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- A continuous integrand is integrable over a torus. -/
theorem torusIntegrable_of_continuous {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : Continuous fun θ : Fin n → ℝ => f (torusMap c R θ)) : TorusIntegrable f c R :=
  (hf.continuousOn).integrableOn_compact isCompact_Icc

/-- The points of a torus of radius `R` avoid every point of the open polydisc of radius `R`. -/
theorem torusMap_sub_ne_zero {c : Fin n → ℂ} {R : Fin n → ℝ} {z : Fin n → ℂ}
    (hz : ∀ i, z i ∈ Metric.ball (c i) (R i)) (θ : Fin n → ℝ) (i : Fin n) :
    torusMap c R θ i - z i ≠ 0 := by
  have hdist : dist (torusMap c R θ i) (c i) = |R i| :=
    Metric.mem_sphere.1 (circleMap_mem_sphere' (c i) (R i) (θ i))
  have hz' : dist (z i) (c i) < R i := Metric.mem_ball.1 (hz i)
  intro h
  have heq : torusMap c R θ i = z i := sub_eq_zero.1 h
  rw [heq] at hdist
  rw [hdist] at hz'
  exact absurd hz' (not_lt.2 (le_abs_self _))

/-- The parametrisation of a torus is continuous. -/
theorem continuous_torusMap (c : Fin n → ℂ) (R : Fin n → ℝ) :
    Continuous fun θ : Fin n → ℝ => torusMap c R θ := by
  refine continuous_pi fun i => ?_
  show Continuous fun θ : Fin n → ℝ => circleMap (c i) (R i) (θ i)
  exact (continuous_circleMap _ _).comp (continuous_apply i)

end TorusIntegrable

section ConsDifferentiable

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Prepending a fixed tail to a variable first coordinate is differentiable. -/
theorem differentiable_cons_left {f : (Fin (m + 1) → ℂ) → E} (hf : Differentiable ℂ f)
    (y : Fin m → ℂ) : Differentiable ℂ fun x : ℂ => f (Fin.cons x y) := by
  refine hf.comp ?_
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ ?_ i
  · show Differentiable ℂ fun x : ℂ => (Fin.cons x y : Fin (m + 1) → ℂ) 0
    simp only [Fin.cons_zero]
    exact differentiable_id
  · intro j
    show Differentiable ℂ fun x : ℂ => (Fin.cons x y : Fin (m + 1) → ℂ) j.succ
    simp only [Fin.cons_succ]
    exact differentiable_const _

/-- Prepending a fixed first coordinate to a variable tail is differentiable. -/
theorem differentiable_cons_right {f : (Fin (m + 1) → ℂ) → E} (hf : Differentiable ℂ f) (x : ℂ) :
    Differentiable ℂ fun y : Fin m → ℂ => f (Fin.cons x y) := by
  refine hf.comp ?_
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ ?_ i
  · show Differentiable ℂ fun y : Fin m → ℂ => (Fin.cons x y : Fin (m + 1) → ℂ) 0
    simp only [Fin.cons_zero]
    exact differentiable_const _
  · intro j
    show Differentiable ℂ fun y : Fin m → ℂ => (Fin.cons x y : Fin (m + 1) → ℂ) j.succ
    simp only [Fin.cons_succ]
    exact (differentiable_pi.1 differentiable_id) j

end ConsDifferentiable

section CauchyFormula

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **The Cauchy integral formula on a polydisc.**  An entire function of several complex variables
is the integral of its values on the distinguished boundary of a polydisc against the product Cauchy
kernel.  The proof peels off one coordinate at a time: the recurrence for the torus integral turns
the outermost variable into a circle integral, the remaining kernel factors out, and the one-variable
Cauchy formula finishes each step. -/
theorem polydiscCauchyFormula : ∀ (n : ℕ) (f : (Fin n → ℂ) → E), Differentiable ℂ f →
    ∀ (c : Fin n → ℂ) (R : Fin n → ℝ) (z : Fin n → ℂ),
      (∀ i, z i ∈ Metric.ball (c i) (R i)) →
      (∯ ζ in T(c, R), (∏ i, (ζ i - z i)⁻¹) • f ζ) =
        ((2 * Real.pi * Complex.I) ^ n : ℂ) • f z := by
  intro n
  induction n with
  | zero =>
      intro f _ c _ z _
      rw [torusIntegral_dim0]
      have hcz : c = z := Subsingleton.elim c z
      rw [hcz]
      simp
  | succ m ih =>
      intro f hf c R z hz
      have hne : ∀ (θ : Fin (m + 1) → ℝ) (i : Fin (m + 1)), torusMap c R θ i - z i ≠ 0 :=
        torusMap_sub_ne_zero hz
      have hmap : Continuous fun θ : Fin (m + 1) → ℝ => torusMap c R θ := continuous_torusMap c R
      have hcontint : Continuous fun θ : Fin (m + 1) → ℝ =>
          (∏ i, (torusMap c R θ i - z i)⁻¹) • f (torusMap c R θ) := by
        refine Continuous.smul ?_ (hf.continuous.comp hmap)
        refine continuous_finsetProd _ fun i _ => ?_
        exact (((continuous_apply i).comp hmap).sub continuous_const).inv₀ fun θ => hne θ i
      have hint : TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) • f ζ) c R :=
        torusIntegrable_of_continuous hcontint
      have hz' : ∀ i : Fin m, (z ∘ Fin.succ) i ∈
          Metric.ball ((c ∘ Fin.succ) i) ((R ∘ Fin.succ) i) := fun i => hz i.succ
      -- the inner integral, for every value of the outer variable
      have hinner : ∀ x : ℂ,
          (∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
              (∏ i, ((Fin.cons x y : Fin (m + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y)) =
            (x - z 0)⁻¹ •
              (((2 * Real.pi * Complex.I) ^ m : ℂ) • f (Fin.cons x (z ∘ Fin.succ))) := by
        intro x
        have hfun : (fun y : Fin m → ℂ =>
              (∏ i, ((Fin.cons x y : Fin (m + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y)) =
            fun y : Fin m → ℂ => (x - z 0)⁻¹ •
              ((∏ i : Fin m, (y i - (z ∘ Fin.succ) i)⁻¹) • f (Fin.cons x y)) := by
          funext y
          rw [Fin.prod_univ_succ, Fin.cons_zero, mul_smul]
          congr 2
        rw [hfun, torusIntegral_smul,
          ih (fun y : Fin m → ℂ => f (Fin.cons x y)) (differentiable_cons_right hf x)
            (c ∘ Fin.succ) (R ∘ Fin.succ) (z ∘ Fin.succ) hz']
      rw [torusIntegral_succ hint]
      simp only [hinner]
      have hswap : ∀ x : ℂ, (x - z 0)⁻¹ •
          (((2 * Real.pi * Complex.I) ^ m : ℂ) • f (Fin.cons x (z ∘ Fin.succ))) =
          ((2 * Real.pi * Complex.I) ^ m : ℂ) •
            ((x - z 0)⁻¹ • f (Fin.cons x (z ∘ Fin.succ))) := fun x => smul_comm _ _ _
      simp only [hswap]
      rw [circleIntegral.integral_smul,
        DiffContOnCl.circleIntegral_sub_inv_smul
          (differentiable_cons_left hf (z ∘ Fin.succ)).diffContOnCl (hz 0)]
      have hcons : (Fin.cons (z 0) (z ∘ Fin.succ) : Fin (m + 1) → ℂ) = z := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rw [Fin.cons_zero]
        · intro j
          rw [Fin.cons_succ]
          rfl
      rw [hcons, smul_smul, ← pow_succ]

end CauchyFormula

end GaloisForLFunctions.HTGeometry
