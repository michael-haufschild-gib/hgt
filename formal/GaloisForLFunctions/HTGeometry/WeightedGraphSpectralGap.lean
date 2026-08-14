import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The spectral gap of a finite weighted graph

Garland's vanishing method runs on the spectral gap of the links of a simplicial complex, and a link
enters the argument only through its one-skeleton with the weights inherited from the complex.  This
file sets up that one-skeleton: a finite weighted graph, its vertex masses, the mass inner product,
the Dirichlet form, and the statement that a real number is a spectral gap for it.

The gap is carried as a property of a real number rather than as an infimum, because that is the
form Garland's inequality consumes and it needs no compactness.

* `WeightedGraph` : a finite symmetric nonnegative weight with no loops.
* `mass`, `massInner`, `dirichlet` : the vertex masses, the mass inner product, the Dirichlet form.
* `dirichlet_self_eq` : **the Dirichlet form is the mass norm minus the averaging form.**
* `HasSpectralGap`, `spectralGap_apply` : **a spectral gap bounds the deviation from the mass
  average.**
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A finite weighted graph**: a symmetric nonnegative weight with no loops. -/
structure WeightedGraph (V : Type*) where
  /-- the weight of an edge -/
  w : V → V → ℝ
  /-- the weight is symmetric -/
  w_symm : ∀ u v, w u v = w v u
  /-- the weight is nonnegative -/
  w_nonneg : ∀ u v, 0 ≤ w u v
  /-- there are no loops -/
  w_diag : ∀ v, w v v = 0

namespace WeightedGraph

variable {V : Type*} [Fintype V] (G : WeightedGraph V)

/-- The mass of a vertex: the total weight of the edges at it. -/
def mass (v : V) : ℝ := ∑ u, G.w v u

theorem mass_nonneg (v : V) : 0 ≤ G.mass v :=
  Finset.sum_nonneg fun u _ => G.w_nonneg v u

/-- The total mass of the graph. -/
def totalMass : ℝ := ∑ v, G.mass v

theorem totalMass_nonneg : 0 ≤ G.totalMass :=
  Finset.sum_nonneg fun v _ => G.mass_nonneg v

/-- The inner product on functions weighted by the vertex masses. -/
def massInner (f g : V → ℝ) : ℝ := ∑ v, G.mass v * (f v * g v)

theorem massInner_self_nonneg (f : V → ℝ) : 0 ≤ G.massInner f f :=
  Finset.sum_nonneg fun v _ => mul_nonneg (G.mass_nonneg v) (mul_self_nonneg _)

/-- The Dirichlet form of the graph. -/
noncomputable def dirichlet (f g : V → ℝ) : ℝ :=
  (∑ v, ∑ u, G.w v u * ((f v - f u) * (g v - g u))) / 2

theorem dirichlet_self_nonneg (f : V → ℝ) : 0 ≤ G.dirichlet f f := by
  refine div_nonneg (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun u _ => ?_) (by norm_num)
  exact mul_nonneg (G.w_nonneg v u) (mul_self_nonneg _)

theorem dirichlet_sub_const (f : V → ℝ) (c : ℝ) :
    G.dirichlet (fun v => f v - c) (fun v => f v - c) = G.dirichlet f f := by
  refine congrArg (· / 2) (Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_)
  ring_nf

theorem sum_sum_w_mul_left (h : V → ℝ) :
    (∑ v, ∑ u, G.w v u * h v) = ∑ v, G.mass v * h v :=
  Finset.sum_congr rfl fun _ _ => (Finset.sum_mul _ _ _).symm

theorem sum_sum_w_mul_right (h : V → ℝ) :
    (∑ v, ∑ u, G.w v u * h u) = ∑ v, G.mass v * h v := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_mul]
  exact congrArg (· * h u) (Finset.sum_congr rfl fun v _ => G.w_symm v u)

/-- **The Dirichlet form as mass norm minus averaging.** -/
theorem dirichlet_self_eq (f : V → ℝ) :
    G.dirichlet f f = G.massInner f f - ∑ v, ∑ u, G.w v u * (f v * f u) := by
  have h1 : (∑ v, ∑ u, G.w v u * ((f v - f u) * (f v - f u)))
      = (∑ v, ∑ u, (G.w v u * (f v * f v) + G.w v u * (f u * f u)
          - 2 * (G.w v u * (f v * f u)))) :=
    Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by ring
  have h2 : ∀ F₁ F₂ F₃ : V → V → ℝ,
      (∑ v, ∑ u, (F₁ v u + F₂ v u - 2 * F₃ v u))
        = (∑ v, ∑ u, F₁ v u) + (∑ v, ∑ u, F₂ v u) - 2 * ∑ v, ∑ u, F₃ v u := by
    intro F₁ F₂ F₃
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [dirichlet, h1, h2, G.sum_sum_w_mul_left (fun v => f v * f v),
    G.sum_sum_w_mul_right (fun v => f v * f v)]
  show (G.massInner f f + G.massInner f f - 2 * ∑ v, ∑ u, G.w v u * (f v * f u)) / 2 = _
  ring

/-- The mass average of a function. -/
noncomputable def mean (f : V → ℝ) : ℝ := (∑ v, G.mass v * f v) / G.totalMass

theorem sum_mass_sub_mean (f : V → ℝ) (htot : G.totalMass ≠ 0) :
    (∑ v, G.mass v * (f v - G.mean f)) = 0 := by
  have h : (∑ v, G.mass v * (f v - G.mean f))
      = (∑ v, G.mass v * f v) - G.mean f * G.totalMass := by
    rw [totalMass, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [h, mean, div_mul_cancel₀ _ htot, sub_self]

/-- **A spectral gap for the graph**: `lam` bounds the Rayleigh quotient from below on functions of
mass average zero. -/
def HasSpectralGap (lam : ℝ) : Prop :=
  ∀ f : V → ℝ, (∑ v, G.mass v * f v) = 0 → lam * G.massInner f f ≤ G.dirichlet f f

/-- **The spectral gap controls the deviation from the mean**: the Dirichlet form of any function
dominates `lam` times the mass norm of its deviation from its mass average. -/
theorem spectralGap_apply {lam : ℝ} (h : G.HasSpectralGap lam) (htot : G.totalMass ≠ 0)
    (f : V → ℝ) :
    lam * G.massInner (fun v => f v - G.mean f) (fun v => f v - G.mean f)
      ≤ G.dirichlet f f := by
  have hmean := h (fun v => f v - G.mean f) (G.sum_mass_sub_mean f htot)
  rwa [G.dirichlet_sub_const f (G.mean f)] at hmean

/-- **A bound on the averaging form gives a spectral gap.**  Since the Dirichlet form is the mass
norm minus the averaging form, a bound `⟨Af, f⟩ ≤ θ‖f‖²` on functions of mass average zero is
exactly the spectral gap `1 - θ`. -/
theorem hasSpectralGap_of_bound (θ : ℝ)
    (h : ∀ f : V → ℝ, (∑ v, G.mass v * f v) = 0 →
      (∑ v, ∑ u, G.w v u * (f v * f u)) ≤ θ * G.massInner f f) :
    G.HasSpectralGap (1 - θ) := by
  intro f hf
  rw [G.dirichlet_self_eq f]
  have hb := h f hf
  have hexp : (1 - θ) * G.massInner f f
      = G.massInner f f - θ * G.massInner f f := by ring
  rw [hexp]
  linarith

/-- The averaging form of a weighted graph. -/
def averaging (f g : V → ℝ) : ℝ := ∑ v, ∑ u, G.w v u * (f v * g u)

theorem dirichlet_self_eq_sub (f : V → ℝ) :
    G.dirichlet f f = G.massInner f f - G.averaging f f := G.dirichlet_self_eq f


end WeightedGraph

end GaloisForLFunctions.HTGeometry
