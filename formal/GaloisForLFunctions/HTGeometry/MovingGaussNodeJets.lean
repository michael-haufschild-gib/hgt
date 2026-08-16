import GaloisForLFunctions.HTGeometry.MovingGaussNodes
import GaloisForLFunctions.HTGeometry.DefectLadderJet

/-!
# The contact jet of a moving Gauss node

The moment flow `∂_y s k = -(k+1) s (k+1)` moves a Gauss quadrature by the exact node and weight
velocities

`x_i' = -x_i² - 2N h/γ_i`,  `w_i' = -w_i x_i + 4N λ_i h/p'(x_i)²`,

where `h = L(p²)` is the first invisible moment defect.  Assembling these gives, for every
exponent, the quadrature moment velocity

`(∑ w_i x_i^{m+1})' = -(m+2) ∑ w_i x_i^{m+2} + h · c_m(x)`,

so the sequence of Padé defects `δ_r = s(2N+r) - ∑ w_i x_i^{2N+r}` forms a ladder

`δ_r' = -(2N+r+1) δ_{r+1} - δ_0 · c_{2N+r-1}(x)`.

Every correction term carries the bottom rung `δ_0` as a factor.  Hence at a face whose first
`d` defects vanish the ladder descends purely, `δ_0` is flat to order `d-1`, and its first
surviving derivative is the descending product of the ladder constants times `δ_d`.  Since the
hard node coordinate `u_i = 1/x_i - y` has velocity `2N δ_0/(x_i² γ_i)`, it inherits the same
contact order: `u_i^{(r)}(y₀) = 0` for `r ≤ d`, with

`u_i^{(d+1)}(y₀) = (-1)^d 2N(2N+1)⋯(2N+d) δ_d/(x_i² γ_i)`,

the same value for every node.
-/

open Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry (iteratedDeriv_ladder iteratedDeriv_ladder_bottom_eq_zero
  iteratedDeriv_ladder_bottom_top iteratedDeriv_eq_zero_of_velocity_flat
  iteratedDeriv_velocity_flat_top)

noncomputable section

namespace HTGeometry

variable {n : ℕ}

/-! ## The quadrature moment correction -/

/-- The contribution of one node to the departure of the quadrature moment flow from the atomic
Möbius flow. -/
def nodeQuadCorrectionTerm (m : ℕ) (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (2 * (n : ℝ) + 2) * (2 * nodeLogDeriv x i * (x i) ^ (m + 1) - ((m : ℝ) + 1) * (x i) ^ m)
    / (nodeSeparation x i) ^ 2

/-- The total departure of the quadrature moment flow of order `m+1` from the atomic Möbius flow,
per unit of the invisible defect. -/
def nodeQuadCorrection (m : ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, nodeQuadCorrectionTerm m x i

theorem nodeSeparation_ne_zero_of_dist {x : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (hdist : ∀ j ∈ Finset.univ.erase i, x i - x j ≠ 0) : nodeSeparation x i ≠ 0 :=
  Finset.prod_ne_zero_iff.2 hdist

set_option maxHeartbeats 2000000 in
/-- **The quadrature moment velocity.**  Every quadrature moment moves by the atomic Möbius rate
corrected by a multiple of the invisible defect `L(p²)`. -/
theorem hasDerivAt_quadratureMoment {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hsep : ∀ i, nodeSeparation (fun j => x j y) i ≠ 0)
    (hdist : ∀ i : Fin (n + 1), ∀ k ∈ Finset.univ.erase i, x i y - x k y ≠ 0)
    (m : ℕ) :
    HasDerivAt (fun t => ∑ i, w i t * (x i t) ^ (m + 1))
      (-((m : ℝ) + 2) * (∑ i, w i y * (x i y) ^ (m + 2))
        + momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ 2)
            * nodeQuadCorrection m (fun j => x j y)) y := by
  have hterm : ∀ i : Fin (n + 1),
      HasDerivAt (fun t => w i t * (x i t) ^ (m + 1))
        (w' i * (x i y) ^ (m + 1)
          + w i y * (((m + 1 : ℕ) : ℝ) * (x i y) ^ m * x' i)) y := by
    intro i
    have hpow : HasDerivAt (fun t => (x i t) ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * (x i y) ^ (m + 1 - 1) * x' i) y := (hx i).pow _
    have hpow' : HasDerivAt (fun t => (x i t) ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * (x i y) ^ m * x' i) y := by simpa using hpow
    exact (hw i).mul hpow'
  have hsum0 : HasDerivAt (∑ i : Fin (n + 1), fun t : ℝ => w i t * (x i t) ^ (m + 1))
      (∑ i : Fin (n + 1), (w' i * (x i y) ^ (m + 1)
        + w i y * (((m + 1 : ℕ) : ℝ) * (x i y) ^ m * x' i))) y :=
    HasDerivAt.sum (A := fun i t => w i t * (x i t) ^ (m + 1))
      (A' := fun i => w' i * (x i y) ^ (m + 1)
        + w i y * (((m + 1 : ℕ) : ℝ) * (x i y) ^ m * x' i)) fun i _ => hterm i
  have hfun : (∑ i : Fin (n + 1), fun t : ℝ => w i t * (x i t) ^ (m + 1))
      = fun t : ℝ => ∑ i : Fin (n + 1), w i t * (x i t) ^ (m + 1) := by
    funext t
    rw [Finset.sum_apply]
  rw [hfun] at hsum0
  have hval : ∀ i : Fin (n + 1),
      w' i * (x i y) ^ (m + 1) + w i y * (((m + 1 : ℕ) : ℝ) * (x i y) ^ m * x' i)
        = -((m : ℝ) + 2) * (w i y * (x i y) ^ (m + 2))
          + momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ 2)
              * nodeQuadCorrectionTerm m (fun j => x j y) i := by
    intro i
    have hwv := weightVelocity hs hx hw hquad i (hsep i) (hdist i)
    have hxv := weight_mul_nodeVelocity hs hx hw hquad i (hsep i)
    have hrw : w i y * (((m + 1 : ℕ) : ℝ) * (x i y) ^ m * x' i)
        = ((m + 1 : ℕ) : ℝ) * (x i y) ^ m * (w i y * x' i) := by ring
    rw [hwv, hrw, hxv]
    simp only [nodeQuadCorrectionTerm]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => hval i, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at hsum0
  exact hsum0

/-- **The defect ladder.**  The Padé defect of order `m+1` moves at rate `-(m+2)` times the defect
of order `m+2`, corrected by a multiple of the invisible defect `L(p²)`. -/
theorem hasDerivAt_quadDefect {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hsep : ∀ i, nodeSeparation (fun j => x j y) i ≠ 0)
    (hdist : ∀ i : Fin (n + 1), ∀ k ∈ Finset.univ.erase i, x i y - x k y ≠ 0)
    (m : ℕ) :
    HasDerivAt (fun t => s t (m + 1) - ∑ i, w i t * (x i t) ^ (m + 1))
      (-((m : ℝ) + 2) * (s y (m + 2) - ∑ i, w i y * (x i y) ^ (m + 2))
        - momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ 2)
            * nodeQuadCorrection m (fun j => x j y)) y := by
  have hsderiv : HasDerivAt (fun t => s t (m + 1)) (-(((m : ℝ) + 2) * s y (m + 2))) y := by
    have h := hs (m + 1)
    have hcast : (((m + 1 : ℕ) : ℝ) + 1) = (m : ℝ) + 2 := by push_cast; ring
    rw [hcast] at h
    have hidx : m + 1 + 1 = m + 2 := by omega
    rwa [hidx] at h
  have hsub := hsderiv.sub (hasDerivAt_quadratureMoment hs hx hw hquad hsep hdist m)
  have hval : -(((m : ℝ) + 2) * s y (m + 2))
      - (-((m : ℝ) + 2) * (∑ i, w i y * (x i y) ^ (m + 2))
        + momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ 2)
            * nodeQuadCorrection m (fun j => x j y))
      = -((m : ℝ) + 2) * (s y (m + 2) - ∑ i, w i y * (x i y) ^ (m + 2))
        - momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ 2)
            * nodeQuadCorrection m (fun j => x j y) := by ring
  rwa [hval] at hsub

/-- **The bottom rung is the invisible defect.**  Exactness through degree `2N-1` identifies the
first Padé defect with `L(p²)`. -/
theorem quadDefect_zero_eq {s : ℕ → ℝ} {x w : Fin (n + 1) → ℝ}
    (hquad : ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional s g = ∑ i, w i * g.eval (x i)) :
    s (2 * n + 2) - ∑ i, w i * (x i) ^ (2 * n + 2) = momentFunctional s ((nodePoly x) ^ 2) := by
  have hdeg : (Polynomial.X ^ (2 * n + 2) : Polynomial ℝ).natDegree ≤ 2 * n + 2 := by
    rw [Polynomial.natDegree_X_pow]
  have h := momentFunctional_eq_quadSum_add_top hquad (Polynomial.X ^ (2 * n + 2)) hdeg
  rw [momentFunctional_X_pow] at h
  have hcoeff : (Polynomial.X ^ (2 * n + 2) : Polynomial ℝ).coeff (2 * n + 2) = 1 := by
    simp
  rw [hcoeff, one_mul] at h
  have heval : ∑ i, w i * (Polynomial.X ^ (2 * n + 2) : Polynomial ℝ).eval (x i)
      = ∑ i, w i * (x i) ^ (2 * n + 2) :=
    Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_pow, Polynomial.eval_X]
  rw [heval] at h
  linarith

/-! ## Smoothness of the ladder data -/

theorem contDiffAt_quadDefectFun {s : ℝ → ℕ → ℝ} {x w : Fin (n + 1) → ℝ → ℝ} {y₀ : ℝ}
    (hss : ∀ j k : ℕ, ContDiffAt ℝ k (fun t => s t j) y₀)
    (hsx : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (x i) y₀)
    (hsw : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (w i) y₀)
    (m k : ℕ) :
    ContDiffAt ℝ k (fun t => s t m - ∑ i, w i t * (x i t) ^ m) y₀ :=
  (hss m k).sub (ContDiffAt.sum fun i _ => (hsw i k).mul ((hsx i k).pow m))

theorem contDiffAt_nodeSeparationFun {x : Fin (n + 1) → ℝ → ℝ} {y₀ : ℝ}
    (hsx : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (x i) y₀)
    (i : Fin (n + 1)) (k : ℕ) :
    ContDiffAt ℝ k (fun t => nodeSeparation (fun j => x j t) i) y₀ := by
  classical
  simp only [nodeSeparation]
  exact contDiffAt_prod fun j _ => (hsx i k).sub (hsx j k)

theorem contDiffAt_nodeLogDerivFun {x : Fin (n + 1) → ℝ → ℝ} {y₀ : ℝ}
    (hsx : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (x i) y₀)
    (i : Fin (n + 1)) (hdist : ∀ j ∈ Finset.univ.erase i, x i y₀ - x j y₀ ≠ 0) (k : ℕ) :
    ContDiffAt ℝ k (fun t => nodeLogDeriv (fun j => x j t) i) y₀ := by
  classical
  simp only [nodeLogDeriv]
  refine ContDiffAt.sum fun j hj => ?_
  exact ((hsx i k).sub (hsx j k)).inv (hdist j hj)

theorem contDiffAt_nodeQuadCorrectionFun {x : Fin (n + 1) → ℝ → ℝ} {y₀ : ℝ}
    (hsx : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (x i) y₀)
    (hdist : ∀ (i : Fin (n + 1)), ∀ j ∈ Finset.univ.erase i, x i y₀ - x j y₀ ≠ 0)
    (m k : ℕ) :
    ContDiffAt ℝ k (fun t => nodeQuadCorrection m (fun j => x j t)) y₀ := by
  classical
  simp only [nodeQuadCorrection, nodeQuadCorrectionTerm]
  refine ContDiffAt.sum fun i _ => ?_
  have hnum : ContDiffAt ℝ k (fun t => (2 * (n : ℝ) + 2)
      * (2 * nodeLogDeriv (fun j => x j t) i * (x i t) ^ (m + 1)
        - ((m : ℝ) + 1) * (x i t) ^ m)) y₀ :=
    contDiffAt_const.mul
      ((((contDiffAt_const).mul (contDiffAt_nodeLogDerivFun hsx i (hdist i) k)).mul
          ((hsx i k).pow (m + 1))).sub (contDiffAt_const.mul ((hsx i k).pow m)))
  have hden : ContDiffAt ℝ k (fun t => (nodeSeparation (fun j => x j t) i) ^ 2) y₀ :=
    (contDiffAt_nodeSeparationFun hsx i k).pow 2
  have hne : (fun t => (nodeSeparation (fun j => x j t) i) ^ 2) y₀ ≠ 0 :=
    pow_ne_zero 2 (nodeSeparation_ne_zero_of_dist (hdist i))
  exact hnum.div hden hne

/-! ## The contact jet -/

set_option maxHeartbeats 2000000 in
/-- **(GJRS.16) The defect jet at a flat face.**  When the first `d` Padé defects vanish, the
invisible defect `δ_0` is flat to order `d-1` and its `r`-th derivative descends the ladder. -/
theorem iteratedDeriv_quadDefect {s : ℝ → ℕ → ℝ} {y₀ : ℝ} {x w x' w' : Fin (n + 1) → ℝ → ℝ}
    (hs : ∀ (t : ℝ) (k : ℕ), HasDerivAt (fun z => s z k) (-(((k : ℝ) + 1) * s t (k + 1))) t)
    (hx : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (x i) (x' i t) t)
    (hw : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (w i) (w' i t) t)
    (hquad : ∀ (t : ℝ) (g : Polynomial ℝ), g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hdist : ∀ (t : ℝ) (i : Fin (n + 1)), ∀ j ∈ Finset.univ.erase i, x i t - x j t ≠ 0)
    (hss : ∀ j k : ℕ, ContDiffAt ℝ k (fun t => s t j) y₀)
    (hsx : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (x i) y₀)
    (hsw : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (w i) y₀)
    {d : ℕ}
    (hvan : ∀ j < d, s y₀ (2 * n + 2 + j) - ∑ i, w i y₀ * (x i y₀) ^ (2 * n + 2 + j) = 0)
    (r : ℕ) (hr : r ≤ d) :
    iteratedDeriv r (fun t => s t (2 * n + 2) - ∑ i, w i t * (x i t) ^ (2 * n + 2)) y₀
      = (-1) ^ r * (∏ j ∈ Finset.range r, (2 * (n : ℝ) + 3 + j))
        * (s y₀ (2 * n + 2 + r) - ∑ i, w i y₀ * (x i y₀) ^ (2 * n + 2 + r)) := by
  classical
  set A : ℕ → ℝ → ℝ :=
    fun q t => s t (2 * n + 2 + q) - ∑ i, w i t * (x i t) ^ (2 * n + 2 + q) with hA_def
  set E : ℕ → ℝ → ℝ := fun q t => nodeQuadCorrection (2 * n + 1 + q) (fun j => x j t) with hE_def
  set c : ℕ → ℝ := fun q => 2 * (n : ℝ) + 3 + q with hc_def
  have hAsmooth : ∀ q, ∀ k : ℕ, ContDiffAt ℝ k (A q) y₀ := fun q k =>
    contDiffAt_quadDefectFun hss hsx hsw _ k
  have hEsmooth : ∀ q, ∀ k : ℕ, ContDiffAt ℝ k (E q) y₀ := fun q k =>
    contDiffAt_nodeQuadCorrectionFun hsx (hdist y₀) _ k
  have hsep : ∀ (t : ℝ) (i : Fin (n + 1)), nodeSeparation (fun j => x j t) i ≠ 0 := fun t i =>
    nodeSeparation_ne_zero_of_dist (hdist t i)
  have hladder : ∀ q, deriv (A q) =ᶠ[𝓝 y₀] fun t => -(c q * A (q + 1) t) - A 0 t * E q t := by
    intro q
    refine Filter.Eventually.of_forall fun t => ?_
    have hstep := hasDerivAt_quadDefect (s := s) (y := t) (x := x) (w := w)
      (x' := fun i => x' i t) (w' := fun i => w' i t)
      (fun k => hs t k) (fun i => hx t i) (fun i => hw t i) hquad (fun i => hsep t i)
      (hdist t) (2 * n + 1 + q)
    have hidx1 : 2 * n + 1 + q + 1 = 2 * n + 2 + q := by omega
    have hidx2 : 2 * n + 1 + q + 2 = 2 * n + 2 + (q + 1) := by omega
    have hcast : ((2 * n + 1 + q : ℕ) : ℝ) + 2 = c q := by rw [hc_def]; push_cast; ring
    rw [hidx1, hidx2, hcast] at hstep
    have hbot : momentFunctional (s t) ((nodePoly (fun j => x j t)) ^ 2) = A 0 t := by
      rw [hA_def]
      simp only [Nat.add_zero]
      exact (quadDefect_zero_eq (fun g hg => hquad t g hg)).symm
    rw [hbot] at hstep
    have hfin : HasDerivAt (A q) (-(c q * A (q + 1) t) - A 0 t * E q t) t := by
      rw [hA_def, hE_def]
      convert hstep using 1
      ring
    exact hfin.deriv
  have hvan' : ∀ j < d, A j y₀ = 0 := fun j hj => hvan j hj
  have hmain := iteratedDeriv_ladder hAsmooth hEsmooth hladder hvan' r hr 0
  simpa using hmain

/-! ## The hard coordinate -/

/-- The reciprocal Christoffel factor through which the invisible defect drives the hard node
coordinate. -/
def hardCoordinateFactor (x w : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (2 * (n : ℝ) + 2) / ((x i) ^ 2 * nodeEnergy x w i)

theorem contDiffAt_hardCoordinateFactorFun {x w : Fin (n + 1) → ℝ → ℝ} {y₀ : ℝ}
    (hsx : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (x i) y₀)
    (hsw : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (w i) y₀)
    (i₀ : Fin (n + 1)) (hdist : ∀ j ∈ Finset.univ.erase i₀, x i₀ y₀ - x j y₀ ≠ 0)
    (hx0 : x i₀ y₀ ≠ 0) (hw0 : w i₀ y₀ ≠ 0) (k : ℕ) :
    ContDiffAt ℝ k (fun t => hardCoordinateFactor (fun j => x j t) (fun j => w j t) i₀) y₀ := by
  classical
  simp only [hardCoordinateFactor, nodeEnergy]
  refine contDiffAt_const.div (((hsx i₀ k).pow 2).mul
    ((hsw i₀ k).mul ((contDiffAt_nodeSeparationFun hsx i₀ k).pow 2))) ?_
  exact mul_ne_zero (pow_ne_zero 2 hx0)
    (mul_ne_zero hw0 (pow_ne_zero 2 (nodeSeparation_ne_zero_of_dist hdist)))

/-- **The hard-coordinate velocity in defect form.**  `u_i = 1/x_i - y` moves at the invisible
defect times the reciprocal Christoffel factor. -/
theorem deriv_hardNodeCoordinate_eq {s : ℝ → ℕ → ℝ} {x w x' w' : Fin (n + 1) → ℝ → ℝ}
    (hs : ∀ (t : ℝ) (k : ℕ), HasDerivAt (fun z => s z k) (-(((k : ℝ) + 1) * s t (k + 1))) t)
    (hx : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (x i) (x' i t) t)
    (hw : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (w i) (w' i t) t)
    (hquad : ∀ (t : ℝ) (g : Polynomial ℝ), g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hdist : ∀ (t : ℝ) (i : Fin (n + 1)), ∀ j ∈ Finset.univ.erase i, x i t - x j t ≠ 0)
    (i₀ : Fin (n + 1)) (hwne : ∀ t : ℝ, w i₀ t ≠ 0) (hxne : ∀ t : ℝ, x i₀ t ≠ 0) (t : ℝ) :
    deriv (fun z => (x i₀ z)⁻¹ - z) t
      = (s t (2 * n + 2) - ∑ i, w i t * (x i t) ^ (2 * n + 2))
        * hardCoordinateFactor (fun j => x j t) (fun j => w j t) i₀ := by
  classical
  have hsep : ∀ i : Fin (n + 1), nodeSeparation (fun j => x j t) i ≠ 0 := fun i =>
    nodeSeparation_ne_zero_of_dist (hdist t i)
  have hstep := hasDerivAt_hardNodeCoordinate (s := s) (y := t) (x := x) (w := w)
    (x' := fun i => x' i t) (w' := fun i => w' i t)
    (fun k => hs t k) (fun i => hx t i) (fun i => hw t i) hquad i₀ (hsep i₀) (hwne t) (hxne t)
  have hbot : momentFunctional (s t) ((nodePoly (fun j => x j t)) ^ 2)
      = s t (2 * n + 2) - ∑ i, w i t * (x i t) ^ (2 * n + 2) :=
    (quadDefect_zero_eq (fun g hg => hquad t g hg)).symm
  rw [hbot] at hstep
  have heq : (s t (2 * n + 2) - ∑ i, w i t * (x i t) ^ (2 * n + 2))
      * hardCoordinateFactor (fun j => x j t) (fun j => w j t) i₀
      = (2 * (n : ℝ) + 2) * (s t (2 * n + 2) - ∑ i, w i t * (x i t) ^ (2 * n + 2))
          / ((x i₀ t) ^ 2 * nodeEnergy (fun j => x j t) (fun j => w j t) i₀) := by
    simp only [hardCoordinateFactor]
    ring
  rw [heq]
  exact hstep.deriv

/-- The invisible defect is flat below the contact order. -/
theorem iteratedDeriv_quadDefect_eq_zero {s : ℝ → ℕ → ℝ} {y₀ : ℝ} {x w x' w' : Fin (n + 1) → ℝ → ℝ}
    (hs : ∀ (t : ℝ) (k : ℕ), HasDerivAt (fun z => s z k) (-(((k : ℝ) + 1) * s t (k + 1))) t)
    (hx : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (x i) (x' i t) t)
    (hw : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (w i) (w' i t) t)
    (hquad : ∀ (t : ℝ) (g : Polynomial ℝ), g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hdist : ∀ (t : ℝ) (i : Fin (n + 1)), ∀ j ∈ Finset.univ.erase i, x i t - x j t ≠ 0)
    (hss : ∀ j k : ℕ, ContDiffAt ℝ k (fun t => s t j) y₀)
    (hsx : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (x i) y₀)
    (hsw : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (w i) y₀)
    {d : ℕ}
    (hvan : ∀ j < d, s y₀ (2 * n + 2 + j) - ∑ i, w i y₀ * (x i y₀) ^ (2 * n + 2 + j) = 0)
    (j : ℕ) (hj : j < d) :
    iteratedDeriv j (fun t => s t (2 * n + 2) - ∑ i, w i t * (x i t) ^ (2 * n + 2)) y₀ = 0 := by
  rw [iteratedDeriv_quadDefect (x' := x') (w' := w') hs hx hw hquad hdist hss hsx hsw hvan j
    (le_of_lt hj), hvan j hj, mul_zero]

/-- **(GJRS.19) The flat hard-coordinate jet.**  At a face of contact order `d` every hard node
coordinate `u_i = 1/x_i - y` has vanishing derivatives of every order `1 ≤ r ≤ d`. -/
theorem iteratedDeriv_hardNodeCoordinate_eq_zero {s : ℝ → ℕ → ℝ} {y₀ : ℝ}
    {x w x' w' : Fin (n + 1) → ℝ → ℝ}
    (hs : ∀ (t : ℝ) (k : ℕ), HasDerivAt (fun z => s z k) (-(((k : ℝ) + 1) * s t (k + 1))) t)
    (hx : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (x i) (x' i t) t)
    (hw : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (w i) (w' i t) t)
    (hquad : ∀ (t : ℝ) (g : Polynomial ℝ), g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hdist : ∀ (t : ℝ) (i : Fin (n + 1)), ∀ j ∈ Finset.univ.erase i, x i t - x j t ≠ 0)
    (hss : ∀ j k : ℕ, ContDiffAt ℝ k (fun t => s t j) y₀)
    (hsx : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (x i) y₀)
    (hsw : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (w i) y₀)
    (i₀ : Fin (n + 1)) (hwne : ∀ t : ℝ, w i₀ t ≠ 0) (hxne : ∀ t : ℝ, x i₀ t ≠ 0)
    {d : ℕ} (hd : 1 ≤ d)
    (hvan : ∀ j < d, s y₀ (2 * n + 2 + j) - ∑ i, w i y₀ * (x i y₀) ^ (2 * n + 2 + j) = 0)
    {r : ℕ} (hr1 : 1 ≤ r) (hrd : r ≤ d) :
    iteratedDeriv r (fun t => (x i₀ t)⁻¹ - t) y₀ = 0 := by
  classical
  refine iteratedDeriv_eq_zero_of_velocity_flat
    (D := fun t => s t (2 * n + 2) - ∑ i, w i t * (x i t) ^ (2 * n + 2))
    (G := fun t => hardCoordinateFactor (fun j => x j t) (fun j => w j t) i₀)
    (contDiffAt_quadDefectFun hss hsx hsw _)
    (contDiffAt_hardCoordinateFactorFun hsx hsw i₀ (hdist y₀ i₀) (hxne y₀) (hwne y₀))
    (Filter.Eventually.of_forall fun t =>
      deriv_hardNodeCoordinate_eq (x' := x') (w' := w') hs hx hw hquad hdist i₀ hwne hxne t)
    (fun j hj => iteratedDeriv_quadDefect_eq_zero (x' := x') (w' := w') hs hx hw hquad hdist
      hss hsx hsw hvan j (by omega)) hr1 hrd

/-- **(GJRS.20) The first surviving hard-coordinate jet.**  At contact order `d` every hard node
coordinate has the same derivative of order `d+1`, the signed rising factorial of the ladder
constants times the first nonvanishing Padé defect, divided by `x_i² γ_i`. -/
theorem iteratedDeriv_hardNodeCoordinate_top {s : ℝ → ℕ → ℝ} {y₀ : ℝ}
    {x w x' w' : Fin (n + 1) → ℝ → ℝ}
    (hs : ∀ (t : ℝ) (k : ℕ), HasDerivAt (fun z => s z k) (-(((k : ℝ) + 1) * s t (k + 1))) t)
    (hx : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (x i) (x' i t) t)
    (hw : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (w i) (w' i t) t)
    (hquad : ∀ (t : ℝ) (g : Polynomial ℝ), g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hdist : ∀ (t : ℝ) (i : Fin (n + 1)), ∀ j ∈ Finset.univ.erase i, x i t - x j t ≠ 0)
    (hss : ∀ j k : ℕ, ContDiffAt ℝ k (fun t => s t j) y₀)
    (hsx : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (x i) y₀)
    (hsw : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (w i) y₀)
    (i₀ : Fin (n + 1)) (hwne : ∀ t : ℝ, w i₀ t ≠ 0) (hxne : ∀ t : ℝ, x i₀ t ≠ 0)
    {d : ℕ}
    (hvan : ∀ j < d, s y₀ (2 * n + 2 + j) - ∑ i, w i y₀ * (x i y₀) ^ (2 * n + 2 + j) = 0) :
    iteratedDeriv (d + 1) (fun t => (x i₀ t)⁻¹ - t) y₀
      = ((-1) ^ d * (∏ j ∈ Finset.range d, (2 * (n : ℝ) + 3 + j))
          * (s y₀ (2 * n + 2 + d) - ∑ i, w i y₀ * (x i y₀) ^ (2 * n + 2 + d)))
        * hardCoordinateFactor (fun j => x j y₀) (fun j => w j y₀) i₀ := by
  classical
  have htop := iteratedDeriv_velocity_flat_top
    (D := fun t => s t (2 * n + 2) - ∑ i, w i t * (x i t) ^ (2 * n + 2))
    (G := fun t => hardCoordinateFactor (fun j => x j t) (fun j => w j t) i₀)
    (u := fun t => (x i₀ t)⁻¹ - t)
    (contDiffAt_quadDefectFun hss hsx hsw _)
    (contDiffAt_hardCoordinateFactorFun hsx hsw i₀ (hdist y₀ i₀) (hxne y₀) (hwne y₀))
    (Filter.Eventually.of_forall fun t =>
      deriv_hardNodeCoordinate_eq (x' := x') (w' := w') hs hx hw hquad hdist i₀ hwne hxne t)
    (fun j hj => iteratedDeriv_quadDefect_eq_zero (x' := x') (w' := w') hs hx hw hquad hdist
      hss hsx hsw hvan j hj)
  rw [htop, iteratedDeriv_quadDefect (x' := x') (w' := w') hs hx hw hquad hdist hss hsx hsw
    hvan d le_rfl]

/-- **(GJRS.21) Coherent orientation.**  When the first nonvanishing Padé defect carries the
right-face sign `(-1)^d δ_{2N+d} > 0`, every positive hard node coordinate has the same strictly
positive first nonvanishing derivative. -/
theorem iteratedDeriv_hardNodeCoordinate_pos {s : ℝ → ℕ → ℝ} {y₀ : ℝ}
    {x w x' w' : Fin (n + 1) → ℝ → ℝ}
    (hs : ∀ (t : ℝ) (k : ℕ), HasDerivAt (fun z => s z k) (-(((k : ℝ) + 1) * s t (k + 1))) t)
    (hx : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (x i) (x' i t) t)
    (hw : ∀ (t : ℝ) (i : Fin (n + 1)), HasDerivAt (w i) (w' i t) t)
    (hquad : ∀ (t : ℝ) (g : Polynomial ℝ), g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hdist : ∀ (t : ℝ) (i : Fin (n + 1)), ∀ j ∈ Finset.univ.erase i, x i t - x j t ≠ 0)
    (hss : ∀ j k : ℕ, ContDiffAt ℝ k (fun t => s t j) y₀)
    (hsx : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (x i) y₀)
    (hsw : ∀ (i : Fin (n + 1)) (k : ℕ), ContDiffAt ℝ k (w i) y₀)
    (i₀ : Fin (n + 1)) (hwne : ∀ t : ℝ, w i₀ t ≠ 0) (hxne : ∀ t : ℝ, x i₀ t ≠ 0)
    (hE : 0 < nodeEnergy (fun j => x j y₀) (fun j => w j y₀) i₀)
    {d : ℕ}
    (hvan : ∀ j < d, s y₀ (2 * n + 2 + j) - ∑ i, w i y₀ * (x i y₀) ^ (2 * n + 2 + j) = 0)
    (hsign : 0 < (-1 : ℝ) ^ d
      * (s y₀ (2 * n + 2 + d) - ∑ i, w i y₀ * (x i y₀) ^ (2 * n + 2 + d))) :
    0 < iteratedDeriv (d + 1) (fun t => (x i₀ t)⁻¹ - t) y₀ := by
  classical
  rw [iteratedDeriv_hardNodeCoordinate_top (x' := x') (w' := w') hs hx hw hquad hdist
    hss hsx hsw i₀ hwne hxne hvan]
  have hprod : 0 < ∏ j ∈ Finset.range d, (2 * (n : ℝ) + 3 + j) :=
    Finset.prod_pos fun j _ => by positivity
  have hfac : 0 < hardCoordinateFactor (fun j => x j y₀) (fun j => w j y₀) i₀ := by
    rw [hardCoordinateFactor]
    exact div_pos (by positivity) (mul_pos (pow_two_pos_of_ne_zero (hxne y₀)) hE)
  have hrw : (-1 : ℝ) ^ d * (∏ j ∈ Finset.range d, (2 * (n : ℝ) + 3 + j))
      * (s y₀ (2 * n + 2 + d) - ∑ i, w i y₀ * (x i y₀) ^ (2 * n + 2 + d))
      = (∏ j ∈ Finset.range d, (2 * (n : ℝ) + 3 + j))
        * ((-1 : ℝ) ^ d * (s y₀ (2 * n + 2 + d) - ∑ i, w i y₀ * (x i y₀) ^ (2 * n + 2 + d))) := by
    ring
  rw [hrw]
  exact mul_pos (mul_pos hprod hsign) hfac

end HTGeometry
