/-
Height calculus adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.HyperbolicAxisLaplacian

/-!
# Logarithmic height identities

The transformed-height denominator satisfies `AD=B²+C²`. Logarithmic
height `log(v)−log(Q)` has hyperbolic gradient norm one and Laplacian minus two.
These identities determine the Laplacian of every smooth height profile.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def quadraticHeightDenominator (A B C D x y v : ℝ) : ℝ :=
  A*(x^2+y^2+v^2)+2*(B*x+C*y)+D

lemma quadraticHeightDenominator_hasDerivAt_x (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D t y v)
      (2*(A*x+B)) x := by
  unfold quadraticHeightDenominator
  convert (((((hasDerivAt_id x).pow 2).add_const (y^2)).add_const (v^2)).const_mul A).add
    ((((hasDerivAt_id x).const_mul B).add_const (C*y)).const_mul 2) |>.add_const D using 1 <;> try rfl
  all_goals try dsimp
  all_goals ring

lemma quadraticHeightDenominator_hasDerivAt_y (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D x t v)
      (2*(A*y+C)) y := by
  unfold quadraticHeightDenominator
  convert (((((hasDerivAt_id y).pow 2).const_add (x^2)).add_const (v^2)).const_mul A).add
    ((((hasDerivAt_id y).const_mul C).const_add (B*x)).const_mul 2) |>.add_const D using 1 <;> try rfl
  all_goals try dsimp
  all_goals ring

lemma quadraticHeightDenominator_hasDerivAt_v (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D x y t)
      (2*A*v) v := by
  unfold quadraticHeightDenominator
  convert ((((hasDerivAt_id v).pow 2).const_add (x^2+y^2)).const_mul A).add_const
    (2*(B*x+C*y)+D) using 1 <;> try rfl
  all_goals try dsimp
  all_goals ring

def heightLogDx (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*x+B)/quadraticHeightDenominator A B C D x y v)
def heightLogDy (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*y+C)/quadraticHeightDenominator A B C D x y v)
def heightLogDv (A B C D x y v : ℝ) : ℝ :=
  1/v - 2*A*v/quadraticHeightDenominator A B C D x y v

def heightLogDxx (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*x+B))*(2*(A*x+B)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDyy (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*y+C))*(2*(A*y+C)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDvv (A B C D x y v : ℝ) : ℝ :=
  -(1/v^2) - ((2*A*quadraticHeightDenominator A B C D x y v -
    (2*A*v)*(2*A*v))/(quadraticHeightDenominator A B C D x y v)^2)

lemma quadraticHeight_gradient_square (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) :
    (A*x+B)^2 + (A*y+C)^2 + (A*v)^2 =
      A*quadraticHeightDenominator A B C D x y v := by
  unfold quadraticHeightDenominator
  nlinarith only [hrel]

lemma heightLog_eikonal (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    v^2 * ((heightLogDx A B C D x y v)^2 +
      (heightLogDy A B C D x y v)^2 + (heightLogDv A B C D x y v)^2) = 1 := by
  calc
    _ = 1 + 4*v^2/(quadraticHeightDenominator A B C D x y v)^2 *
        ((A*x+B)^2+(A*y+C)^2+(A*v)^2 - A*quadraticHeightDenominator A B C D x y v) := by
      unfold heightLogDx heightLogDy heightLogDv
      field_simp [hv,hq]
      ; ring
    _ = 1 := by rw [quadraticHeight_gradient_square A B C D x y v hrel]; ring

lemma heightLog_laplacian (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    v^2 * (heightLogDxx A B C D x y v +
      heightLogDyy A B C D x y v + heightLogDvv A B C D x y v) -
      v*heightLogDv A B C D x y v = -2 := by
  calc
    _ = -2 + 4*v^2/(quadraticHeightDenominator A B C D x y v)^2 *
        ((A*x+B)^2+(A*y+C)^2+(A*v)^2 - A*quadraticHeightDenominator A B C D x y v) := by
      unfold heightLogDxx heightLogDyy heightLogDvv heightLogDv
      field_simp [hv,hq]
      ; ring
    _ = -2 := by rw [quadraticHeight_gradient_square A B C D x y v hrel]; ring

lemma complex_row_quadratic_relation (c d : ℂ) :
    Complex.normSq c * Complex.normSq d = (c*star d).re^2 + (-(c*star d).im)^2 := by
  simp only [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im]
  ring

lemma heightDenominator_eq_quadratic (u : Fin 2 → ℂ) (x y v : ℝ) :
    heightDenominator ((x:ℂ)+(y:ℂ)*Complex.I) v u =
      quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  unfold heightDenominator quadraticHeightDenominator
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

def spatialLogD (A B C D : ℝ) (p : SpatialCoordinates) : Fin 3 → ℝ :=
  ![heightLogDx A B C D (p 0) (p 1) (p 2),
    heightLogDy A B C D (p 0) (p 1) (p 2),
    heightLogDv A B C D (p 0) (p 1) (p 2)]
def spatialLogDD (A B C D : ℝ) (p : SpatialCoordinates) : Fin 3 → ℝ :=
  ![heightLogDxx A B C D (p 0) (p 1) (p 2),
    heightLogDyy A B C D (p 0) (p 1) (p 2),
    heightLogDvv A B C D (p 0) (p 1) (p 2)]

def rowLogD (u : Fin 2 → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ :=
  spatialLogD (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) p j

def rowLogDD (u : Fin 2 → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ :=
  spatialLogDD (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) p j

lemma row_denominator_pos (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) :
    0 < quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
      (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2) := by
  rw [← heightDenominator_eq_quadratic]
  exact heightDenominator_pos _ _ hv u hu

def rowHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℝ :=
  p 2 / quadraticHeightDenominator (Complex.normSq (u 0)) (u 0*star (u 1)).re
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2)

lemma rowHeight_pos (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    0<rowHeight u p := div_pos hp (row_denominator_pos u hu p hp)
lemma cosetHeight_upperPoint_rowHeight (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) :
    cosetHeight r (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=rowHeight (embeddedRow r) p := by
  change (rowEnergy (rowOperator (upperSection ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) (embeddedRow r)))⁻¹=_
  rw [rowEnergy_upperSection,inv_div,heightDenominator_eq_quadratic]
  rfl

lemma rowHeight_contDiffAt (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (rowHeight u) p := by
  have hq : ContDiffAt ℝ ∞
      (fun q : SpatialCoordinates => quadraticHeightDenominator (Complex.normSq (u 0))
        (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (q 0) (q 1) (q 2)) p := by
    unfold quadraticHeightDenominator
    fun_prop
  exact (show ContDiffAt ℝ ∞ (fun q : SpatialCoordinates => q 2) p by fun_prop).div hq
    (row_denominator_pos u hu p hp).ne'

lemma continuous_axis_update (p : SpatialCoordinates) (j : Fin 3) :
    Continuous (fun t : ℝ => Function.update p j t) := by
  apply continuous_pi
  intro k
  by_cases h : k=j
  · subst k
    simp only [Function.update_self]
    fun_prop
  · simpa only [Function.update_of_ne h] using (continuous_const : Continuous (fun _ : ℝ => p k))

#print axioms quadraticHeightDenominator_hasDerivAt_x
#print axioms quadraticHeightDenominator_hasDerivAt_y
#print axioms quadraticHeightDenominator_hasDerivAt_v
#print axioms heightLog_eikonal
#print axioms heightLog_laplacian
#print axioms cosetHeight_upperPoint_rowHeight
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
