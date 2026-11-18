import GaloisForLFunctions.Bottcher.ChordalMetric
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Quantitative rational changes of orthogonal frame in the plane

Integral orthogonal matrices of determinant one give only four planar
rotations. Clearing the denominator of a rational rotation yields integral
orthogonal columns of common length. Stereographic projection supplies
such frames within chord distance 1/B at denominator at most 5B².
-/

noncomputable section
open Matrix
namespace GaloisForLFunctions.CollectiveDiophantineGeometry.PlaneFrames

def cx (t : ℝ) : ℝ := (1-t^2)/(1+t^2)
def cy (t : ℝ) : ℝ := 2*t/(1+t^2)

theorem chart_unit (t : ℝ) : (cx t)^2+(cy t)^2=1 := by
  dsimp [cx,cy]
  field_simp
  ring

/-- The exact chord distance compares angular accuracy with parameter accuracy. -/
theorem chord (s t : ℝ) :
    (cx s-cx t)^2+(cy s-cy t)^2=4*(s-t)^2/((1+s^2)*(1+t^2)) := by
  have h := Bottcher.chordal_stereo_identity s 0 t 0
  have hz (x : ℝ) : (x^2-1)/(1+x^2) = -cx x := by
    unfold cx
    ring
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero,mul_zero,zero_div,sub_self,hz,← cy] at h
  linear_combination h

private theorem chord_bound (s t : ℝ) :
    (cx s-cx t)^2+(cy s-cy t)^2 ≤ 4*(s-t)^2 := by
  rw [chord,div_le_iff₀ (by positivity)]
  exact le_mul_of_one_le_right (by positivity)
    (one_le_mul_of_one_le_of_one_le (by nlinarith only [sq_nonneg s]) (by nlinarith only [sq_nonneg t]))

/-- One chart covers the right semicircle with bounded parameters. -/
theorem right_source (x y : ℝ) (hx : 0 ≤ x) (h : x^2+y^2=1) :
    ∃ t : ℝ, |t| ≤ 1 ∧ cx t=x ∧ cy t=y := by
  have hp : 0<1+x := by linarith only [hx]
  have h₁ : 1+(y/(1+x))^2=2/(1+x) := by
    field_simp
    linarith only [h]
  have h₂ : 1-(y/(1+x))^2=2*x/(1+x) := by
    field_simp
    linarith only [h]
  refine ⟨y/(1+x),?_,?_,?_⟩
  · rw [abs_div,abs_of_pos hp,div_le_one hp]
    have hy : |y| ≤ 1 := by nlinarith only [h,sq_nonneg x,sq_abs y,abs_nonneg y]
    linarith only [hy,hx]
  · rw [cx,h₁,h₂]
    field_simp
  · rw [cy,h₁]
    field_simp

/-- Integer numerator of the rational rotation with parameter a/b. -/
def frame (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![b^2-a^2,-(2*a*b); 2*a*b,b^2-a^2]

/-- Orthogonal columns of common length a²+b² are obtained without rounding
any individual matrix entry. -/
theorem frame_gram (a b : ℤ) :
    (frame a b).transpose * frame a b = (a^2+b^2)^2 • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frame,mul_apply,Fin.sum_univ_succ,one_apply] <;> ring

theorem frame_det (a b : ℤ) : (frame a b).det=(a^2+b^2)^2 := by
  rw [Matrix.det_fin_two]
  dsimp [frame]
  ring

theorem normalized_column (a b : ℤ) (hb : b ≠ 0) :
    ((frame a b 0 0 : ℤ) : ℝ)/(a^2+b^2)=cx ((a : ℝ)/b) ∧
      ((frame a b 1 0 : ℤ) : ℝ)/(a^2+b^2)=cy ((a : ℝ)/b) := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hd : (a : ℝ)^2+(b : ℝ)^2 ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hb')).ne'
  constructor <;> simp [frame,cx,cy] <;> field_simp <;> ring

private theorem rounded (t : ℝ) (B : ℕ+) (ht : |t| ≤ 1) :
    ∃ a : ℤ, |(a : ℝ)-(B : ℝ)*t| ≤ 1/2 ∧ (a : ℝ)^2+(B : ℝ)^2 ≤ 5*(B : ℝ)^2 := by
  let a := ⌊(B : ℝ)*t+1/2⌋
  have h₁ := Int.floor_le ((B : ℝ)*t+1/2)
  have h₂ := Int.lt_floor_add_one ((B : ℝ)*t+1/2)
  have ha : |(a : ℝ)-(B : ℝ)*t| ≤ 1/2 := abs_le.mpr
    ⟨by dsimp [a]; linarith only [h₂],by dsimp [a]; linarith only [h₁]⟩
  refine ⟨a,ha,?_⟩
  have hB : (1 : ℝ) ≤ B := by exact_mod_cast B.pos
  have hnorm : |(a : ℝ)| ≤ 2*(B : ℝ) := by
    have hh := abs_add_le ((a : ℝ)-(B : ℝ)*t) ((B : ℝ)*t)
    rw [sub_add_cancel,abs_mul,abs_of_pos (by exact_mod_cast B.pos : (0 : ℝ)<B)] at hh
    have hh' := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (B : ℝ))
    linarith only [ha,hh,hB,hh']
  have hs := sq_le_sq' ((abs_le.mp hnorm).1) ((abs_le.mp hnorm).2)
  nlinarith only [hs]

/-- In every semicircle, integer rounding gives squared chord error at most
1/B² with an explicit height bound on the cleared rotation. -/
theorem bounded_rotation (x y : ℝ) (h : x^2+y^2=1) (B : ℕ+) :
    ∃ a : ℤ, ∃ ε : ℤ, (ε=1 ∨ ε= -1) ∧ (a : ℝ)^2+(B : ℝ)^2 ≤ 5*(B : ℝ)^2 ∧
      (x-ε*cx ((a : ℝ)/B))^2+(y-ε*cy ((a : ℝ)/B))^2 ≤ 1/(B : ℝ)^2 := by
  have right (x y : ℝ) (hx : 0 ≤ x) (hu : x^2+y^2=1) :
      ∃ a : ℤ, (a : ℝ)^2+(B : ℝ)^2 ≤ 5*(B : ℝ)^2 ∧
        (x-cx ((a : ℝ)/B))^2+(y-cy ((a : ℝ)/B))^2 ≤ 1/(B : ℝ)^2 := by
    obtain ⟨t,ht,rfl,rfl⟩ := right_source x y hx hu
    obtain ⟨a,ha,hbound⟩ := rounded t B ht
    refine ⟨a,hbound,(chord_bound _ _).trans ?_⟩
    have hB : (0 : ℝ)<B := by exact_mod_cast B.pos
    rw [le_div_iff₀ (sq_pos_of_pos hB)]
    have he : 4*(t-(a : ℝ)/B)^2*(B : ℝ)^2 = (2*((a : ℝ)-(B : ℝ)*t))^2 := by
      field_simp
      ring
    rw [he]
    have hle := abs_le.mp ha
    apply (sq_le_one_iff_abs_le_one _).2
    rw [abs_le]
    constructor <;> linarith only [hle.1,hle.2]
  by_cases hx : 0≤x
  · obtain ⟨a,ha,hh⟩ := right x y hx h
    exact ⟨a,1,Or.inl rfl,ha,by simpa only [Int.cast_one,one_mul] using hh⟩
  · obtain ⟨a,ha,hh⟩ := right (-x) (-y) (by linarith) (by simpa only [neg_sq] using h)
    exact ⟨a,-1,Or.inr rfl,ha,by push_cast; linarith only [hh]⟩

end GaloisForLFunctions.CollectiveDiophantineGeometry.PlaneFrames

#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.PlaneFrames.chart_unit
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.PlaneFrames.chord
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.PlaneFrames.right_source
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.PlaneFrames.frame_gram
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.PlaneFrames.frame_det
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.PlaneFrames.normalized_column
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.PlaneFrames.bounded_rotation
