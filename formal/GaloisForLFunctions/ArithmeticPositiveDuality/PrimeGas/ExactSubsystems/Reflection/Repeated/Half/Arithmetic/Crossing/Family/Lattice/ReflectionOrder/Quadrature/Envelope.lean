import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-! # Sharp real-quadrature envelope for a phase and its double -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature

open Real

/-- Intersection of the increasing first quadrature and the decreasing
part of the second, with relative gain c. -/
def radius (c : ℝ) := (sqrt (1+8*c^2)-1)/(4*c)

private theorem root_data {c : ℝ} (hc : 1≤c) :
    0<radius c ∧ 2*c*(radius c)^2+radius c=c := by
  have cp : 0<c := zero_lt_one.trans_le hc
  have sq := sq_sqrt (show 0≤1+8*c^2 by positivity)
  have sp := sqrt_nonneg (1+8*c^2)
  have large : 1<sqrt (1+8*c^2) := by
    by_contra! h
    nlinarith only [sq,sq_pos_of_pos cp,mul_nonneg (sub_nonneg.mpr h) (by linarith only [sp] : 0≤1+sqrt (1+8*c^2))]
  have linear : 4*c*radius c+1=sqrt (1+8*c^2) := by
    unfold radius
    field_simp
    ring
  have squared : (4*c*radius c+1)^2=1+8*c^2 := by rw [linear,sq]
  have eq : (8*c)*(2*c*(radius c)^2+radius c-c)=0 := by nlinarith only [squared]
  exact ⟨div_pos (sub_pos.mpr large) (by positivity),sub_eq_zero.mp
    ((mul_eq_zero.mp eq).resolve_left (mul_ne_zero (by norm_num) cp.ne'))⟩

theorem radius_bounds {c : ℝ} (hc : 1≤c) : 1/2≤radius c ∧ radius c<1 := by
  obtain ⟨pos,root⟩ := root_data hc
  have cp := zero_lt_one.trans_le hc
  constructor
  · by_contra! h
    have prod := mul_pos (sub_pos.mpr h) (show 0<2*c*(1/2+radius c)+1 by positivity)
    nlinarith only [prod,root,hc]
  · by_contra! h
    have prod := mul_nonneg (sub_nonneg.mpr h) (show 0≤2*c*(radius c+1)+1 by positivity)
    nlinarith only [prod,root,hc]

def phaseGain (c y : ℝ) := max |cos y| (c*|cos (2*y)|)

private theorem max_exact {c u : ℝ} (hc : 1≤c) (hu : 0≤u) :
    radius c≤max u (c*|2*u^2-1|) ∧ (max u (c*|2*u^2-1|)=radius c ↔ u=radius c) := by
  obtain ⟨pos,root⟩ := root_data hc
  have cp := zero_lt_one.trans_le hc
  rcases lt_trichotomy u (radius c) with h | h | h
  · have diff : 0<2*c*((radius c)^2-u^2) := by
      apply mul_pos (by positivity)
      nlinarith only [mul_pos (sub_pos.mpr h) (add_pos_of_pos_of_nonneg pos hu)]
    have strong : radius c<c*|2*u^2-1| := by
      have lo := mul_le_mul_of_nonneg_left (neg_le_abs (2*u^2-1)) cp.le
      linarith only [show radius c<c*(-(2*u^2-1)) by nlinarith only [diff,root],lo]
    have bigger := strong.trans_le (le_max_right u _)
    exact ⟨bigger.le,iff_of_false bigger.ne' h.ne⟩
  · subst u
    have neg : 2*(radius c)^2-1≤0 := by
      by_contra! h
      nlinarith only [mul_pos cp h,root,pos]
    rw [abs_of_nonpos neg,show c*(-(2*(radius c)^2-1))=radius c by nlinarith only [root],max_self]
    exact ⟨le_rfl,Iff.rfl⟩
  · have bigger := h.trans_le (le_max_left u (c*|2*u^2-1|))
    exact ⟨bigger.le,iff_of_false bigger.ne' h.ne'⟩

/-- The lower envelope over all phases, with its precise equality case. -/
theorem sharp_phase {c : ℝ} (hc : 1≤c) (y : ℝ) :
    radius c≤phaseGain c y ∧ (phaseGain c y=radius c ↔ |cos y|=radius c) := by
  simpa only [phaseGain,cos_two_mul,sq_abs] using max_exact hc (abs_nonneg (cos y))

/-- The minimizing phase can be chosen explicitly for each relative gain. -/
theorem attaining_phase {c : ℝ} (hc : 1≤c) : phaseGain c (arccos (radius c))=radius c := by
  obtain ⟨lo,hi⟩ := radius_bounds hc
  have pos := (root_data hc).1
  exact (sharp_phase hc _).2.mpr (by rw [cos_arccos (by linarith only [lo]) hi.le,abs_of_pos pos])

#print axioms radius_bounds
#print axioms sharp_phase
#print axioms attaining_phase

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature
