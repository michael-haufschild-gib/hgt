import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

/-!
# An entire reflected cubic countermodel

The marked cubic `(h^3 - 3*h - 2)/4` has a fixed nodal correspondence with its
reflected exponential multiple. We normalize that correspondence, then remove
its three singularities by exact divided differences. For every real nonzero
mark parameter this produces a real entire reflection-symmetric source with
a global cubic lift and two off-line zeros of exactly order two.

The final existence theorem uses the integer mark `log 2` and has no premises.
This is a countermodel to reflection-only zero selection, not a claim about Xi.
Its formula is differentially algebraic; it does not model Xi hypertranscendence.
-/

noncomputable section
open Complex Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.ReflectedCubicExponentialModel

def cubic (x : ℂ) : ℂ := (x - 2) * (x + 1)^2 / 4

theorem cubic_eq (x : ℂ) : cubic x = (x^3-3*x-2)/4 := by
  dsimp [cubic]
  ring

private theorem entire_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (dslope f c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (by simp)).mpr hf.differentiableOn

def tripleQuotient (f : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  dslope (dslope (dslope f 0) c) (-c)

theorem tripleQuotient_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (tripleQuotient f c) :=
  entire_dslope (entire_dslope (entire_dslope hf 0) c) (-c)

theorem tripleQuotient_factor {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hf0 : f 0 = 0) (hfc : f c = 0) (hfmc : f (-c) = 0) (z : ℂ) :
    z * (z-c) * (z+c) * tripleQuotient f c z = f z := by
  have h1 (w : ℂ) : w * dslope f 0 w = f w := by
    simpa [smul_eq_mul, hf0] using sub_smul_dslope f 0 w
  have h1c : dslope f 0 c = 0 := by
    exact (mul_eq_zero.mp ((h1 c).trans hfc)).resolve_left hc
  have h1mc : dslope f 0 (-c) = 0 := by
    exact (mul_eq_zero.mp ((h1 (-c)).trans hfmc)).resolve_left (neg_ne_zero.mpr hc)
  have h2 (w : ℂ) : (w-c) * dslope (dslope f 0) c w = dslope f 0 w := by
    simpa [smul_eq_mul, h1c] using sub_smul_dslope (dslope f 0) c w
  have hcc : -c-c ≠ 0 := by intro h; apply hc; linear_combination -(1/2 : ℂ)*h
  have h2mc : dslope (dslope f 0) c (-c) = 0 := by
    exact (mul_eq_zero.mp ((h2 (-c)).trans h1mc)).resolve_left hcc
  have h3 (w : ℂ) : (w+c) * tripleQuotient f c w = dslope (dslope f 0) c w := by
    simpa [tripleQuotient, smul_eq_mul, h2mc] using
      sub_smul_dslope (dslope (dslope f 0) c) (-c) w
  linear_combination h1 z + z * h2 z + z * (z-c) * h3 z

def rootThree : ℂ := (Real.sqrt 3 : ℝ)
def anchor : ℂ := 2 * Real.pi / (3 * rootThree)
def seam : ℂ := (2 * Real.pi / 3) * I
def numerator (z : ℂ) : ℂ := (anchor-z) - exp (-z) * (anchor+z)
def quotient : ℂ → ℂ := tripleQuotient numerator seam
def lift (z : ℂ) : ℂ := 2 + (3/2 : ℂ) * (anchor-z)^2 * quotient z

theorem rootThree_sq : rootThree^2 = 3 := by
  dsimp [rootThree]
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))

theorem rootThree_ne_zero : rootThree ≠ 0 := by
  intro h
  have hs := rootThree_sq
  rw [h] at hs
  norm_num at hs

theorem anchor_ne_zero : anchor ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  · exact mul_ne_zero (by norm_num) rootThree_ne_zero

theorem seam_ne_zero : seam ≠ 0 := by
  exact mul_ne_zero (div_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) (by norm_num)) I_ne_zero

theorem seam_sq : seam^2 = -3 * anchor^2 := by
  simp only [seam, anchor, div_pow, mul_pow, I_sq, rootThree_sq]
  ring

theorem exp_neg_seam : exp (-seam) = (-1 - rootThree * I) / 2 := by
  have hc : Real.cos (-2 * Real.pi / 3) = -1/2 := by
    rw [show -2 * Real.pi / 3 = -(2 * (Real.pi / 3)) by ring,
      Real.cos_neg, Real.cos_two_mul, Real.cos_pi_div_three]
    norm_num
  have hs : Real.sin (-2 * Real.pi / 3) = -Real.sqrt 3 / 2 := by
    rw [show -2 * Real.pi / 3 = -(2 * (Real.pi / 3)) by ring,
      Real.sin_neg, Real.sin_two_mul, Real.sin_pi_div_three, Real.cos_pi_div_three]
    ring
  rw [show -seam = ((-2 * Real.pi / 3 : ℝ) : ℂ) * I by
    simp only [seam]; push_cast; ring, exp_ofReal_mul_I, hc, hs]
  simp only [rootThree]
  push_cast
  ring

theorem numerator_zero : numerator 0 = 0 := by simp [numerator]

theorem numerator_seam : numerator seam = 0 := by
  rw [numerator, exp_neg_seam]
  simp only [anchor, seam]
  field_simp [rootThree_ne_zero]
  ring_nf
  simp only [I_sq, rootThree_sq]
  ring

theorem numerator_neg (z : ℂ) : numerator (-z) = -exp z * numerator z := by
  simp only [numerator, neg_neg, sub_neg_eq_add]
  have he : exp z * exp (-z) = 1 := by rw [← exp_add]; simp
  linear_combination -(anchor+z) * he

theorem numerator_neg_seam : numerator (-seam) = 0 := by
  rw [numerator_neg, numerator_seam, mul_zero]

theorem numerator_entire : Differentiable ℂ numerator := by
  change Differentiable ℂ (fun z => (anchor-z) - exp (-z) * (anchor+z))
  fun_prop

theorem quotient_entire : Differentiable ℂ quotient :=
  tripleQuotient_entire numerator_entire seam

theorem lift_entire : Differentiable ℂ lift := by
  have hq := quotient_entire
  change Differentiable ℂ (fun z => 2 + (3/2 : ℂ) * (anchor-z)^2 * quotient z)
  fun_prop

theorem quotient_factor (z : ℂ) : z * (z^2 + 3*anchor^2) * quotient z = numerator z := by
  have h := tripleQuotient_factor seam_ne_zero numerator_zero numerator_seam
    numerator_neg_seam z
  change z * (z-seam) * (z+seam) * quotient z = numerator z at h
  calc
    _ = z * (z-seam) * (z+seam) * quotient z := by
      linear_combination z * quotient z * seam_sq
    _ = _ := h

theorem lift_anchor : lift anchor = 2 := by simp [lift]

theorem lift_neg_anchor : lift (-anchor) = -1 := by
  have h := quotient_factor (-anchor)
  simp only [numerator, sub_neg_eq_add, add_neg_cancel, mul_zero, sub_zero] at h
  have hq : anchor^2 * quotient (-anchor) = -1/2 := by
    apply (mul_left_cancel₀ anchor_ne_zero)
    linear_combination -(1/4 : ℂ) * h
  dsimp [lift]
  linear_combination 6 * hq

theorem quotient_neg (z : ℂ) : quotient (-z) = exp z * quotient z := by
  have hd1 : Differentiable ℂ (fun w => quotient (-w)) := by
    have hq := quotient_entire
    fun_prop
  have hd2 : Differentiable ℂ (fun w => exp w * quotient w) :=
    Complex.differentiable_exp.mul quotient_entire
  have hD : ContinuousAt (fun w : ℂ => w * (w^2+3*anchor^2)) anchor := by fun_prop
  have hDa : anchor * (anchor^2+3*anchor^2) ≠ 0 := by
    convert mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 3 anchor_ne_zero) using 1
    ring
  have heq : (fun w => quotient (-w)) =ᶠ[𝓝 anchor] (fun w => exp w * quotient w) := by
    filter_upwards [hD.eventually_ne hDa] with w hw
    apply mul_left_cancel₀ hw
    have hp := quotient_factor w
    have hm := quotient_factor (-w)
    rw [numerator_neg] at hm
    linear_combination -hm - exp w * hp
  exact congrFun (AnalyticOnNhd.eq_of_eventuallyEq
    (fun w _ => hd1.analyticAt w) (fun w _ => hd2.analyticAt w) heq) z

theorem lift_plus_cross (z : ℂ) :
    (anchor+z) * (lift (-z)+1) = exp z * (anchor-z) * (lift z+1) := by
  have hf := quotient_factor z
  have he : exp z * exp (-z) = 1 := by rw [← exp_add]; simp
  dsimp [lift]
  rw [quotient_neg]
  dsimp [numerator] at hf
  linear_combination 3 * exp z * hf - 3 * (anchor+z) * he

theorem cubic_lift_neg (z : ℂ) : cubic (lift (-z)) = exp z ^ 3 * cubic (lift z) := by
  have hp := congrArg (fun w : ℂ => w^2) (lift_plus_cross z)
  have hm : lift (-z)-2 = (3/2 : ℂ) * (anchor+z)^2 * exp z * quotient z := by
    rw [lift, quotient_neg]
    ring
  have hz : lift z-2 = (3/2 : ℂ) * (anchor-z)^2 * quotient z := by rw [lift]; ring
  simp only [cubic, hm, hz]
  linear_combination (3/8 : ℂ) * exp z * quotient z * hp

theorem anchor_conj : conj anchor = anchor := by simp [anchor, rootThree, map_ofNat]

theorem numerator_conj (z : ℂ) : numerator (conj z) = conj (numerator z) := by
  simp [numerator, map_sub, map_add, map_mul, ← exp_conj, anchor_conj]

private theorem quotient_unique {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (he : ∀ z, z * (z^2+3*anchor^2) * g z = numerator z) : g = quotient := by
  have hD : ContinuousAt (fun w : ℂ => w * (w^2+3*anchor^2)) anchor := by fun_prop
  have hDa : anchor * (anchor^2+3*anchor^2) ≠ 0 := by
    convert mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 3 anchor_ne_zero) using 1
    ring
  apply AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hg.analyticAt z)
    (fun z _ => quotient_entire.analyticAt z)
  filter_upwards [hD.eventually_ne hDa] with z hz
  exact mul_left_cancel₀ hz ((he z).trans (quotient_factor z).symm)

theorem quotient_conj (z : ℂ) : quotient (conj z) = conj (quotient z) := by
  have hd : Differentiable ℂ (fun w => conj (quotient (conj w))) := by
    intro w
    simpa [Function.comp_def] using (quotient_entire (conj w)).conj_conj
  have he := quotient_unique hd (fun w => by
    have h := congrArg conj (quotient_factor (conj w))
    simpa [map_mul, map_add, map_pow, map_ofNat, numerator_conj, anchor_conj] using h)
  simpa using (congrFun he (conj z)).symm

theorem lift_conj (z : ℂ) : lift (conj z) = conj (lift z) := by
  simp [lift, quotient_conj, map_add, map_mul, map_sub, map_pow, map_div₀, map_ofNat, anchor_conj]

theorem quotient_anchor_ne_zero : quotient anchor ≠ 0 := by
  intro hq
  have h := quotient_factor anchor
  rw [hq, mul_zero] at h
  have hn : numerator anchor ≠ 0 := by
    simp [numerator, show anchor+anchor=2*anchor by ring,
      exp_ne_zero, anchor_ne_zero]
  exact hn h.symm

def scaled (L : ℝ) (s : ℂ) : ℂ := (2*L/3) * (s-1/2)
def markedLift (L : ℝ) (s : ℂ) : ℂ := lift (scaled L s)
def source (L : ℝ) (s : ℂ) : ℂ := exp (L*s) * cubic (markedLift L s)
def displacement (L : ℝ) : ℝ := Real.pi / (Real.sqrt 3 * L)
def rightZero (L : ℝ) : ℂ := ((1/2 + displacement L : ℝ) : ℂ)
def rightUnit (L : ℝ) (s : ℂ) : ℂ :=
  (3/8 : ℂ) * exp (L*s) * (2*L/3)^2 * quotient (scaled L s) *
    (lift (scaled L s)+1)^2

theorem markedLift_entire (L : ℝ) : Differentiable ℂ (markedLift L) := by
  apply lift_entire.comp
  change Differentiable ℂ (fun s : ℂ => (2*L/3)*(s-1/2))
  fun_prop

theorem source_entire (L : ℝ) : Differentiable ℂ (source L) := by
  have hh := markedLift_entire L
  change Differentiable ℂ (fun s => exp (L*s) *
    ((markedLift L s-2)*(markedLift L s+1)^2/4))
  fun_prop

theorem rightUnit_entire (L : ℝ) : Differentiable ℂ (rightUnit L) := by
  have hq := quotient_entire
  have hh := lift_entire
  change Differentiable ℂ (fun s : ℂ => (3/8 : ℂ) * exp (L*s) * (2*L/3)^2 *
    quotient ((2*L/3)*(s-1/2)) * (lift ((2*L/3)*(s-1/2))+1)^2)
  fun_prop

theorem source_reflection (L : ℝ) (s : ℂ) : source L (1-s) = source L s := by
  have hs : scaled L (1-s) = -scaled L s := by dsimp [scaled]; ring
  simp only [source, markedLift, hs, cubic_lift_neg]
  rw [← mul_assoc, ← exp_nat_mul, ← exp_add]
  congr 2
  dsimp [scaled]
  ring

theorem source_conj (L : ℝ) (s : ℂ) : source L (conj s) = conj (source L s) := by
  have hs : scaled L (conj s) = conj (scaled L s) := by
    simp [scaled, map_sub, map_mul, map_div₀, map_ofNat]
  simp [source, markedLift, hs, lift_conj, cubic, map_sub, map_add, map_mul,
    map_div₀, map_pow, map_ofNat, ← exp_conj]

theorem source_marked (L : ℝ) (s : ℂ) :
    source L s * exp (-L*s) = cubic (markedLift L s) := by
  have he : exp (L*s) * exp (-L*s) = 1 := by
    rw [← exp_add, show (L : ℂ)*s + -L*s = 0 by ring, exp_zero]
  dsimp [source]
  linear_combination cubic (markedLift L s) * he

theorem displacement_ne_zero {L : ℝ} (hL : L ≠ 0) : displacement L ≠ 0 :=
  div_ne_zero Real.pi_ne_zero (mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)) hL)

theorem rightZero_off_line {L : ℝ} (hL : L ≠ 0) : (rightZero L).re ≠ 1/2 := by
  simpa [rightZero] using displacement_ne_zero hL

theorem scaled_rightZero {L : ℝ} (hL : L ≠ 0) : scaled L (rightZero L) = anchor := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  dsimp [scaled, rightZero, displacement, anchor, rootThree]
  push_cast
  field_simp
  ring

theorem anchor_sub_scaled {L : ℝ} (hL : L ≠ 0) (s : ℂ) :
    anchor - scaled L s = -(2*L/3) * (s-rightZero L) := by
  have h := scaled_rightZero hL
  dsimp [scaled] at *
  linear_combination -h

theorem source_factor {L : ℝ} (hL : L ≠ 0) (s : ℂ) :
    source L s = (s-rightZero L)^2 * rightUnit L s := by
  have hh : lift (scaled L s)-2 =
      (3/2 : ℂ) * (anchor-scaled L s)^2 * quotient (scaled L s) := by rw [lift]; ring
  simp only [source, markedLift, cubic, hh, anchor_sub_scaled hL, rightUnit]
  ring

theorem rightUnit_at_rightZero_ne_zero {L : ℝ} (hL : L ≠ 0) :
    rightUnit L (rightZero L) ≠ 0 := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  simp [rightUnit, scaled_rightZero hL, lift_anchor, exp_ne_zero,
    hLc, quotient_anchor_ne_zero]
  norm_num

theorem source_right_order {L : ℝ} (hL : L ≠ 0) :
    analyticOrderAt (source L) (rightZero L) = 2 := by
  apply ((source_entire L).analyticAt (rightZero L)).analyticOrderAt_eq_natCast.mpr
  exact ⟨rightUnit L, (rightUnit_entire L).analyticAt _,
    rightUnit_at_rightZero_ne_zero hL, Filter.Eventually.of_forall
      (fun s => by simpa [smul_eq_mul] using source_factor hL s)⟩

theorem source_left_order {L : ℝ} (hL : L ≠ 0) :
    analyticOrderAt (source L) (1-rightZero L) = 2 := by
  have hu : Differentiable ℂ (fun s => rightUnit L (1-s)) := by
    have h := rightUnit_entire L
    fun_prop
  apply ((source_entire L).analyticAt (1-rightZero L)).analyticOrderAt_eq_natCast.mpr
  refine ⟨fun s => rightUnit L (1-s), hu.analyticAt _, ?_,
    Filter.Eventually.of_forall (fun s => ?_)⟩
  · simpa using rightUnit_at_rightZero_ne_zero hL
  · rw [← source_reflection L s, source_factor hL]
    simp only [smul_eq_mul]
    ring

theorem source_right_zero {L : ℝ} (hL : L ≠ 0) : source L (rightZero L) = 0 := by
  rw [source_factor hL]
  simp

theorem source_left_zero {L : ℝ} (hL : L ≠ 0) : source L (1-rightZero L) = 0 := by
  rw [source_reflection, source_right_zero hL]

theorem leftZero_off_line {L : ℝ} (hL : L ≠ 0) : (1-rightZero L).re ≠ 1/2 := by
  intro h
  apply rightZero_off_line hL
  simp only [Complex.sub_re, Complex.one_re] at h
  linarith

/-- Reflection, reality and a global cubic lift of the integer-marked source coexist
with a pair of off-line zeros of exact multiplicity two. This is not Xi. -/
theorem exists_reflected_integer_marked_cubic_countermodel :
    ∃ (F h : ℂ → ℂ) (ρ : ℂ), Differentiable ℂ F ∧ Differentiable ℂ h ∧
      (∀ s, F (1-s) = F s) ∧ (∀ s, F (conj s) = conj (F s)) ∧
      (∀ s, F s * exp (-(Real.log 2 : ℂ)*s) = cubic (h s)) ∧
      ρ.re ≠ 1/2 ∧ (1-ρ).re ≠ 1/2 ∧ F ρ = 0 ∧ F (1-ρ) = 0 ∧
      analyticOrderAt F ρ = 2 ∧ analyticOrderAt F (1-ρ) = 2 := by
  have hL : Real.log 2 ≠ 0 := Real.log_ne_zero.mpr (by norm_num)
  exact ⟨source (Real.log 2), markedLift (Real.log 2), rightZero (Real.log 2),
    source_entire _, markedLift_entire _, source_reflection _, source_conj _,
    source_marked _, rightZero_off_line hL, leftZero_off_line hL,
    source_right_zero hL, source_left_zero hL, source_right_order hL, source_left_order hL⟩

end GaloisForLFunctions.HTGeometry.ReflectedCubicExponentialModel
