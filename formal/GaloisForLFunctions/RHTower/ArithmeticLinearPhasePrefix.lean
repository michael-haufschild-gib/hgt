import GaloisForLFunctions.RHTower.ZetaCentredSawtoothContinuation
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Exact signs of constant-speed Bernoulli phase prefixes

For the actual periodic quadratic `b(x)=(fract(x)^(2 : ℕ)-fract(x))/2`, every
constant-speed prefix `integral_0^A b(x) sin(lam*x) dx` is nonpositive when
`0 < lam < 2*pi` and `A >= 0`. At a complete phase turn its value is an exact
function of the fractional endpoint; equality holds precisely at integer endpoints.

Individual complete turns need not be nonpositive: the second turn at frequency
`4*pi/3` is strictly positive. Thus nonpositive prefixes can retain positive blocks.
These are statements about a constant-speed model. They do not transfer its sign
to the logarithmic phase of the zeta remainder and supply no zero-exclusion law.
The proofs use finite integration, trigonometric identities, and order arguments.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- The constant-speed integral of the actual periodic quadratic, anchored at zero. -/
def linearPhasePrefix (lam A : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..A, RHTower.bernoulliPeriodic x * Real.sin (lam*x)

private def phasePrimitive (lam m x : ℝ) : ℝ :=
  -((x-m)^(2 : ℕ)-(x-m))/2 * Real.cos (lam*x)/lam +
    (x-m-1/2)*Real.sin (lam*x)/lam^(2 : ℕ) + Real.cos (lam*x)/lam^(3 : ℕ)

private theorem phasePrimitive_deriv {lam : ℝ} (hlam : lam ≠ 0) (m x : ℝ) :
    HasDerivAt (phasePrimitive lam m)
      (((x-m)^(2 : ℕ)-(x-m))/2 * Real.sin (lam*x)) x := by
  have hy := (hasDerivAt_id x).sub_const m
  have hb := ((hy.pow 2).sub hy).neg.div_const 2
  have hc := (Real.hasDerivAt_cos (lam*x)).comp x ((hasDerivAt_id x).const_mul lam)
  have hs := (Real.hasDerivAt_sin (lam*x)).comp x ((hasDerivAt_id x).const_mul lam)
  have h := (((hb.mul hc).div_const lam).add
    (((hy.sub_const (1/2)).mul hs).div_const (lam^(2 : ℕ)))).add (hc.div_const (lam^(3 : ℕ)))
  convert! h using 1
  dsimp [phasePrimitive]
  norm_num
  field_simp [hlam]
  ring

private theorem phase_integrable (lam a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => RHTower.bernoulliPeriodic x * Real.sin (lam*x))
      volume a b := by
  have hc : Continuous RHTower.bernoulliPeriodic :=
    (show Continuous (fun x : ℝ => (x^(2 : ℕ)-x)/2) by fun_prop).continuousOn.comp_fract'' (by norm_num)
  exact (hc.mul (by fun_prop)).intervalIntegrable a b

private theorem phase_cell_eq {lam r : ℝ} (hlam : lam ≠ 0) (m : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (∫ x in (m:ℝ)..((m:ℝ)+r), RHTower.bernoulliPeriodic x * Real.sin (lam*x)) =
      phasePrimitive lam m ((m:ℝ)+r) - phasePrimitive lam m m := by
  have he : (∫ x in (m:ℝ)..((m:ℝ)+r),
      RHTower.bernoulliPeriodic x * Real.sin (lam*x)) =
      ∫ x in (m:ℝ)..((m:ℝ)+r),
        (((x-(m:ℝ))^(2 : ℕ)-(x-(m:ℝ)))/2) * Real.sin (lam*x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    by_cases hxe : x = (m:ℝ)+1
    · subst x
      simp [RHTower.bernoulliPeriodic]
    · have hxl : x < (m:ℝ)+1 := lt_of_le_of_ne (by linarith [hx.2]) hxe
      have hf : Int.floor x = (m:ℤ) := Int.floor_eq_iff.mpr (by simpa using And.intro hx.1 hxl)
      simp [RHTower.bernoulliPeriodic, Int.fract, hf]
  rw [he]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => phasePrimitive_deriv hlam m x) (by
      apply Continuous.intervalIntegrable
      fun_prop)

private theorem phase_prefix_nat {lam : ℝ} (hlam : lam ≠ 0) (m : ℕ) :
    linearPhasePrefix lam m =
      -(1/2)*Real.sin (lam*(m:ℝ))/lam^(2 : ℕ) + (Real.cos (lam*(m:ℝ))-1)/lam^(3 : ℕ) +
        (∑ j ∈ Finset.range m, Real.sin (lam*((j:ℝ)+1)))/lam^(2 : ℕ) := by
  induction m with
  | zero => simp [linearPhasePrefix]
  | succ m ih =>
    have h := intervalIntegral.integral_add_adjacent_intervals
      (phase_integrable lam 0 m) (phase_integrable lam m ((m:ℝ)+1))
    change linearPhasePrefix lam m + _ = linearPhasePrefix lam ((m:ℝ)+1) at h
    rw [phase_cell_eq hlam m (by norm_num) (by norm_num), ih] at h
    simp only [Nat.cast_succ, Finset.sum_range_succ]
    rw [← h]
    simp only [phasePrimitive]
    ring

/-- Exact finite-cell decomposition, including the fractional cell and every slope jump. -/
theorem linearPhasePrefix_eq_finite_endpoint {lam r : ℝ} (hlam : lam ≠ 0)
    (m : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    linearPhasePrefix lam ((m:ℝ)+r) =
      -(r^(2 : ℕ)-r)/2 * Real.cos (lam*((m:ℝ)+r))/lam +
        (r-1/2)*Real.sin (lam*((m:ℝ)+r))/lam^(2 : ℕ) +
        (Real.cos (lam*((m:ℝ)+r))-1)/lam^(3 : ℕ) +
        (∑ j ∈ Finset.range m, Real.sin (lam*((j:ℝ)+1)))/lam^(2 : ℕ) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (phase_integrable lam 0 m) (phase_integrable lam m ((m:ℝ)+r))
  change linearPhasePrefix lam m + _ = linearPhasePrefix lam ((m:ℝ)+r) at h
  rw [phase_cell_eq hlam m hr0 hr1, phase_prefix_nat hlam m] at h
  rw [← h]
  simp only [phasePrimitive]
  ring

private theorem phase_sine_sum (lam : ℝ) (m : ℕ) :
    (2*Real.sin (lam/2))*(∑ j ∈ Finset.range m, Real.sin (lam*((j:ℝ)+1))) =
      Real.cos (lam/2)-Real.cos (lam*((m:ℝ)+1/2)) := by
  induction m with
  | zero => simp [div_eq_mul_inv]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have he : 2*Real.sin (lam/2)*Real.sin (lam*((m:ℝ)+1)) =
        Real.cos (lam*((m:ℝ)+1/2))-Real.cos (lam*((m:ℝ)+3/2)) := by
      have h := Real.cos_sub (lam*((m:ℝ)+1)) (lam/2)
      have h' := Real.cos_add (lam*((m:ℝ)+1)) (lam/2)
      rw [show lam*((m:ℝ)+1)-lam/2=lam*((m:ℝ)+1/2) by ring] at h
      rw [show lam*((m:ℝ)+1)+lam/2=lam*((m:ℝ)+3/2) by ring] at h'
      nlinarith [h, h']
    rw [he]
    push_cast
    rw [show (m:ℝ)+1+1/2=(m:ℝ)+3/2 by ring]
    ring

/-- At a complete turn, the finite sine sum reduces to the fractional endpoint. -/
theorem linearPhasePrefix_eq_complete_turn {lam r : ℝ}
    (hlam : 0 < lam) (hlam' : lam < 2*Real.pi) (m K : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hturn : lam*((m:ℝ)+r)=2*Real.pi*K) :
    linearPhasePrefix lam ((m:ℝ)+r) = r*(1-r)/(2*lam) -
      Real.sin (r*lam/2)*Real.sin ((1-r)*lam/2)/(lam^(2 : ℕ)*Real.sin (lam/2)) := by
  have hsin : Real.sin (lam*((m:ℝ)+r))=0 := by
    rw [hturn]
    simpa [mul_comm, mul_left_comm, mul_assoc] using Real.sin_add_nat_mul_two_pi 0 K
  have hcos : Real.cos (lam*((m:ℝ)+r))=1 := by
    rw [hturn]
    simpa [mul_comm, mul_left_comm, mul_assoc] using Real.cos_add_nat_mul_two_pi 0 K
  have hsn : Real.sin (lam/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hsum := phase_sine_sum lam m
  have hc : Real.cos (lam*((m:ℝ)+1/2))=Real.cos ((1/2-r)*lam) := by
    rw [show lam*((m:ℝ)+1/2)=lam*((m:ℝ)+r)-((r-1/2)*lam) by ring,
      Real.cos_sub, hsin, hcos]
    simp only [one_mul, zero_mul, add_zero]
    rw [show (r-1/2)*lam=-((1/2-r)*lam) by ring, Real.cos_neg]
  have hp : Real.cos (lam/2)-Real.cos ((1/2-r)*lam) =
      -2*Real.sin (r*lam/2)*Real.sin ((1-r)*lam/2) := by
    have h1 := Real.cos_add (r*lam/2) ((1-r)*lam/2)
    have h2 := Real.cos_sub ((1-r)*lam/2) (r*lam/2)
    rw [show r*lam/2+(1-r)*lam/2=lam/2 by ring] at h1
    rw [show (1-r)*lam/2-r*lam/2=(1/2-r)*lam by ring] at h2
    nlinarith [h1,h2]
  rw [hc,hp] at hsum
  have he : (∑ j ∈ Finset.range m, Real.sin (lam*((j:ℝ)+1))) =
      -Real.sin (r*lam/2)*Real.sin ((1-r)*lam/2)/Real.sin (lam/2) := by
    apply (eq_div_iff hsn).mpr
    nlinarith [hsum]
  rw [linearPhasePrefix_eq_finite_endpoint hlam.ne' m hr0 hr1, hsin, hcos, he]
  ring

private theorem sin_sub_mul_cos_pos {y : ℝ} (hy : 0 < y) (hy' : y < Real.pi) :
    y*Real.cos y < Real.sin y := by
  have hd (x : ℝ) : HasDerivAt (fun z : ℝ => Real.sin z-z*Real.cos z)
      (x*Real.sin x) x := by
    convert! (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1
    simp [id_eq]
  have hm : StrictMonoOn (fun z : ℝ => Real.sin z-z*Real.cos z) (Icc 0 Real.pi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by fun_prop)
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    exact mul_pos hx.1 (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)
  have h := hm (show (0:ℝ) ∈ Icc 0 Real.pi by exact ⟨le_rfl,Real.pi_pos.le⟩)
    (show y ∈ Icc 0 Real.pi from ⟨hy.le,hy'.le⟩) hy
  simpa using h

/-- The endpoint inequality is strict for every genuine split of an angle below pi. -/
theorem phase_endpoint_strict_inequality {x r : ℝ} (hx : 0 < x) (hx' : x < Real.pi)
    (hr : 0 < r) (hr' : r < 1) :
    x*r*(1-r)*Real.sin x < Real.sin (r*x)*Real.sin ((1-r)*x) := by
  have ha0 : 0 < r*x := mul_pos hr hx
  have hb0 : 0 < (1-r)*x := mul_pos (by linarith) hx
  have ha1 : r*x < Real.pi := lt_trans (by nlinarith : r*x<x) hx'
  have hb1 : (1-r)*x < Real.pi := lt_trans (by nlinarith : (1-r)*x<x) hx'
  have hsa := Real.sin_pos_of_pos_of_lt_pi ha0 ha1
  have hsb := Real.sin_pos_of_pos_of_lt_pi hb0 hb1
  have ha := mul_lt_mul_of_pos_right (sin_sub_mul_cos_pos ha0 ha1)
    (mul_pos (by linarith : 0<1-r) hsb)
  have hb := mul_lt_mul_of_pos_right (sin_sub_mul_cos_pos hb0 hb1) (mul_pos hr hsa)
  have hadd : Real.sin x = Real.sin (r*x)*Real.cos ((1-r)*x)+
      Real.cos (r*x)*Real.sin ((1-r)*x) := by
    rw [← Real.sin_add]
    congr 1
    ring
  rw [hadd]
  nlinarith [ha,hb]

/-- A noninteger complete-turn endpoint gives a strictly negative prefix. -/
theorem linearPhasePrefix_complete_turn_neg {lam r : ℝ}
    (hlam : 0 < lam) (hlam' : lam < 2*Real.pi) (m K : ℕ)
    (hr0 : 0 < r) (hr1 : r < 1) (hturn : lam*((m:ℝ)+r)=2*Real.pi*K) :
    linearPhasePrefix lam ((m:ℝ)+r) < 0 := by
  rw [linearPhasePrefix_eq_complete_turn hlam hlam' m K hr0.le hr1.le hturn]
  have hi := phase_endpoint_strict_inequality (by linarith : 0<lam/2)
    (by linarith : lam/2<Real.pi) hr0 hr1
  have hs := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0<lam/2)
    (by linarith : lam/2<Real.pi)
  have hd : 0 < lam^(2 : ℕ)*Real.sin (lam/2) := mul_pos (sq_pos_of_pos hlam) hs
  apply sub_neg.mpr
  apply (lt_div_iff₀ hd).mpr
  convert! hi using 1 <;> field_simp [hlam.ne']

/-- Every complete-turn prefix has nonpositive sign, including the cell boundaries. -/
theorem linearPhasePrefix_complete_turn_nonpos {lam r : ℝ}
    (hlam : 0 < lam) (hlam' : lam < 2*Real.pi) (m K : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hturn : lam*((m:ℝ)+r)=2*Real.pi*K) :
    linearPhasePrefix lam ((m:ℝ)+r) ≤ 0 := by
  rcases eq_or_lt_of_le hr0 with h0 | h0
  · subst r
    rw [linearPhasePrefix_eq_complete_turn hlam hlam' m K hr0 hr1 hturn]
    simp
  rcases eq_or_lt_of_le hr1 with h1 | h1
  · subst r
    rw [linearPhasePrefix_eq_complete_turn hlam hlam' m K hr0 hr1 hturn]
    simp
  exact (linearPhasePrefix_complete_turn_neg hlam hlam' m K h0 h1 hturn).le

/-- The complete-turn equality cases are exactly the integer endpoints. -/
theorem linearPhasePrefix_complete_turn_eq_zero_iff {lam r : ℝ}
    (hlam : 0 < lam) (hlam' : lam < 2*Real.pi) (m K : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hturn : lam*((m:ℝ)+r)=2*Real.pi*K) :
    linearPhasePrefix lam ((m:ℝ)+r) = 0 ↔ r = 0 := by
  constructor
  · intro he
    by_contra hn
    have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hn)
    have h := linearPhasePrefix_complete_turn_neg hlam hlam' m K hrp hr1 hturn
    linarith
  · intro he
    subst r
    rw [linearPhasePrefix_eq_complete_turn hlam hlam' m K hr0 hr1.le hturn]
    simp

/-- The endpoint formula at every natural turn number; floor supplies exhaustive coverage. -/
theorem linearPhasePrefix_at_turn {lam : ℝ} (hlam : 0 < lam)
    (hlam' : lam < 2*Real.pi) (K : ℕ) :
    let A := 2*Real.pi*K/lam
    let r := Int.fract A
    linearPhasePrefix lam A = r*(1-r)/(2*lam) -
      Real.sin (r*lam/2)*Real.sin ((1-r)*lam/2)/(lam^(2 : ℕ)*Real.sin (lam/2)) := by
  dsimp only
  let A := 2*Real.pi*K/lam
  have ha : 0 ≤ A := by dsimp [A]; positivity
  have he : (⌊A⌋₊:ℝ)+Int.fract A=A := by
    rw [natCast_floor_eq_intCast_floor ha, Int.floor_add_fract]
  have ht : lam*((⌊A⌋₊:ℝ)+Int.fract A)=2*Real.pi*K := by
    rw [he]
    dsimp [A]
    field_simp
  have h := linearPhasePrefix_eq_complete_turn hlam hlam' ⌊A⌋₊ K
    (Int.fract_nonneg A) (Int.fract_lt_one A).le ht
  rw [he] at h
  exact h

/-- All natural turn numbers satisfy the sign law, with no endpoint-selection premise. -/
theorem linearPhasePrefix_at_turn_nonpos {lam : ℝ} (hlam : 0 < lam)
    (hlam' : lam < 2*Real.pi) (K : ℕ) :
    linearPhasePrefix lam (2*Real.pi*K/lam) ≤ 0 := by
  let A := 2*Real.pi*K/lam
  have ha : 0 ≤ A := by dsimp [A]; positivity
  have he : (⌊A⌋₊:ℝ)+Int.fract A=A := by
    rw [natCast_floor_eq_intCast_floor ha, Int.floor_add_fract]
  have ht : lam*((⌊A⌋₊:ℝ)+Int.fract A)=2*Real.pi*K := by
    rw [he]
    dsimp [A]
    field_simp
  have h := linearPhasePrefix_complete_turn_nonpos hlam hlam' ⌊A⌋₊ K
    (Int.fract_nonneg A) (Int.fract_lt_one A).le ht
  rw [he] at h
  exact h

/-- Exact classification of all natural-turn equalities by their fractional endpoint. -/
theorem linearPhasePrefix_at_turn_eq_zero_iff {lam : ℝ} (hlam : 0 < lam)
    (hlam' : lam < 2*Real.pi) (K : ℕ) :
    linearPhasePrefix lam (2*Real.pi*K/lam) = 0 ↔ Int.fract (2*Real.pi*K/lam) = 0 := by
  let A := 2*Real.pi*K/lam
  have ha : 0 ≤ A := by dsimp [A]; positivity
  have he : (⌊A⌋₊:ℝ)+Int.fract A=A := by
    rw [natCast_floor_eq_intCast_floor ha, Int.floor_add_fract]
  have ht : lam*((⌊A⌋₊:ℝ)+Int.fract A)=2*Real.pi*K := by
    rw [he]
    dsimp [A]
    field_simp
  have h := linearPhasePrefix_complete_turn_eq_zero_iff hlam hlam' ⌊A⌋₊ K
    (Int.fract_nonneg A) (Int.fract_lt_one A) ht
  rw [he] at h
  exact h

/-- A positive complete turn can restore a negative prefix exactly to zero. -/
theorem linearPhase_second_turn_pos :
    0 < ∫ x in (3/2:ℝ)..3,
      RHTower.bernoulliPeriodic x * Real.sin ((4*Real.pi/3)*x) := by
  have hl : 0 < 4*Real.pi/3 := by positivity
  have hl' : 4*Real.pi/3 < 2*Real.pi := by nlinarith [Real.pi_pos]
  have hneg := linearPhasePrefix_complete_turn_neg hl hl' 1 1
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) (by push_cast; ring)
  have he : linearPhasePrefix (4*Real.pi/3) 3=0 := by
    have h := linearPhasePrefix_complete_turn_eq_zero_iff hl hl' 3 2
      (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)<1) (by push_cast; ring)
    simpa using h.mpr rfl
  have h := intervalIntegral.integral_add_adjacent_intervals
    (phase_integrable (4*Real.pi/3) 0 (3/2)) (phase_integrable (4*Real.pi/3) (3/2) 3)
  change linearPhasePrefix (4*Real.pi/3) (3/2)+_=linearPhasePrefix (4*Real.pi/3) 3 at h
  norm_num at hneg
  linarith

/-- Every finite prefix is nonpositive: inside a turn, its maximum is at an endpoint. -/
theorem linearPhasePrefix_nonpos {lam A : ℝ} (hlam : 0 < lam)
    (hlam' : lam < 2*Real.pi) (hA : 0 ≤ A) : linearPhasePrefix lam A ≤ 0 := by
  let K := ⌊lam*A/(2*Real.pi)⌋₊
  let L := 2*Real.pi*K/lam
  let U := 2*Real.pi*(K+1)/lam
  have hp : 0 < 2*Real.pi := by positivity
  have hk0 := Nat.floor_le (show 0 ≤ lam*A/(2*Real.pi) by positivity)
  have hk1 := Nat.lt_floor_add_one (lam*A/(2*Real.pi))
  have hLA : L ≤ A := by
    apply (div_le_iff₀ hlam).mpr
    have h := (le_div_iff₀ hp).mp hk0
    dsimp [K] at *
    nlinarith [h]
  have hAU : A ≤ U := by
    apply (le_div_iff₀ hlam).mpr
    have h := (div_lt_iff₀ hp).mp hk1
    dsimp [K] at *
    nlinarith [h]
  have hL : lam*L=2*Real.pi*K := by dsimp [L]; field_simp
  have hU : lam*U=2*Real.pi*(K+1) := by dsimp [U]; field_simp
  have hb (x : ℝ) : RHTower.bernoulliPeriodic x ≤ 0 := by
    dsimp [RHTower.bernoulliPeriodic]
    have hz := Int.fract_nonneg x
    have ho := Int.fract_lt_one x
    nlinarith [mul_nonneg hz (show 0 ≤ 1-Int.fract x by linarith)]
  have hshift (x : ℝ) : Real.sin (lam*x)=Real.sin (lam*x-2*Real.pi*K) := by
    have h := Real.sin_add_nat_mul_two_pi (lam*x-2*Real.pi*K) K
    convert h using 1
    congr 1
    ring
  by_cases hh : lam*A-2*Real.pi*K ≤ Real.pi
  · have hn : 0 ≤ ∫ x in L..A, -(RHTower.bernoulliPeriodic x*Real.sin (lam*x)) := by
      apply intervalIntegral.integral_nonneg hLA
      intro x hx
      have hx0 : 0 ≤ lam*x-2*Real.pi*K := by nlinarith [hx.1]
      have hx1 : lam*x-2*Real.pi*K ≤ Real.pi := by nlinarith [hx.2]
      rw [neg_nonneg, hshift]
      exact mul_nonpos_of_nonpos_of_nonneg (hb x)
        (Real.sin_nonneg_of_nonneg_of_le_pi hx0 hx1)
    rw [intervalIntegral.integral_neg] at hn
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (phase_integrable lam 0 L) (phase_integrable lam L A)
    change linearPhasePrefix lam L+_=linearPhasePrefix lam A at hadd
    have hle := linearPhasePrefix_at_turn_nonpos hlam hlam' K
    change linearPhasePrefix lam L ≤ 0 at hle
    linarith
  · have hn : 0 ≤ ∫ x in A..U, RHTower.bernoulliPeriodic x*Real.sin (lam*x) := by
      apply intervalIntegral.integral_nonneg hAU
      intro x hx
      have hx0 : -Real.pi ≤ lam*x-2*Real.pi*(K+1) := by nlinarith [hx.1]
      have hx1 : lam*x-2*Real.pi*(K+1) ≤ 0 := by nlinarith [hx.2]
      have hsh : Real.sin (lam*x)=Real.sin (lam*x-2*Real.pi*(K+1)) := by
        have h := Real.sin_add_nat_mul_two_pi (lam*x-2*Real.pi*(K+1)) (K+1)
        convert h using 1
        push_cast
        congr 1
        ring
      rw [hsh]
      exact mul_nonneg_of_nonpos_of_nonpos (hb x)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le hx1 hx0)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (phase_integrable lam 0 A) (phase_integrable lam A U)
    change linearPhasePrefix lam A+_=linearPhasePrefix lam U at hadd
    have hle := linearPhasePrefix_at_turn_nonpos hlam hlam' (K+1)
    push_cast at hle
    change linearPhasePrefix lam U ≤ 0 at hle
    linarith

end RHTower.DeletionMixedRefinement
