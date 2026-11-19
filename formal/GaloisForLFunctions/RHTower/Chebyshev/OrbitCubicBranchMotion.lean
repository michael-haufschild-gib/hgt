import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceGeometry
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Motion of the real orbit-cubic roots

The secular equation gives an explicit inverse to each root branch.
Its divided difference exceeds one throughout each pole interval. Thus
the roots move strictly more slowly than the parameter. Their velocities
are the positive derivative residues appearing in the codifferent.
-/

noncomputable section
namespace RHTower.OrbitCubic

/-- The components cut out by the two poles of the secular equation. -/
inductive Branch | left | middle | right

def Branch.contains : Branch → ℝ → Prop
  | .left, x => x < 0
  | .middle, x => 0 < x ∧ x < 1
  | .right, x => 1 < x

private theorem branch_exists (s : Branch) (q : ℝ) :
    ∃ x, s.contains x ∧ binary q x 1 = 0 := by
  obtain ⟨a,b,c,ha,hb,hb',hc,ea,eb,ec⟩ := roots_straddle_poles q
  cases s
  · exact ⟨a,ha,ea⟩
  · exact ⟨b,⟨hb,hb'⟩,eb⟩
  · exact ⟨c,hc,ec⟩

/-- Root in the specified pole interval. -/
def branchRoot (s : Branch) (q : ℝ) : ℝ := Classical.choose (branch_exists s q)

private theorem root_spec (s : Branch) (q : ℝ) :
    s.contains (branchRoot s q) ∧ binary q (branchRoot s q) 1 = 0 :=
  Classical.choose_spec (branch_exists s q)

/-- Parameter determined by a root away from the two poles. -/
def parameterOf (x : ℝ) := x-1/2-x⁻¹-(x-1)⁻¹

private theorem away {s : Branch} {x : ℝ} (h : s.contains x) : x ≠ 0 ∧ x-1 ≠ 0 := by
  cases s with
  | left => change x < 0 at h; exact ⟨h.ne, by linarith⟩
  | middle => exact ⟨h.1.ne', (sub_neg.mpr h.2).ne⟩
  | right => change 1 < x at h; exact ⟨by linarith, (sub_pos.mpr h).ne'⟩

private theorem parameter_factor {s : Branch} {x : ℝ} (hx : s.contains x) (q : ℝ) :
    binary q x 1 = (x*(x-1))*(parameterOf x-q) := by
  rw [arrowhead_secular]
  unfold parameterOf
  field_simp [(away hx).1,(away hx).2]
  ring

private theorem parameter_root (s : Branch) (q : ℝ) : parameterOf (branchRoot s q) = q := by
  obtain ⟨hl,he⟩ := root_spec s q
  rw [parameter_factor hl] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (away hl).1 (away hl).2))

private def stiffness (x y : ℝ) := 1+(x*y)⁻¹+((x-1)*(y-1))⁻¹

private theorem stiffness_gt {s : Branch} {x y : ℝ} (hx : s.contains x) (hy : s.contains y) :
    1 < stiffness x y := by
  have hp : 0 < x*y ∧ 0 < (x-1)*(y-1) := by
    cases s with
    | left =>
      exact ⟨mul_pos_of_neg_of_neg hx hy,mul_pos_of_neg_of_neg
        (by change x < 0 at hx; linarith) (by change y < 0 at hy; linarith)⟩
    | middle =>
      exact ⟨mul_pos hx.1 hy.1,mul_pos_of_neg_of_neg (sub_neg.mpr hx.2) (sub_neg.mpr hy.2)⟩
    | right =>
      change 1 < x at hx
      change 1 < y at hy
      exact ⟨mul_pos (by linarith) (by linarith),mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)⟩
  unfold stiffness
  linarith only [inv_pos.mpr hp.1, inv_pos.mpr hp.2]

private theorem parameter_secant {s : Branch} {x y : ℝ} (hx : s.contains x) (hy : s.contains y) :
    parameterOf x - parameterOf y = (x-y)*stiffness x y := by
  unfold parameterOf stiffness
  field_simp [(away hx).1,(away hx).2,(away hy).1,(away hy).2]
  ring

/-- Each whole pole interval is parametrized by exactly one root branch. -/
theorem branchRoot_iff (s : Branch) (q x : ℝ) :
    branchRoot s q = x ↔ s.contains x ∧ binary q x 1 = 0 := by
  constructor
  · rintro rfl
    exact root_spec s q
  · rintro ⟨hx,he⟩
    rw [parameter_factor hx] at he
    have hp := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (away hx).1 (away hx).2))
    have hf := parameter_secant (root_spec s q).1 hx
    rw [parameter_root,hp,sub_self] at hf
    have hn : stiffness (branchRoot s q) x ≠ 0 := by linarith only [stiffness_gt (root_spec s q).1 hx]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf.symm).resolve_right hn)

/-- Finite displacement is completely determined by the two endpoint roots. -/
theorem branch_displacement (s : Branch) (p q : ℝ) :
    let x := branchRoot s p
    let y := branchRoot s q
    p-q = (x-y)*(1+(x*y)⁻¹+((x-1)*(y-1))⁻¹) := by
  simpa only [parameter_root,stiffness] using parameter_secant (root_spec s p).1 (root_spec s q).1

/-- The three roots increase strictly, with every nonzero secant slope below one. -/
theorem branch_increment (s : Branch) (q h : ℝ) :
    0 < branchRoot s (q+Real.exp h)-branchRoot s q ∧
      branchRoot s (q+Real.exp h)-branchRoot s q < Real.exp h := by
  let x := branchRoot s (q+Real.exp h)
  let y := branchRoot s q
  have he : Real.exp h = (x-y)*stiffness x y := by
    simpa only [add_sub_cancel_left,x,y,stiffness] using branch_displacement s (q+Real.exp h) q
  have hc : 1 < stiffness x y := stiffness_gt (root_spec s _).1 (root_spec s _).1
  have hxy : 0 < x-y := pos_of_mul_pos_left (he ▸ Real.exp_pos h) (by linarith only [hc])
  change 0 < x-y ∧ x-y < Real.exp h
  exact ⟨hxy, by rw [he]; simpa only [mul_one] using mul_lt_mul_of_pos_left hc hxy⟩

theorem branch_lipschitz (s : Branch) : LipschitzWith 1 (branchRoot s) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro p q
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  have hf := congrArg abs (parameter_secant (root_spec s p).1 (root_spec s q).1)
  have hs := stiffness_gt (root_spec s p).1 (root_spec s q).1
  rw [parameter_root,parameter_root,abs_mul,abs_of_pos (by linarith only [hs] :
    0 < stiffness (branchRoot s p) (branchRoot s q))] at hf
  rw [hf]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hs.le (abs_nonneg (branchRoot s p-branchRoot s q))

/-- Inverse squared eigenvector norm is the exact branch velocity. -/
theorem branch_hasDerivAt (s : Branch) (q : ℝ) :
    let x := branchRoot s q
    HasDerivAt (branchRoot s) (1+(x^2)⁻¹+((x-1)^2)⁻¹)⁻¹ q := by
  let x := branchRoot s q
  obtain ⟨h0,h1⟩ := away (root_spec s q).1
  have hf : HasDerivAt parameterOf (1+(x^2)⁻¹+((x-1)^2)⁻¹) x := by
    have hi := ((hasDerivAt_id x).sub_const 1).inv h1
    have hd := (((hasDerivAt_id x).sub_const (1/2:ℝ)).sub (hasDerivAt_inv (x := x) h0)).sub hi
    change HasDerivAt parameterOf (1-(-(x^2)⁻¹)-(-1/(x-1)^2)) x at hd
    simpa only [neg_div,one_div,sub_neg_eq_add] using hd
  have hp : 1 < 1+(x^2)⁻¹+((x-1)^2)⁻¹ := by
    simpa only [stiffness,← pow_two] using stiffness_gt (root_spec s q).1 (root_spec s q).1
  exact hf.of_local_left_inverse (branch_lipschitz s).continuous.continuousAt (by linarith only [hp])
    (Filter.Eventually.of_forall (parameter_root s))

private theorem residue_denominator (x : ℝ) (h0 : x≠0) (h1 : x-1≠0) :
    3*x^2-2*(parameterOf x+3/2)*x+parameterOf x-3/2 = x*(x-1)*stiffness x x := by
  simp only [parameterOf,stiffness,mul_inv_rev]
  field_simp [h0,h1]
  ring

/-- The trace-dual numerator divided by the ordinary cubic derivative is
the velocity of each root as the orbit parameter changes. -/
theorem branch_deriv_residue (s : Branch) (q : ℝ) :
    let x := branchRoot s q
    deriv (branchRoot s) q = x*(x-1)/(3*x^2-2*(q+3/2)*x+q-3/2) := by
  let x := branchRoot s q
  obtain ⟨h0,h1⟩ := away (root_spec s q).1
  have hs : 0 < stiffness x x := by linarith only [stiffness_gt (root_spec s q).1 (root_spec s q).1]
  have hf : 3*x^2-2*(q+3/2)*x+q-3/2 = (x*(x-1))*stiffness x x := by
    conv_lhs => rw [← parameter_root s q]
    exact residue_denominator x h0 h1
  change deriv (branchRoot s) q = x*(x-1)/_
  rw [(branch_hasDerivAt s q).deriv,hf]
  change (1+(x^2)⁻¹+((x-1)^2)⁻¹)⁻¹ = _
  simp only [pow_two]
  change (stiffness x x)⁻¹ = _
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero h0 h1) hs.ne')).mpr
  rw [mul_left_comm,inv_mul_cancel₀ hs.ne',mul_one]

end RHTower.OrbitCubic
