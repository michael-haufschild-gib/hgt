import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel
import GaloisForLFunctions.HTGeometry.DiscreteAbelRing

/-!
# The Dirichlet kernel for square-root Abel means

The reciprocal clock `u(x)=sqrt x+sqrt(x+1)` satisfies
`u(x)*(sqrt(x+1)-sqrt x)=1`. Multiplying the unit Dirichlet difference by
this clock gives a kernel of size `O(x^(-Re(s)-1/2))`. Its next unit
difference is `O(x^(-Re(s)-3/2))`, the summable gain needed for a second
Abel summation against a linearly bounded weighted prefix.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower
open GaloisForLFunctions.RHTower

/-- The reciprocal of the unit square-root increment. -/
def squareRootAbelReciprocalClock (x : ℝ) : ℝ := Real.sqrt x+Real.sqrt (x+1)

/-- Unit Dirichlet difference multiplied by the reciprocal square-root clock. -/
def squareRootAbelDirichletKernel (x : ℝ) (s : ℂ) : ℂ :=
  (squareRootAbelReciprocalClock x : ℂ)*((x:ℂ)^(-s)-((x+1:ℝ):ℂ)^(-s))

/-- The reciprocal clock is nonnegative. -/
theorem squareRootAbelReciprocalClock_nonneg (x : ℝ) : 0 ≤ squareRootAbelReciprocalClock x := by
  unfold squareRootAbelReciprocalClock
  positivity

/-- Exact cancellation of the clock increment, including the endpoint zero. -/
theorem squareRootAbelReciprocalClock_mul_step {x : ℝ} (hx : 0 ≤ x) :
    squareRootAbelReciprocalClock x*(Real.sqrt (x+1)-Real.sqrt x)=1 := by
  unfold squareRootAbelReciprocalClock
  nlinarith [Real.sq_sqrt hx,Real.sq_sqrt (show 0 ≤ x+1 by linarith)]

/-- A uniform square-root envelope from scale one onward. -/
theorem squareRootAbelReciprocalClock_le {x : ℝ} (hx : 1 ≤ x) :
    squareRootAbelReciprocalClock x ≤ 3*Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hh : Real.sqrt (x+1) ≤ 2*Real.sqrt x := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hx0]
  unfold squareRootAbelReciprocalClock
  linarith

/-- The next clock difference has inverse-square-root size. -/
theorem abs_squareRootAbelReciprocalClock_step_le {x : ℝ} (hx : 0 < x) :
    |squareRootAbelReciprocalClock (x+1)-squareRootAbelReciprocalClock x| ≤ 1/Real.sqrt x := by
  have hmono : Real.sqrt x ≤ Real.sqrt (x+2) := Real.sqrt_le_sqrt (by linarith)
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have he : squareRootAbelReciprocalClock (x+1)-squareRootAbelReciprocalClock x =
      Real.sqrt (x+2)-Real.sqrt x := by
    unfold squareRootAbelReciprocalClock
    rw [show x+1+1=x+2 by ring]
    ring
  rw [he,abs_of_nonneg (sub_nonneg.mpr hmono)]
  apply (le_div_iff₀ hspos).mpr
  nlinarith [Real.sq_sqrt hx.le,Real.sq_sqrt (show 0 ≤ x+2 by linarith),
    sq_nonneg (Real.sqrt (x+2)-Real.sqrt x)]

private theorem sqrt_mul_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Real.sqrt x*x^y=x^(y+1/2) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_add hx]
  congr 1
  ring

private theorem rpow_div_sqrt {x : ℝ} (hx : 0 < x) (y : ℝ) :
    x^y/Real.sqrt x=x^(y-1/2) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_sub hx]

/-- The first weighted Dirichlet kernel gains one half power. -/
theorem norm_squareRootAbelDirichletKernel_le {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : 0 < s.re) :
    ‖squareRootAbelDirichletKernel x s‖ ≤ 3*‖s‖*x^(-s.re-1/2) := by
  have hx0 : 0 < x := by linarith
  unfold squareRootAbelDirichletKernel
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (squareRootAbelReciprocalClock_nonneg x)]
  calc
    _ ≤ (3*Real.sqrt x)*(‖s‖*x^(-s.re-1)) :=
      mul_le_mul (squareRootAbelReciprocalClock_le hx) (norm_cpow_unit_diff_le hs hx0)
        (norm_nonneg _) (by positivity)
    _ = (3*‖s‖)*(Real.sqrt x*x^(-s.re-1)) := by ring
    _ = _ := by
      rw [sqrt_mul_rpow hx0]
      congr 2
      ring

/-- The next unit difference gains a further full power. -/
theorem norm_squareRootAbelDirichletKernel_sub_succ_le {x : ℝ} (hx : 1 ≤ x) {s : ℂ}
    (hs : 0 < s.re) :
    ‖squareRootAbelDirichletKernel x s-squareRootAbelDirichletKernel (x+1) s‖ ≤
      (3*‖s‖*‖s+1‖+‖s‖)*x^(-s.re-3/2) := by
  have hx0 : 0 < x := by linarith
  have he : squareRootAbelDirichletKernel x s-squareRootAbelDirichletKernel (x+1) s =
      (squareRootAbelReciprocalClock x:ℂ)*
        ((x:ℂ)^(-s)-2*((x+1:ℝ):ℂ)^(-s)+((x+2:ℝ):ℂ)^(-s)) -
      ((squareRootAbelReciprocalClock (x+1)-squareRootAbelReciprocalClock x:ℝ):ℂ)*
        (((x+1:ℝ):ℂ)^(-s)-((x+2:ℝ):ℂ)^(-s)) := by
    unfold squareRootAbelDirichletKernel
    rw [show x+1+1=x+2 by ring]
    push_cast
    ring
  have hf : ‖((x+1:ℝ):ℂ)^(-s)-((x+2:ℝ):ℂ)^(-s)‖ ≤ ‖s‖*x^(-s.re-1) := by
    have h := norm_cpow_unit_diff_le hs (show 0 < x+1 by linarith)
    rw [show x+1+1=x+2 by ring] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
  have hp1 : Real.sqrt x*x^(-s.re-2)=x^(-s.re-3/2) := by
    rw [sqrt_mul_rpow hx0]
    congr 1
    ring
  have hp2 : x^(-s.re-1)/Real.sqrt x=x^(-s.re-3/2) := by
    rw [rpow_div_sqrt hx0]
    congr 1
    ring
  rw [he]
  calc
    _ ≤ ‖(squareRootAbelReciprocalClock x:ℂ)*
        ((x:ℂ)^(-s)-2*((x+1:ℝ):ℂ)^(-s)+((x+2:ℝ):ℂ)^(-s))‖ +
      ‖((squareRootAbelReciprocalClock (x+1)-squareRootAbelReciprocalClock x:ℝ):ℂ)*
        (((x+1:ℝ):ℂ)^(-s)-((x+2:ℝ):ℂ)^(-s))‖ := norm_sub_le _ _
    _ ≤ (3*Real.sqrt x)*(‖s‖*‖s+1‖*x^(-s.re-2)) +
        (1/Real.sqrt x)*(‖s‖*x^(-s.re-1)) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply add_le_add
      · rw [abs_of_nonneg (squareRootAbelReciprocalClock_nonneg x)]
        exact mul_le_mul (squareRootAbelReciprocalClock_le hx)
          (norm_second_difference_cpow_le hs hx0) (norm_nonneg _) (by positivity)
      · exact mul_le_mul (abs_squareRootAbelReciprocalClock_step_le hx0) hf
          (norm_nonneg _) (by positivity)
    _ = (3*‖s‖*‖s+1‖)*(Real.sqrt x*x^(-s.re-2)) +
        ‖s‖*(x^(-s.re-1)/Real.sqrt x) := by ring
    _ = _ := by rw [hp1,hp2]; ring

/-- For positive source scale, the weighted kernel is entire in its Mellin exponent. -/
theorem differentiable_squareRootAbelDirichletKernel {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (squareRootAbelDirichletKernel x) := by
  have h0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h1 : ((x+1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  intro s
  have hd0 : DifferentiableAt ℂ (fun s : ℂ => (x:ℂ)^(-s)) s :=
    DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl h0)
  have hd1 : DifferentiableAt ℂ (fun s : ℂ => ((x+1:ℝ):ℂ)^(-s)) s :=
    DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl h1)
  exact (hd0.sub hd1).const_mul _

end RHTower
