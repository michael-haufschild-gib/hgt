import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts.Range

/-! # The threshold in normalized three-shell multiplicity coordinates -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts

open Real Set Filter Topology

/-- At positive excess k, the signed bit compares the total fraction on
the two extreme shells with this threshold. -/
def outerCut (k x : ℝ) := (k*sinh x*cosh (k*x)/sinh (k*x)-1)/(cosh x-1)

private def ratio (k x : ℝ) := gap k (1-k) x/gap k (1+k) x

private def transform (k r : ℝ) := k*(1+r)/(1-r)

private theorem cut_coordinates {k x : ℝ} (hk : 0<k) (hx : 0<x) :
    ratio k x<1 ∧ outerCut k x=transform k (ratio k x) := by
  let A := gap k (1-k) x
  let C := gap k (1+k) x
  have cp : 0<C := gap_pos hk (lt_one_add _) hx
  have ch := sub_pos.mpr (one_lt_cosh.mpr hx.ne')
  have sh := sinh_pos_iff.mpr (mul_pos hk hx)
  have add : C+A=2*(k*sinh x*cosh (k*x)-sinh (k*x)) := by
    simp only [C,A,gap,add_mul,sub_mul,one_mul,sinh_add,sinh_sub]
    ring
  have sub : C-A=2*k*(cosh x-1)*sinh (k*x) := by
    simp only [C,A,gap,add_mul,sub_mul,one_mul,sinh_add,sinh_sub]
    ring
  have diff : 0<C-A := sub.symm ▸ mul_pos (mul_pos (mul_pos zero_lt_two hk) ch) sh
  have small : A/C<1 := (div_lt_one cp).mpr (sub_pos.mp diff)
  refine ⟨small,?_⟩
  change _=k*(1+A/C)/(1-A/C)
  rw [show 1+A/C=(C+A)/C by rw [add_div,div_self cp.ne'],
    show 1-A/C=(C-A)/C by rw [sub_div,div_self cp.ne'],
    ← mul_div_assoc,div_div_div_cancel_right₀ cp.ne',add,sub]
  unfold outerCut
  field_simp [sh.ne',ch.ne',hk.ne']

/-- For every real normalized imbalance between zero and one half, the
outer-fraction threshold is strictly decreasing on the positive axis. -/
theorem outerCut_strictAnti {k : ℝ} (hk : 0<k) (half : k<1/2) :
    StrictAntiOn (outerCut k) (Ioi 0) := by
  intro x hx y hy lt
  have smaller := gap_ratio_strictAnti hk (show k<1-k by linarith only [half])
    (show 1-k<1+k by linarith only [hk]) hx hy lt
  change ratio k y<ratio k x at smaller
  obtain ⟨xl,xf⟩ := cut_coordinates hk hx
  obtain ⟨yl,yf⟩ := cut_coordinates hk hy
  rw [xf,yf,transform,transform,div_lt_div_iff₀ (sub_pos.mpr yl) (sub_pos.mpr xl)]
  nlinarith only [mul_pos hk (sub_pos.mpr smaller)]

/-- The attainable thresholds run from the normalized third-moment boundary
down to the imbalance itself. -/
theorem outerCut_limits {k : ℝ} (hk : 0<k) (half : k<1/2) :
    Tendsto (outerCut k) (𝓝[>] 0) (𝓝 ((1+2*k^2)/3)) ∧
    Tendsto (outerCut k) atTop (𝓝 k) := by
  have hb : k<1-k := by linarith only [half]
  have hc : 1-k<1+k := by linarith only [hk]
  let w := wall k (1-k) (1+k)
  have constants : w=((1-k)*(1-2*k))/((1+k)*(1+2*k)) := by
    unfold w wall
    rw [show (1-k)^2-k^2=1-2*k from by ring,show (1+k)^2-k^2=1+2*k from by ring]
  have den : 0<(1+k)*(1+2*k) := by positivity
  have small : w<1 := by
    rw [constants,div_lt_one den]
    linarith only [hk]
  have cont (r : ℝ) (lt : r<1) : ContinuousAt (transform k) r := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact (sub_pos.mpr lt).ne'
  have top : transform k w=(1+2*k^2)/3 := by
    rw [transform,div_eq_iff (sub_pos.mpr small).ne',constants]
    field_simp [den.ne']; ring
  constructor
  · have lim := (cont w small).tendsto.comp (gap_ratio_wall hk hb hc)
    rw [top] at lim
    have positive : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0<x := self_mem_nhdsWithin
    exact lim.congr' (positive.mono fun _ hx => (cut_coordinates hk hx).2.symm)
  · have lim := (cont 0 zero_lt_one).tendsto.comp (gap_ratio_infty hk hb hc)
    rw [show transform k 0=k by simp [transform]] at lim
    exact lim.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx => (cut_coordinates hk hx).2.symm)

#print axioms outerCut_strictAnti
#print axioms outerCut_limits

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts
