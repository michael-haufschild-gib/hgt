import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringMellin
import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaContinuation

/-! In the absolute-convergence chamber, the subtracted disc-valued Mellin
state equals the original kernel integral. Real positive periods identify
that integral with two independently convergent Barnes double zeta series. -/

open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringKernel MayerScatteringMellin
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringChamber

private theorem period_pos (z : Disc) : 0 < (1+z.1).re := by
  have hr := (neg_le_abs (z.1-1).re).trans (Complex.abs_re_le_norm (z.1-1))
  have hd : ‖z.1-1‖ ≤ (3/2 : ℝ) := by
    simpa only [outer,Metric.mem_closedBall,dist_eq_norm] using z.property
  simp only [Complex.sub_re,Complex.one_re] at hr
  simp only [Complex.add_re,Complex.one_re]
  linarith only [hr,hd]

private theorem head_integrable {w : ℂ} (hw : 0 < w.re) (z : Disc) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(w-1)*regularKernel (1+z.1) (t : ℂ)) (Ioc 0 1) := by
  have h : IntegrableOn
      (fun t : ℝ => evaluation z ((t : ℂ)^(w-1) • headInput t)) (Ioi 0) :=
    (evaluation z).integrable_comp (mellinConvergent_headInput hw)
  refine (h.mono_set (fun t (ht : t ∈ Ioc (0 : ℝ) 1) => ht.1)).congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp only [headInput,Set.indicator_of_mem ht,map_smul,evaluation_apply,
    headDisc_apply,abs_of_nonneg ht.1.le,smul_eq_mul]

private theorem tail_integrable {w : ℂ} (hw : 0 < w.re) (z : Disc) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(w-1)*kernel (1+z.1) (t : ℂ)) (Ioi 1) := by
  have h : IntegrableOn
      (fun t : ℝ => evaluation z ((t : ℂ)^(w-1) • tailInput t)) (Ioi 0) :=
    (evaluation z).integrable_comp (mellinConvergent_tailInput hw)
  refine (h.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp only [tailInput,Set.indicator_of_mem ht,map_smul,evaluation_apply,
    tailDisc_apply,max_eq_right (le_of_lt (show (1 : ℝ) < t from ht)),smul_eq_mul]

private theorem weighted_kernel_decomposition (w : ℂ) (z : Disc) {t : ℝ} (ht : 0 < t) :
    (t : ℂ)^(w-1)*kernel (1+z.1) (t : ℂ)=
      (2/(1+z.1))*((t : ℂ)^(w-1)*(t : ℂ)^(-2 : ℂ))+
        (t : ℂ)^(w-1)*regularKernel (1+z.1) (t : ℂ) := by
  rw [kernel_decomposition (period_pos z) ht]
  simp only [Complex.cpow_neg,Complex.cpow_two,
    div_eq_mul_inv,mul_inv_rev]
  ring

/-- In the absolute chamber, subtracting the quadratic kernel singularity preserves the
original Mellin integral exactly. -/
theorem state_eq_mellinKernel {w : ℂ} (hw : 2 < w.re) (z : Disc) :
    (state w).1 z=(Complex.Gamma w)⁻¹*mellin
      (fun t : ℝ => kernel (1+z.1) (t : ℂ)) w := by
  have h0 : 0 < w.re := by linarith only [hw]
  have hp : 0 < w.re+(-2 : ℂ).re := by norm_num; linarith only [hw]
  have hi := (integrableOn_cpow_mul_cpow_Ioc (-2 : ℂ) hp).const_mul (2/(1+z.1))
  have hh := head_integrable h0 z
  have hk : IntegrableOn (fun t : ℝ => (t : ℂ)^(w-1)*kernel (1+z.1) (t : ℂ)) (Ioc 0 1) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hi.add hh) ?_ measurableSet_Ioc
    intro t ht
    exact (weighted_kernel_decomposition w z ht.1).symm
  have hhead : (∫ t in Ioc (0 : ℝ) 1, (t : ℂ)^(w-1)*kernel (1+z.1) (t : ℂ))=
      (2/(w-2))*(1+z.1)⁻¹+
        ∫ t in Ioc (0 : ℝ) 1, (t : ℂ)^(w-1)*regularKernel (1+z.1) (t : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun t ht => weighted_kernel_decomposition w z ht.1),integral_add hi hh,
      integral_const_mul,integral_cpow_mul_cpow_Ioc (-2 : ℂ) hp]
    congr 1
    ring
  have hd : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht')
  rw [state_apply h0,mellin]
  simp only [smul_eq_mul]
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_union hd measurableSet_Ioi hk (tail_integrable h0 z),hhead]

private theorem real_kernel_eq_barnes (a t : ℝ) :
    kernel (a : ℂ) (t : ℂ)=barnesConeKernel a 1 1 t+barnesConeKernel a 1 a t := by
  simp only [kernel,barnesConeKernel,one_mul,← Complex.ofReal_neg,← Complex.ofReal_mul,
    ← Complex.ofReal_exp,neg_mul]
  rw [mul_comm (1-(Real.exp (-t) : ℂ)) (1-(Real.exp (-(a*t)) : ℂ)),add_div]

private theorem barnes_integrable {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    {w : ℂ} (hw : 2 < w.re) : MellinConvergent (barnesConeKernel a 1 x) w := by
  change IntegrableOn (fun t : ℝ => (t : ℂ)^(w-1) • barnesConeKernel a 1 x t) (Ioi 0)
  simp only [smul_eq_mul]
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact (integrableOn_cpow_mul_barnesConeKernel_Ioc ha zero_lt_one hw).union
    (integrableOn_cpow_mul_barnesConeKernel_Ioi_one ha zero_lt_one hx (by linarith only [hw]))

/-- For a real positive period, the disc kernel is the sum of the two boundary Barnes kernels. -/
theorem mellinKernel_real {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 2 < w.re) :
    mellin (fun t : ℝ => kernel (a : ℂ) (t : ℂ)) w=
      Complex.Gamma w*(barnesDoubleZeta a 1 w 1+barnesDoubleZeta a 1 w (a : ℂ)) := by
  have h1 := barnes_integrable ha zero_lt_one hw
  have ha' := barnes_integrable ha ha hw
  have he : (fun t : ℝ => kernel (a : ℂ) (t : ℂ))=
      fun t => barnesConeKernel a 1 1 t+barnesConeKernel a 1 a t :=
    funext (real_kernel_eq_barnes a)
  rw [he,mellin]
  simp only [smul_add]
  rw [integral_add h1 ha']
  change mellin (barnesConeKernel a 1 1) w+mellin (barnesConeKernel a 1 a) w=_
  rw [← Gamma_mul_barnesDoubleZeta_eq_mellin ha zero_lt_one zero_lt_one hw,
    ← Gamma_mul_barnesDoubleZeta_eq_mellin ha zero_lt_one ha hw]
  simp only [Complex.ofReal_one]
  ring

/-- The actual state has a convergent Barnes-series value at each real disc point. -/
theorem state_apply_real {w : ℂ} (hw : 2 < w.re) (z : Disc) (x : ℝ)
    (hz : z.1=(x : ℂ)) :
    (state w).1 z=barnesDoubleZeta (1+x) 1 w 1+
      barnesDoubleZeta (1+x) 1 w ((1+x : ℝ) : ℂ) := by
  have ha : 0 < 1+x := by simpa only [hz,Complex.add_re,Complex.one_re,Complex.ofReal_re] using period_pos z
  have hG : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.neg_re,Complex.natCast_re] at hr
    linarith only [hr,hw,Nat.cast_nonneg (α := ℝ) n]
  rw [state_eq_mellinKernel hw,hz,show (1 : ℂ)+(x : ℂ)=((1+x : ℝ) : ℂ) by push_cast; rfl,
    mellinKernel_real ha hw,inv_mul_cancel_left₀ (Complex.Gamma_ne_zero hG)]

private theorem barnesSingleZeta_self {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 1 < w.re) :
    barnesSingleZeta a w (a : ℂ)=(a : ℂ)^(-w)*riemannZeta w := by
  rw [barnesSingleZeta,zeta_eq_tsum_one_div_nat_add_one_cpow hw,← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : (a : ℂ)+(((n : ℝ)*a : ℝ) : ℂ)=(a : ℂ)*((n+1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he,Complex.mul_cpow_ofReal_nonneg ha.le (by positivity)]
  simp only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,
    Complex.cpow_neg,one_div]

/-- The two boundary Barnes series contain the two zeta rays and twice the strict cone. -/
theorem barnes_boundary_pair {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 2 < w.re) :
    barnesDoubleZeta a 1 w 1+barnesDoubleZeta a 1 w (a : ℂ)=
      riemannZeta w*(1+(a : ℂ)^(-w))+2*barnesDoubleZeta a 1 w (1+(a : ℂ)) := by
  have hf := barnesDoubleZeta_add_fst (o1 := a) (o2 := 1) (z := 1)
    ha zero_lt_one hw (by norm_num)
  have hs := barnesDoubleZeta_add_snd (o1 := a) (o2 := 1) (z := (a : ℂ))
    ha zero_lt_one hw (by exact ha)
  have h1 : 1 < w.re := by linarith only [hw]
  rw [show (1 : ℂ)=((1 : ℝ) : ℂ) from rfl,barnesSingleZeta_self zero_lt_one h1] at hf
  simp only [Complex.ofReal_one,Complex.one_cpow,one_mul] at hf
  rw [barnesSingleZeta_self ha h1] at hs
  simp only [Complex.ofReal_one] at hs
  rw [add_comm (a : ℂ) 1] at hs
  linear_combination -hf-hs

/-- The continued state agrees with the full positive-lattice expression at real disc points. -/
theorem state_apply_real_expanded {w : ℂ} (hw : 2 < w.re) (z : Disc) (x : ℝ)
    (hz : z.1=(x : ℂ)) :
    (state w).1 z=riemannZeta w*(1+((1+x : ℝ) : ℂ)^(-w))+
      2*barnesDoubleZeta (1+x) 1 w ((2+x : ℝ) : ℂ) := by
  have ha : 0 < 1+x := by simpa only [hz,Complex.add_re,Complex.one_re,Complex.ofReal_re] using period_pos z
  rw [state_apply_real hw z x hz,barnes_boundary_pair ha hw]
  congr 2
  push_cast
  ring

#print axioms state_eq_mellinKernel
#print axioms mellinKernel_real
#print axioms state_apply_real
#print axioms barnes_boundary_pair
#print axioms state_apply_real_expanded
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringChamber
