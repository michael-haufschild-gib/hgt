import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheBoundaryFourierPowerOfAConfinedState
import GaloisForLFunctions.SquareRootThreshold.FiniteExceptionsGiveCriticalLineCrowding
import GaloisForLFunctions.HTGeometry.HardyBoundary.DecayAtInfinityFromAnInteriorLine
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Zero crowding forces decay of the confined trace

A nonzero rescaled Laplace peak would persist on a fixed interval by Cauchy's
estimate. The logarithmically growing number of critical-line copies in that
interval would violate the uniform bound on its total squared sample mass.
-/

noncomputable section
open MeasureTheory Set Complex Filter Metric Zeta23
open scoped Topology ComplexConjugate
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private def iy (y : ℝ) : ℂ := (y : ℂ)*I
private theorem axis_lipschitz {H : ℂ → ℂ} {K : ℝ}
    (hd : ∀ z : ℂ, -4 < z.re → DifferentiableAt ℂ H z)
    (hb : ∀ z : ℂ, -4 ≤ z.re → ‖H z‖ ≤ K) (x y : ℝ) :
    ‖H (iy y) - H (iy x)‖ ≤ K*|y-x| := by
  have hinner (t : ℝ) : -4 < (iy t).re := by simp [iy]
  have hder (t : ℝ) : ‖deriv H (iy t)‖ ≤ K := by
    have hball (z : ℂ) (hz : z ∈ closedBall (iy t) 1) : -4 < z.re := by
      have := (Complex.abs_re_le_norm (z - iy t)).trans (mem_closedBall_iff_norm.mp hz)
      simp only [iy,sub_re,mul_I_re,ofReal_im,neg_zero,sub_zero] at this
      linarith only [(abs_le.mp this).1]
    have hdiff : DifferentiableOn ℂ H (closedBall (iy t) 1) :=
      fun z hz => (hd z (hball z hz)).differentiableWithinAt
    simpa only [div_one] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by norm_num : (0:ℝ)<1) (hdiff.diffContOnCl_ball Subset.rfl)
      (fun z hz => hb z (hball z (sphere_subset_closedBall hz)).le)
  have ht (t : ℝ) : HasDerivAt (fun s : ℝ => H (iy s)) (deriv H (iy t)*I) t := by
    have h := ((hd _ (hinner t)).hasDerivAt.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const I)).comp_ofReal
    simpa only [id_eq,one_mul,Function.comp_def,iy] using h
  have hu := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (ht t).hasDerivWithinAt)
    (fun t _ => by simpa only [norm_mul,norm_I,mul_one] using hder t)
    (mem_univ x) (mem_univ y)
  exact hu

/-- A uniformly Lipschitz peak costs squared mass at every nearby sample. -/
private theorem decay_from_crowding {ι : Type*} {γ : ι → ℝ} {f : ℝ → ℂ} {K C : ℝ}
    (hK : 0 < K) (hlip : ∀ x y : ℝ, ‖f y-f x‖ ≤ K*|y-x|)
    (hmass : ∀ (y : ℝ) (S : Finset ι), (∀ q ∈ S, |γ q-y| ≤ 1) →
      ∑ q ∈ S, ‖f (γ q)‖^2 ≤ C)
    (hcrowd : ∀ h : ℝ, 0 < h → ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in atTop,
      ∃ S : Finset ι, c*Real.log y ≤ S.card ∧ ∀ q ∈ S, |γ q-y| ≤ h) :
    Tendsto (fun y => ‖f y‖) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let p := ε/2
  have hp : 0 < p := div_pos hε two_pos
  let h := min 1 (p/K)
  have hh : 0 < h := lt_min zero_lt_one (div_pos hp hK)
  obtain ⟨c,hc,hcnt⟩ := hcrowd h hh
  have hpc : 0 < p^2*c := mul_pos (sq_pos_of_pos hp) hc
  filter_upwards [hcnt,Real.tendsto_log_atTop.eventually (eventually_gt_atTop (C/(p^2*c)))]
    with y hyst hlog
  obtain ⟨S,hnum,hS⟩ := hyst
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  by_contra! hpeak
  have hlarge (q : ι) (hq : q ∈ S) : p ≤ ‖f (γ q)‖ := by
    have hd := hlip (γ q) y
    rw [abs_sub_comm y] at hd
    have hgap := (le_div_iff₀ hK).mp ((hS q hq).trans (min_le_right _ _))
    have hl := (norm_sub_norm_le (f y) (f (γ q))).trans hd
    dsimp only [p] at hgap ⊢
    linarith only [hpeak,hgap,hl]
  have hbudget : (S.card : ℝ)*p^2 ≤ C := calc
    _ = ∑ _q ∈ S, p^2 := by simp
    _ ≤ ∑ q ∈ S, ‖f (γ q)‖^2 := Finset.sum_le_sum fun q hq =>
      pow_le_pow_left₀ hp.le (hlarge q hq) 2
    _ ≤ C := hmass y S (fun q hq => (hS q hq).trans (min_le_left _ _))
  have hmore := (div_lt_iff₀ hpc).mp hlog
  linarith only [hbudget,hmore,mul_le_mul_of_nonneg_right hnum (sq_nonneg p)]

private def axisH (F : ℝ → ℝ) (w : ℂ) : ℂ := (w+5)*negativeHalfLineLaplace (cx F) w

/-- Retain the original multiplicity while restricting the counting window
to the subtype carrying the positive trace measure. -/
private theorem line_copies_crowd (hf : BacklundConverse.FiniteOffLine) (h : ℝ) (hh : 0 < h) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in atTop, ∃ S : Finset onLineCopies,
      c*Real.log y ≤ S.card ∧ ∀ q ∈ S, |(centredZero q).im-y| ≤ h := by
  obtain ⟨c,hc,hc'⟩ := SquareRootThreshold.critical_line_crowding_of_finiteOffLine hf hh
  refine ⟨c,hc,?_⟩
  filter_upwards [hc'] with y hy
  obtain ⟨s,hs,hq⟩ := hy
  have hon (q : XiZeroCopy) (hm : q ∈ s) : q ∈ onLineCopies := by
    change (centredZero q).re = 0
    simp [centredZero,(hq q hm).1]
  let e : {q // q ∈ s} ↪ onLineCopies :=
    ⟨fun q => ⟨q.val,hon q.val q.property⟩,fun _ _ he => Subtype.ext (congrArg (fun q : onLineCopies => q.val) he)⟩
  refine ⟨s.attach.map e,by simpa only [Finset.card_map,Finset.card_attach] using hs,?_⟩
  intro q hm
  obtain ⟨r,_,rfl⟩ := Finset.mem_map.mp hm
  simpa [e,centredZero] using (hq r.val r.property).2

private theorem axis_at_copy (q : onLineCopies) : iy (centredZero q).im = centredZero q := by
  have h : (centredZero q).re = 0 := q.property
  apply Complex.ext <;> simp [iy,h]

private theorem scaled_unit_mass {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hf : BacklundConverse.FiniteOffLine) :
    ∃ C : ℝ, ∀ (y : ℝ) (S : Finset onLineCopies), (∀ q ∈ S, |(centredZero q).im-y| ≤ 1) →
      ∑ q ∈ S, ‖axisH F (iy (centredZero q).im)‖^2 ≤ C := by
  obtain ⟨B,hB⟩ := hF.local_critical_line_mass hr hf
  have hm := (domain_zeroParseval_of_finiteOffLine hF.1 hf).1
  refine ⟨30*B,?_⟩
  intro y S hS
  let m := fun q : onLineCopies => if |(centredZero q).im-y| ≤ 1 then zeroValueMass F q else 0
  have hn (q : onLineCopies) : 0 ≤ m q := by
    unfold m; split_ifs <;> first | exact zeroValueMass_nonneg _ _ | exact le_rfl
  have hs : Summable m := hm.of_nonneg_of_le hn (fun q => by
    unfold m; split_ifs <;> first | exact le_rfl | exact zeroValueMass_nonneg _ _)
  have hpt (q : onLineCopies) (hq : q ∈ S) :
      ‖axisH F (iy (centredZero q).im)‖^2 ≤ (30*(1+y^2))*m q := by
    let t := (centredZero q).im
    have hd : |t-y| ≤ 1 := hS q hq
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hd 2
    rw [sq_abs,one_pow] at hsq
    have ha : ‖iy t + 5‖^2 = 25+t^2 := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simp [iy]; ring
    unfold axisH
    rw [norm_mul,mul_pow,ha,axis_at_copy,show m q = zeroValueMass F q from if_pos hd]
    apply mul_le_mul_of_nonneg_right _ (zeroValueMass_nonneg F q)
    nlinarith only [hsq,sq_nonneg (t-2*y),sq_nonneg y]
  have hsum := hs.sum_le_tsum S (fun q _ => hn q)
  calc _ ≤ ∑ q ∈ S, (30*(1+y^2))*m q := Finset.sum_le_sum hpt
       _ = 30*(1+y^2)*(∑ q ∈ S, m q) := (Finset.mul_sum ..).symm
       _ ≤ 30*(1+y^2)*(∑' q, m q) := mul_le_mul_of_nonneg_left hsum (by positivity)
       _ ≤ 30*B := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hB y) (by norm_num)

private theorem axis_decay {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun y => ‖axisH F (iy y)‖) atTop (𝓝 0) := by
  obtain ⟨K,hK⟩ := hF.halfPlane_laplace_decay hr hf
  have hd (w : ℂ) (hw : -4 < w.re) : DifferentiableAt ℂ (axisH F) w :=
    (differentiableAt_id.add_const _).mul (differentiableAt_laplace hF.1 hw)
  obtain ⟨C,hC⟩ := scaled_unit_mass hr hF hf
  exact decay_from_crowding (K := |K|+1) (by positivity)
    (axis_lipschitz hd (fun z hz => (hK z hz).trans (by linarith only [le_abs_self K])))
    hC (line_copies_crowd hf)

private theorem axis_norm_abs (F : ℝ → ℝ) (y : ℝ) :
    ‖axisH F (iy |y|)‖ = ‖axisH F (iy y)‖ := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg hy]
    have he : iy (-y) = conj (iy y) := by simp [iy]
    have hc : axisH F (iy (-y)) = conj (axisH F (iy y)) := by
      unfold axisH
      rw [he,show negativeHalfLineLaplace (cx F) (conj (iy y)) =
        conj (negativeHalfLineLaplace (cx F) (iy y)) from negativeHalfLineLaplace_real_conj F _]
      simp
    rw [hc,Complex.norm_conj]

/-- With finitely many off-line zeros, the Laplace transform of every positive-ratio
confined state is little-o of inverse height on the entire critical line. -/
theorem IsConfinedNullVector.critical_line_laplace_little_o {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun y : ℝ => |y| * ‖negativeHalfLineLaplace (cx F) ((y:ℂ)*I)‖)
      (cocompact ℝ) (𝓝 0) := by
  have habs : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
    simpa only [Real.norm_eq_abs] using (tendsto_norm_cocompact_atTop (E := ℝ))
  apply squeeze_zero (fun y => mul_nonneg (abs_nonneg _) (norm_nonneg _)) _
    ((axis_decay hr hF hf).comp habs)
  intro y
  change |y| * ‖negativeHalfLineLaplace (cx F) (iy y)‖ ≤ ‖axisH F (iy |y|)‖
  rw [axis_norm_abs,axisH,norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa [iy] using Complex.abs_im_le_norm (iy y+5)

/-- The normalized transform tends to zero in every closed half-plane lying
strictly to the right of the confinement boundary. The cutoff is uniform
in the real part and the ordinate. -/
theorem IsConfinedNullVector.interior_half_plane_laplace_little_o {R : ℝ} (hr : 0 < R)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) (hf : BacklundConverse.FiniteOffLine)
    {b ε : ℝ} (hb : -4 < b) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ w : ℂ, b ≤ w.re → T ≤ ‖w‖ →
      ‖(w+5)*negativeHalfLineLaplace (cx F) w‖ ≤ ε := by
  obtain ⟨K,hK⟩ := hF.halfPlane_laplace_decay hr hf
  apply interior_half_plane_decay_of_axis (H := axisH F) (K := K) (by norm_num : (-4:ℝ)<0) _ _ _ hb hε
  · intro w hw
    exact (differentiableAt_id.add_const _).mul (differentiableAt_laplace hF.1 hw)
  · exact fun w hw => hK w hw.le
  · intro η hη
    obtain ⟨Y,hY⟩ := Metric.tendsto_atTop.mp (axis_decay hr hF hf) η hη
    refine ⟨Y,fun y hy => ?_⟩
    have h := hY |y| hy
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _),axis_norm_abs] at h
    exact h.le

#print axioms IsConfinedNullVector.interior_half_plane_laplace_little_o
#print axioms IsConfinedNullVector.critical_line_laplace_little_o
end GaloisForLFunctions.ExclusionOfTheCriticalState
