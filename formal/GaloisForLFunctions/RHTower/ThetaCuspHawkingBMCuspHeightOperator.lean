import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspHeightTest
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWindowDifferential

/-!
The original modular operator acts on constructed compact cusp profiles by the literal height differential expression.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

private theorem separated_first (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (z v : ℂ) :
    fderiv ℝ (fun w : ℂ => a w.re*b w.im) z v =
      (v.re:ℂ)*deriv a z.re*b z.im+(v.im:ℂ)*a z.re*deriv b z.im := by
  have hdA := ((ha.differentiable (by simp)).differentiableAt.hasFDerivAt).comp z
    Complex.reCLM.hasFDerivAt
  have hdB := ((hb.differentiable (by simp)).differentiableAt.hasFDerivAt).comp z
    Complex.imCLM.hasFDerivAt
  have hp := hdA.mul hdB
  change HasFDerivAt (fun w : ℂ => a w.re*b w.im) _ z at hp
  have he := congrArg (fun l : ℂ →L[ℝ] ℂ => l v) hp.fderiv
  simpa [Function.comp_def,Pi.mul_apply,fderiv_eq_smul_deriv,Complex.real_smul,
    mul_assoc,mul_left_comm,mul_comm,add_comm] using he

private theorem separated_second (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (z : ℂ) :
    (∑ i : Fin 2, fderiv ℝ (fun w => fderiv ℝ (fun q : ℂ => a q.re*b q.im) w
      (direction i)) z (direction i)) =
      deriv (deriv a) z.re*b z.im+a z.re*deriv (deriv b) z.im := by
  have hx : (fun w : ℂ => fderiv ℝ (fun q : ℂ => a q.re*b q.im) w 1) =
      (fun w => deriv a w.re*b w.im) := by
    funext w
    simpa using separated_first a b ha hb w 1
  have hy : (fun w : ℂ => fderiv ℝ (fun q : ℂ => a q.re*b q.im) w Complex.I) =
      (fun w => a w.re*deriv b w.im) := by
    funext w
    simpa using separated_first a b ha hb w Complex.I
  simp only [Fin.sum_univ_two,direction,Matrix.cons_val_zero,Matrix.cons_val_one,hx,hy]
  rw [separated_first _ _ (contDiff_infty_iff_deriv.mp ha).2 hb,
    separated_first _ _ ha (contDiff_infty_iff_deriv.mp hb).2]
  simp

/-- The actual planar generator's full hyperbolic Laplacian, with its
horizontal window derivative explicitly retained before periodization. -/
theorem CuspHeightTest.laplaceTest_field (h : CuspHeightTest) (z : ℂ) :
    h.planarTest.laplaceTest.field z = (z.im:ℂ)^2*
      (deriv (deriv complexCuspWindow) z.re*h.field z.im+
        (cuspWindow z.re:ℂ)*deriv (deriv h.field) z.im) := by
  rw [PlanarChartTest.laplaceTest_field]
  change (z.im:ℂ)^2*(∑ i : Fin 2, fderiv ℝ
    (fun w => fderiv ℝ (fun q : ℂ => complexCuspWindow q.re*h.field q.im) w
      (direction i)) z (direction i)) = _
  rw [separated_second _ _ complexCuspWindow_smooth h.smooth]
  rfl

private theorem CuspHeightTest.laplaceTest_low (h : CuspHeightTest)
    (z : UpperHalfPlane) (hz : z.im ≤ 2) : h.planarTest.laplaceTest.toChartTest.field z = 0 := by
  have hdd : deriv (deriv h.field) z.im = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => (not_lt_of_ge hz)
      (h.support (tsupport_deriv_subset (tsupport_deriv_subset hm))))
  change h.planarTest.laplaceTest.field (z:ℂ) = 0
  rw [h.laplaceTest_field]
  change (z.im:ℂ)^2*(_*h.field z.im+_*deriv (deriv h.field) z.im) = 0
  rw [h.zero_low hz,hdd]
  ring

/-- The complete modular sum cancels every horizontal cutoff derivative and
leaves exactly the original height Laplacian on the closed cell. -/
theorem CuspHeightTest.periodize_laplaceTest (h : CuspHeightTest)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    periodize h.planarTest.laplaceTest.toChartTest.field z =
      (z.im:ℂ)^2*deriv (deriv h.field) z.im := by
  classical
  rw [periodize_high_cusp _ h.laplaceTest_low z hz]
  have ht (n : ℤ) : h.planarTest.laplaceTest.toChartTest.field (T^n • z) =
      (z.im:ℂ)^2*(deriv (deriv complexCuspWindow) (z.re+n)*h.field z.im+
        complexCuspWindow (z.re+n)*deriv (deriv h.field) z.im) := by
    change h.planarTest.laplaceTest.field ((T^n • z : UpperHalfPlane):ℂ) = _
    rw [h.laplaceTest_field]
    change ((T^n • z).im:ℂ)^2*(deriv (deriv complexCuspWindow) (T^n • z).re*
      h.field (T^n • z).im+complexCuspWindow (T^n • z).re*
        deriv (deriv h.field) (T^n • z).im) = _
    rw [ModularGroup.re_T_zpow_smul,ModularGroup.im_T_zpow_smul]
  simp_rw [ht]
  rw [tsum_eq_sum (s := {-1,0,1})]
  · rw [Finset.sum_insert (by norm_num : (-1:ℤ) ∉ ({0,1}:Finset ℤ)),
      Finset.sum_insert (by norm_num : (0:ℤ) ∉ ({1}:Finset ℤ)),Finset.sum_singleton]
    simp only [Int.cast_neg,Int.cast_one,Int.cast_zero,add_zero,← sub_eq_add_neg]
    have ha := complexCuspWindow_triple z.re (hz.2.trans (by norm_num))
    have hd := complexCuspWindow_second_triple z.re hz.2
    calc
      _ = (z.im:ℂ)^2*((deriv (deriv complexCuspWindow) (z.re-1)+
          deriv (deriv complexCuspWindow) z.re+deriv (deriv complexCuspWindow) (z.re+1))*
            h.field z.im+(complexCuspWindow (z.re-1)+complexCuspWindow z.re+
              complexCuspWindow (z.re+1))*deriv (deriv h.field) z.im) := by ring
      _ = _ := by rw [ha,hd]; ring
  · intro n hn
    have hn' : n ≠ -1 ∧ n ≠ 0 ∧ n ≠ 1 := by simpa using hn
    have hc : n ≤ -2 ∨ 2 ≤ n := by omega
    have hxr : z.re+n < -1 ∨ 1 < z.re+n := by
      have hx := abs_le.mp hz.2
      rcases hc with hl | hr
      · left
        have hl' : (n:ℝ) ≤ -2 := by exact_mod_cast hl
        linarith
      · right
        have hr' : (2:ℝ) ≤ n := by exact_mod_cast hr
        linarith
    have ha : complexCuspWindow (z.re+n) = 0 := by
      unfold complexCuspWindow
      rcases hxr with hl | hr
      · rw [cuspWindow_zero_left hl.le,Complex.ofReal_zero]
      · rw [cuspWindow_zero_right hr.le,Complex.ofReal_zero]
    have hd : deriv (deriv complexCuspWindow) (z.re+n) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hh := complexCuspWindow_second_support hm
      rcases hxr with hl | hr
      · exact (not_lt_of_ge hh.1) hl
      · exact (not_lt_of_ge hh.2) hr
    rw [ha,hd]
    ring

/-- The original unbounded modular operator acts on the admitted cusp field
by the exact native differential expression `h-y^2*h''`. -/
theorem CuspHeightTest.energyOperator_coe (h : CuspHeightTest) :
    (energyOperator h.operatorVector : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun z => h.field z.im-(z.im:ℂ)^2*deriv (deriv h.field) z.im) := by
  have he : energyOperator h.operatorVector =
      embedding h.planarTest.toChartTest.energyTest-h.planarTest.laplaceVector :=
    h.planarTest.energyOperator_apply
  rw [he]
  filter_upwards [Lp.coeFn_sub (embedding h.planarTest.toChartTest.energyTest)
      h.planarTest.laplaceVector,h.operatorVector_coe,
    h.planarTest.laplaceTest.toChartTest.energyTest_scalar,
    ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hs hh hl hz
  rw [hs]
  change (embedding h.planarTest.toChartTest.energyTest : UpperHalfPlane → ℂ) z-
    (h.planarTest.laplaceVector : UpperHalfPlane → ℂ) z = _
  change (embedding h.planarTest.toChartTest.energyTest : UpperHalfPlane → ℂ) z = _ at hh
  rw [hh]
  change h.field z.im-(embedding h.planarTest.laplaceTest.toChartTest.energyTest :
    UpperHalfPlane → ℂ) z = _
  rw [hl,h.periodize_laplaceTest z hz]

end
end RHTower.D4BMModularCore
