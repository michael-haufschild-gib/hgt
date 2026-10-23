import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullCoreOperator
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspHeightOperator
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspWindowAbsoluteRegrouping
import Mathlib.Algebra.Order.Round
/-!
Full compact positive-height seeds belong to the original modular operator domain.
Each integer translation row cancels the horizontal window's second derivative.
Every primitive height row remains in the exact native operator image, including
seeds reaching below the standard cusp. No high-cusp support restriction is imposed.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
set_option autoImplicit false
namespace RHTower.D4BMModularCore
noncomputable section
/-- A smooth compact height profile supported strictly above height zero. -/
structure PositiveHeightTest where
  field : ℝ → ℂ
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field
  support : tsupport field ⊆ Ioi 0

theorem PositiveHeightTest.zero_low (h : PositiveHeightTest) {y : ℝ} (hy : y ≤ 0) : h.field y = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hm => (not_lt_of_ge hy) (h.support hm))

/-- The actual compact planar generator whose full modular periodization produces the profile. -/
def PositiveHeightTest.planarField (h : PositiveHeightTest) (z : ℂ) : ℂ :=
  (cuspWindow z.re : ℂ)*h.field z.im

theorem PositiveHeightTest.planarField_smooth (h : PositiveHeightTest) :
    ContDiff ℝ ∞ h.planarField :=
  (Complex.ofRealCLM.contDiff.comp (cuspWindow_smooth.comp Complex.reCLM.contDiff)).mul
    (h.smooth.comp Complex.imCLM.contDiff)

private theorem PositiveHeightTest.planarField_support (h : PositiveHeightTest) :
    tsupport h.planarField ⊆ {z : ℂ | z.re ∈ Icc (-1) 1 ∧ z.im ∈ tsupport h.field} := by
  apply closure_minimal _ (isClosed_Icc.reProdIm isClosed_closure)
  intro z hz
  have hl : cuspWindow z.re ≠ 0 := by
    intro he
    exact hz (by simp [PositiveHeightTest.planarField,he])
  have hr : h.field z.im ≠ 0 := by
    intro he
    exact hz (by simp [PositiveHeightTest.planarField,he])
  exact ⟨cuspWindow_support (subset_tsupport _ hl),subset_tsupport _ hr⟩

def PositiveHeightTest.planarTest (h : PositiveHeightTest) : PlanarChartTest where
  field := h.planarField
  smooth := h.planarField_smooth
  compact := (isCompact_Icc.reProdIm h.compact).of_isClosed_subset isClosed_closure
    h.planarField_support
  support := by
    intro z hz
    have hh := h.support (h.planarField_support hz).2
    change 0 < z.im at hh
    change 0 < z.im
    linarith

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
theorem PositiveHeightTest.laplaceTest_field (h : PositiveHeightTest) (z : ℂ) :
    h.planarTest.laplaceTest.field z = (z.im:ℂ)^(2 : ℕ)*
      (deriv (deriv complexCuspWindow) z.re*h.field z.im+
        (cuspWindow z.re:ℂ)*deriv (deriv h.field) z.im) := by
  rw [PlanarChartTest.laplaceTest_field]
  change (z.im:ℂ)^(2 : ℕ)*(∑ i : Fin 2, fderiv ℝ
    (fun w => fderiv ℝ (fun q : ℂ => complexCuspWindow q.re*h.field q.im) w
      (direction i)) z (direction i)) = _
  rw [separated_second _ _ complexCuspWindow_smooth h.smooth]
  rfl


private theorem second_partition_center (x : ℝ) (hx : |x| ≤ 1/2) :
    (∑' n : ℤ, deriv (deriv complexCuspWindow) (x+n)) = 0 := by
  classical
  rw [tsum_eq_sum (s := {-1,0,1})]
  · rw [Finset.sum_insert (by norm_num : (-1:ℤ) ∉ ({0,1}:Finset ℤ)),
      Finset.sum_insert (by norm_num : (0:ℤ) ∉ ({1}:Finset ℤ)),Finset.sum_singleton]
    simpa only [Int.cast_neg,Int.cast_one,Int.cast_zero,add_zero,← sub_eq_add_neg,add_assoc] using
      complexCuspWindow_second_triple x hx
  · intro n hn
    have hn' : n ≠ -1 ∧ n ≠ 0 ∧ n ≠ 1 := by simpa using hn
    have hc : n ≤ -2 ∨ 2 ≤ n := by omega
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh := complexCuspWindow_second_support hm
    have hb := abs_le.mp hx
    rcases hc with hl | hr
    · have hl' : (n:ℝ) ≤ -2 := by exact_mod_cast hl
      linarith [hh.1]
    · have hr' : (2:ℝ) ≤ n := by exact_mod_cast hr
      linarith [hh.2]

/-- Complete horizontal derivative cancellation at every point, before summing primitive rows. -/
theorem complexCuspWindow_second_partition (x : ℝ) :
    (∑' n : ℤ, deriv (deriv complexCuspWindow) (x+n)) = 0 := by
  let k : ℤ := round x
  calc
    _ = ∑' n : ℤ, deriv (deriv complexCuspWindow) (x-(k:ℝ)+(n+k:ℤ)) := by
      apply tsum_congr
      intro n
      congr 1
      push_cast
      ring
    _ = ∑' n : ℤ, deriv (deriv complexCuspWindow) (x-(k:ℝ)+n) :=
      (Equiv.addRight k).tsum_eq (fun n : ℤ => deriv (deriv complexCuspWindow) (x-(k:ℝ)+n))
    _ = 0 := second_partition_center _ (abs_sub_round x)

private theorem second_translation_finite (x : ℝ) :
    Function.HasFiniteSupport (fun n : ℤ => deriv (deriv complexCuspWindow) (x+n)) := by
  apply (Set.finite_Icc ⌊-x-1⌋ ⌈1-x⌉).subset
  intro n hn
  have hh := complexCuspWindow_second_support (subset_tsupport _ hn)
  constructor
  · have h : (⌊-x-1⌋:ℝ) ≤ (n:ℝ) := by linarith [hh.1,Int.floor_le (-x-1)]
    exact_mod_cast h
  · have h : (n:ℝ) ≤ (⌈1-x⌉:ℝ) := by linarith [hh.2,Int.le_ceil (1-x)]
    exact_mod_cast h

private theorem PositiveHeightTest.laplace_translation (h : PositiveHeightTest)
    (v : gammaSetHalf) (z : UpperHalfPlane) :
    (∑' n : ℤ, h.planarTest.laplaceTest.toChartTest.field (cuspOrbitEquiv (v,n) • z)) =
      ((gammaSetMatrix v.1 • z).im:ℂ)^(2 : ℕ)*deriv (deriv h.field) (gammaSetMatrix v.1 • z).im := by
  have ht (n : ℤ) : h.planarTest.laplaceTest.toChartTest.field (cuspOrbitEquiv (v,n) • z) =
      ((gammaSetMatrix v.1 • z).im:ℂ)^(2 : ℕ)*
        (deriv (deriv complexCuspWindow) ((gammaSetMatrix v.1 • z).re+n)*h.field (gammaSetMatrix v.1 • z).im+
         (cuspWindow ((gammaSetMatrix v.1 • z).re+n):ℂ)*deriv (deriv h.field) (gammaSetMatrix v.1 • z).im) := by
    rw [cuspOrbitEquiv_smul]
    change h.planarTest.laplaceTest.field ((T^n • (gammaSetMatrix v.1 • z):UpperHalfPlane):ℂ) = _
    rw [h.laplaceTest_field]
    change ((T^n • (gammaSetMatrix v.1 • z)).im:ℂ)^(2 : ℕ) *
      (deriv (deriv complexCuspWindow) (T^n • (gammaSetMatrix v.1 • z)).re *
       h.field (T^n • (gammaSetMatrix v.1 • z)).im +
       (cuspWindow (T^n • (gammaSetMatrix v.1 • z)).re:ℂ) *
       deriv (deriv h.field) (T^n • (gammaSetMatrix v.1 • z)).im) = _
    rw [ModularGroup.re_T_zpow_smul,ModularGroup.im_T_zpow_smul]
  have hd : Summable (fun n : ℤ => deriv (deriv complexCuspWindow) ((gammaSetMatrix v.1 • z).re+n)) :=
    summable_of_hasFiniteSupport (second_translation_finite (gammaSetMatrix v.1 • z).re)
  have hw : Summable (fun n : ℤ => (cuspWindow ((gammaSetMatrix v.1 • z).re+n):ℂ)) :=
    Complex.ofRealCLM.summable (summable_of_hasFiniteSupport (cuspWindow_translation_finite _))
  simp_rw [ht]
  rw [tsum_mul_left,(hd.mul_right _).tsum_add (hw.mul_right _),
    tsum_mul_right,tsum_mul_right,complexCuspWindow_second_partition,
    ← Complex.ofReal_tsum,cuspWindow_partition_all]
  simp

/-- Full compact positive-height periodization retains every nonparabolic height derivative. -/
theorem PositiveHeightTest.periodize_laplace_rows (h : PositiveHeightTest) (z : UpperHalfPlane) :
    periodize h.planarTest.laplaceTest.toChartTest.field z =
      ∑' v : gammaSetHalf, ((gammaSetMatrix v.1 • z).im:ℂ)^(2 : ℕ)*
        deriv (deriv h.field) (gammaSetMatrix v.1 • z).im := by
  have hp : Summable (fun p : gammaSetHalf × ℤ => h.planarTest.laplaceTest.toChartTest.field (cuspOrbitEquiv p • z)) :=
    (cuspOrbitEquiv.summable_iff (f := fun γ : PSL2Z =>
      h.planarTest.laplaceTest.toChartTest.field (γ • z))).mpr
      (h.planarTest.laplaceTest.toChartTest.orbit_summable z)
  rw [periodize,← cuspOrbitEquiv.tsum_eq (fun γ : PSL2Z => h.planarTest.laplaceTest.toChartTest.field (γ • z)),hp.tsum_prod]
  exact tsum_congr (fun v => h.laplace_translation v z)

/-- All Laplacian rows are absolutely admitted by the constructed compact seed. -/
theorem PositiveHeightTest.laplace_rows_summable (h : PositiveHeightTest) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => ((gammaSetMatrix v.1 • z).im:ℂ)^(2 : ℕ)*
      deriv (deriv h.field) (gammaSetMatrix v.1 • z).im) := by
  have hp : Summable (fun p : gammaSetHalf × ℤ => h.planarTest.laplaceTest.toChartTest.field (cuspOrbitEquiv p • z)) :=
    (cuspOrbitEquiv.summable_iff (f := fun γ : PSL2Z =>
      h.planarTest.laplaceTest.toChartTest.field (γ • z))).mpr
      (h.planarTest.laplaceTest.toChartTest.orbit_summable z)
  exact hp.prod.congr (fun v => h.laplace_translation v z)

/-- Actual native graph vector of the full compact positive-height source. -/
def PositiveHeightTest.operatorVector (h : PositiveHeightTest) : energyOperator.domain :=
  ⟨embedding h.planarTest.toChartTest.energyTest,h.planarTest.mem_energyOperator_domain⟩

theorem PositiveHeightTest.operatorVector_coe (h : PositiveHeightTest) :
    ((h.operatorVector : Space) : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun z => ∑' v : gammaSetHalf, h.field (gammaSetMatrix v.1 • z).im) := by
  filter_upwards [h.planarTest.toChartTest.energyTest_scalar] with z he
  exact he.trans (periodize_cuspHeightSeed_eq_rows_of_summable h.field z
    (h.planarTest.toChartTest.orbit_summable z))

/-- The actual native operator image contains the complete height-row differential expression. -/
theorem PositiveHeightTest.energyOperator_coe (h : PositiveHeightTest) :
    (energyOperator h.operatorVector : UpperHalfPlane → ℂ) =ᵐ[measure]
      (fun z => (∑' v : gammaSetHalf, h.field (gammaSetMatrix v.1 • z).im)-
        ∑' v : gammaSetHalf, ((gammaSetMatrix v.1 • z).im:ℂ)^(2 : ℕ)*
          deriv (deriv h.field) (gammaSetMatrix v.1 • z).im) := by
  rw [show energyOperator h.operatorVector =
      embedding h.planarTest.toChartTest.energyTest-h.planarTest.laplaceVector from
      h.planarTest.energyOperator_apply]
  filter_upwards [Lp.coeFn_sub (embedding h.planarTest.toChartTest.energyTest) h.planarTest.laplaceVector,
    h.operatorVector_coe,h.planarTest.laplaceTest.toChartTest.energyTest_scalar] with z hs hh hl
  rw [hs]
  change (embedding h.planarTest.toChartTest.energyTest : Space) z-
    (embedding h.planarTest.laplaceTest.toChartTest.energyTest : Space) z = _
  rw [show (embedding h.planarTest.toChartTest.energyTest : Space) z = _ from hh,hl,
    h.periodize_laplace_rows z]

end
end RHTower.D4BMModularCore
