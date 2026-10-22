import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCharacteristicContact
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullCovectorModular
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalForcingProductBounds
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullSourceCircleGrowth

/-!
# Global growth input for the literal native characteristic current

The literal native radial current is controlled through the actual source
Laplacian.  This file first records its modular invariance, before deriving
the required cusp-to-global growth estimate and applying the Volterra formula.

Proof-chain role:
`literal direct normal face -> native characteristic current majorant ->
normal derivative interchange -> corrected-future cap coefficient -> HB B2`.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMNativeCircle
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open D4BMOriginalForcingProductBounds D4BMJointSource
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- Each literal forcing component used in the source Laplacian is a modular
scalar.  The `gradient` branch is the actual full gradient energy, divided by
its original factor two. -/
private theorem sourceField_modular (q : XiZeroCopy) (gradient : Bool)
    (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    sourceField q gradient (coordinates (A • z)) =
      sourceField q gradient (coordinates z) := by
  cases gradient
  · simpa [sourceField] using fullSquarePotential_modular q A z
  · simpa [sourceField, mul_div_assoc] using
      congrArg (fun w : ℂ => w / 2) (fullGradientEnergy_modular q A z)

/-- The actual scalar Laplacian of the literal half-square is a modular
scalar.  Its proof retains both the full half-square and its gradient-energy
forcing; no eigenvalue-only replacement is made. -/
theorem scalarLaplacian_fullSquarePotential_modular (q : XiZeroCopy)
    (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    scalarLaplacian (fullSquarePotential q) (coordinates (A • z)) =
      scalarLaplacian (fullSquarePotential q) (coordinates z) := by
  calc
    scalarLaplacian (fullSquarePotential q) (coordinates (A • z)) =
        2 * (physicalRate q false + 1) * (physicalRate q false + 2) *
            fullSquarePotential q (coordinates (A • z)) +
          fullGradientEnergy q (coordinates (A • z)) :=
      fullSquarePotential_laplacian q false _ (A • z).im_pos
    _ = 2 * (physicalRate q false + 1) * (physicalRate q false + 2) *
            fullSquarePotential q (coordinates z) +
          fullGradientEnergy q (coordinates z) := by
      rw [fullSquarePotential_modular q A z, fullGradientEnergy_modular q A z]
    _ = scalarLaplacian (fullSquarePotential q) (coordinates z) :=
      (fullSquarePotential_laplacian q false _ z.im_pos).symm

private theorem principalExponent_re_le_sourceGrowth (q : XiZeroCopy) (i : Fin 3) :
    (principalExponent q i).re ≤ sourceGrowthExponent q := by
  fin_cases i <;>
    simp [principalExponent, sourceGrowthExponent, D4BMGlobalAngularResponse.center,
      Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_im, Complex.one_im] <;>
    nlinarith [le_abs_self ((q.1 : ℂ).re - 1 / 2),
      neg_le_abs ((q.1 : ℂ).re - 1 / 2)]

private theorem sourcePrincipal_cusp_growth (q : XiZeroCopy) (branch gradient : Bool)
    (gamma : ℝ) (hgamma : sourceGrowthExponent q < gamma) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 1 ≤ z 1 →
      ‖sourcePrincipal q branch gradient z‖ ≤ C * (z 1) ^ gamma := by
  let C := ∑ i : Fin 3, ‖sourceCoefficient q branch gradient i‖
  refine ⟨C, Finset.sum_nonneg (fun i _ => norm_nonneg _), ?_⟩
  intro z hz
  have hy : 0 < z 1 := lt_of_lt_of_le (by norm_num) hz
  rw [sourcePrincipal]
  calc
    ‖∑ i : Fin 3, sourceCoefficient q branch gradient i *
        (z 1 : ℂ) ^ (principalExponent q i)‖ ≤
        ∑ i : Fin 3, ‖sourceCoefficient q branch gradient i *
          (z 1 : ℂ) ^ (principalExponent q i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖sourceCoefficient q branch gradient i‖ *
        (z 1) ^ (principalExponent q i).re := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    _ ≤ ∑ i : Fin 3, ‖sourceCoefficient q branch gradient i‖ * (z 1) ^ gamma := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hz
          ((principalExponent_re_le_sourceGrowth q i).trans hgamma.le))
        (norm_nonneg _)
    _ = C * (z 1) ^ gamma := by
      rw [Finset.sum_mul]

private theorem sourceRemainder_cusp_growth (q : XiZeroCopy) (branch gradient : Bool)
    (gamma : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 1 ≤ z 1 →
      ‖sourceRemainder q branch gradient z‖ ≤ C * (z 1) ^ gamma := by
  obtain ⟨C, hC, hbound⟩ :=
    source_remainder_weighted q branch gradient (-(gamma : ℂ))
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hy : 0 < z 1 := lt_of_lt_of_le (by norm_num) hz
  have hne : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hfactor : sourceRemainder q branch gradient z =
      (z 1 : ℂ) ^ (gamma : ℂ) *
        ((z 1 : ℂ) ^ (-(gamma : ℂ)) * sourceRemainder q branch gradient z) := by
    rw [← mul_assoc, ← Complex.cpow_add _ _ hne]
    simp
  rw [hfactor, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have h := hbound z hz
  simpa only [Complex.neg_re, Complex.ofReal_re, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hy.le _), mul_comm] using
    mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hy.le gamma)

private theorem sourceField_cusp_growth (q : XiZeroCopy) (branch gradient : Bool)
    (gamma : ℝ) (hgamma : sourceGrowthExponent q < gamma) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 1 ≤ z 1 →
      ‖sourceField q gradient z‖ ≤ C * (z 1) ^ gamma := by
  obtain ⟨A, hA, hprincipal⟩ := sourcePrincipal_cusp_growth q branch gradient gamma hgamma
  obtain ⟨B, hB, hremainder⟩ := sourceRemainder_cusp_growth q branch gradient gamma
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro z hz
  have hsplit : sourceField q gradient z =
      sourcePrincipal q branch gradient z + sourceRemainder q branch gradient z := by
    unfold sourceRemainder
    ring
  rw [hsplit]
  calc
    _ ≤ ‖sourcePrincipal q branch gradient z‖ +
        ‖sourceRemainder q branch gradient z‖ := norm_add_le _ _
    _ ≤ A * (z 1) ^ gamma + B * (z 1) ^ gamma :=
      add_le_add (hprincipal z hz) (hremainder z hz)
    _ = (A + B) * (z 1) ^ gamma := by ring

private theorem coordinates_continuous :
    Continuous (coordinates : UpperHalfPlane → Fin 2 → ℝ) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact UpperHalfPlane.continuous_re
  · exact UpperHalfPlane.continuous_im

private theorem sourceField_continuous (q : XiZeroCopy) (gradient : Bool) :
    Continuous (fun z : UpperHalfPlane => sourceField q gradient (coordinates z)) := by
  cases gradient
  · simpa [sourceField, Function.comp_def] using
      (continuous_iff_continuousAt.mpr (fun z =>
        (fullSquarePotential_smooth q _ z.im_pos 0).continuousAt.comp
          coordinates_continuous.continuousAt))
  · simpa [sourceField, Function.comp_def] using
      (continuous_iff_continuousAt.mpr (fun z =>
        ((fullGradientEnergy_smooth q _ z.im_pos).continuousAt.div_const 2).comp
          coordinates_continuous.continuousAt))

private theorem sourceGrowthExponent_nonneg (q : XiZeroCopy) :
    0 ≤ sourceGrowthExponent q := by
  have h := (sourceGrowthExponent_bounds q).1
  linarith

private theorem sourceField_global_growth (q : XiZeroCopy) (branch gradient : Bool)
    (gamma : ℝ) (hgamma : sourceGrowthExponent q < gamma) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane,
      ‖sourceField q gradient (coordinates z)‖ ≤
        C * (max 1 (max z.im (1 / z.im))) ^ gamma := by
  obtain ⟨D, hD, hDgrowth⟩ := sourceField_cusp_growth q branch gradient gamma hgamma
  have hgamma0 : 0 ≤ gamma := (sourceGrowthExponent_nonneg q).trans hgamma.le
  obtain ⟨K, hK⟩ := (truncated_cell_compact 1).exists_bound_of_continuousOn
    (sourceField_continuous q gradient).continuousOn
  let C := max 0 (max K D)
  have hC : 0 ≤ C := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro z
  obtain ⟨A, hA⟩ := exists_smul_mem_fd z
  have hinv := sourceField_modular q gradient A z
  have hheight : (A • z).im ≤ max z.im (1 / z.im) := by
    by_cases hc : A 1 0 = 0
    · obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      rw [hn z, ModularGroup.im_T_zpow_smul]
      exact le_max_left _ _
    · exact (nonparabolic_height_le A hc z).trans (le_max_right _ _)
  rw [← hinv]
  by_cases hy : (A • z).im ≤ 1
  · have hM : 1 ≤ max 1 (max z.im (1 / z.im)) := le_max_left _ _
    calc
      _ ≤ K := hK (A • z) ⟨hA, hy⟩
      _ ≤ C := (le_max_left K D).trans (le_max_right 0 _)
      _ ≤ C * (max 1 (max z.im (1 / z.im)) ^ gamma) :=
        le_mul_of_one_le_right hC (Real.one_le_rpow hM hgamma0)
  · have hy1 : 1 ≤ (A • z).im := (lt_of_not_ge hy).le
    have hM : (A • z).im ≤ max 1 (max z.im (1 / z.im)) :=
      hheight.trans (le_max_right _ _)
    calc
      _ ≤ D * ((A • z).im) ^ gamma := hDgrowth _ hy1
      _ ≤ D * (max 1 (max z.im (1 / z.im)) ^ gamma) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hM hgamma0) hD
      _ ≤ C * (max 1 (max z.im (1 / z.im)) ^ gamma) := by
        gcongr
        exact (le_max_right K D).trans (le_max_right 0 _)

/-- Global strict-rate growth of the actual scalar Laplacian.  This is not a
bound for a proxy: the full half-square and the complete gradient energy are
each retained through `fullSquarePotential_laplacian`. -/
theorem scalarLaplacian_fullSquarePotential_global_growth_at (q : XiZeroCopy)
    (gamma : ℝ) (hgamma : sourceGrowthExponent q < gamma) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane,
      ‖scalarLaplacian (fullSquarePotential q) (coordinates z)‖ ≤
        C * (max 1 (max z.im (1 / z.im)) ^ gamma) := by
  obtain ⟨A, hA, hsource⟩ := sourceField_global_growth q false false gamma hgamma
  obtain ⟨B, hB, hgradient⟩ := sourceField_global_growth q false true gamma hgamma
  let c : ℂ := 2 * (physicalRate q false + 1) * (physicalRate q false + 2)
  let C := ‖c‖ * A + 2 * B
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, ?_⟩
  intro z
  let M : ℝ := max 1 (max z.im (1 / z.im))
  have hsource' : ‖fullSquarePotential q (coordinates z)‖ ≤ A * M ^ gamma := by
    exact hsource z
  have hgradient' : ‖fullGradientEnergy q (coordinates z)‖ ≤ 2 * B * M ^ gamma := by
    have h := hgradient z
    change ‖fullGradientEnergy q (coordinates z) / 2‖ ≤ B * M ^ gamma at h
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have h2 : ‖fullGradientEnergy q (coordinates z)‖ =
        2 * ‖fullGradientEnergy q (coordinates z) / 2‖ := by
      rw [norm_div, hnorm2]
      ring
    rw [h2, mul_assoc]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have hlap := fullSquarePotential_laplacian q false (coordinates z) z.im_pos
  change scalarLaplacian (fullSquarePotential q) (coordinates z) =
    c * fullSquarePotential q (coordinates z) + fullGradientEnergy q (coordinates z) at hlap
  rw [hlap]
  calc
    ‖c * fullSquarePotential q (coordinates z) + fullGradientEnergy q (coordinates z)‖ ≤
        ‖c‖ * ‖fullSquarePotential q (coordinates z)‖ +
          ‖fullGradientEnergy q (coordinates z)‖ := by
      rw [← norm_mul]
      exact norm_add_le _ _
    _ ≤ ‖c‖ * (A * M ^ gamma) + 2 * B * M ^ gamma :=
      add_le_add (mul_le_mul_of_nonneg_left hsource' (norm_nonneg _)) hgradient'
    _ = C * M ^ gamma := by
      dsimp only [C]
      ring

private theorem denominator_bounds (d theta : ℝ) (hd : 0 ≤ d) :
    Real.exp (-d) ≤ denominator d theta ∧ denominator d theta ≤ Real.exp d := by
  rw [← Real.cosh_sub_sinh, ← Real.cosh_add_sinh]
  have hs := Real.sinh_nonneg_iff.mpr hd
  dsimp [denominator]
  constructor <;> nlinarith [Real.cos_le_one theta, Real.neg_one_le_cos theta]

private theorem average_norm_le {f : ℝ → ℂ} {C : ℝ}
    (h : ∀ theta, ‖f theta‖ ≤ C) : ‖average f‖ ≤ C := by
  have hb := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc 0 (2 * Real.pi)))
    (Filter.Eventually.of_forall h)
  have hm : (volume.restrict (Ioc 0 (2 * Real.pi))).real Set.univ = 2 * Real.pi := by
    simp [Measure.real, Real.volume_Ioc, Real.pi_pos.le]
  rw [hm] at hb
  dsimp only [average]
  rw [norm_mul, norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (C * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by field_simp

/-- The actual native angular action has any strictly-super-source global
radial growth rate.  Its proof averages the literal source Laplacian; no
native modal surrogate is introduced. -/
theorem angularAction_global_growth_at (q : XiZeroCopy) (X k gamma : ℝ)
    (hgamma : sourceGrowthExponent q < gamma) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 1 ≤ z →
      ‖angularAction q z X k‖ ≤ C * Real.exp (gamma * Real.arcosh z) := by
  obtain ⟨D, hD, hglobal⟩ :=
    scalarLaplacian_fullSquarePotential_global_growth_at q gamma hgamma
  have hgamma0 : 0 ≤ gamma := (sourceGrowthExponent_nonneg q).trans hgamma.le
  let C := D * Real.exp (gamma * |k|)
  refine ⟨C, mul_nonneg hD (Real.exp_nonneg _), ?_⟩
  intro z hz
  let d := Real.arcosh z
  have hd : 0 ≤ d := by
    dsimp [d]
    exact Real.arcosh_nonneg hz
  have hpoint (theta : ℝ) :
      ‖scalarLaplacian (fullSquarePotential q) (logCircle d theta X k)‖ ≤
        C * Real.exp (gamma * d) := by
    let Y : ℝ := Real.exp k / denominator d theta
    have hY : 0 < Y := div_pos (Real.exp_pos _) (denominator_pos _ _)
    let w : UpperHalfPlane := ⟨⟨logCircle d theta X k 0, Y⟩, hY⟩
    have hw : coordinates w = logCircle d theta X k := by
      ext i
      fin_cases i
      · rfl
      · dsimp [coordinates, w, Y, logCircle, circle, height]
        ring
    have hden := denominator_bounds d theta hd
    have hYupper : Y ≤ Real.exp (d + |k|) := by
      calc
        Y ≤ Real.exp k / Real.exp (-d) :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hden.1
        _ = Real.exp (k + d) := by
          rw [← Real.exp_sub]
          congr 1
          ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith [le_abs_self k])
    have hYinv : 1 / Y ≤ Real.exp (d + |k|) := by
      calc
        1 / Y = denominator d theta / Real.exp k := by
          dsimp [Y]
          field_simp
        _ ≤ Real.exp d / Real.exp k :=
          div_le_div_of_nonneg_right hden.2 (Real.exp_pos _).le
        _ = Real.exp (d - k) := (Real.exp_sub d k).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith [neg_le_abs k])
    have hM : max 1 (max w.im (1 / w.im)) ≤ Real.exp (d + |k|) := by
      apply max_le
      · exact Real.one_le_exp_iff.mpr (by positivity)
      · exact max_le hYupper hYinv
    have h := (hglobal w).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hM hgamma0) hD)
    rw [← Real.exp_mul] at h
    rw [← hw]
    calc
      _ ≤ D * Real.exp ((d + |k|) * gamma) := h
      _ = C * Real.exp (gamma * d) := by
        dsimp only [C]
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring
  have haction : angularAction q z X k =
      average (fun theta => scalarLaplacian (fullSquarePotential q)
        (logCircle d theta X k)) := by
    dsimp only [d]
    simpa only [angularAction, angularKernel] using
      (mean_laplacian_commutes q (Real.arcosh z) X k)
  rw [haction]
  exact average_norm_le hpoint

/-- The nonsingular Volterra current has the same strict radial growth as its
literal angular source. -/
theorem characteristicFirst_global_growth_at (q : XiZeroCopy) (X k gamma : ℝ)
    (hgamma : sourceGrowthExponent q < gamma) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 1 ≤ z →
      ‖characteristicFirst q z X k‖ ≤ C * Real.exp (gamma * Real.arcosh z) := by
  obtain ⟨A, hA, haction⟩ := angularAction_global_growth_at q X k gamma hgamma
  have hgamma0 : 0 ≤ gamma := (sourceGrowthExponent_nonneg q).trans hgamma.le
  refine ⟨A, hA, ?_⟩
  intro z hz
  let K : ℝ := A * Real.exp (gamma * Real.arcosh z)
  have hK : 0 ≤ K := mul_nonneg hA (Real.exp_nonneg _)
  have hintegral : ‖∫ t in (0 : ℝ)..1, angularAction q (1 + t * (z - 1)) X k‖ ≤ K := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t : ℝ => angularAction q (1 + t * (z - 1)) X k)
      (a := (0 : ℝ)) (b := 1) (C := K) (fun t ht => by
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
          exact ⟨ht.1.le, ht.2⟩
        have hr : 1 ≤ 1 + t * (z - 1) := by
          exact le_add_of_nonneg_right (mul_nonneg ht'.1 (sub_nonneg.mpr hz))
        have hrz : 1 + t * (z - 1) ≤ z := by
          nlinarith [mul_le_mul_of_nonneg_right ht'.2 (sub_nonneg.mpr hz)]
        have harcosh : Real.arcosh (1 + t * (z - 1)) ≤ Real.arcosh z :=
          (Real.arcosh_le_arcosh (by positivity) (by positivity)).mpr hrz
        calc
          _ ≤ A * Real.exp (gamma * Real.arcosh (1 + t * (z - 1))) :=
            haction _ hr
          _ ≤ A * Real.exp (gamma * Real.arcosh z) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left harcosh hgamma0)) hA
          _ = K := rfl)
    simpa using h
  have hden : 1 ≤ ‖(z + 1 : ℂ)‖ := by
    rw [show ((z : ℂ) + 1) = (((z + 1 : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  unfold characteristicFirst
  calc
    ‖(∫ t in (0 : ℝ)..1, angularAction q (1 + t * (z - 1)) X k) / (z + 1 : ℂ)‖ =
        ‖∫ t in (0 : ℝ)..1, angularAction q (1 + t * (z - 1)) X k‖ /
          ‖(z + 1 : ℂ)‖ := norm_div _ _
    _ ≤ ‖∫ t in (0 : ℝ)..1, angularAction q (1 + t * (z - 1)) X k‖ :=
      div_le_self (norm_nonneg _) hden
    _ ≤ K := hintegral
    _ = A * Real.exp (gamma * Real.arcosh z) := rfl

/-- The physical interior radial derivative has strict global growth because
the exact Volterra formula identifies it with `characteristicFirst`. -/
theorem argumentFirst_global_growth_at (q : XiZeroCopy) (X k gamma : ℝ)
    (hgamma : sourceGrowthExponent q < gamma) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Ioi (1 : ℝ),
      ‖argumentFirst q z X k‖ ≤ C * Real.exp (gamma * Real.arcosh z.val) := by
  obtain ⟨C, hC, hbound⟩ := characteristicFirst_global_growth_at q X k gamma hgamma
  refine ⟨C, hC, ?_⟩
  intro z
  rw [argumentFirst_volterra q X k z]
  exact hbound z.val z.property.le

end
end RHTower.D4BMNativeCircle
