import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheBoundaryFourierPowerOfAConfinedState
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# High-frequency confinement mass

After removal of distant critical-line copies the boundary Fourier power
and the remaining Poisson-weighted copies have a positive joint limit.
The limit equals four times the confinement mass of the state.
-/

noncomputable section
open MeasureTheory Set Complex Filter Zeta23
open scoped Topology ComplexConjugate
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private abbrev Off := (↑onLineCopiesᶜ : Type)

private theorem reflect_centre (q : XiZeroCopy) :
    centredZero (xiZeroCopyReflectEquiv q) = -centredZero q := by
  simp only [centredZero,xiZeroCopy_reflect_val]
  ring

private def reflectOff : Off ≃ Off := xiZeroCopyReflectEquiv.subtypeEquiv fun q => by
  change (¬ (centredZero q).re = 0) ↔ (¬ (centredZero (xiZeroCopyReflectEquiv q)).re = 0)
  rw [reflect_centre,neg_re,neg_eq_zero]

/-- Reflected products are even on the centred divisor, so their first
moment vanishes on every finite off-line layer. -/
private theorem off_first_moment (F : ℝ → ℝ) [Fintype Off] :
    ∑ q : Off, reflectedLaplaceProduct F q * centredZero q = 0 := by
  let A := fun q : Off => reflectedLaplaceProduct F q * centredZero q
  have hneg (q : Off) : A (reflectOff q) = -(A q) := by
    change reflectedLaplaceProduct F (xiZeroCopyReflectEquiv q) * centredZero (xiZeroCopyReflectEquiv q) = _
    simp only [A,reflectedLaplaceProduct,reflect_centre,neg_neg]
    ring
  have h := reflectOff.sum_comp A
  simp_rw [hneg,Finset.sum_neg_distrib] at h
  change ∑ q, A q = 0
  linear_combination -(h / 2)

/-- The off-line coefficient sum is real. Its deficit pays for all
critical-line mass and the confinement term. -/
private theorem off_total {R : ℝ} {F : ℝ → ℝ} (hF : IsConfinedNullVector R F)
    (hfin : BacklundConverse.FiniteOffLine) :
    (∑' q : Off, reflectedLaplaceProduct F q) =
      ((-(criticalAliasCoefficient R * criticalHalfLineExponentialPair F F) -
        ∑' q : onLineCopies, zeroValueMass F q : ℝ) : ℂ) := by
  have h := (domain_zeroParseval_of_finiteOffLine hF.1 hfin).2
  have hn := hF.2.2 F hF.1
  rw [criticalHalfLineMixedEnergy_eq_bare_add,setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun u hu => by rw [hF.1.support u (not_lt.mp hu),zero_mul,zero_mul])] at hn
  change bareMixedEnergy F F + criticalAliasCoefficient R * criticalHalfLineExponentialPair F F = 0 at hn
  have hb : bareMixedEnergy F F = -(criticalAliasCoefficient R * criticalHalfLineExponentialPair F F) := by
    linarith only [hn]
  rw [hb] at h
  change (↑(∑' q : onLineCopies, zeroValueMass F q) : ℂ) + (∑' q : Off, reflectedLaplaceProduct F q) = _ at h
  rw [Complex.ofReal_sub]
  linear_combination h

private theorem inv_vertical_tendsto (b : ℂ) :
    Tendsto (fun y : ℝ => (b+(y:ℂ)*I)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  apply tendsto_inv_atTop_zero.comp
  have ht : Tendsto (fun y : ℝ => y+b.im) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  apply tendsto_atTop_mono _ ht
  intro y
  have h := (le_abs_self (b+(y:ℂ)*I).im).trans (Complex.abs_im_le_norm _)
  simpa only [add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,
    Complex.I_re,mul_one,mul_zero,add_zero,add_comm] using h

private theorem expanded_kernel (b : ℂ) (y : ℝ) (hn : b+(y:ℂ)*I ≠ 0) :
    (y:ℂ)^2 * (b+(y:ℂ)*I)⁻¹ =
      b-(y:ℂ)*I-b^2*(b+(y:ℂ)*I)⁻¹ := by
  have he : (b-(y:ℂ)*I)*(b+(y:ℂ)*I) = b^2+(y:ℂ)^2 := by
    calc _ = b^2-(y:ℂ)^2*Complex.I^2 := by ring
         _ = _ := by rw [Complex.I_sq]; ring
  calc _ = ((b-(y:ℂ)*I)*(b+(y:ℂ)*I)-b^2)*(b+(y:ℂ)*I)⁻¹ := by rw [he]; ring
       _ = _ := by rw [sub_mul,mul_assoc,mul_inv_cancel₀ hn,mul_one]

/-- At large ordinates the real part of the off-line transform reads its total
mass. The first centred moment cancels by reflection. -/
private theorem off_scaled_limit {R : ℝ} {F : ℝ → ℝ} (hF : IsConfinedNullVector R F)
    (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun y : ℝ => y^2 * (-(reflectedOffLineResolvent F ⟨4,y⟩).re)) atTop
      (𝓝 (4*(criticalAliasCoefficient R * criticalHalfLineExponentialPair F F +
        ∑' q : onLineCopies, zeroValueMass F q))) := by
  classical
  letI : Fintype Off := (compl_onLineCopies_finite_of_finiteOffLine hf).fintype
  let A := fun q : Off => reflectedLaplaceProduct F q
  let b := fun q : Off => 4 - centredZero q
  let E := fun (y : ℝ) (q : Off) => (A q*(b q)^2) * (b q+(y:ℂ)*I)⁻¹
  let S := -(criticalAliasCoefficient R*criticalHalfLineExponentialPair F F) -
    ∑' q : onLineCopies, zeroValueMass F q
  have hA : ∑ q, A q = (S:ℂ) := by simpa only [tsum_fintype,A,S] using off_total hF hf
  have hfirst : ∑ q : Off, A q * centredZero q = 0 := off_first_moment F
  have hE : Tendsto (fun y : ℝ => ∑ q : Off, E y q) atTop (𝓝 0) := by
    have h (q : Off) : Tendsto (fun y => E y q) atTop (𝓝 0) := by
      simpa only [E,mul_zero] using (inv_vertical_tendsto (b q)).const_mul (A q * (b q)^2)
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun q _ => h q)
  have he (y : ℝ) : ((y^2:ℝ):ℂ) * reflectedOffLineResolvent F ⟨4,y⟩ =
      (4-(y:ℂ)*I)*(S:ℂ) - ∑ q : Off, E y q := by
    calc _ = ((4-(y:ℂ)*I) * ∑ q, A q) - (∑ q : Off, A q*centredZero q) - ∑ q : Off, E y q := by
          rw [reflectedOffLineResolvent,tsum_fintype,Finset.mul_sum,Finset.mul_sum,
            ← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro q _
          have hz : 0 < (b q + (y:ℂ)*I).re := by
            have h := (abs_lt.mp (abs_re_centredZero_lt q.val)).2
            simp only [b,add_re,sub_re,re_ofNat,Complex.mul_re,Complex.I_re,Complex.I_im,
              Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
            linarith only [h]
          have hk := expanded_kernel (b q) y (fun e => hz.ne' (congrArg Complex.re e))
          have hp : (⟨4,y⟩ : ℂ) - centredZero q = b q+(y:ℂ)*I := by
            apply Complex.ext <;> simp [b,Complex.mul_re,Complex.mul_im,sub_eq_add_neg,add_comm]
          rw [hp,Complex.ofReal_pow]
          dsimp only [E]
          change (y:ℂ)^2*(A q*_) = _
          dsimp only [b] at hk ⊢
          linear_combination A q * hk
         _ = _ := by rw [hA,hfirst,sub_zero]
  have hre (y : ℝ) : y^2 * (-(reflectedOffLineResolvent F ⟨4,y⟩).re) =
      (∑ q : Off, E y q).re - 4*S := by
    have h := congrArg Complex.re (he y)
    simp only [sub_re,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,re_ofNat] at h
    linarith only [h]
  have hlim : Tendsto (fun y : ℝ => (∑ q : Off, E y q).re - 4*S) atTop (𝓝 (-(4*S))) := by
    simpa only [Function.comp_apply,Complex.zero_re,zero_sub] using
      (Complex.continuous_re.continuousAt.tendsto.comp hE).sub_const (4*S)
  rw [show -(4*S) = 4*(criticalAliasCoefficient R * criticalHalfLineExponentialPair F F +
    ∑' q : onLineCopies, zeroValueMass F q) by dsimp only [S]; ring] at hlim
  exact hlim.congr fun y => (hre y).symm

private def poissonWeight (y γ : ℝ) : ℝ := 4/(16+(y-γ)^2)

private theorem weight_nonneg (y γ : ℝ) : 0 ≤ poissonWeight y γ := by
  unfold poissonWeight
  positivity

private theorem weight_le_one (y γ : ℝ) : poissonWeight y γ ≤ 1 := by
  apply (div_le_one (by positivity : 0 < 16+(y-γ)^2)).mpr
  linarith only [sq_nonneg (y-γ)]

private theorem scaled_weight_tendsto (γ : ℝ) :
    Tendsto (fun y : ℝ => y^2*poissonWeight y γ) atTop (𝓝 4) := by
  have h0 : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hd : Tendsto (fun y : ℝ => 16*y⁻¹^2+(1-γ*y⁻¹)^2) atTop (𝓝 1) := by
    simpa only [zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero,one_pow,zero_add] using
      ((h0.pow 2).const_mul 16).add ((tendsto_const_nhds (x := (1:ℝ))).sub (h0.const_mul γ) |>.pow 2)
  have h : Tendsto (fun y : ℝ => 4/(16*y⁻¹^2+(1-γ*y⁻¹)^2)) atTop (𝓝 4) := by
    have hdiv := (tendsto_const_nhds (x := (4:ℝ))).div hd one_ne_zero
    change Tendsto (fun y : ℝ => (4:ℝ)/(16*y⁻¹^2+(1-γ*y⁻¹)^2)) atTop (𝓝 (4/(1:ℝ))) at hdiv
    rwa [div_one] at hdiv
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have hpos : 0 < 16*y⁻¹^2+(1-γ*y⁻¹)^2 := by positivity
  have hd0 : 0 < 16+(y-γ)^2 := by positivity
  unfold poissonWeight
  rw [mul_div_assoc',div_eq_div_iff hpos.ne' hd0.ne']
  field_simp [hy.ne']

private def farTerm (δ y γ m : ℝ) : ℝ := if |y-γ| < δ*y then 0 else y^2*poissonWeight y γ*m

/-- Removing a fixed relative neighborhood leaves a dominated sum: the
Poisson weight of each fixed copy tends to four after rescaling. -/
private theorem far_scaled_limit {ι : Type*} {m γ : ι → ℝ} (hm : Summable m)
    (hn : ∀ q, 0 ≤ m q) {δ : ℝ} (hδ : 0 < δ) (h₁ : δ < 1) :
    Tendsto (fun y : ℝ => ∑' q, farTerm δ y (γ q) (m q)) atTop (𝓝 (4*∑' q, m q)) := by
  rw [← tsum_mul_left]
  apply tendsto_tsum_of_dominated_convergence (hm.mul_left (4/δ^2))
  · intro q
    refine ((scaled_weight_tendsto (γ q)).mul_const (m q)).congr' ?_
    filter_upwards [eventually_ge_atTop ((γ q)/(1-δ))] with y hy
    have h := (div_le_iff₀ (sub_pos.mpr h₁)).mp hy
    have hfar : ¬ |y-γ q| < δ*y := not_lt.mpr ((by linarith only [h] : δ*y ≤ y-γ q).trans (le_abs_self _))
    simp only [farTerm,if_neg hfar]
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy q
    unfold farTerm
    split_ifs with hnear
    · rw [norm_zero]
      exact mul_nonneg (by positivity) (hn _)
    · rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (weight_nonneg _ _)) (hn _))]
      apply mul_le_mul_of_nonneg_right _ (hn _)
      have hδy := le_of_not_gt hnear
      have hmajor : δ^2*y^2 ≤ (y-γ q)^2 := by
        calc _ = (δ*y)^2 := (mul_pow _ _ _).symm
             _ ≤ |y-γ q|^2 := pow_le_pow_left₀ (mul_pos hδ hy).le hδy 2
             _ = _ := sq_abs _
      unfold poissonWeight
      rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (pow_pos hδ 2)]
      nlinarith only [hmajor]

/-- Every relative ordinate window retains the same positive high-frequency
mass after the distant critical-line background is subtracted. -/
theorem IsConfinedNullVector.localized_high_frequency_mass {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hf : BacklundConverse.FiniteOffLine) {δ : ℝ}
    (hδ : 0 < δ) (h₁ : δ < 1) :
    0 < 4*(criticalAliasCoefficient R * criticalHalfLineExponentialPair F F) ∧
    Tendsto (fun y : ℝ => y^2*((criticalAliasCoefficient R/2)*‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2 +
      ∑' q : onLineCopies, if |y-(centredZero q).im| < δ*y then
        zeroValueMass F q * (4/(16+(y-(centredZero q).im)^2)) else 0)) atTop
      (𝓝 (4*(criticalAliasCoefficient R * criticalHalfLineExponentialPair F F))) := by
  let m := fun q : onLineCopies => zeroValueMass F q
  let γ := fun q : onLineCopies => (centredZero q).im
  have hm : Summable m := (domain_zeroParseval_of_finiteOffLine hF.1 hf).1
  have hn (q : onLineCopies) : 0 ≤ m q := zeroValueMass_nonneg _ _
  have hfar := far_scaled_limit (γ := γ) hm hn hδ h₁
  have hlim := (off_scaled_limit hF hf).sub hfar
  have e : 4*(criticalAliasCoefficient R * criticalHalfLineExponentialPair F F + ∑' q, m q) -
      4*∑' q, m q = 4*(criticalAliasCoefficient R * criticalHalfLineExponentialPair F F) := by ring
  rw [e] at hlim
  refine ⟨mul_pos (by norm_num) (mul_pos (criticalAliasCoefficient_positive hr)
    (exponentialPair_self_pos hF.1 hF.2.1)), hlim.congr fun y => ?_⟩
  let w := fun q : onLineCopies => m q * poissonWeight y (γ q)
  let n := fun q : onLineCopies => if |y-γ q| < δ*y then w q else 0
  let d := fun q : onLineCopies => if |y-γ q| < δ*y then 0 else w q
  have hw : Summable w := hm.of_nonneg_of_le (fun q => mul_nonneg (hn _) (weight_nonneg _ _))
    (fun q => mul_le_of_le_one_right (hn q) (weight_le_one _ _))
  have hw0 (q : onLineCopies) : 0 ≤ w q := mul_nonneg (hn _) (weight_nonneg _ _)
  have hns : Summable n := hw.of_nonneg_of_le (fun q => by unfold n; split_ifs <;> simp [hw0])
    (fun q => by unfold n; split_ifs <;> simp [hw0])
  have hds : Summable d := hw.of_nonneg_of_le (fun q => by unfold d; split_ifs <;> simp [hw0])
    (fun q => by unfold d; split_ifs <;> simp [hw0])
  have hs : ∑' q, w q = (∑' q, n q) + ∑' q, d q := by
    rw [← hns.tsum_add hds]
    apply tsum_congr
    intro q
    dsimp only [n,d]
    split_ifs <;> simp
  have he : (∑' q, farTerm δ y (γ q) (m q)) = y^2*(∑' q, d q) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro q
    unfold farTerm d w
    split_ifs <;> ring
  have hb := hF.boundary_poisson_identity hr y
  change _ + (∑' q, w q) = _ at hb
  change y^2*(-(reflectedOffLineResolvent F ⟨4,y⟩).re) - (∑' q, farTerm δ y (γ q) (m q)) =
    y^2*((criticalAliasCoefficient R/2)*‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2 + ∑' q, n q)
  rw [← hb,hs,he]
  ring

#print axioms IsConfinedNullVector.localized_high_frequency_mass
end GaloisForLFunctions.ExclusionOfTheCriticalState
