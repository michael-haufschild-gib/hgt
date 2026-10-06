import GaloisForLFunctions.RHTower.ChiCubicExteriorMultiplier

/-!
# Complete exterior estimate for the physical cubic

The exact normal symbol gives the full shrinking-cone exterior as a
regularized inverse-defect multiplier of the normal Fourier iterate.
Every Schwartz seminorm of the actual physical exterior is bounded by
C N^M / (N log^3 N H^k epsilon^(k+R)), with M,R fixed before k.
There is no frequency truncation, sheet restriction or source-norm premise.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff FourierTransform
namespace RHTower.BAGTrace
private abbrev E := BAGPhysicalSpace

/-- Canonical full exterior in frequency space. It uses the zeroth
inverse-power multiplier, exactly 1-chi(D/epsilon). -/
def bagCubicExteriorFourier (ε : ℝ) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  bagCubicExteriorMultiply 0 ε (𝓕 f)

/-- Canonical physical exterior; no compact support is imposed. -/
def bagCubicExteriorPhysical (ε : ℝ) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  𝓕⁻ (bagCubicExteriorFourier ε f)

theorem bagCubicExteriorFourier_apply (ε : ℝ) (f : SchwartzMap E ℂ) (x : E) :
    bagCubicExteriorFourier ε f x =
      (1-bagCubicConeCutoff (bagCubicSignedDefect x/ε)) • (𝓕 f) x := by
  simp only [bagCubicExteriorFourier,bagCubicExteriorMultiply_apply,
    bagCubicExteriorMultiplier,bagCubicExteriorInversePower,pow_zero,div_one]
  rw [div_eq_inv_mul]

/-- Exact normal integration by parts for the COMPLETE exterior. The
identity includes zero defect and all signed sheets. -/
theorem bagCubicExteriorFourier_normal (k : ℕ) (ε : {r : ℝ // 0 < r})
    (f : SchwartzMap E ℂ) :
    bagCubicExteriorFourier ε.1 f =
      (((2*Real.pi*Complex.I : ℂ)^k)⁻¹ * ((ε.1 : ℂ)^k)⁻¹) •
        bagCubicExteriorMultiply k ε.1 (𝓕 (bagCubicNormalOperator^[k] f)) := by
  ext x
  rw [bagCubicExteriorFourier_apply]
  change _ = _ * bagCubicExteriorMultiply k ε.1 (𝓕 (bagCubicNormalOperator^[k] f)) x
  rw [bagCubicExteriorMultiply_apply,bagCubicNormalOperator_iterate_fourier]
  simp only [bagCubicExteriorMultiplier,bagCubicExteriorInversePower,Complex.real_smul,
    bagCubicSignedDefect]
  by_cases hx : x 2+x 0*x 1 = 0
  · have hc : bagCubicConeCutoff 0 = 1 := bagCubicConeCutoff.one_of_mem_closedBall
      (by simp [bagCubicConeCutoff])
    simp only [hx,zero_div,mul_zero,sub_self,zero_mul,hc,Complex.ofReal_zero]
  · have hε : (ε.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ε.2.ne'
    have hxC : ((x 2+x 0*x 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    have hc : (2*Real.pi*Complex.I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    rw [show ε.1⁻¹*(x 2+x 0*x 1) = (x 2+x 0*x 1)/ε.1 by ring]
    push_cast only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
    rw [div_pow]
    field_simp


/-- The paid normal Fourier budgets survive the entire shrinking
multiplier. Polynomial degree is chosen before normal iteration. -/
theorem bagCubicControlledPhysicalSchwartz_normal_exterior_fourier_seminorm (p n : ℕ) :
    ∃ M : ℕ, ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ N : {r : ℝ // Real.exp 1 ≤ r},
      ∀ H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)}, 1 ≤ H.1 →
      ∀ ε : {r : ℝ // r ∈ Ioc (0 : ℝ) 1},
        SchwartzMap.seminorm ℂ p n (bagCubicExteriorMultiply k ε.1
          (𝓕 (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H)))) ≤
            C*N.1^M/(N.1*Real.log N.1^3*H.1^k*ε.1^n) := by
  obtain ⟨K,hK⟩ := bagCubicExteriorMultiply_seminorm p n
  choose M hM using fun i : ℕ × ℕ =>
    bagCubicControlledPhysicalSchwartz_normal_fourier_seminorm i.1 i.2
  refine ⟨K.sup M,fun k => ?_⟩
  obtain ⟨B,hB,hBb⟩ := hK k
  choose A hA hAb using fun i : ℕ × ℕ => hM i k
  let C : ℝ := 1+∑ i ∈ K, A i
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ i ∈ K, A i := Finset.sum_nonneg (fun i _ => (hA i).le)
    dsimp only [C]; linarith
  refine ⟨B*C,mul_pos hB hC,fun N H hH ε => ?_⟩
  have hN1 : 1 < N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
  have hN : 0 < N.1 := lt_trans zero_lt_one hN1
  have hε : 0 < ε.1 := ε.2.1
  let den := N.1*Real.log N.1^3*H.1^k
  have hden : 0 < den := mul_pos (mul_pos hN (pow_pos (Real.log_pos hN1) 3)) (pow_pos H.2.1 k)
  let f := 𝓕 (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H))
  have hs : (K.sup (schwartzSeminormFamily ℂ E ℂ)) f ≤ C*N.1^(K.sup M)/den := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i hi
    have hAC : A i ≤ C := (Finset.single_le_sum (fun j _ => (hA j).le) hi).trans
      (by dsimp only [C]; linarith)
    exact (hAb i N H hH).trans (div_le_div_of_nonneg_right
      (mul_le_mul hAC (pow_le_pow_right₀ hN1.le (Finset.le_sup hi))
        (pow_nonneg hN.le _) hC.le) hden.le)
  calc
    _ ≤ B/ε.1^n*(K.sup (schwartzSeminormFamily ℂ E ℂ)) f := hBb ε f
    _ ≤ B/ε.1^n*(C*N.1^(K.sup M)/den) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by dsimp only [den]; ring

private theorem inverse_fourier_seminorm_control (p n : ℕ) :
    ∃ K : Finset (ℕ × ℕ), ∃ B : ℝ, 0 ≤ B ∧ ∀ f : SchwartzMap E ℂ,
      SchwartzMap.seminorm ℂ p n (𝓕⁻ f) ≤ B*(K.sup (schwartzSeminormFamily ℂ E ℂ)) f := by
  let T : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
    (FourierTransform.fourierCLE ℂ (SchwartzMap E ℂ)).symm.toContinuousLinearMap
  let q : Seminorm ℂ (SchwartzMap E ℂ) := (SchwartzMap.seminorm ℂ p n).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℂ E ℂ).continuous_seminorm (p,n)).comp T.continuous
  obtain ⟨K,B,_,hb⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq
  refine ⟨K,B,B.coe_nonneg,fun f => ?_⟩
  have he := hb f
  rw [_root_.smul_apply, NNReal.smul_def, smul_eq_mul] at he
  exact he


private theorem normal_exterior_inverse_seminorm (p n : ℕ) :
    ∃ M R : ℕ, ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ N : {r : ℝ // Real.exp 1 ≤ r},
      ∀ H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)}, 1 ≤ H.1 →
      ∀ ε : {r : ℝ // r ∈ Ioc (0 : ℝ) 1},
        SchwartzMap.seminorm ℂ p n (𝓕⁻ (bagCubicExteriorMultiply k ε.1
          (𝓕 (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H))))) ≤
            C*N.1^M/(N.1*Real.log N.1^3*H.1^k*ε.1^R) := by
  obtain ⟨K,B,hB,hBb⟩ := inverse_fourier_seminorm_control p n
  choose M hM using fun i : ℕ × ℕ =>
    bagCubicControlledPhysicalSchwartz_normal_exterior_fourier_seminorm i.1 i.2
  refine ⟨K.sup M,K.sup Prod.snd,fun k => ?_⟩
  choose A hA hAb using fun i : ℕ × ℕ => hM i k
  let C : ℝ := 1+∑ i ∈ K, A i
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ i ∈ K, A i := Finset.sum_nonneg (fun i _ => (hA i).le)
    dsimp only [C]; linarith
  refine ⟨B*C+1,by positivity,fun N H hH ε => ?_⟩
  have hN1 : 1 < N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
  have hN : 0 < N.1 := lt_trans zero_lt_one hN1
  have hε : 0 < ε.1 := ε.2.1
  let den := N.1*Real.log N.1^3*H.1^k
  have hden : 0 < den := mul_pos (mul_pos hN (pow_pos (Real.log_pos hN1) 3)) (pow_pos H.2.1 k)
  let f := bagCubicExteriorMultiply k ε.1
    (𝓕 (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H)))
  have hs : (K.sup (schwartzSeminormFamily ℂ E ℂ)) f ≤
      C*N.1^(K.sup M)/(den*ε.1^(K.sup Prod.snd)) := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i hi
    have hAC : A i ≤ C := (Finset.single_le_sum (fun j _ => (hA j).le) hi).trans
      (by dsimp only [C]; linarith)
    refine (hAb i N H hH ε).trans (div_le_div₀ (by positivity) ?_ (by positivity) ?_)
    · exact mul_le_mul hAC (pow_le_pow_right₀ hN1.le (Finset.le_sup hi))
        (pow_nonneg hN.le _) hC.le
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hε.le ε.2.2 (Finset.le_sup hi)) hden.le
  calc
    _ ≤ B*(K.sup (schwartzSeminormFamily ℂ E ℂ)) f := hBb f
    _ ≤ B*(C*N.1^(K.sup M)/(den*ε.1^(K.sup Prod.snd))) := mul_le_mul_of_nonneg_left hs hB
    _ = (B*C)*N.1^(K.sup M)/(den*ε.1^(K.sup Prod.snd)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hN.le _)) (by positivity)

/-- Complete physical-space exterior estimate for the literal amplitude.
Every recipient Schwartz seminorm has fixed costs M,R BEFORE k, and
retains H^(-k) epsilon^(-k). No arithmetic norm or inverse-defect bound
is assumed, and no sheet, transition region, or infinite tail is dropped. -/
theorem bagCubicControlledPhysicalSchwartz_exterior_seminorm (p n : ℕ) :
    ∃ M R : ℕ, ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ N : {r : ℝ // Real.exp 1 ≤ r},
      ∀ H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)}, 1 ≤ H.1 →
      ∀ ε : {r : ℝ // r ∈ Ioc (0 : ℝ) 1},
        SchwartzMap.seminorm ℂ p n
          (bagCubicExteriorPhysical ε.1 (bagCubicExpControlledPhysicalSchwartz N H)) ≤
            C*N.1^M/(N.1*Real.log N.1^3*H.1^k*ε.1^(k+R)) := by
  obtain ⟨M,R,hMR⟩ := normal_exterior_inverse_seminorm p n
  refine ⟨M,R,fun k => ?_⟩
  obtain ⟨C,hC,hCb⟩ := hMR k
  let a : ℂ := ((2*Real.pi*Complex.I : ℂ)^k)⁻¹
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr (inv_ne_zero (pow_ne_zero k
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)))
  refine ⟨‖a‖*C,mul_pos ha hC,fun N H hH ε => ?_⟩
  rw [bagCubicExteriorPhysical,bagCubicExteriorFourier_normal k ⟨ε.1,ε.2.1⟩,
    FourierTransform.fourierInv_smul,map_smul_eq_mul]
  have he : ‖a*((ε.1 : ℂ)^k)⁻¹‖ = ‖a‖/ε.1^k := by
    simp only [norm_mul,norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ε.2.1,div_eq_mul_inv]
  change ‖a*((ε.1 : ℂ)^k)⁻¹‖ * _ ≤ _
  rw [he]
  calc
    _ ≤ (‖a‖/ε.1^k)*(C*N.1^M/(N.1*Real.log N.1^3*H.1^k*ε.1^R)) :=
      mul_le_mul_of_nonneg_left (hCb N H hH ε) (div_nonneg ha.le (pow_nonneg ε.2.1.le k))
    _ = _ := by rw [pow_add]; ring


end RHTower.BAGTrace
