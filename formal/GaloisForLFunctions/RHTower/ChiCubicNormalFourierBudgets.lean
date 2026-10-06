import GaloisForLFunctions.RHTower.ChiCubicPhysicalNormalJets

/-!
# Weighted Fourier control of the actual normal iterates

The literal physical support and all-order jet bounds pay every physical
Schwartz seminorm. Continuity of Fourier transformation then preserves
the complete normal-order gain H^(-k) in EVERY weighted Fourier seminorm.
The polynomial cost in N is selected before k. Thus further normal
iteration gains decay without increasing that polynomial cost.
-/

noncomputable section
open Set
open scoped FourierTransform NNReal
namespace RHTower.BAGTrace
private abbrev E := BAGPhysicalSpace
private def box : Set E := {v | ∀ i, v i ∈ Icc (1 : ℝ) 2}
private theorem box_compact : IsCompact box := by
  have he : box = (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)) ⁻¹'
      (Set.univ.pi (fun _ : Fin 3 => Icc (1 : ℝ) 2)) := by
    ext v
    change (∀ i, v i ∈ Icc (1 : ℝ) 2) ↔
      ∀ i ∈ (Set.univ : Set (Fin 3)), v i ∈ Icc (1 : ℝ) 2
    simp only [Set.mem_univ, forall_const]
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc (a := (1 : ℝ)) (b := 2)))

private theorem cube_norm_bound : ∃ B : ℝ, 0 < B ∧
    ∀ N : {r : ℝ // 0 < r}, ∀ x : E, (∀ i, x i ∈ Icc N.1 (2*N.1)) → ‖x‖ ≤ B*N.1 := by
  obtain ⟨B,hB⟩ := box_compact.exists_bound_of_continuousOn (continuous_id : Continuous (id : E → E)).continuousOn
  refine ⟨max B 0+1,by positivity,fun N x hx => ?_⟩
  let v : E := (1/N.1) • x
  have hv : v ∈ box := by
    intro i
    change 1 ≤ (1/N.1)*x i ∧ (1/N.1)*x i ≤ 2
    rw [show (1/N.1)*x i = x i/N.1 by ring]
    exact ⟨(le_div_iff₀ N.2).mpr (by simpa using (hx i).1),
      (div_le_iff₀ N.2).mpr ((hx i).2)⟩
  have he : N.1 • v = x := by
    dsimp only [v]
    rw [smul_smul, show N.1*(1/N.1)=1 by field_simp [N.2.ne'], one_smul]
  calc
    ‖x‖ = N.1*‖v‖ := by rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos N.2]
    _ ≤ N.1*(max B 0+1) := mul_le_mul_of_nonneg_left
      ((hB v hv).trans (by linarith [le_max_left B 0])) N.2.le
    _ = _ := by ring

/-- Every physical Schwartz seminorm retains the full normal-order gain.
Its polynomial degree in N is the physical weight order, independently
of the number of normal iterations. -/
theorem bagCubicControlledPhysicalSchwartz_normal_seminorm (k p n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : {r : ℝ // Real.exp 1 ≤ r},
      ∀ H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)}, 1 ≤ H.1 →
        SchwartzMap.seminorm ℂ p n
          (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H)) ≤
            C*N.1^p/(N.1*Real.log N.1^3*H.1^k) := by
  obtain ⟨A,hA,hb⟩ := bagCubicControlledPhysicalSchwartz_normal_uniform_jets k n
  obtain ⟨B,hB,hBb⟩ := cube_norm_bound
  refine ⟨B^p*A,mul_pos (pow_pos hB p) hA,fun N H hH => ?_⟩
  have hN1 : 1 < N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
  have hN : 0 < N.1 := lt_trans zero_lt_one hN1
  have hden : 0 < N.1*Real.log N.1^3*H.1^k :=
    mul_pos (mul_pos hN (pow_pos (Real.log_pos hN1) 3)) (pow_pos H.2.1 k)
  apply SchwartzMap.seminorm_le_bound ℂ p n _ (by positivity)
  intro x
  by_cases hx : ∀ i, x i ∈ Icc N.1 (2*N.1)
  · calc
      _ ≤ (B*N.1)^p*(A/(N.1*Real.log N.1^3*H.1^k)) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hBb ⟨N.1,hN⟩ x hx) p)
          (hb N H hH x) (norm_nonneg _) (pow_nonneg (mul_pos hB hN).le p)
      _ = _ := by rw [mul_pow]; ring
  · rw [bagCubicControlledPhysicalSchwartz_normal_jet_off k n N H ⟨x,hx⟩, norm_zero, mul_zero]
    positivity

private theorem fourier_seminorm_control (p n : ℕ) :
    ∃ K : Finset (ℕ × ℕ), ∃ B : ℝ, 0 ≤ B ∧ ∀ f : SchwartzMap E ℂ,
      SchwartzMap.seminorm ℂ p n (𝓕 f) ≤ B*(K.sup (schwartzSeminormFamily ℂ E ℂ)) f := by
  let T : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ := SchwartzMap.fourierTransformCLM ℂ
  let q : Seminorm ℂ (SchwartzMap E ℂ) := (SchwartzMap.seminorm ℂ p n).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℂ E ℂ).continuous_seminorm (p,n)).comp T.continuous
  obtain ⟨K,B,_,hb⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq
  refine ⟨K,B,B.coe_nonneg,fun f => ?_⟩
  have he := hb f
  rw [_root_.smul_apply, NNReal.smul_def, smul_eq_mul] at he
  exact he

/-- ALL weighted Fourier jets of the actual normal iterates retain the
complete H^(-k) gain. The polynomial degree M is chosen BEFORE k and
therefore cannot consume the gain obtained by further normal iteration. -/
theorem bagCubicControlledPhysicalSchwartz_normal_fourier_seminorm (p n : ℕ) :
    ∃ M : ℕ, ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : {r : ℝ // Real.exp 1 ≤ r},
      ∀ H : {r : ℝ // r ∈ Ioo (0 : ℝ) (N.1/2)}, 1 ≤ H.1 →
        SchwartzMap.seminorm ℂ p n
          (𝓕 (bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H))) ≤
            C*N.1^M/(N.1*Real.log N.1^3*H.1^k) := by
  obtain ⟨K,B,hB,hBb⟩ := fourier_seminorm_control p n
  refine ⟨K.sup Prod.fst,fun k => ?_⟩
  choose A hA hAb using fun i : ℕ × ℕ => bagCubicControlledPhysicalSchwartz_normal_seminorm k i.1 i.2
  let C : ℝ := (∑ i ∈ K, A i)+1
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ i ∈ K, A i := Finset.sum_nonneg (fun i _ => (hA i).le)
    dsimp only [C]
    linarith
  refine ⟨B*C+1,by positivity,fun N H hH => ?_⟩
  have hN1 : 1 < N.1 := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2
  have hN : 0 < N.1 := lt_trans zero_lt_one hN1
  let den := N.1*Real.log N.1^3*H.1^k
  have hden : 0 < den := mul_pos (mul_pos hN (pow_pos (Real.log_pos hN1) 3)) (pow_pos H.2.1 k)
  let f := bagCubicNormalOperator^[k] (bagCubicExpControlledPhysicalSchwartz N H)
  have hs : (K.sup (schwartzSeminormFamily ℂ E ℂ)) f ≤ C*N.1^(K.sup Prod.fst)/den := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i hi
    have hAC : A i ≤ C := (Finset.single_le_sum (fun j _ => (hA j).le) hi).trans (by dsimp only [C]; linarith)
    have hiM : i.1 ≤ K.sup Prod.fst := Finset.le_sup hi
    exact (hAb i N H hH).trans (div_le_div_of_nonneg_right
      (mul_le_mul hAC (pow_le_pow_right₀ hN1.le hiM) (pow_nonneg hN.le _) hC.le) hden.le)
  calc
    _ ≤ B*(K.sup (schwartzSeminormFamily ℂ E ℂ)) f := hBb f
    _ ≤ B*(C*N.1^(K.sup Prod.fst)/den) := mul_le_mul_of_nonneg_left hs hB
    _ = (B*C)*N.1^(K.sup Prod.fst)/den := by ring
    _ ≤ (B*C+1)*N.1^(K.sup Prod.fst)/den := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hN.le _)) hden.le

end RHTower.BAGTrace
