import GaloisForLFunctions.HTGeometry.FormationGradeChannels

/-!
# Formation-grade properness inversion

The depth-two response `𝓡^{(2)}_{T,𝒟} f_j = g_j` of the crowded prime pairs is the bounded
operator `ℓ²(ℕ) → ⊕_ℓ L²((0,T]; ℓ²(ℕ≥1))` obtained from the orthonormal normalized channels
`ψ_j = g_j/s_j` and the diagonal `diag(s_j)`, so `‖𝓡^{(2)} x‖² = ∑_j |x_j|² s_j²` `(FGP.10)`.
Since `s_j > 0` and `s_j → 0` it is injective and compact with dense nonclosed range in
`span{ψ_j}`, and the unit response `ψ_j` costs `s_j^{-2} → ∞` (Theorem 4.1).  Bounded processing
cannot repair this (Corollary 4.2); any diagonal weight restoring a lower bound must grow like
`R_j e^{c R_j^{1/10}}` (Corollary 4.3).  Hence the properness spectrum satisfies
`α_1(T) ≥ b_2(T) > 0` and `α_2(T) = 0` `(FGP.12)`–`(FGP.13)`.
-/

open scoped InnerProductSpace
open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-- Pair controls `ℓ²(ℕ)`. -/
abbrev PairControls : Type := lp (fun _ : ℕ => ℂ) 2

theorem lp_norm_sq_eq_tsum {ι : Type*} (c : lp (fun _ : ι => ℂ) 2) :
    ‖c‖ ^ 2 = ∑' i, ‖c i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) c
  simpa using h

theorem norm_single_one_nat (j : ℕ) : ‖(lp.single 2 j (1 : ℂ) : PairControls)‖ = 1 := by
  rw [lp.norm_single (by norm_num)]
  simp

namespace CrowdedPairs

variable (P : CrowdedPairs) (D : DiffFamily) {T : ℝ}

theorem singular_nonneg (T : ℝ) (j : ℕ) : 0 ≤ P.singular D T j := norm_nonneg _

theorem inner_responseVec_self (T : ℝ) (j : ℕ) :
    ⟪P.responseVec D T j, P.responseVec D T j⟫_ℂ = ((P.singular D T j ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, singular, Complex.ofReal_pow]
  rfl

/-- The normalized channels `ψ_j = s_j⁻¹ g_j`. -/
def normalizedChannel (T : ℝ) (j : ℕ) : OutSpace T D.M :=
  ((P.singular D T j)⁻¹ : ℂ) • P.responseVec D T j

theorem orthonormal_normalizedChannel (hT : 0 < T) :
    Orthonormal ℂ (P.normalizedChannel D T) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [normalizedChannel, normalizedChannel, inner_smul_left, inner_smul_right]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, inner_responseVec_self]
    have hs : (P.singular D T i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (P.singular_pos D hT i).ne'
    rw [map_inv₀, Complex.conj_ofReal]
    push_cast
    field_simp
  · rw [if_neg hij, P.inner_responseVec_of_ne D T hij, mul_zero, mul_zero]

theorem bddAbove_singular (hT : 0 ≤ T) : BddAbove (Set.range (P.singular D T)) :=
  (P.tendsto_singular D hT).bddAbove_range

/-- A uniform bound for the singular values. -/
def singularSup (T : ℝ) : ℝ := ⨆ j, P.singular D T j

theorem singular_le_sup (hT : 0 ≤ T) (j : ℕ) : P.singular D T j ≤ P.singularSup D T :=
  le_ciSup (P.bddAbove_singular D hT) j

theorem singularSup_nonneg (hT : 0 ≤ T) : 0 ≤ P.singularSup D T :=
  (norm_nonneg _).trans (P.singular_le_sup D hT 0)

/-- `diag(s_j)` on `ℓ²(ℕ)`. -/
def singularDiag (hT : 0 ≤ T) : PairControls →L[ℂ] PairControls :=
  LpDiagonal.lpDiag (fun j => (P.singular D T j : ℂ)) (P.singularSup D T)
    (P.singularSup_nonneg D hT) fun j => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (P.singular_nonneg D T j)]
      exact P.singular_le_sup D hT j

theorem singularDiag_apply (hT : 0 ≤ T) (x : PairControls) (j : ℕ) :
    P.singularDiag D hT x j = (P.singular D T j : ℂ) * x j := rfl

/-- **`(FGP.8)`: the joint depth-two response** `𝓡^{(2)}_{T,𝒟}`. -/
def depthTwoResponse (hT : 0 < T) : PairControls →L[ℂ] OutSpace T D.M :=
  (P.orthonormal_normalizedChannel D hT).orthogonalFamily.linearIsometry.toContinuousLinearMap ∘L
    P.singularDiag D hT.le

theorem singularDiag_single (hT : 0 ≤ T) (j : ℕ) (a : ℂ) :
    P.singularDiag D hT (lp.single 2 j a) = lp.single 2 j ((P.singular D T j : ℂ) * a) := by
  ext i
  rw [singularDiag_apply, lp.single_apply, lp.single_apply]
  by_cases hi : i = j
  · subst hi; simp
  · simp [hi]

/-- `𝓡^{(2)} f_j = g_j`: the operator extends `(FGP.8)`. -/
theorem depthTwoResponse_single (hT : 0 < T) (j : ℕ) :
    P.depthTwoResponse D hT (lp.single 2 j 1) = P.responseVec D T j := by
  rw [depthTwoResponse, ContinuousLinearMap.comp_apply, singularDiag_single,
    LinearIsometry.coe_toContinuousLinearMap, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply, normalizedChannel, smul_smul, mul_one,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (P.singular_pos D hT j).ne'), one_smul]

theorem norm_depthTwoResponse (hT : 0 < T) (x : PairControls) :
    ‖P.depthTwoResponse D hT x‖ = ‖P.singularDiag D hT.le x‖ := by
  rw [depthTwoResponse, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map]

/-- **`(FGP.10)`**: `‖𝓡^{(2)} x‖² = ∑_j |x_j|² s_j²`. -/
theorem norm_sq_depthTwoResponse (hT : 0 < T) (x : PairControls) :
    ‖P.depthTwoResponse D hT x‖ ^ 2 = ∑' j, ‖x j‖ ^ 2 * P.singular D T j ^ 2 := by
  rw [norm_depthTwoResponse, lp_norm_sq_eq_tsum]
  refine tsum_congr fun j => ?_
  rw [singularDiag_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (P.singular_nonneg D T j)]
  ring

theorem norm_depthTwoResponse_single (hT : 0 < T) (j : ℕ) :
    ‖P.depthTwoResponse D hT (lp.single 2 j 1)‖ = P.singular D T j := by
  rw [depthTwoResponse_single]
  rfl

theorem singularDiag_injective (hT : 0 < T) : Function.Injective (P.singularDiag D hT.le) := by
  intro x y h
  ext j
  have hj := congrArg (fun z : PairControls => z j) h
  simp only [singularDiag_apply] at hj
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (P.singular_pos D hT j).ne') hj

/-- **Theorem 4.1(3)**: injective. -/
theorem depthTwoResponse_injective (hT : 0 < T) :
    Function.Injective (P.depthTwoResponse D hT) :=
  ((P.orthonormal_normalizedChannel D hT).orthogonalFamily.linearIsometry.injective).comp
    (P.singularDiag_injective D hT)

/-- **Theorem 4.1(3)**: compact. -/
theorem isCompactOperator_depthTwoResponse (hT : 0 < T) :
    IsCompactOperator (P.depthTwoResponse D hT) := by
  have hlim : Tendsto (fun j => ‖(P.singular D T j : ℂ)‖) cofinite (𝓝 0) := by
    have hfun : (fun j => ‖(P.singular D T j : ℂ)‖) = P.singular D T := funext fun j => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (P.singular_nonneg D T j)]
    rw [hfun, Nat.cofinite_eq_atTop]
    exact P.tendsto_singular D hT.le
  exact (LpDiagonal.isCompactOperator_lpDiag _ _ (P.singularSup_nonneg D hT.le) _ hlim).clm_comp
    (P.orthonormal_normalizedChannel D hT).orthogonalFamily.linearIsometry.toContinuousLinearMap

/-- The carrier of the normalized response channels. -/
def channelCarrier (T : ℝ) : Submodule ℂ (OutSpace T D.M) :=
  (Submodule.span ℂ (Set.range (P.normalizedChannel D T))).topologicalClosure

theorem normalizedChannel_eq (hT : 0 < T) (j : ℕ) :
    P.normalizedChannel D T j =
      P.depthTwoResponse D hT (lp.single 2 j ((P.singular D T j : ℂ))⁻¹) := by
  rw [show (lp.single 2 j ((P.singular D T j : ℂ))⁻¹ : PairControls) =
      ((P.singular D T j : ℂ))⁻¹ • lp.single 2 j (1 : ℂ) by
        rw [← lp.single_smul, smul_eq_mul, mul_one], map_smul, depthTwoResponse_single]
  rfl

/-- **Theorem 4.1(4)**: the range is dense in the channel carrier. -/
theorem closure_range_depthTwoResponse (hT : 0 < T) :
    (LinearMap.range
        (P.depthTwoResponse D hT : PairControls →ₗ[ℂ] OutSpace T D.M)).topologicalClosure =
      P.channelCarrier D T := by
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
    rintro _ ⟨x, rfl⟩
    have hsum := (lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) x).mapL
      (P.depthTwoResponse D hT)
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hsum
      (Eventually.of_forall fun s => ?_)
    refine Submodule.le_topologicalClosure _ (Submodule.sum_mem _ fun j _ => ?_)
    have h : P.depthTwoResponse D hT (lp.single 2 j (x j)) =
        (x j * (P.singular D T j : ℂ)) • P.normalizedChannel D T j := by
      rw [show (lp.single 2 j (x j) : PairControls) = x j • lp.single 2 j (1 : ℂ) by
          rw [← lp.single_smul, smul_eq_mul, mul_one], map_smul, depthTwoResponse_single,
        normalizedChannel, smul_smul, mul_assoc,
        mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (P.singular_pos D hT j).ne'), mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · refine Submodule.topologicalClosure_mono ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨_, (P.normalizedChannel_eq D hT j).symm⟩

/-- **Theorem 4.1(4)**: the range is not closed. -/
theorem not_isClosed_range_depthTwoResponse (hT : 0 < T) :
    ¬ IsClosed (Set.range (P.depthTwoResponse D hT)) := by
  intro hcl
  have h4 := ((globalProperness_tfae (P.depthTwoResponse D hT)).out 0 3).mp hcl
  apply h4
  have hker : invisibleKernel (P.depthTwoResponse D hT) = ⊥ := by
    rw [invisibleKernel, LinearMap.ker_eq_bot]
    exact P.depthTwoResponse_injective D hT
  refine ⟨fun j => lp.single 2 j 1, fun j => by rw [hker, Submodule.bot_orthogonal_eq_top]; trivial,
    fun j => norm_single_one_nat j, ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_depthTwoResponse_single]
  exact P.tendsto_singular D hT.le

/-- **Theorem 4.1(5)**: the unit response `ψ_j` costs `s_j^{-2}`. -/
theorem inverseCost_normalizedChannel (hT : 0 < T) (j : ℕ) {x : PairControls}
    (hx : P.depthTwoResponse D hT x = P.normalizedChannel D T j) :
    ‖x‖ ^ 2 = (P.singular D T j ^ 2)⁻¹ := by
  rw [P.normalizedChannel_eq D hT j] at hx
  have h := P.depthTwoResponse_injective D hT hx
  rw [h, lp.norm_single (by norm_num), norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (P.singular_nonneg D T j), inv_pow]

theorem tendsto_inverseCost (hT : 0 < T) :
    Tendsto (fun j => (P.singular D T j ^ 2)⁻¹) atTop atTop := by
  have h : Tendsto (fun j => P.singular D T j ^ 2) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun j => pow_pos (P.singular_pos D hT j) 2⟩
    simpa using (P.tendsto_singular D hT.le).pow 2
  exact tendsto_inv_nhdsGT_zero.comp h

/-! ### Corollaries -/

/-- **Corollary 4.2: bounded processing cannot repair the wall.** -/
theorem bounded_processing_collapse (hT : 0 < T) {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] (B : OutSpace T D.M →L[ℂ] Z) (C : PairControls ≃L[ℂ] PairControls)
    (j : ℕ) :
    ‖((‖C.symm (lp.single 2 j 1)‖⁻¹ : ℝ) : ℂ) • C.symm (lp.single 2 j 1)‖ = 1 ∧
      ‖B (P.depthTwoResponse D hT (C (((‖C.symm (lp.single 2 j 1)‖⁻¹ : ℝ) : ℂ) •
          C.symm (lp.single 2 j 1))))‖ ≤
        ‖B‖ * ‖(C : PairControls →L[ℂ] PairControls)‖ * P.singular D T j := by
  set u := C.symm (lp.single 2 j (1 : ℂ))
  have hu : u ≠ 0 := fun h => by
    have := congrArg C h
    rw [ContinuousLinearEquiv.apply_symm_apply, map_zero] at this
    have h1 := norm_single_one_nat j
    rw [this, norm_zero] at h1
    exact zero_ne_one h1
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hCu : 1 ≤ ‖(C : PairControls →L[ℂ] PairControls)‖ * ‖u‖ := by
    have h := (C : PairControls →L[ℂ] PairControls).le_opNorm u
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      norm_single_one_nat] at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hupos),
      inv_mul_cancel₀ hupos.ne']
  · rw [map_smul, ContinuousLinearEquiv.apply_symm_apply, map_smul, depthTwoResponse_single,
      map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hupos)]
    calc ‖u‖⁻¹ * ‖B (P.responseVec D T j)‖ ≤ ‖u‖⁻¹ * (‖B‖ * P.singular D T j) :=
          mul_le_mul_of_nonneg_left (B.le_opNorm _) (inv_nonneg.mpr hupos.le)
      _ ≤ ‖(C : PairControls →L[ℂ] PairControls)‖ * (‖B‖ * P.singular D T j) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          rw [inv_le_iff_one_le_mul₀ hupos]
          exact hCu
      _ = ‖B‖ * ‖(C : PairControls →L[ℂ] PairControls)‖ * P.singular D T j := by ring

/-- The constant-channel response norm `σ_j` (the channel `(P, k) = (1, 0)`). -/
def constChannelNorm (T : ℝ) (j : ℕ) : ℝ := ‖(P.responseVec D T j).ofLp 0‖

/-- `σ_j ≤ √T · 3η_j/R_j`, from `(FGP.7)`. -/
theorem constChannelNorm_le {T : ℝ} (hT : 0 ≤ T) (j : ℕ) :
    P.constChannelNorm D T j ≤ Real.sqrt T * (3 * P.η j / P.base j) := by
  have hβ : 0 ≤ 3 * P.η j / P.base j := div_nonneg (by linarith [P.η_pos j]) (by
    linarith [P.base_ge j])
  have hsq : P.constChannelNorm D T j ^ 2 ≤ T * (3 * P.η j / P.base j) ^ 2 := by
    rw [constChannelNorm, responseVec, PiLp.toLp_apply, norm_sq_toLp]
    simp_rw [norm_channelProfile]
    have hle : ∫ t, ‖P.channelCoeff D 0 j t‖ ^ 2 ∂(timeMeasure T) ≤
        ∫ _t, (3 * P.η j / P.base j) ^ 2 ∂(timeMeasure T) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
        (integrable_const _) ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [channelCoeff_zero, Complex.norm_real, Real.norm_eq_abs]
      exact P.abs_defect_le j ht.1.le
    rw [integral_const, measureReal_restrict_apply_univ, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hT, smul_eq_mul] at hle
    exact hle
  rw [show T * (3 * P.η j / P.base j) ^ 2 = (Real.sqrt T * (3 * P.η j / P.base j)) ^ 2 by
    rw [mul_pow, Real.sq_sqrt hT]] at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem η_eq (j : ℕ) : P.η j = P.K * Real.exp (-(P.c * P.base j ^ ((1 : ℝ) / 10))) := rfl

/-- **Corollary 4.3, `(FGP.11)`: every diagonal repair of the constant channel is singular**:
`|w_j| ≥ α R_j/(3√T K) · e^{c R_j^{1/10}}`. -/
theorem diagonal_repair_const {T : ℝ} (hT : 0 < T) {w : ℕ → ℂ} {α : ℝ}
    (hw : ∀ j, α ≤ ‖w j‖ * P.constChannelNorm D T j) (j : ℕ) :
    α * P.base j / (3 * Real.sqrt T * P.K) * Real.exp (P.c * P.base j ^ ((1 : ℝ) / 10)) ≤
      ‖w j‖ := by
  have hR : 0 < P.base j := by linarith [P.base_ge j]
  have hs := Real.sqrt_pos.mpr hT
  have hK := P.hK
  have h1 := hw j
  have h2 := P.constChannelNorm_le D hT.le j
  have h3 : α ≤ ‖w j‖ * (Real.sqrt T * (3 * P.η j / P.base j)) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  rw [η_eq] at h3
  have hE : Real.exp (-(P.c * P.base j ^ ((1 : ℝ) / 10))) *
      Real.exp (P.c * P.base j ^ ((1 : ℝ) / 10)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc α * P.base j * Real.exp (P.c * P.base j ^ ((1 : ℝ) / 10))
      ≤ ‖w j‖ * (Real.sqrt T * (3 * (P.K * Real.exp (-(P.c * P.base j ^ ((1 : ℝ) / 10)))) /
          P.base j)) * P.base j * Real.exp (P.c * P.base j ^ ((1 : ℝ) / 10)) := by
        gcongr
    _ = ‖w j‖ * (3 * Real.sqrt T * P.K) *
          (Real.exp (-(P.c * P.base j ^ ((1 : ℝ) / 10))) *
            Real.exp (P.c * P.base j ^ ((1 : ℝ) / 10))) := by
        field_simp
    _ = ‖w j‖ * (3 * Real.sqrt T * P.K) := by rw [hE, mul_one]

theorem coeffMass_pos {Q : MvPolynomial (Fin 2) ℂ} (hQ : Q ≠ 0) : 0 < coeffMass Q := by
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hQ
  have hmem : m ∈ Q.support := MvPolynomial.mem_support_iff.mpr hm
  exact lt_of_lt_of_le (norm_pos_iff.mpr hm)
    (Finset.single_le_sum (f := fun m => ‖Q.coeff m‖) (fun _ _ => norm_nonneg _) hmem)

theorem familyConst_pos : 0 < familyConst D := by
  have h0 : 0 < channelConst D 0 := by
    unfold channelConst
    have h1 : D.P 0 ≠ 0 := by rw [D.P_zero]; exact one_ne_zero
    have := coeffMass_pos h1
    have := derivConst_pos (D.k 0)
    positivity
  exact lt_of_lt_of_le h0 (Finset.single_le_sum (fun ℓ _ => channelConst_nonneg D ℓ)
    (Finset.mem_univ 0))

/-- **Corollary 4.3, general family**: a diagonal repair with `α ≤ |w_j| s_j` grows at least like
`R_j^{1-D-κ} e^{c R_j^{1/10}}`. -/
theorem diagonal_repair_family {T : ℝ} (hT : 0 < T) {w : ℕ → ℂ} {α : ℝ}
    (hw : ∀ j, α ≤ ‖w j‖ * P.singular D T j) (j : ℕ) :
    α / (Real.sqrt T * familyConst D * P.K) *
        P.base j ^ (-(((D.degree + D.order : ℕ) - 1 : ℤ))) *
        Real.exp (P.c * P.base j ^ ((1 : ℝ) / 10)) ≤ ‖w j‖ := by
  set N : ℤ := (D.degree + D.order : ℕ) - 1
  have hR : 0 < P.base j := by linarith [P.base_ge j]
  have hs := Real.sqrt_pos.mpr hT
  have hC := familyConst_pos D
  have hK := P.hK
  have h3 : α ≤ ‖w j‖ * (Real.sqrt T * familyConst D * P.base j ^ N * P.η j) :=
    (hw j).trans (mul_le_mul_of_nonneg_left (P.singular_le D hT.le j) (norm_nonneg _))
  rw [η_eq] at h3
  have hE : Real.exp (-(P.c * P.base j ^ ((1 : ℝ) / 10))) *
      Real.exp (P.c * P.base j ^ ((1 : ℝ) / 10)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hRN : P.base j ^ N * P.base j ^ (-N) = 1 := by
    rw [← zpow_add₀ hR.ne', add_neg_cancel, zpow_zero]
  have hpos : 0 < Real.sqrt T * familyConst D * P.K := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hpos]
  calc α * P.base j ^ (-N) * Real.exp (P.c * P.base j ^ ((1 : ℝ) / 10))
      ≤ ‖w j‖ * (Real.sqrt T * familyConst D * P.base j ^ N *
          (P.K * Real.exp (-(P.c * P.base j ^ ((1 : ℝ) / 10))))) * P.base j ^ (-N) *
          Real.exp (P.c * P.base j ^ ((1 : ℝ) / 10)) := by
        gcongr
    _ = ‖w j‖ * (Real.sqrt T * familyConst D * P.K) * (P.base j ^ N * P.base j ^ (-N)) *
          (Real.exp (-(P.c * P.base j ^ ((1 : ℝ) / 10))) *
            Real.exp (P.c * P.base j ^ ((1 : ℝ) / 10))) := by ring
    _ = ‖w j‖ * (Real.sqrt T * familyConst D * P.K) := by rw [hRN, hE, mul_one, mul_one]

end CrowdedPairs

/-! ### The properness spectrum -/

/-- The properness constant `α(𝓡) = inf {‖𝓡 x‖ : ‖x‖ = 1, x ⊥ ker 𝓡}` `(FGP.12)`. -/
def propernessConst {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (R : E →L[ℂ] F) : ℝ :=
  sInf ((fun x => ‖R x‖) '' {x | x ∈ (invisibleKernel R)ᗮ ∧ ‖x‖ = 1})

/-- **`(FGP.13)`, grade one**: `α_1(T) ≥ b_2(T) > 0`. -/
theorem propernessConst_comResponse {T : ℝ} (hT : 0 < T) :
    profile T primeTwo ≤ propernessConst (comResponse T) := by
  have hker : invisibleKernel (comResponse T) = ⊥ := by
    rw [invisibleKernel, LinearMap.ker_eq_bot]
    exact comResponse_injective hT
  have hmem : (lp.single 2 primeTwo 1 : PrimeControls) ∈ (invisibleKernel (comResponse T))ᗮ := by
    rw [hker, Submodule.bot_orthogonal_eq_top]
    trivial
  refine le_csInf ⟨_, ⟨lp.single 2 primeTwo 1, ⟨hmem, norm_single_one primeTwo⟩, rfl⟩⟩ ?_
  rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
  have h := profile_two_mul_le hT.le x
  rwa [hx, mul_one] at h

/-- **`(FGP.13)`, grade two**: `α_2(T) = 0` for every finite differential family. -/
theorem propernessConst_depthTwoResponse (P : CrowdedPairs) (D : DiffFamily) {T : ℝ}
    (hT : 0 < T) : propernessConst (P.depthTwoResponse D hT) = 0 := by
  have hker : invisibleKernel (P.depthTwoResponse D hT) = ⊥ := by
    rw [invisibleKernel, LinearMap.ker_eq_bot]
    exact P.depthTwoResponse_injective D hT
  have hperp : ∀ x : PairControls, x ∈ (invisibleKernel (P.depthTwoResponse D hT))ᗮ := by
    intro x
    rw [hker, Submodule.bot_orthogonal_eq_top]
    trivial
  have hmem : ∀ j : ℕ, P.singular D T j ∈ (fun x => ‖P.depthTwoResponse D hT x‖) ''
      {x | x ∈ (invisibleKernel (P.depthTwoResponse D hT))ᗮ ∧ ‖x‖ = 1} := fun j =>
    ⟨lp.single 2 j 1, ⟨hperp _, norm_single_one_nat j⟩, P.norm_depthTwoResponse_single D hT j⟩
  have hbdd : BddBelow ((fun x => ‖P.depthTwoResponse D hT x‖) ''
      {x | x ∈ (invisibleKernel (P.depthTwoResponse D hT))ᗮ ∧ ‖x‖ = 1}) :=
    ⟨0, by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _⟩
  apply le_antisymm
  · exact ge_of_tendsto' (P.tendsto_singular D hT.le) fun j => csInf_le hbdd (hmem j)
  · exact le_csInf ⟨_, hmem 0⟩ (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
