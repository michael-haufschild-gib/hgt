import GaloisForLFunctions.HTGeometry.PrimeHodgeResidueClock
import GaloisForLFunctions.HTGeometry.VectorSequenceShift
import GaloisForLFunctions.HTGeometry.OperatorCertificateCofinal
import GaloisForLFunctions.RHTower.PositiveOperatorTraceComparison

/-!
# The prime–Hodge singular gauge and its Toeplitz horizons

With `m_n = 105/((2n+3)(2n+5)(2n+7))`, `w_n = m_n - m_{n+1}`, the unilateral shift `U` and the
forced survival shift `C e_n = √(m_{n+1}/m_n) e_{n+1}` on `ℓ²(ℕ)`:

* **(A)** the singular gauge `Q = diag(√m_n)` is positive, compact, injective, with dense
  nonclosed range, and `C Q = Q U`.
* **(B)** on `ℓ²(ℕ; K)` with `𝒰 = U ⊗ 1`, `𝒢_A = diag(m) ⊗ A`, `𝒯_A = diag(w) ⊗ A`:
  `𝒢_A - 𝒰* 𝒢_A 𝒰 = 𝒯_A` and `𝒢_A = ∑_j 𝒰*ʲ 𝒯_A 𝒰ʲ` in trace norm; for `A ≥ 0` trace class,
  `‖𝒯_A‖₁ = tr A`, `‖𝒢_A‖₁ = (7/4) tr A`, `∑_j ‖𝒰*ʲ 𝒯_A 𝒰ʲ‖₁ = (7/4) tr A`.
* **(C)** `X - 𝒰* X 𝒰 = 𝒯_A` iff `R = X - 𝒢_A` is a shift fixed point, iff `R` has
  Toeplitz blocks `R_{n+1,m+1} = R_{n,m}`.
* **(D)** a compact shift fixed point vanishes; `𝒢_A` is the unique compact solution.
* **(E)** a positive solution satisfies `X ≥ 𝒢_A`; its horizon repeats its mass at every grade.
* **(F)** the harmonic lift `I ⊗ p` is a positive shift fixed point with grade-zero block `p`,
  noncompact and not trace class for `p ≠ 0`.
* **(G)** the first-exit lift `Φ ⊗ p = 𝒢_p - 𝒰* 𝒢_p 𝒰` is positive trace class with trace
  `tr p`, and its history blocks `w_n p` sum to `p`.
-/

open Filter Topology ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## The arithmetic singular gauge -/

theorem hodgeSurvivalMass_le_one (n : ℕ) : PrimeHodgeHistory.m n ≤ 1 := by
  have := PrimeHodgeHistory.m_antitone (Nat.zero_le n)
  rwa [PrimeHodgeHistory.m_zero] at this

theorem norm_sqrt_hodgeSurvivalMass_le (n : ℕ) :
    ‖((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr (hodgeSurvivalMass_le_one n)

/-- **(PHSTH.2).**  The singular gauge `Q e_n = √m_n e_n`. -/
def singularGauge : HistoryLine →L[ℂ] HistoryLine :=
  _root_.HTGeometry.ellTwoDiagonal (fun n => ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ))
    norm_sqrt_hodgeSurvivalMass_le

theorem singularGauge_coord (f : HistoryLine) (n : ℕ) :
    (singularGauge f : ℕ → ℂ) n
      = ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ) * (f : ℕ → ℂ) n := by
  rw [singularGauge, _root_.HTGeometry.ellTwoDiagonal_apply]

theorem singularGauge_basis (n : ℕ) :
    singularGauge (historyCoord n)
      = ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ) • historyCoord n :=
  diagonal_historyCoord _ _ n

/-- **(PHSTH.2).**  `Q² = G = diag(m_n)`. -/
theorem singularGauge_comp_self : singularGauge ∘L singularGauge = steinGramian := by
  ext f n
  rw [comp_apply, singularGauge_coord, singularGauge_coord, steinGramian_coord, ← mul_assoc,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (PrimeHodgeHistory.m_pos n).le]

/-- **Theorem PHSTH-A.**  `Q ≥ 0`. -/
theorem singularGauge_isPositive : singularGauge.IsPositive :=
  isPositive_ellTwoDiagonal_ofReal _ _ fun _ => Real.sqrt_nonneg _

theorem tendsto_sqrt_hodgeSurvivalMass :
    Tendsto (fun n => Real.sqrt (PrimeHodgeHistory.m n)) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp hasSum_m.summable.tendsto_atTop_zero
  rw [Real.sqrt_zero] at h
  exact h

/-- **Theorem PHSTH-A.**  `Q` is compact. -/
theorem isCompactOperator_singularGauge : IsCompactOperator singularGauge := by
  refine isCompactOperator_of_diag_tendsto_cofinite historyCoord
    (c := fun n => ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ)) singularGauge_basis ?_
  rw [Nat.cofinite_eq_atTop]
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
    tendsto_sqrt_hodgeSurvivalMass.norm

/-- **Theorem PHSTH-A.**  `Q` is injective. -/
theorem singularGauge_injective : Function.Injective singularGauge := by
  intro f g h
  ext n
  have hn := congrArg (fun x : HistoryLine => (x : ℕ → ℂ) n) h
  simp only [singularGauge_coord] at hn
  have hne : ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (PrimeHodgeHistory.m_pos n)).ne'
  exact mul_left_cancel₀ hne hn

theorem singularGauge_inv_basis (n : ℕ) :
    singularGauge ((((Real.sqrt (PrimeHodgeHistory.m n))⁻¹ : ℝ) : ℂ) • historyCoord n)
      = historyCoord n := by
  rw [map_smul, singularGauge_basis, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (PrimeHodgeHistory.m_pos n)).ne', Complex.ofReal_one,
    one_smul]

/-- **Theorem PHSTH-A.**  `Q` has dense range. -/
theorem denseRange_singularGauge : DenseRange singularGauge := by
  have hspan : Submodule.span ℂ (Set.range historyCoord)
      ≤ LinearMap.range (singularGauge : HistoryLine →ₗ[ℂ] HistoryLine) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact ⟨_, singularGauge_inv_basis n⟩
  have hd : Dense (Submodule.span ℂ (Set.range historyCoord) : Set HistoryLine) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr historyCoord.dense_span
  refine hd.mono fun x hx => ?_
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hspan hx)
  exact ⟨y, hy⟩

/-- **Theorem PHSTH-A.**  The range of `Q` is not closed: `Q⁻¹` is unbounded. -/
theorem not_isClosed_range_singularGauge : ¬IsClosed (Set.range singularGauge) := by
  intro hcl
  have hsurj : Function.Surjective singularGauge := by
    intro y
    have hy : y ∈ closure (Set.range singularGauge) := by
      rw [denseRange_singularGauge.closure_range]
      trivial
    rwa [hcl.closure_eq] at hy
  let e := ContinuousLinearEquiv.ofBijective singularGauge
    (LinearMap.ker_eq_bot.mpr singularGauge_injective) (LinearMap.range_eq_top.mpr hsurj)
  have hbound : ∀ n, (1 : ℝ)
      ≤ ‖(e.symm : HistoryLine →L[ℂ] HistoryLine)‖ * Real.sqrt (PrimeHodgeHistory.m n) := by
    intro n
    have h1 : historyCoord n = e.symm (singularGauge (historyCoord n)) :=
      (e.symm_apply_apply _).symm
    have h2 := (e.symm : HistoryLine →L[ℂ] HistoryLine).le_opNorm (singularGauge (historyCoord n))
    simp only [ContinuousLinearEquiv.coe_coe] at h2
    rw [← h1, norm_historyCoord, singularGauge_basis, norm_smul, norm_historyCoord, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h2
    exact h2
  have hlim := tendsto_sqrt_hodgeSurvivalMass.const_mul
    ‖(e.symm : HistoryLine →L[ℂ] HistoryLine)‖
  rw [mul_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
  linarith [hbound n]

/-- **(PHSTH.3).**  `C Q = Q U`. -/
theorem survivalShift_comp_singularGauge :
    primeHodgeHistorySurvivalShift ∘L singularGauge = singularGauge ∘L vecForward := by
  ext f n
  rw [comp_apply, comp_apply]
  cases n with
  | zero => rw [survivalShift_coord_zero, singularGauge_coord, vecForward_apply_zero, mul_zero]
  | succ n =>
    rw [survivalShift_coord_succ, singularGauge_coord, singularGauge_coord, vecForward_apply_succ,
      primeHodgeHistorySurvivalWeight, ← mul_assoc, ← Complex.ofReal_mul,
      PrimeHodgeHistory.survivalRatio,
      ← Real.sqrt_mul (div_nonneg (PrimeHodgeHistory.m_pos _).le (PrimeHodgeHistory.m_pos _).le),
      div_mul_cancel₀ _ (PrimeHodgeHistory.m_pos n).ne']

/-! ## Shift powers on `ℓ²(ℕ; K)` -/

section Shift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem vecBack_pow_apply (j : ℕ) (g : VecSeq E) (n : ℕ) :
    ((vecBack ^ j) g : ℕ → E) n = (g : ℕ → E) (n + j) := by
  induction j generalizing g with
  | zero => rfl
  | succ j ih => rw [pow_succ, mul_apply_eq_comp, ih, vecBack_apply, add_assoc]

theorem vecForward_pow_apply_add (j : ℕ) (f : VecSeq E) (n : ℕ) :
    ((vecForward ^ j) f : ℕ → E) (n + j) = (f : ℕ → E) n := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', mul_apply_eq_comp, ← add_assoc, vecForward_apply_succ, ih]

theorem vecForward_pow_apply_lt (j : ℕ) (f : VecSeq E) {k : ℕ} (hk : k < j) :
    ((vecForward ^ j) f : ℕ → E) k = 0 := by
  induction j generalizing k with
  | zero => omega
  | succ j ih =>
    rw [pow_succ', mul_apply_eq_comp]
    cases k with
    | zero => exact vecForward_apply_zero _
    | succ k => rw [vecForward_apply_succ]; exact ih (by omega)

theorem norm_vecForward_pow_apply (j : ℕ) (f : VecSeq E) : ‖(vecForward ^ j) f‖ = ‖f‖ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', mul_apply_eq_comp, norm_vecForward_apply, ih]

theorem vecForward_single (n : ℕ) (x : E) :
    vecForward (lp.single 2 n x) = lp.single 2 (n + 1) x := by
  ext k
  cases k with
  | zero => simp [lp.single_apply]
  | succ k => simp [lp.single_apply, Pi.single_apply]

/-- Shift conjugation of a history tensor shifts its weights. -/
theorem vecBack_pow_historyMap_vecForward_pow (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (A : E →L[ℂ] E) (j : ℕ) :
    (vecBack ^ j) ∘L historyMap a ha A ∘L (vecForward ^ j)
      = historyMap (fun n => a (n + j)) (fun n => ha (n + j)) A := by
  ext f n
  rw [comp_apply, comp_apply, vecBack_pow_apply, historyMap_apply, historyMap_apply,
    vecForward_pow_apply_add]

/-- Operators on `ℓ²(ℕ; K)` are determined by their blocks between grade vectors. -/
theorem historyL2_ext_single {A B : VecSeq E →L[ℂ] VecSeq E}
    (h : ∀ n m (x y : E), ⟪lp.single 2 n x, A (lp.single 2 m y)⟫_ℂ
      = ⟪lp.single 2 n x, B (lp.single 2 m y)⟫_ℂ) : A = B := by
  have hsingle : ∀ m (y : E), A (lp.single 2 m y) = B (lp.single 2 m y) := fun m y => by
    ext n
    refine ext_inner_left ℂ fun x => ?_
    have h1 : ⟪lp.single 2 n x, A (lp.single 2 m y)⟫_ℂ
        = ⟪x, (A (lp.single 2 m y) : ℕ → E) n⟫_ℂ := lp.inner_single_left _ _ _
    have h2 : ⟪lp.single 2 n x, B (lp.single 2 m y)⟫_ℂ
        = ⟪x, (B (lp.single 2 m y) : ℕ → E) n⟫_ℂ := lp.inner_single_left _ _ _
    rw [← h1, ← h2, h]
  refine ContinuousLinearMap.ext fun f => ?_
  have hf := lp.hasSum_single (E := fun _ : ℕ => E) (p := 2) (by norm_num) f
  exact (hf.mapL A).unique (by simpa only [hsingle] using hf.mapL B)

variable [CompleteSpace E]

theorem adjoint_vecForward_pow (j : ℕ) :
    adjoint ((vecForward : VecSeq E →L[ℂ] VecSeq E) ^ j) = vecBack ^ j := by
  induction j with
  | zero => simp only [pow_zero, one_def, adjoint_id]
  | succ j ih => rw [pow_succ', mul_def, adjoint_comp, ih, adjoint_vecForward, pow_succ, mul_def]

omit [CompleteSpace E] in
theorem fixed_iter {R : VecSeq E →L[ℂ] VecSeq E} (hfix : vecBack ∘L R ∘L vecForward = R)
    (N : ℕ) : (vecBack ^ N) ∘L R ∘L (vecForward ^ N) = R := by
  induction N with
  | zero => simp only [pow_zero, one_def, id_comp, comp_id]
  | succ N ih =>
    rw [pow_succ vecBack N, pow_succ' vecForward N, mul_def, mul_def]
    calc ((vecBack ^ N) ∘L vecBack) ∘L R ∘L vecForward ∘L (vecForward ^ N)
        = (vecBack ^ N) ∘L (vecBack ∘L R ∘L vecForward) ∘L (vecForward ^ N) := by
          simp only [comp_assoc]
      _ = R := by rw [hfix, ih]

theorem inner_fixed_iter {R : VecSeq E →L[ℂ] VecSeq E} (hfix : vecBack ∘L R ∘L vecForward = R)
    (N : ℕ) (x y : VecSeq E) :
    ⟪y, R x⟫_ℂ = ⟪(vecForward ^ N) y, R ((vecForward ^ N) x)⟫_ℂ := by
  conv_lhs => rw [← fixed_iter hfix N]
  rw [comp_apply, comp_apply, ← adjoint_vecForward_pow, adjoint_inner_right]

/-- Shifted vectors are weakly null. -/
theorem tendsto_compact_vecForward_pow {K : VecSeq E →L[ℂ] VecSeq E} (hK : IsCompactOperator K)
    (x : VecSeq E) : Tendsto (fun N => K ((vecForward ^ N) x)) atTop (𝓝 0) := by
  set c : ℝ := ‖x‖ + 1
  have hc : 0 < c := by positivity
  let u : ℕ → VecSeq E := fun N => ((c⁻¹ : ℝ) : ℂ) • (vecForward ^ N) x
  have hb : ∀ N, ‖u N‖ ≤ 1 := fun N => by
    rw [norm_smul, norm_vecForward_pow_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hc), inv_mul_le_iff₀ hc]
    linarith
  have hcoord : ∀ n, Tendsto (fun N => (u N : ℕ → E) n) atTop (𝓝 0) := fun n =>
    tendsto_const_nhds.congr' ((eventually_gt_atTop n).mono fun N hN => by
      simp only [u, lp.coeFn_smul, Pi.smul_apply, vecForward_pow_apply_lt N x hN, smul_zero])
  have hK0 := tendsto_compactOperator_of_weaklyNull_hilbert K hK u hb
    (tendsto_inner_vecSeq_of_coord u zero_le_one hb hcoord)
  have hmul := hK0.const_smul ((c : ℝ) : ℂ)
  rw [smul_zero] at hmul
  refine hmul.congr fun N => ?_
  rw [map_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne', Complex.ofReal_one,
    one_smul]

/-- **Theorem PHSTH-D.**  A compact fixed point of `R ↦ 𝒰* R 𝒰` is zero. -/
theorem eq_zero_of_compact_fixed {R : VecSeq E →L[ℂ] VecSeq E} (hR : IsCompactOperator R)
    (hfix : vecBack ∘L R ∘L vecForward = R) : R = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [zero_apply]
  refine ext_inner_left ℂ fun y => ?_
  rw [inner_zero_right]
  have hlim : Tendsto (fun N => ⟪(vecForward ^ N) y, R ((vecForward ^ N) x)⟫_ℂ) atTop (𝓝 0) := by
    have ha : Tendsto (fun N => ‖y‖ * ‖R ((vecForward ^ N) x)‖) atTop (𝓝 0) := by
      have h := (tendsto_compact_vecForward_pow hR x).norm.const_mul ‖y‖
      rwa [norm_zero, mul_zero] at h
    refine squeeze_zero_norm (fun N => ?_) ha
    calc ‖⟪(vecForward ^ N) y, R ((vecForward ^ N) x)⟫_ℂ‖
        ≤ ‖(vecForward ^ N) y‖ * ‖R ((vecForward ^ N) x)‖ := norm_inner_le_norm _ _
      _ = ‖y‖ * ‖R ((vecForward ^ N) x)‖ := by rw [norm_vecForward_pow_apply]
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun N => inner_fixed_iter hfix N x y) hlim

/-- **(PHSTH.10).**  Shift fixed points are exactly the operators with Toeplitz blocks. -/
theorem fixed_iff_toeplitz (R : VecSeq E →L[ℂ] VecSeq E) :
    vecBack ∘L R ∘L vecForward = R ↔ ∀ n m (x y : E),
      ⟪lp.single 2 (n + 1) x, R (lp.single 2 (m + 1) y)⟫_ℂ
        = ⟪lp.single 2 n x, R (lp.single 2 m y)⟫_ℂ := by
  have key : ∀ n m (x y : E),
      ⟪lp.single 2 n x, (vecBack ∘L R ∘L vecForward) (lp.single 2 m y)⟫_ℂ
        = ⟪lp.single 2 (n + 1) x, R (lp.single 2 (m + 1) y)⟫_ℂ := fun n m x y => by
    rw [comp_apply, comp_apply, ← adjoint_vecForward, adjoint_inner_right, vecForward_single,
      vecForward_single]
  constructor
  · intro h n m x y
    rw [← key, h]
  · intro h
    exact historyL2_ext_single fun n m x y => by rw [key, h]

end Shift

/-! ## The shift displacement -/

section Displacement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_hodgeSurvivalMass_le (n : ℕ) : ‖((PrimeHodgeHistory.m n : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (PrimeHodgeHistory.m_pos n)]
  exact hodgeSurvivalMass_le_one n

/-- **(PHSTH.4).**  The compact completion `𝒢_A = G ⊗ A`. -/
def gaugeCompletion (A : E →L[ℂ] E) : HistoryL2 E →L[ℂ] HistoryL2 E :=
  historyMap (fun n => ((PrimeHodgeHistory.m n : ℝ) : ℂ)) norm_hodgeSurvivalMass_le A

/-- **Theorem PHSTH-B, (PHSTH.5).**  `𝒢_A - 𝒰* 𝒢_A 𝒰 = 𝒯_A`. -/
theorem gaugeCompletion_displacement (A : E →L[ℂ] E) :
    gaugeCompletion A - adjoint vecForward ∘L gaugeCompletion A ∘L vecForward
      = fluxTensor A := by
  rw [adjoint_vecForward]
  ext f n
  simp only [sub_apply, comp_apply, lp.coeFn_sub, Pi.sub_apply, gaugeCompletion, fluxTensor,
    historyMap_apply, vecBack_apply, vecForward_apply_succ]
  rw [← sub_smul, PrimeHodgeHistory.w, Complex.ofReal_sub]

omit [CompleteSpace E] in
theorem tail_gaugeCompletion (A : E →L[ℂ] E) (N : ℕ) :
    (vecBack ^ N) ∘L gaugeCompletion A ∘L (vecForward ^ N)
      = historyMap (fun n => ((PrimeHodgeHistory.m (n + N) : ℝ) : ℂ))
        (fun n => norm_hodgeSurvivalMass_le (n + N)) A :=
  vecBack_pow_historyMap_vecForward_pow _ _ A N

omit [CompleteSpace E] in
theorem conj_fluxTensor (A : E →L[ℂ] E) (j : ℕ) :
    (vecBack ^ j) ∘L fluxTensor A ∘L (vecForward ^ j)
      = historyMap (fun n => ((PrimeHodgeHistory.w (n + j) : ℝ) : ℂ))
        (fun n => historyFlux_norm_le (n + j)) A :=
  vecBack_pow_historyMap_vecForward_pow _ _ A j

omit [CompleteSpace E] in
/-- **(PHSTH.6).**  `∑_{j<N} 𝒰*ʲ 𝒯_A 𝒰ʲ = 𝒢_A - 𝒰*ᴺ 𝒢_A 𝒰ᴺ`. -/
theorem sum_conj_fluxTensor (A : E →L[ℂ] E) (N : ℕ) :
    ∑ j ∈ Finset.range N, (vecBack ^ j) ∘L fluxTensor A ∘L (vecForward ^ j)
      = gaugeCompletion A - (vecBack ^ N) ∘L gaugeCompletion A ∘L (vecForward ^ N) := by
  induction N with
  | zero => simp only [Finset.sum_range_zero, pow_zero, one_def, id_comp, comp_id, sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, tail_gaugeCompletion, tail_gaugeCompletion, conj_fluxTensor]
    ext f n
    simp only [add_apply, sub_apply, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
      historyMap_apply, PrimeHodgeHistory.w, Complex.ofReal_sub, sub_smul, ← add_assoc]
    abel

/-- `c ⊗ A` for nonnegative summable weights and positive trace-class `A`. -/
theorem historyMap_nonneg_traceClass {c : ℕ → ℝ} (hc0 : ∀ n, 0 ≤ c n) (hc1 : ∀ n, c n ≤ 1)
    (hcs : Summable c) {A : E →L[ℂ] E} (hA : A.IsPositive) (hA1 : MemSchattenClass 1 A) :
    (historyMap (fun n => ((c n : ℝ) : ℂ)) (norm_ofReal_weight_le_one hc0 hc1) A).IsPositive ∧
      MemSchattenClass 1 (historyMap (fun n => ((c n : ℝ) : ℂ))
        (norm_ofReal_weight_le_one hc0 hc1) A) ∧
      opTrace (historyMap (fun n => ((c n : ℝ) : ℂ)) (norm_ofReal_weight_le_one hc0 hc1) A)
        = (((∑' n, c n) : ℝ) : ℂ) * opTrace A ∧
      traceNorm (HistoryL2 E) (historyMap (fun n => ((c n : ℝ) : ℂ))
        (norm_ofReal_weight_le_one hc0 hc1) A) = (∑' n, c n) * (opTrace A).re := by
  have hSS : adjoint (traceClassRoot A) ∘L traceClassRoot A = A := by
    rw [(isSelfAdjoint_traceClassRoot A).adjoint_eq, traceClassRoot_comp_self,
      absOp_of_nonneg ((nonneg_iff_isPositive A).mpr hA)]
  have htr : opTrace A = ((ContinuousLinearMap.hsNormSq (traceClassRoot A) : ℝ) : ℂ) := by
    conv_lhs => rw [← hSS]
    rw [opTrace_adjoint_comp_self, hsInner_self_eq_ofReal_hsNormSq']
  obtain ⟨h1, h2, h3⟩ := historyMap_weight_traceClass hc0 hc1 hcs
    (traceClassRoot_isHilbertSchmidt hA1)
  rw [hSS] at h1 h2 h3
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h3, htr, Complex.ofReal_mul]
  · rw [traceNorm_eq_re_opTrace_of_isPositive h2 h1, h3, htr, Complex.ofReal_re,
      Complex.ofReal_re]

theorem hasSum_w_add (j : ℕ) :
    HasSum (fun n => PrimeHodgeHistory.w (n + j)) (PrimeHodgeHistory.m j) := by
  have h := (hasSum_nat_add_iff' j).mpr PrimeHodgeHistory.hasSum_w
  have hsum : ∑ i ∈ Finset.range j, PrimeHodgeHistory.w i = 1 - PrimeHodgeHistory.m j := by
    simp only [PrimeHodgeHistory.w]
    rw [Finset.sum_range_sub' PrimeHodgeHistory.m j, PrimeHodgeHistory.m_zero]
  rwa [hsum, sub_sub_cancel] at h

variable {A : E →L[ℂ] E} (hA : A.IsPositive) (hA1 : MemSchattenClass 1 A)
include hA hA1

/-- **Theorem PHSTH-B, (PHSTH.7).**  `‖𝒯_A‖₁ = tr A`. -/
theorem traceNorm_fluxTensor : traceNorm (HistoryL2 E) (fluxTensor A) = (opTrace A).re := by
  have h := (historyMap_nonneg_traceClass historyFlux_nonneg historyFlux_le_one
    PrimeHodgeHistory.summable_w hA hA1).2.2.2
  rw [PrimeHodgeHistory.tsum_w, one_mul] at h
  exact h

/-- **Theorem PHSTH-B, (PHSTH.7).**  `𝒢_A ≥ 0` is trace class with `‖𝒢_A‖₁ = (7/4) tr A`. -/
theorem gaugeCompletion_traceClass :
    (gaugeCompletion A).IsPositive ∧ MemSchattenClass 1 (gaugeCompletion A) ∧
      traceNorm (HistoryL2 E) (gaugeCompletion A) = 7 / 4 * (opTrace A).re := by
  obtain ⟨h1, h2, -, h4⟩ := historyMap_nonneg_traceClass (fun n => (PrimeHodgeHistory.m_pos n).le)
    hodgeSurvivalMass_le_one hasSum_m.summable hA hA1
  exact ⟨h1, h2, by rw [gaugeCompletion, h4, hasSum_m.tsum_eq]⟩

/-- **(PHSTH.7).**  `‖𝒰*ʲ 𝒯_A 𝒰ʲ‖₁ = m_j tr A`, summing to `(7/4) tr A`. -/
theorem traceNorm_conj_fluxTensor (j : ℕ) :
    traceNorm (HistoryL2 E) ((vecBack ^ j) ∘L fluxTensor A ∘L (vecForward ^ j))
      = PrimeHodgeHistory.m j * (opTrace A).re := by
  rw [conj_fluxTensor]
  have h := (historyMap_nonneg_traceClass (fun n => historyFlux_nonneg (n + j))
    (fun n => historyFlux_le_one (n + j)) (hasSum_w_add j).summable hA hA1).2.2.2
  rw [(hasSum_w_add j).tsum_eq] at h
  exact h

theorem hasSum_traceNorm_conj_fluxTensor :
    HasSum (fun j => traceNorm (HistoryL2 E) ((vecBack ^ j) ∘L fluxTensor A ∘L (vecForward ^ j)))
      (7 / 4 * (opTrace A).re) := by
  simp_rw [traceNorm_conj_fluxTensor hA hA1]
  exact hasSum_m.mul_right _

/-- **Theorem PHSTH-B, (PHSTH.6).**  `∑_j 𝒰*ʲ 𝒯_A 𝒰ʲ → 𝒢_A` in trace norm. -/
theorem tendsto_traceNorm_gaugeCompletion_sub :
    Tendsto (fun N => traceNorm (HistoryL2 E) (gaugeCompletion A -
      ∑ j ∈ Finset.range N, (vecBack ^ j) ∘L fluxTensor A ∘L (vecForward ^ j))) atTop (𝓝 0) := by
  have hval : ∀ N, traceNorm (HistoryL2 E) (gaugeCompletion A -
      ∑ j ∈ Finset.range N, (vecBack ^ j) ∘L fluxTensor A ∘L (vecForward ^ j))
        = (∑' n, PrimeHodgeHistory.m (n + N)) * (opTrace A).re := fun N => by
    rw [sum_conj_fluxTensor, sub_sub_cancel, tail_gaugeCompletion]
    exact (historyMap_nonneg_traceClass (fun n => (PrimeHodgeHistory.m_pos (n + N)).le)
      (fun n => hodgeSurvivalMass_le_one (n + N)) ((summable_nat_add_iff N).mpr hasSum_m.summable)
      hA hA1).2.2.2
  simp_rw [hval]
  simpa using (tendsto_sum_nat_add PrimeHodgeHistory.m).mul_const (opTrace A).re

omit hA hA1

/-! ## Completions with the same defect -/

/-- **Theorem PHSTH-C, (PHSTH.9).**  `X - 𝒰* X 𝒰 = 𝒯_A` iff `X - 𝒢_A` is a shift fixed point. -/
theorem displacement_eq_iff (A : E →L[ℂ] E) (X : HistoryL2 E →L[ℂ] HistoryL2 E) :
    X - adjoint vecForward ∘L X ∘L vecForward = fluxTensor A ↔
      vecBack ∘L (X - gaugeCompletion A) ∘L vecForward = X - gaugeCompletion A := by
  have h5 := gaugeCompletion_displacement A
  rw [adjoint_vecForward] at h5 ⊢
  have hD : X - vecBack ∘L X ∘L vecForward - fluxTensor A
      = (X - gaugeCompletion A) - vecBack ∘L (X - gaugeCompletion A) ∘L vecForward := by
    rw [← h5]
    simp only [comp_sub, sub_comp]
    abel
  constructor
  · intro h
    rw [h, sub_self] at hD
    exact (sub_eq_zero.mp hD.symm).symm
  · intro h
    rw [h, sub_self] at hD
    exact sub_eq_zero.mp hD

/-- **Theorem PHSTH-D.**  `𝒢_A` is the unique compact solution of `X - 𝒰* X 𝒰 = 𝒯_A`. -/
theorem eq_gaugeCompletion_of_compact {A : E →L[ℂ] E} (hA : A.IsPositive)
    (hA1 : MemSchattenClass 1 A) {X : HistoryL2 E →L[ℂ] HistoryL2 E} (hXc : IsCompactOperator X)
    (hX : X - adjoint vecForward ∘L X ∘L vecForward = fluxTensor A) : X = gaugeCompletion A := by
  have hG := ((gaugeCompletion_traceClass hA hA1).2.1).isCompactOperator one_pos
  have hR := eq_zero_of_compact_fixed (hXc.sub hG) ((displacement_eq_iff A X).mp hX)
  exact sub_eq_zero.mp hR

/-- **Theorem PHSTH-E, (PHSTH.11).**  A positive solution dominates `𝒢_A`. -/
theorem isPositive_sub_gaugeCompletion {A : E →L[ℂ] E} (hA : A.IsPositive)
    (hA1 : MemSchattenClass 1 A) {X : HistoryL2 E →L[ℂ] HistoryL2 E} (hXp : X.IsPositive)
    (hX : X - adjoint vecForward ∘L X ∘L vecForward = fluxTensor A) :
    (X - gaugeCompletion A).IsPositive := by
  have hfix := (displacement_eq_iff A X).mp hX
  have hG := (gaugeCompletion_traceClass hA hA1).1
  rw [ContinuousLinearMap.isPositive_iff_complex] at hXp hG ⊢
  intro x
  have hreal : ((RCLike.re ⟪(X - gaugeCompletion A) x, x⟫_ℂ : ℝ) : ℂ)
      = ⟪(X - gaugeCompletion A) x, x⟫_ℂ := by
    rw [sub_apply, inner_sub_left, map_sub, Complex.ofReal_sub, (hXp x).1, (hG x).1]
  refine ⟨hreal, ?_⟩
  have hbound : ∀ N : ℕ, -(PrimeHodgeHistory.m N * ‖A‖ * ‖x‖ ^ 2)
      ≤ RCLike.re ⟪(X - gaugeCompletion A) x, x⟫_ℂ := fun N => by
    set y := (vecForward ^ N) x
    have hiter : ⟪(X - gaugeCompletion A) x, x⟫_ℂ = ⟪(X - gaugeCompletion A) y, y⟫_ℂ := by
      rw [← inner_conj_symm, inner_fixed_iter hfix N x x, inner_conj_symm]
    have hGy : ⟪gaugeCompletion A y, y⟫_ℂ
        = ⟪((vecBack ^ N) ∘L gaugeCompletion A ∘L (vecForward ^ N)) x, x⟫_ℂ := by
      rw [comp_apply, comp_apply, ← adjoint_vecForward_pow, adjoint_inner_left]
    have hnorm : ‖(vecBack ^ N) ∘L gaugeCompletion A ∘L (vecForward ^ N)‖
        ≤ PrimeHodgeHistory.m N * ‖A‖ := by
      rw [tail_gaugeCompletion]
      refine norm_historyMap_le _ _ A (PrimeHodgeHistory.m_pos N).le fun n => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (PrimeHodgeHistory.m_pos _)]
      exact PrimeHodgeHistory.m_antitone (Nat.le_add_left N n)
    have hGle : RCLike.re ⟪gaugeCompletion A y, y⟫_ℂ ≤ PrimeHodgeHistory.m N * ‖A‖ * ‖x‖ ^ 2 := by
      rw [hGy]
      calc RCLike.re ⟪((vecBack ^ N) ∘L gaugeCompletion A ∘L (vecForward ^ N)) x, x⟫_ℂ
          ≤ ‖⟪((vecBack ^ N) ∘L gaugeCompletion A ∘L (vecForward ^ N)) x, x⟫_ℂ‖ :=
            RCLike.re_le_norm _
        _ ≤ ‖((vecBack ^ N) ∘L gaugeCompletion A ∘L (vecForward ^ N)) x‖ * ‖x‖ :=
            norm_inner_le_norm _ _
        _ ≤ (PrimeHodgeHistory.m N * ‖A‖ * ‖x‖) * ‖x‖ := by
            gcongr
            exact (le_opNorm _ _).trans (by gcongr)
        _ = PrimeHodgeHistory.m N * ‖A‖ * ‖x‖ ^ 2 := by ring
    rw [hiter, sub_apply, inner_sub_left, map_sub]
    linarith [(hXp y).2]
  have hlim : Tendsto (fun N : ℕ => -(PrimeHodgeHistory.m N * ‖A‖ * ‖x‖ ^ 2)) atTop (𝓝 0) := by
    simpa using ((hasSum_m.summable.tendsto_atTop_zero.mul_const ‖A‖).mul_const (‖x‖ ^ 2)).neg
  exact le_of_tendsto hlim (Eventually.of_forall hbound)

/-- **(PHSTH.12).**  A positive trace-class solution is `𝒢_A`. -/
theorem eq_gaugeCompletion_of_traceClass {A : E →L[ℂ] E} (hA : A.IsPositive)
    (hA1 : MemSchattenClass 1 A) {X : HistoryL2 E →L[ℂ] HistoryL2 E} (hX1 : MemSchattenClass 1 X)
    (hX : X - adjoint vecForward ∘L X ∘L vecForward = fluxTensor A) : X = gaugeCompletion A :=
  eq_gaugeCompletion_of_compact hA hA1 (hX1.isCompactOperator one_pos) hX

/-- **Theorem PHSTH-E.**  A shift-fixed horizon repeats its grade mass: every `e_n ⊗ v` sees
the same expectation. -/
theorem inner_fixed_single {R : HistoryL2 E →L[ℂ] HistoryL2 E}
    (hfix : vecBack ∘L R ∘L vecForward = R) (n : ℕ) (v : E) :
    ⟪lp.single 2 n v, R (lp.single 2 n v)⟫_ℂ = ⟪lp.single 2 0 v, R (lp.single 2 0 v)⟫_ℂ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [(fixed_iff_toeplitz R).mp hfix n n v v, ih]

/-- **Theorem PHSTH-E.**  A nonzero positive horizon is not compact and not trace class. -/
theorem not_compact_of_fixed_ne_zero {R : HistoryL2 E →L[ℂ] HistoryL2 E}
    (hfix : vecBack ∘L R ∘L vecForward = R) (hR : R ≠ 0) :
    ¬IsCompactOperator R ∧ ¬MemSchattenClass 1 R :=
  ⟨fun h => hR (eq_zero_of_compact_fixed h hfix),
    fun h => hR (eq_zero_of_compact_fixed (h.isCompactOperator one_pos) hfix)⟩

/-- A positive operator vanishes on every vector of zero expectation. -/
theorem apply_eq_zero_of_inner_eq_zero {R : HistoryL2 E →L[ℂ] HistoryL2 E} (hR : R.IsPositive)
    {z : HistoryL2 E} (hz : RCLike.re ⟪R z, z⟫_ℂ = 0) : R z = 0 := by
  set S := traceClassRoot R
  have hSS : S ∘L S = R := by
    rw [traceClassRoot_comp_self, absOp_of_nonneg ((nonneg_iff_isPositive R).mpr hR)]
  have hSadj : adjoint S = S := (isSelfAdjoint_traceClassRoot R).adjoint_eq
  have hnorm : ‖S z‖ ^ 2 = RCLike.re ⟪R z, z⟫_ℂ := by
    rw [← hSS, comp_apply, ← hSadj, adjoint_inner_left, hSadj, inner_self_eq_norm_sq]
  have hSz : S z = 0 := by
    rw [hz] at hnorm
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hnorm)
  rw [← hSS, comp_apply, hSz, map_zero]

/-- **Theorem PHSTH-E.**  A nonzero positive horizon carries a fixed positive mass `b` at every
history grade. -/
theorem exists_repeated_mass {R : HistoryL2 E →L[ℂ] HistoryL2 E} (hR : R.IsPositive)
    (hfix : vecBack ∘L R ∘L vecForward = R) (hne : R ≠ 0) :
    ∃ v : E, 0 < RCLike.re ⟪R (lp.single 2 0 v), lp.single 2 0 v⟫_ℂ ∧
      ∀ n, ⟪R (lp.single 2 n v), lp.single 2 n v⟫_ℂ
        = ⟪R (lp.single 2 0 v), lp.single 2 0 v⟫_ℂ := by
  have hrep : ∀ n (v : E), ⟪R (lp.single 2 n v), lp.single 2 n v⟫_ℂ
      = ⟪R (lp.single 2 0 v), lp.single 2 0 v⟫_ℂ := fun n v => by
    rw [← inner_conj_symm, inner_fixed_single hfix n v, inner_conj_symm]
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  apply hne
  refine historyL2_ext_single fun n m x y => ?_
  have hzero : R (lp.single 2 m y) = 0 := by
    refine apply_eq_zero_of_inner_eq_zero hR (le_antisymm ?_ (hR.re_inner_nonneg_left _))
    rw [hrep m y]
    by_contra hpos
    exact hcon y (lt_of_not_ge hpos) fun n => hrep n y
  rw [hzero, zero_apply, inner_zero_right]

/-! ## The two lifts of a finite observer -/

/-- **(PHSTH.13).**  The harmonic lift `H_p = I ⊗ p`. -/
def harmonicLift (p : E →L[ℂ] E) : HistoryL2 E →L[ℂ] HistoryL2 E :=
  historyMap (fun _ => 1) (fun _ => by simp) p

omit [CompleteSpace E] in
/-- **Theorem PHSTH-F.**  `𝒰* H_p 𝒰 = H_p`. -/
theorem harmonicLift_fixed (p : E →L[ℂ] E) :
    vecBack ∘L harmonicLift p ∘L vecForward = harmonicLift p := by
  have h := vecBack_pow_historyMap_vecForward_pow (fun _ => (1 : ℂ)) (fun _ => by simp) p 1
  simp only [pow_one] at h
  exact h

omit [CompleteSpace E] in
/-- **Theorem PHSTH-F.**  The grade-zero block of `H_p` is `p`. -/
theorem inner_single_harmonicLift (p : E →L[ℂ] E) (x y : E) :
    ⟪lp.single 2 0 x, harmonicLift p (lp.single 2 0 y)⟫_ℂ = ⟪x, p y⟫_ℂ := by
  have h : ⟪lp.single 2 0 x, harmonicLift p (lp.single 2 0 y)⟫_ℂ
      = ⟪x, (harmonicLift p (lp.single 2 0 y) : ℕ → E) 0⟫_ℂ := lp.inner_single_left _ _ _
  rw [h, harmonicLift, historyMap_apply, one_smul, lp.single_apply_self]

theorem harmonicLift_isPositive {p : E →L[ℂ] E} (hp : p.IsPositive) :
    (harmonicLift p).IsPositive := by
  have hSS : adjoint (traceClassRoot p) ∘L traceClassRoot p = p := by
    rw [(isSelfAdjoint_traceClassRoot p).adjoint_eq, traceClassRoot_comp_self,
      absOp_of_nonneg ((nonneg_iff_isPositive p).mpr hp)]
  have h := historyMap_adjoint_comp_self (w := fun _ => 1) (fun _ => zero_le_one)
    (fun _ => le_rfl) (traceClassRoot p)
  rw [hSS] at h
  have heq : harmonicLift p = historyMap (fun _ => ((1 : ℝ) : ℂ))
      (norm_ofReal_weight_le_one (fun _ => zero_le_one) fun _ => le_rfl) p :=
    historyMap_congr _ _ (funext fun _ => Complex.ofReal_one.symm) _
  rw [heq, h]
  exact isPositive_adjoint_comp_self _

omit [CompleteSpace E] in
theorem harmonicLift_ne_zero {p : E →L[ℂ] E} (hp : p ≠ 0) : harmonicLift p ≠ 0 := by
  intro h
  apply hp
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [← inner_single_harmonicLift, h, zero_apply, inner_zero_right, zero_apply, inner_zero_right]

/-- **Theorem PHSTH-F.**  For `p ≠ 0`, `H_p` is noncompact and not trace class. -/
theorem harmonicLift_not_compact {p : E →L[ℂ] E} (hp : p ≠ 0) :
    ¬IsCompactOperator (harmonicLift p) ∧ ¬MemSchattenClass 1 (harmonicLift p) :=
  not_compact_of_fixed_ne_zero (harmonicLift_fixed p) (harmonicLift_ne_zero hp)

/-- **Theorem PHSTH-G, (PHSTH.14).**  The first-exit lift `E_p = Φ ⊗ p` is positive trace class
with `tr E_p = tr p`. -/
theorem fluxTensor_traceClass {p : E →L[ℂ] E} (hp : p.IsPositive) (hp1 : MemSchattenClass 1 p) :
    (fluxTensor p).IsPositive ∧ MemSchattenClass 1 (fluxTensor p) ∧
      opTrace (fluxTensor p) = opTrace p := by
  obtain ⟨h1, h2, h3, -⟩ := historyMap_nonneg_traceClass historyFlux_nonneg historyFlux_le_one
    PrimeHodgeHistory.summable_w hp hp1
  refine ⟨h1, h2, ?_⟩
  rw [fluxTensor, h3, PrimeHodgeHistory.tsum_w, Complex.ofReal_one, one_mul]

omit [CompleteSpace E] in
/-- **Theorem PHSTH-G.**  The history blocks of `E_p` are `w_n p`. -/
theorem inner_single_fluxTensor (p : E →L[ℂ] E) (n : ℕ) (x y : E) :
    ⟪lp.single 2 n x, fluxTensor p (lp.single 2 n y)⟫_ℂ
      = (PrimeHodgeHistory.w n : ℂ) * ⟪x, p y⟫_ℂ := by
  have h : ⟪lp.single 2 n x, fluxTensor p (lp.single 2 n y)⟫_ℂ
      = ⟪x, (fluxTensor p (lp.single 2 n y) : ℕ → E) n⟫_ℂ := lp.inner_single_left _ _ _
  rw [h, fluxTensor, historyMap_apply, lp.single_apply_self, inner_smul_right]

omit [CompleteSpace E] in
/-- **Theorem PHSTH-G.**  The history blocks `w_n p` of `E_p` sum to `p`. -/
theorem hasSum_fluxTensor_blocks (p : E →L[ℂ] E) :
    HasSum (fun n => (PrimeHodgeHistory.w n : ℂ) • p) p := by
  simpa using (Complex.hasSum_ofReal.mpr PrimeHodgeHistory.hasSum_w).smul_const p

end Displacement

/-! ## The prime–Hodge completion -/

/-- The literal positive trace-one prime Cauchy-cube formation operator `A_d`. -/
abbrev primeFormation {d : ℝ} (hd : 0 < d) : PrimeHilbert →L[ℂ] PrimeHilbert :=
  adjoint (burnolPrimeSynthesis hd) ∘L burnolPrimeSynthesis hd

theorem primeFormation_traceClass {d : ℝ} (hd : 0 < d) :
    (primeFormation hd).IsPositive ∧ MemSchattenClass 1 (primeFormation hd) ∧
      opTrace (primeFormation hd) = 1 := by
  have hV := isHilbertSchmidt_burnolPrimeSynthesis hd
  refine ⟨isPositive_adjoint_comp_self _, memSchattenClass_one_comp hV.adjoint hV, ?_⟩
  rw [opTrace_adjoint_comp_self, hsInner_self_eq_ofReal_hsNormSq', burnolPrimeSynthesis,
    hsNormSq_commonRadialPrimeSynthesis, Complex.ofReal_one]

/-- **Theorem PHSTH-B.**  The prime–Hodge defect is the signed shift displacement of the compact
completion `G ⊗ A_{|t|}`. -/
theorem historyDefect_eq_displacement {t : ℝ} (ht : t ≠ 0) :
    historyDefect t = ((Real.sign t : ℝ) : ℂ) •
      (gaugeCompletion (primeFormation (abs_pos.mpr ht)) - adjoint vecForward ∘L
        gaugeCompletion (primeFormation (abs_pos.mpr ht)) ∘L vecForward) := by
  rw [historyDefect_of_ne ht, gaugeCompletion_displacement]

/-- **(PHSTH.7).**  For `tr A_d = 1`: defect mass one, completion mass `7/4`. -/
theorem prime_completion_masses {d : ℝ} (hd : 0 < d) :
    traceNorm (HistoryL2 PrimeHilbert) (fluxTensor (primeFormation hd)) = 1 ∧
      traceNorm (HistoryL2 PrimeHilbert) (gaugeCompletion (primeFormation hd)) = 7 / 4 := by
  obtain ⟨h1, h2, h3⟩ := primeFormation_traceClass hd
  refine ⟨?_, ?_⟩
  · rw [traceNorm_fluxTensor h1 h2, h3, Complex.one_re]
  · rw [(gaugeCompletion_traceClass h1 h2).2.2, h3, Complex.one_re, mul_one]

/-- **ULF-PHSTH-001.**  The singular gauge `Q = diag(√m_n)` is positive, compact, injective, with
dense nonclosed range and `C Q = Q U`; for every positive trace-class `A`, `𝒢_A = G ⊗ A` has
shift displacement `𝒯_A = Φ ⊗ A`, is the trace-norm sum of the transported defects with the
`1 / (7/4) / (7/4)` trace laws, and is the unique compact solution; every solution differs from it
by a shift fixed point (a Toeplitz horizon); positive solutions dominate it; a nonzero horizon is
noncompact and not trace class; the harmonic lift `I ⊗ p` is such a horizon with grade-zero block
`p`, while the first-exit lift `Φ ⊗ p` is positive trace class with trace `tr p` and blocks `w_n p`
summing to `p`; and the literal prime–Hodge defect is the signed displacement of `G ⊗ A_d`. -/
theorem prime_hodge_singular_gauge_toeplitz_horizon :
    (singularGauge.IsPositive ∧ IsCompactOperator singularGauge ∧
      Function.Injective singularGauge ∧ DenseRange singularGauge ∧
      ¬IsClosed (Set.range singularGauge) ∧
      primeHodgeHistorySurvivalShift ∘L singularGauge = singularGauge ∘L vecForward ∧
      singularGauge ∘L singularGauge = steinGramian) ∧
    (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (A : E →L[ℂ] E), A.IsPositive → MemSchattenClass 1 A →
      gaugeCompletion A - adjoint vecForward ∘L gaugeCompletion A ∘L vecForward
          = fluxTensor A ∧
      Tendsto (fun N => traceNorm (HistoryL2 E) (gaugeCompletion A -
        ∑ j ∈ Finset.range N, (vecBack ^ j) ∘L fluxTensor A ∘L (vecForward ^ j))) atTop (𝓝 0) ∧
      traceNorm (HistoryL2 E) (fluxTensor A) = (opTrace A).re ∧
      traceNorm (HistoryL2 E) (gaugeCompletion A) = 7 / 4 * (opTrace A).re ∧
      HasSum (fun j => traceNorm (HistoryL2 E)
        ((vecBack ^ j) ∘L fluxTensor A ∘L (vecForward ^ j))) (7 / 4 * (opTrace A).re) ∧
      (∀ X : HistoryL2 E →L[ℂ] HistoryL2 E,
        (X - adjoint vecForward ∘L X ∘L vecForward = fluxTensor A ↔
          vecBack ∘L (X - gaugeCompletion A) ∘L vecForward = X - gaugeCompletion A) ∧
        (IsCompactOperator X → X - adjoint vecForward ∘L X ∘L vecForward = fluxTensor A →
          X = gaugeCompletion A) ∧
        (X.IsPositive → X - adjoint vecForward ∘L X ∘L vecForward = fluxTensor A →
          (X - gaugeCompletion A).IsPositive))) ∧
    (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (R : HistoryL2 E →L[ℂ] HistoryL2 E),
      (vecBack ∘L R ∘L vecForward = R ↔ ∀ n m (x y : E),
        ⟪lp.single 2 (n + 1) x, R (lp.single 2 (m + 1) y)⟫_ℂ
          = ⟪lp.single 2 n x, R (lp.single 2 m y)⟫_ℂ) ∧
      (IsCompactOperator R → vecBack ∘L R ∘L vecForward = R → R = 0) ∧
      (R.IsPositive → vecBack ∘L R ∘L vecForward = R → R ≠ 0 →
        (∃ v : E, 0 < RCLike.re ⟪R (lp.single 2 0 v), lp.single 2 0 v⟫_ℂ ∧
          ∀ n, ⟪R (lp.single 2 n v), lp.single 2 n v⟫_ℂ
            = ⟪R (lp.single 2 0 v), lp.single 2 0 v⟫_ℂ) ∧
        ¬IsCompactOperator R ∧ ¬MemSchattenClass 1 R)) ∧
    (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (p : E →L[ℂ] E), p.IsPositive → MemSchattenClass 1 p → p ≠ 0 →
      (harmonicLift p).IsPositive ∧ vecBack ∘L harmonicLift p ∘L vecForward = harmonicLift p ∧
      (∀ x y : E, ⟪lp.single 2 0 x, harmonicLift p (lp.single 2 0 y)⟫_ℂ = ⟪x, p y⟫_ℂ) ∧
      ¬IsCompactOperator (harmonicLift p) ∧ ¬MemSchattenClass 1 (harmonicLift p) ∧
      fluxTensor p = gaugeCompletion p - adjoint vecForward ∘L gaugeCompletion p ∘L vecForward ∧
      (fluxTensor p).IsPositive ∧ MemSchattenClass 1 (fluxTensor p) ∧
      opTrace (fluxTensor p) = opTrace p ∧
      (∀ n (x y : E), ⟪lp.single 2 n x, fluxTensor p (lp.single 2 n y)⟫_ℂ
        = (PrimeHodgeHistory.w n : ℂ) * ⟪x, p y⟫_ℂ) ∧
      HasSum (fun n => (PrimeHodgeHistory.w n : ℂ) • p) p) ∧
    (∀ t : ℝ, (ht : t ≠ 0) → historyDefect t = ((Real.sign t : ℝ) : ℂ) •
      (gaugeCompletion (primeFormation (abs_pos.mpr ht)) - adjoint vecForward ∘L
        gaugeCompletion (primeFormation (abs_pos.mpr ht)) ∘L vecForward)) ∧
    (∀ {d : ℝ} (hd : 0 < d),
      traceNorm (HistoryL2 PrimeHilbert) (fluxTensor (primeFormation hd)) = 1 ∧
      traceNorm (HistoryL2 PrimeHilbert) (gaugeCompletion (primeFormation hd)) = 7 / 4) := by
  refine ⟨⟨singularGauge_isPositive, isCompactOperator_singularGauge, singularGauge_injective,
      denseRange_singularGauge, not_isClosed_range_singularGauge,
      survivalShift_comp_singularGauge, singularGauge_comp_self⟩, ?_, ?_, ?_,
      fun t ht => historyDefect_eq_displacement ht, fun hd => prime_completion_masses hd⟩
  · intro E _ _ _ A hA hA1
    exact ⟨gaugeCompletion_displacement A, tendsto_traceNorm_gaugeCompletion_sub hA hA1,
      traceNorm_fluxTensor hA hA1, (gaugeCompletion_traceClass hA hA1).2.2,
      hasSum_traceNorm_conj_fluxTensor hA hA1, fun X => ⟨displacement_eq_iff A X,
        fun hXc hX => eq_gaugeCompletion_of_compact hA hA1 hXc hX,
        fun hXp hX => isPositive_sub_gaugeCompletion hA hA1 hXp hX⟩⟩
  · intro E _ _ _ R
    exact ⟨fixed_iff_toeplitz R, fun hc hf => eq_zero_of_compact_fixed hc hf,
      fun hp hf hne => ⟨exists_repeated_mass hp hf hne, not_compact_of_fixed_ne_zero hf hne⟩⟩
  · intro E _ _ _ p hp hp1 hne
    obtain ⟨f1, f2, f3⟩ := fluxTensor_traceClass hp hp1
    exact ⟨harmonicLift_isPositive hp, harmonicLift_fixed p, inner_single_harmonicLift p,
      (harmonicLift_not_compact hne).1, (harmonicLift_not_compact hne).2,
      (gaugeCompletion_displacement p).symm, f1, f2, f3, inner_single_fluxTensor p,
      hasSum_fluxTensor_blocks p⟩

end GaloisForLFunctions.HTGeometry
