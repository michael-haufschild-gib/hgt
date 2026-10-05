import GaloisForLFunctions.HTGeometry.CrowdedPrimeLogPairs
import GaloisForLFunctions.HTGeometry.PrimeShiftResponseProperness

/-!
# Depth-two response channels of crowded prime pairs

A finite diagonal logarithmic/time-differential family `𝒟 = {(P_ℓ, k_ℓ)}`, `P_ℓ ∈ ℂ[X,Y]`,
`k_ℓ ∈ ℕ`, `(P_0, k_0) = (1, 0)`, turns the `j`-th crowded prime pair into the response vector
`g_j = (P_ℓ(a_j,b_j) ∂_t^{k_ℓ}(a_j b_j ω_t(a_j,b_j)) e_{p_j q_j})_ℓ` of
`⊕_ℓ L²((0,T]; ℓ²(ℕ≥1))` `(FGP.8)`.  Distinct products `p_j q_j` make the `g_j` orthogonal; the
constant channel makes them nonzero; and `(FGP.4b)`, `(FGP.7)` with the polynomial growth of the
`P_ℓ` give `‖g_j‖ ≤ √T C_𝒟 R_j^{D+κ-1} η_{R_j}` `(FGP.9)`, which tends to zero because the
stretched exponential `η_R = K e^{-c R^{1/10}}` beats every power of `R`.
-/

open scoped InnerProductSpace
open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-! ### The defect as a smooth function of time -/

/-- `t ↦ ab ω_t(a,b)`. -/
def defectFun (a b t : ℝ) : ℝ := a * b * defectKernel t a b

theorem defectFun_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    defectFun a b = fun t => (a - b) / (a + b) * (1 - Real.exp (-(a + b) * t)) +
      Real.exp (-a * t) - Real.exp (-b * t) :=
  funext fun t => defectKernel_closed ha hb t

theorem contDiff_defectFun {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : ContDiff ℝ ⊤ (defectFun a b) := by
  rw [defectFun_eq ha hb]
  fun_prop

theorem continuous_iteratedDeriv_defectFun {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    Continuous (iteratedDeriv k (defectFun a b)) :=
  (contDiff_defectFun ha hb).continuous_iteratedDeriv k le_top

/-! ### Differential families -/

/-- A finite diagonal logarithmic/time-differential family containing `(1, 0)`. -/
structure DiffFamily where
  /-- The number of channels is `M + 1`. -/
  M : ℕ
  /-- The polynomial weights `P_ℓ(a, b)`. -/
  P : Fin (M + 1) → MvPolynomial (Fin 2) ℂ
  /-- The time-derivative orders. -/
  k : Fin (M + 1) → ℕ
  P_zero : P 0 = 1
  k_zero : k 0 = 0

namespace DiffFamily

variable (D : DiffFamily)

/-- The maximal polynomial degree `D`. -/
def degree : ℕ := Finset.univ.sup fun ℓ => (D.P ℓ).totalDegree

/-- The maximal derivative order `κ`. -/
def order : ℕ := Finset.univ.sup D.k

end DiffFamily

/-- The coefficient mass `∑ |coeff|` of a polynomial. -/
def coeffMass (P : MvPolynomial (Fin 2) ℂ) : ℝ := ∑ m ∈ P.support, ‖P.coeff m‖

theorem coeffMass_nonneg (P : MvPolynomial (Fin 2) ℂ) : 0 ≤ coeffMass P :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Polynomial growth: `|P(x)| ≤ ‖P‖₁ B^{deg P}` when `|xᵢ| ≤ B`, `B ≥ 1`. -/
theorem norm_eval_le (P : MvPolynomial (Fin 2) ℂ) {x : Fin 2 → ℂ} {B : ℝ} (hB : 1 ≤ B)
    (hx : ∀ i, ‖x i‖ ≤ B) : ‖MvPolynomial.eval x P‖ ≤ coeffMass P * B ^ P.totalDegree := by
  rw [MvPolynomial.eval_eq, coeffMass, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∏ i ∈ m.support, x i ^ m i‖ = ∏ i ∈ m.support, ‖x i‖ ^ m i := by
        rw [norm_prod]
        simp [norm_pow]
    _ ≤ ∏ i ∈ m.support, B ^ m i :=
        Finset.prod_le_prod (fun _ _ => by positivity)
          fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hx i) _
    _ = B ^ (m.sum fun _ e => e) := by rw [Finsupp.sum, Finset.prod_pow_eq_pow_sum]
    _ ≤ B ^ P.totalDegree := pow_le_pow_right₀ hB (MvPolynomial.le_totalDegree hm)

/-! ### Channels of a crowded pair -/

namespace CrowdedPairs

variable (P : CrowdedPairs) (D : DiffFamily)

/-- The output index `p_j q_j`. -/
def outIndex (j : ℕ) : ℕ+ := ⟨P.p j * P.q j, Nat.mul_pos (P.p_prime j).pos (P.q_prime j).pos⟩

theorem outIndex_injective : Function.Injective P.outIndex := fun _ _ h =>
  P.mul_injective (congrArg PNat.val h)

/-- The source grades `(a_j, b_j)`. -/
def coord (j : ℕ) : Fin 2 → ℂ := ![(P.a j : ℂ), (P.b j : ℂ)]

/-- The channel coefficient `P_ℓ(a_j, b_j) ∂_t^{k_ℓ}(a_j b_j ω_t(a_j, b_j))`. -/
def channelCoeff (ℓ : Fin (D.M + 1)) (j : ℕ) (t : ℝ) : ℂ :=
  MvPolynomial.eval (P.coord j) (D.P ℓ) *
    ((iteratedDeriv (D.k ℓ) (defectFun (P.a j) (P.b j)) t : ℝ) : ℂ)

/-- The channel history `t ↦ channelCoeff · e_{p_j q_j}`. -/
def channelProfile (ℓ : Fin (D.M + 1)) (j : ℕ) (t : ℝ) : ArithSpace :=
  P.channelCoeff D ℓ j t • basisVec (P.outIndex j)

theorem b_pos (j : ℕ) : 0 < P.b j := (P.a_pos j).trans (P.a_lt_b j)

theorem continuous_channelCoeff (ℓ : Fin (D.M + 1)) (j : ℕ) :
    Continuous (P.channelCoeff D ℓ j) :=
  continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_iteratedDeriv_defectFun (P.a_pos j) (P.b_pos j) _))

theorem norm_channelProfile (ℓ : Fin (D.M + 1)) (j : ℕ) (t : ℝ) :
    ‖P.channelProfile D ℓ j t‖ = ‖P.channelCoeff D ℓ j t‖ := by
  rw [channelProfile, norm_smul, norm_basisVec, mul_one]

/-- The channel bound `|P_ℓ(a_j,b_j)| C_{k_ℓ} a_j^{k_ℓ-1} (b_j - a_j)`. -/
def channelBound (ℓ : Fin (D.M + 1)) (j : ℕ) : ℝ :=
  ‖MvPolynomial.eval (P.coord j) (D.P ℓ)‖ *
    (derivConst (D.k ℓ) * P.a j ^ ((D.k ℓ : ℤ) - 1) * (P.b j - P.a j))

theorem norm_channelCoeff_le (ℓ : Fin (D.M + 1)) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖P.channelCoeff D ℓ j t‖ ≤ P.channelBound D ℓ j := by
  rw [channelCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, channelBound]
  exact mul_le_mul_of_nonneg_left
    (abs_iteratedDeriv_defect_le (P.a_pos j) (P.a_lt_b j).le (P.b_le_two_a j) ht _)
    (norm_nonneg _)

theorem memLp_channelProfile (T : ℝ) (ℓ : Fin (D.M + 1)) (j : ℕ) :
    MemLp (P.channelProfile D ℓ j) 2 (timeMeasure T) := by
  refine MemLp.of_bound (((P.continuous_channelCoeff D ℓ j).smul
    continuous_const).aestronglyMeasurable) (P.channelBound D ℓ j) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
  rw [norm_channelProfile]
  exact P.norm_channelCoeff_le D ℓ j ht.1.le

end CrowdedPairs

/-! ### The depth-two response vectors -/

/-- The output space `⊕_ℓ L²((0,T]; ℓ²(ℕ≥1))`. -/
abbrev OutSpace (T : ℝ) (M : ℕ) : Type := PiLp 2 fun _ : Fin (M + 1) => ResponseSpace T

theorem norm_sq_toLp {f : ℝ → ArithSpace} {μ : Measure ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℂ) (hf.toLp f) (hf.toLp f)
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ∫ t, ⟪(hf.toLp f : ℝ → ArithSpace) t, (hf.toLp f : ℝ → ArithSpace) t⟫_ℂ ∂μ =
      ∫ t, ((‖f t‖ ^ 2 : ℝ) : ℂ) ∂μ :=
    integral_congr_ae (hf.coeFn_toLp.mono fun t ht => by
      simp only [ht, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl)
  rw [h2, integral_complex_ofReal] at h
  have h3 := congrArg Complex.re h
  simpa [← Complex.ofReal_pow] using h3

namespace CrowdedPairs

variable (P : CrowdedPairs) (D : DiffFamily)

/-- **`(FGP.8)`: the depth-two response vector** of the `j`-th crowded pair. -/
def responseVec (T : ℝ) (j : ℕ) : OutSpace T D.M :=
  WithLp.toLp 2 fun ℓ => (P.memLp_channelProfile D T ℓ j).toLp

theorem norm_sq_responseVec (T : ℝ) (j : ℕ) :
    ‖P.responseVec D T j‖ ^ 2 =
      ∑ ℓ, ∫ t, ‖P.channelCoeff D ℓ j t‖ ^ 2 ∂(timeMeasure T) := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [responseVec, PiLp.toLp_apply, norm_sq_toLp]
  simp_rw [norm_channelProfile]

/-- Distinct crowded pairs give orthogonal response vectors. -/
theorem inner_responseVec_of_ne (T : ℝ) {i j : ℕ} (hij : i ≠ j) :
    ⟪P.responseVec D T i, P.responseVec D T j⟫_ℂ = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  rw [responseVec, responseVec, PiLp.toLp_apply, PiLp.toLp_apply, MeasureTheory.L2.inner_def]
  have hne : P.outIndex i ≠ P.outIndex j := fun h => hij (P.outIndex_injective h)
  have h0 : ⟪basisVec (P.outIndex i), basisVec (P.outIndex j)⟫_ℂ = 0 := by
    rw [orthonormal_iff_ite.mp orthonormal_basisVec, if_neg hne]
  refine (integral_congr_ae (g := fun _ : ℝ => (0 : ℂ))
    (((P.memLp_channelProfile D T ℓ i).coeFn_toLp).mp
    (((P.memLp_channelProfile D T ℓ j).coeFn_toLp).mono fun t hj hi => ?_))).trans (by simp)
  simp only [hi, hj, channelProfile, inner_smul_left, inner_smul_right, h0, mul_zero]

end CrowdedPairs

/-! ### Stretched-exponential decay beats every power -/

theorem tendsto_pow_mul_exp_neg_mul {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Tendsto (fun y : ℝ => y ^ m * Real.exp (-(c * y))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
    (tendsto_id.const_mul_atTop hc)
  have h2 := h.const_mul (c ^ m)⁻¹
  rw [mul_zero] at h2
  refine h2.congr fun y => ?_
  simp only [Function.comp_apply, id, mul_pow]
  field_simp

/-- `R^N e^{-c R^{1/10}} → 0` for every integer power `N`. -/
theorem tendsto_zpow_mul_crowdWidth {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (N : ℤ) :
    Tendsto (fun R => R ^ N * crowdWidth c K R) atTop (𝓝 0) := by
  set n := N.toNat
  have hy : Tendsto (fun R : ℝ => R ^ ((1 : ℝ) / 10)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h1 := ((tendsto_pow_mul_exp_neg_mul hc (10 * n)).comp hy).const_mul K
  rw [mul_zero] at h1
  have heq : ∀ R : ℝ, 0 ≤ R → K * ((R ^ ((1 : ℝ) / 10)) ^ (10 * n) *
      Real.exp (-(c * R ^ ((1 : ℝ) / 10)))) = R ^ n * crowdWidth c K R := fun R hR => by
    rw [← Real.rpow_natCast (R ^ ((1 : ℝ) / 10)), ← Real.rpow_mul hR, crowdWidth]
    rw [show (1 : ℝ) / 10 * ((10 * n : ℕ) : ℝ) = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  have h2 : Tendsto (fun R => R ^ n * crowdWidth c K R) atTop (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    exact heq R hR
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_ge_atTop 1] with R hR
    exact mul_nonneg (zpow_nonneg (by linarith) _) (crowdWidth_pos (c := c) hK R).le
  · filter_upwards [eventually_ge_atTop 1] with R hR
    refine mul_le_mul_of_nonneg_right ?_ (crowdWidth_pos (c := c) hK R).le
    calc R ^ N ≤ R ^ (n : ℤ) := zpow_le_zpow_right₀ hR (Int.self_le_toNat N)
      _ = R ^ n := zpow_natCast R n

namespace CrowdedPairs

variable (P : CrowdedPairs) (D : DiffFamily)

/-- The singular value `s_j = ‖g_j‖`. -/
def singular (T : ℝ) (j : ℕ) : ℝ := ‖P.responseVec D T j‖

theorem channelCoeff_zero (j : ℕ) (t : ℝ) :
    P.channelCoeff D 0 j t = (defectFun (P.a j) (P.b j) t : ℂ) := by
  simp [channelCoeff, D.P_zero, D.k_zero, iteratedDeriv_zero]

theorem integral_channel_nonneg (T : ℝ) (ℓ : Fin (D.M + 1)) (j : ℕ) :
    0 ≤ ∫ t, ‖P.channelCoeff D ℓ j t‖ ^ 2 ∂(timeMeasure T) :=
  integral_nonneg fun _ => sq_nonneg _

/-- **Theorem 4.1(1)**: `s_j > 0`. -/
theorem singular_pos {T : ℝ} (hT : 0 < T) (j : ℕ) : 0 < P.singular D T j := by
  have h0 : 0 < ∫ t, ‖P.channelCoeff D 0 j t‖ ^ 2 ∂(timeMeasure T) := by
    rw [timeMeasure, ← intervalIntegral.integral_of_le hT.le]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (((P.continuous_channelCoeff D 0 j).norm.pow 2).intervalIntegrable _ _) (fun t ht => ?_) hT
    rw [channelCoeff_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hne : defectFun (P.a j) (P.b j) t ≠ 0 := by
      have := neg_defect_pos (P.a_pos j) (P.a_lt_b j) ht.1
      unfold defectFun
      linarith
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  have hle := Finset.single_le_sum (f := fun ℓ => ∫ t, ‖P.channelCoeff D ℓ j t‖ ^ 2
    ∂(timeMeasure T)) (fun ℓ _ => P.integral_channel_nonneg D T ℓ j) (Finset.mem_univ 0)
  have hsq : 0 < P.singular D T j ^ 2 := by
    rw [singular, P.norm_sq_responseVec D T j]
    exact h0.trans_le hle
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by rw [zero_pow two_ne_zero]; exact hsq)

theorem channelBound_nonneg (ℓ : Fin (D.M + 1)) (j : ℕ) : 0 ≤ P.channelBound D ℓ j := by
  unfold channelBound
  have := (P.a_lt_b j).le
  have := (P.a_pos j).le
  exact mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (derivConst_pos _).le
    (zpow_nonneg (P.a_pos j).le _)) (by linarith))

theorem integral_channel_le {T : ℝ} (hT : 0 ≤ T) (ℓ : Fin (D.M + 1)) (j : ℕ) :
    ∫ t, ‖P.channelCoeff D ℓ j t‖ ^ 2 ∂(timeMeasure T) ≤ T * P.channelBound D ℓ j ^ 2 := by
  have hle : ∫ t, ‖P.channelCoeff D ℓ j t‖ ^ 2 ∂(timeMeasure T) ≤
      ∫ _t, P.channelBound D ℓ j ^ 2 ∂(timeMeasure T) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
      (integrable_const _) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    exact pow_le_pow_left₀ (norm_nonneg _) (P.norm_channelCoeff_le D ℓ j ht.1.le) 2
  rw [integral_const, measureReal_restrict_apply_univ, Measure.real, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal hT, smul_eq_mul] at hle
  exact hle

theorem singular_le_sum {T : ℝ} (hT : 0 ≤ T) (j : ℕ) :
    P.singular D T j ≤ Real.sqrt T * ∑ ℓ, P.channelBound D ℓ j := by
  set S := ∑ ℓ, P.channelBound D ℓ j
  have hS : 0 ≤ S := Finset.sum_nonneg fun ℓ _ => P.channelBound_nonneg D ℓ j
  have hsq : P.singular D T j ^ 2 ≤ (Real.sqrt T * S) ^ 2 := by
    rw [singular, P.norm_sq_responseVec D T j, mul_pow, Real.sq_sqrt hT]
    calc ∑ ℓ, ∫ t, ‖P.channelCoeff D ℓ j t‖ ^ 2 ∂(timeMeasure T)
        ≤ ∑ ℓ, T * P.channelBound D ℓ j ^ 2 :=
          Finset.sum_le_sum fun ℓ _ => P.integral_channel_le D hT ℓ j
      _ = T * ∑ ℓ, P.channelBound D ℓ j * P.channelBound D ℓ j := by
          rw [Finset.mul_sum]; simp_rw [sq]
      _ ≤ T * ∑ ℓ, P.channelBound D ℓ j * S := by
          gcongr with ℓ
          · exact P.channelBound_nonneg D ℓ j
          · exact Finset.single_le_sum (fun ℓ _ => P.channelBound_nonneg D ℓ j)
              (Finset.mem_univ ℓ)
      _ = T * S ^ 2 := by rw [← Finset.sum_mul, sq]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The constant of channel `ℓ` in `(FGP.9)`. -/
def channelConst (ℓ : Fin (D.M + 1)) : ℝ :=
  coeffMass (D.P ℓ) * 4 ^ (D.P ℓ).totalDegree * (derivConst (D.k ℓ) * 2 ^ D.k ℓ) * 3

theorem channelConst_nonneg (ℓ : Fin (D.M + 1)) : 0 ≤ channelConst D ℓ := by
  unfold channelConst
  have := coeffMass_nonneg (D.P ℓ)
  have := derivConst_pos (D.k ℓ)
  positivity

theorem one_le_base (j : ℕ) : 1 ≤ P.base j := by linarith [P.base_ge j]

/-- `β_{ℓ,j} ≤ C_ℓ R_j^{d_ℓ + k_ℓ - 1} η_j`. -/
theorem channelBound_le (ℓ : Fin (D.M + 1)) (j : ℕ) :
    P.channelBound D ℓ j ≤
      channelConst D ℓ * P.base j ^ (((D.P ℓ).totalDegree + D.k ℓ : ℕ) - 1 : ℤ) * P.η j := by
  set R := P.base j
  have hR1 : 1 ≤ R := P.one_le_base j
  have hR0 : 0 < R := by linarith
  have ha := P.a_ge j
  have hb := P.b_le j
  have hab := (P.a_lt_b j).le
  have hapos := P.a_pos j
  have hcoord : ∀ i, ‖P.coord j i‖ ≤ 4 * R := fun i => by
    fin_cases i
    · simp only [coord, Fin.zero_eta, Matrix.cons_val_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hapos]
      linarith
    · simp only [coord, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (P.b_pos j)]
      linarith
  have heval := norm_eval_le (D.P ℓ) (by linarith : (1 : ℝ) ≤ 4 * R) hcoord
  have hapow : P.a j ^ ((D.k ℓ : ℤ) - 1) ≤ 2 ^ D.k ℓ * R ^ ((D.k ℓ : ℤ) - 1) := by
    rcases hk : D.k ℓ with _ | k
    · simp only [CharP.cast_eq_zero, zero_sub, Int.reduceNeg, zpow_neg_one, pow_zero, one_mul]
      exact inv_anti₀ hR0 ha
    · rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast]
      have ha2 : P.a j ≤ 2 * R := by
        have h1 := P.log_p_le j
        have h2 := P.width_le j
        simp only [CrowdedPairs.a]
        linarith
      calc P.a j ^ k ≤ (2 * R) ^ k := pow_le_pow_left₀ hapos.le ha2 k
        _ = 2 ^ k * R ^ k := mul_pow _ _ _
        _ ≤ 2 ^ (k + 1) * R ^ k := by gcongr <;> norm_num
  have hdiff := P.b_sub_a_le j
  have hpow : R ^ (D.P ℓ).totalDegree * R ^ ((D.k ℓ : ℤ) - 1) =
      R ^ (((D.P ℓ).totalDegree + D.k ℓ : ℕ) - 1 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hR0.ne']
    congr 1
    push_cast
    ring
  unfold channelBound channelConst
  calc ‖MvPolynomial.eval (P.coord j) (D.P ℓ)‖ *
        (derivConst (D.k ℓ) * P.a j ^ ((D.k ℓ : ℤ) - 1) * (P.b j - P.a j))
      ≤ (coeffMass (D.P ℓ) * (4 * R) ^ (D.P ℓ).totalDegree) *
        (derivConst (D.k ℓ) * (2 ^ D.k ℓ * R ^ ((D.k ℓ : ℤ) - 1)) * (3 * P.η j)) := by
        have hC := derivConst_pos (D.k ℓ)
        have hcm := coeffMass_nonneg (D.P ℓ)
        refine mul_le_mul heval (mul_le_mul (mul_le_mul_of_nonneg_left hapow hC.le) hdiff
          (by linarith) (by positivity)) (by positivity) (by positivity)
    _ = coeffMass (D.P ℓ) * 4 ^ (D.P ℓ).totalDegree * (derivConst (D.k ℓ) * 2 ^ D.k ℓ) * 3 *
          (R ^ (D.P ℓ).totalDegree * R ^ ((D.k ℓ : ℤ) - 1)) * P.η j := by
        rw [mul_pow]; ring
    _ = _ := by rw [hpow]

/-- The family constant `C_𝒟` of `(FGP.9)`. -/
def familyConst : ℝ := ∑ ℓ, channelConst D ℓ

/-- **`(FGP.9)`**: `s_j ≤ √T C_𝒟 R_j^{D+κ-1} η_{R_j}`. -/
theorem singular_le {T : ℝ} (hT : 0 ≤ T) (j : ℕ) :
    P.singular D T j ≤ Real.sqrt T * familyConst D *
      P.base j ^ ((D.degree + D.order : ℕ) - 1 : ℤ) * P.η j := by
  have hR1 := P.one_le_base j
  refine (P.singular_le_sum D hT j).trans ?_
  rw [mul_assoc (Real.sqrt T), mul_assoc (Real.sqrt T)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [familyConst, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun ℓ _ => (P.channelBound_le D ℓ j).trans ?_
  have hη := (P.η_pos j).le
  have h1 : (D.P ℓ).totalDegree ≤ D.degree :=
    Finset.le_sup (f := fun ℓ => (D.P ℓ).totalDegree) (Finset.mem_univ ℓ)
  have h2 : D.k ℓ ≤ D.order := Finset.le_sup (f := D.k) (Finset.mem_univ ℓ)
  have hexp : (((D.P ℓ).totalDegree + D.k ℓ : ℕ) - 1 : ℤ) ≤ ((D.degree + D.order : ℕ) - 1 : ℤ) := by
    push_cast
    linarith [(by exact_mod_cast h1 : ((D.P ℓ).totalDegree : ℤ) ≤ D.degree),
      (by exact_mod_cast h2 : ((D.k ℓ) : ℤ) ≤ D.order)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hR1 hexp)
    (channelConst_nonneg D ℓ)) hη

theorem tendsto_base : Tendsto P.base atTop atTop := by
  have h : P.base = fun j : ℕ => P.R₀ + 4 * (j : ℝ) := funext P.base_eq
  rw [h]
  exact tendsto_atTop_add_const_left _ _ ((tendsto_natCast_atTop_atTop).const_mul_atTop
    (by norm_num))

/-- **Theorem 4.1(2)**: `s_j → 0`. -/
theorem tendsto_singular {T : ℝ} (hT : 0 ≤ T) : Tendsto (P.singular D T) atTop (𝓝 0) := by
  have h := ((tendsto_zpow_mul_crowdWidth P.hc P.hK ((D.degree + D.order : ℕ) - 1 : ℤ)).comp
    P.tendsto_base).const_mul (Real.sqrt T * familyConst D)
  rw [mul_zero] at h
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) h
  have := P.singular_le D hT j
  simp only [Function.comp_apply, η] at this ⊢
  linarith

end CrowdedPairs

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
