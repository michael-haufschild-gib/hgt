import GaloisForLFunctions.HTGeometry.PrimeShiftResponseProperness

/-!
# Diagonal response histories with distinct arithmetic endpoints

A family of bounded continuous scalar histories `w_i : ℝ → ℝ`, `|w_i| ≤ 1`, attached to pairwise
distinct endpoints `e_{n_i}` of `ℓ²(ℕ≥1)`, defines the response
`(R c)(t) = ∑_i c_i w_i(t) e_{n_i}` from `ℓ²(ι)` into `L²((0,T]; ℓ²(ℕ≥1))`.  Distinct endpoints
make the energy diagonal: `‖R c‖² = ∑_i E_i |c_i|²` with `E_i = ∫₀ᵀ w_i²`.  Uniform bounds
`m ≤ E_i ≤ M` give the frame inequality `m ‖c‖² ≤ ‖R c‖² ≤ M ‖c‖²`; for `m > 0` the response is
injective with closed range, its Gram is `diag(E_i)`, and the inverse cost of `y = R c` is
`∑_i |⟨ψ_i, y⟩|²/E_i` in the orthonormal carrier `ψ_i = E_i^{-1/2} w_i e_{n_i}`.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory Set Filter Topology HTGeometry RHTower

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-- A diagonal family of response histories `t ↦ w_i(t) e_{n_i}` with distinct endpoints. -/
structure HistoryFamily (ι : Type*) where
  /-- The endpoints `n_i`. -/
  endpoint : ι → ℕ+
  endpoint_injective : Function.Injective endpoint
  /-- The scalar histories `w_i`. -/
  weight : ι → ℝ → ℝ
  continuous_weight : ∀ i, Continuous (weight i)
  abs_weight_le : ∀ i t, |weight i t| ≤ 1

namespace HistoryFamily

variable {ι : Type*} [DecidableEq ι] (F : HistoryFamily ι)

/-- The control space `ℓ²(ι)`. -/
abbrev Controls (ι : Type*) : Type _ := lp (fun _ : ι => ℂ) 2

/-- The endpoint embedding `δ_i ↦ e_{n_i}`. -/
def embed : Controls ι →L[ℂ] ArithSpace :=
  (lpScalarInjection F.endpoint F.endpoint_injective).toContinuousLinearMap

theorem norm_embed (x : Controls ι) : ‖F.embed x‖ = ‖x‖ :=
  (lpScalarInjection F.endpoint F.endpoint_injective).norm_map x

theorem inner_embed (x y : Controls ι) : ⟪F.embed x, F.embed y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (lpScalarInjection F.endpoint F.endpoint_injective).inner_map_map x y

theorem embed_single (i : ι) (a : ℂ) : F.embed (lp.single 2 i a) = a • basisVec (F.endpoint i) := by
  rw [embed, LinearIsometry.coe_toContinuousLinearMap, lpScalarInjection_single, basisVec,
    ← lp.single_smul, smul_eq_mul, mul_one]

theorem inner_basisVec_embed (i : ι) (x : Controls ι) :
    ⟪basisVec (F.endpoint i), F.embed x⟫_ℂ = x i := by
  rw [basisVec, lp.inner_single_left, embed, LinearIsometry.coe_toContinuousLinearMap,
    lpScalarInjection_coordinate]
  simp

omit [DecidableEq ι] in
theorem norm_weight_le (t : ℝ) (i : ι) : ‖(F.weight i t : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact F.abs_weight_le i t

/-- The diagonal weight operator at time `t`. -/
def weightDiag (t : ℝ) : Controls ι →L[ℂ] Controls ι :=
  ellTwoDiagonal (fun i => (F.weight i t : ℂ)) (F.norm_weight_le t)

/-- The response history `t ↦ ∑_i c_i w_i(t) e_{n_i}`. -/
def profile (c : Controls ι) (t : ℝ) : ArithSpace := F.embed (F.weightDiag t c)

theorem norm_profile_le (c : Controls ι) (t : ℝ) : ‖F.profile c t‖ ≤ ‖c‖ := by
  rw [profile, norm_embed]
  exact ((F.weightDiag t).le_opNorm c).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_ellTwoDiagonal_le _ _ zero_le_one))

theorem profile_sub (c d : Controls ι) (t : ℝ) :
    F.profile (c - d) t = F.profile c t - F.profile d t := by
  simp [profile, map_sub]

theorem profile_add (c d : Controls ι) : F.profile (c + d) = F.profile c + F.profile d :=
  funext fun t => by simp [profile, map_add]

theorem profile_smul (a : ℂ) (c : Controls ι) : F.profile (a • c) = a • F.profile c :=
  funext fun t => by simp [profile, map_smul]

theorem weightDiag_single (t : ℝ) (i : ι) (a : ℂ) :
    F.weightDiag t (lp.single 2 i a) = lp.single 2 i ((F.weight i t : ℂ) * a) := by
  ext j
  simp only [weightDiag, ellTwoDiagonal_apply, lp.single_apply]
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

theorem profile_single (i : ι) (a : ℂ) (t : ℝ) :
    F.profile (lp.single 2 i a) t = ((F.weight i t : ℂ) * a) • basisVec (F.endpoint i) := by
  rw [profile, weightDiag_single, embed_single]

theorem continuous_profile (c : Controls ι) : Continuous (F.profile c) := by
  set G : Finset ι → ℝ → ArithSpace := fun s => F.profile (∑ i ∈ s, lp.single 2 i (c i))
  have hcG : ∀ s, Continuous (G s) := fun s => by
    have hG : G s = fun t => ∑ i ∈ s, ((F.weight i t : ℂ) * c i) • basisVec (F.endpoint i) := by
      funext t
      simp only [G, profile, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← profile, profile_single]
    rw [hG]
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((Complex.continuous_ofReal.comp (F.continuous_weight i)).mul continuous_const).smul
      continuous_const
  have hsum := lp.hasSum_single (E := fun _ : ι => ℂ) (p := 2) (by norm_num) c
  have hunif : TendstoUniformly G (F.profile c) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h := (Metric.tendsto_nhds.mp hsum) ε hε
    filter_upwards [h] with s hs t
    rw [dist_eq_norm, ← profile_sub]
    exact (F.norm_profile_le _ t).trans_lt (by rwa [dist_eq_norm, norm_sub_rev] at hs)
  exact hunif.continuous (Frequently.of_forall hcG)

theorem inner_profile (c d : Controls ι) (t : ℝ) :
    ⟪F.profile c t, F.profile d t⟫_ℂ =
      ∑' i, ((F.weight i t ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (c i) * d i) := by
  rw [profile, profile, inner_embed, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  simp only [weightDiag, ellTwoDiagonal_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-! ### The response map -/

theorem memLp_profile (T : ℝ) (c : Controls ι) : MemLp (F.profile c) 2 (timeMeasure T) :=
  MemLp.of_bound (F.continuous_profile c).aestronglyMeasurable ‖c‖
    (ae_of_all _ fun t => F.norm_profile_le c t)

/-- The response map as a linear map into `L²`. -/
def responseLin (T : ℝ) : Controls ι →ₗ[ℂ] ResponseSpace T where
  toFun c := (F.memLp_profile T c).toLp
  map_add' c d := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (EventuallyEq.of_eq (F.profile_add c d))
  map_smul' a c := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (EventuallyEq.of_eq (F.profile_smul a c))

theorem coeFn_responseLin (T : ℝ) (c : Controls ι) :
    (F.responseLin T c : ℝ → ArithSpace) =ᵐ[timeMeasure T] F.profile c :=
  (F.memLp_profile T c).coeFn_toLp

/-- The diagonal history response `ℓ²(ι) → L²((0,T]; ℓ²(ℕ≥1))`. -/
def response (T : ℝ) : Controls ι →L[ℂ] ResponseSpace T :=
  LinearMap.mkContinuous (F.responseLin T)
    ((measureUnivNNReal (timeMeasure T) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹) fun c =>
    Lp.norm_le_of_ae_bound (norm_nonneg c)
      ((F.coeFn_responseLin T c).mono fun t ht => by
        rw [ht]; exact F.norm_profile_le c t)

theorem coeFn_response (T : ℝ) (c : Controls ι) :
    (F.response T c : ℝ → ArithSpace) =ᵐ[timeMeasure T] F.profile c :=
  F.coeFn_responseLin T c

/-- The energy `E_i = ∫₀ᵀ w_i(t)² dt` of the `i`-th channel. -/
def energy (T : ℝ) (i : ι) : ℝ := ∫ t in (0 : ℝ)..T, F.weight i t ^ 2

omit [DecidableEq ι] in
theorem energy_nonneg {T : ℝ} (hT : 0 ≤ T) (i : ι) : 0 ≤ F.energy T i :=
  intervalIntegral.integral_nonneg hT fun _ _ => sq_nonneg _

omit [DecidableEq ι] in
theorem energy_le {T : ℝ} (hT : 0 ≤ T) (i : ι) : F.energy T i ≤ T := by
  have h := intervalIntegral.integral_mono_on hT
    (((F.continuous_weight i).pow 2).intervalIntegrable (μ := volume) 0 T)
    (continuous_const.intervalIntegrable (μ := volume) 0 T) fun t _ => by
      have h1 := F.abs_weight_le i t
      show F.weight i t ^ 2 ≤ 1
      nlinarith [abs_nonneg (F.weight i t), sq_abs (F.weight i t)]
  simpa [energy] using h

variable [Countable ι]

/-- `⟨R c, R d⟩ = ∑_i E_i c̄_i d_i`. -/
theorem inner_response {T : ℝ} (hT : 0 ≤ T) (c d : Controls ι) :
    ⟪F.response T c, F.response T d⟫_ℂ =
      ∑' i, (F.energy T i : ℂ) * ((starRingEnd ℂ) (c i) * d i) := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : ∫ t, ⟪(F.response T c : ℝ → ArithSpace) t, (F.response T d : ℝ → ArithSpace) t⟫_ℂ
        ∂(timeMeasure T) = ∫ t, ⟪F.profile c t, F.profile d t⟫_ℂ ∂(timeMeasure T) :=
    integral_congr_ae ((F.coeFn_response T c).mp
      ((F.coeFn_response T d).mono fun t hd hc => by simp only [hc, hd]))
  rw [h1]
  simp_rw [F.inner_profile]
  have hint : ∀ i, Integrable (fun t => ((F.weight i t ^ 2 : ℝ) : ℂ) *
      ((starRingEnd ℂ) (c i) * d i)) (timeMeasure T) := fun i =>
    ((Complex.continuous_ofReal.comp ((F.continuous_weight i).pow 2)).mul
      continuous_const).integrableOn_Ioc
  have hnorm : ∀ i, ∫ t, ‖((F.weight i t ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (c i) * d i)‖
      ∂(timeMeasure T) = F.energy T i * (‖c i‖ * ‖d i‖) := fun i => by
    have he : ∀ t, ‖((F.weight i t ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (c i) * d i)‖ =
        F.weight i t ^ 2 * (‖c i‖ * ‖d i‖) := fun t => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul,
        RCLike.norm_conj]
    simp_rw [he]
    rw [integral_mul_const, energy, intervalIntegral.integral_of_le hT]
  have hsum : Summable fun i => ∫ t, ‖((F.weight i t ^ 2 : ℝ) : ℂ) *
      ((starRingEnd ℂ) (c i) * d i)‖ ∂(timeMeasure T) := by
    simp_rw [hnorm]
    have hcd : Summable fun i => ‖c i‖ * ‖d i‖ := by
      have hc := (lp.memℓp c).summable (p := 2) (by norm_num)
      have hd := (lp.memℓp d).summable (p := 2) (by norm_num)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hc hd
      exact Summable.of_nonneg_of_le (fun _ => by positivity)
        (fun i => by nlinarith [two_mul_le_add_sq ‖c i‖ ‖d i‖, norm_nonneg (c i),
          norm_nonneg (d i)]) (hc.add hd)
    exact Summable.of_nonneg_of_le
      (fun i => mul_nonneg (F.energy_nonneg hT i) (by positivity))
      (fun i => mul_le_mul_of_nonneg_right (F.energy_le hT i) (by positivity))
      (hcd.mul_left T)
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun i => ?_
  rw [integral_mul_const, integral_complex_ofReal, energy, intervalIntegral.integral_of_le hT]

/-- **The energy identity** `‖R c‖² = ∑_i E_i |c_i|²`. -/
theorem norm_response_sq {T : ℝ} (hT : 0 ≤ T) (c : Controls ι) :
    ‖F.response T c‖ ^ 2 = ∑' i, F.energy T i * ‖c i‖ ^ 2 := by
  have h := F.inner_response hT c c
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ∀ i, (F.energy T i : ℂ) * ((starRingEnd ℂ) (c i) * c i) =
      ((F.energy T i * ‖c i‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [Complex.conj_mul']
    push_cast
    ring
  simp_rw [h2] at h
  rw [← Complex.ofReal_tsum] at h
  have h3 := congrArg Complex.re h
  simpa [← Complex.ofReal_pow] using h3

omit [DecidableEq ι] [Countable ι] in
theorem lp_norm_sq (c : Controls ι) : ‖c‖ ^ 2 = ∑' i, ‖c i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) c
  simpa using h

omit [DecidableEq ι] [Countable ι] in
theorem summable_norm_sq (c : Controls ι) : Summable fun i => ‖c i‖ ^ 2 := by
  have h := (lp.memℓp c).summable (p := 2) (by norm_num)
  simpa using h

/-- **The frame inequality** from uniform channel energies `m ≤ E_i ≤ M`. -/
theorem frame_bounds {T : ℝ} (hT : 0 ≤ T) {m M : ℝ} (hm : ∀ i, m ≤ F.energy T i)
    (hM : ∀ i, F.energy T i ≤ M) (c : Controls ι) :
    m * ‖c‖ ^ 2 ≤ ‖F.response T c‖ ^ 2 ∧ ‖F.response T c‖ ^ 2 ≤ M * ‖c‖ ^ 2 := by
  have hsum : Summable fun i => F.energy T i * ‖c i‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (F.energy_nonneg hT i) (by positivity))
      (fun i => mul_le_mul_of_nonneg_right (F.energy_le hT i) (by positivity))
      ((summable_norm_sq c).mul_left T)
  rw [F.norm_response_sq hT, lp_norm_sq, ← tsum_mul_left, ← tsum_mul_left]
  exact ⟨Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_right (hm i) (by positivity))
      ((summable_norm_sq c).mul_left _) hsum,
    Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_right (hM i) (by positivity)) hsum
      ((summable_norm_sq c).mul_left _)⟩

/-- A positive lower frame bound gives `√m ‖c‖ ≤ ‖R c‖`. -/
theorem sqrt_mul_le {T : ℝ} (hT : 0 ≤ T) {m : ℝ} (hm0 : 0 ≤ m) (hm : ∀ i, m ≤ F.energy T i)
    (c : Controls ι) : Real.sqrt m * ‖c‖ ≤ ‖F.response T c‖ := by
  have h := (F.frame_bounds hT hm (M := T) (fun i => F.energy_le hT i) c).1
  rw [← Real.sq_sqrt hm0, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h

theorem response_injective {T : ℝ} (hT : 0 ≤ T) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ i, m ≤ F.energy T i) : Function.Injective (F.response T) := by
  intro c d hcd
  have h := F.sqrt_mul_le hT hm0.le hm (c - d)
  rw [map_sub, hcd, sub_self, norm_zero] at h
  have hs := Real.sqrt_pos.mpr hm0
  have : ‖c - d‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (c - d)]) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem isClosed_range_response {T : ℝ} (hT : 0 ≤ T) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ i, m ≤ F.energy T i) : IsClosed (Set.range (F.response T)) := by
  have hs := Real.sqrt_pos.mpr hm0
  have hanti : AntilipschitzWith (Real.toNNReal (Real.sqrt m)⁻¹) (F.response T) :=
    (F.response T).antilipschitz_of_bound fun c => by
      rw [Real.coe_toNNReal _ (inv_nonneg.mpr hs.le), inv_mul_eq_div, le_div_iff₀ hs, mul_comm]
      exact F.sqrt_mul_le hT hm0.le hm c
  exact hanti.isClosed_range (F.response T).uniformContinuous

theorem norm_le_inv_mul_response {T : ℝ} (hT : 0 ≤ T) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ i, m ≤ F.energy T i) (c : Controls ι) :
    ‖c‖ ≤ (Real.sqrt m)⁻¹ * ‖F.response T c‖ := by
  have hs := Real.sqrt_pos.mpr hm0
  rw [inv_mul_eq_div, le_div_iff₀ hs, mul_comm]
  exact F.sqrt_mul_le hT hm0.le hm c

/-- **The response Gram is diagonal**: `R* R = diag(E_i)`. -/
theorem gram_response {T : ℝ} (hT : 0 ≤ T) :
    ContinuousLinearMap.adjoint (F.response T) ∘L F.response T =
      ellTwoDiagonal (fun i => (F.energy T i : ℂ)) (C := T) fun i => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (F.energy_nonneg hT i)]
        exact F.energy_le hT i := by
  ext1 c
  refine ext_inner_right ℂ fun d => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    F.inner_response hT, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  simp only [ellTwoDiagonal_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-! ### The carrier and the inverse cost -/

/-- The normalized carrier profile `ψ_i(t) = E_i^{-1/2} w_i(t) e_{n_i}`. -/
def carrierProfile (T : ℝ) (i : ι) (t : ℝ) : ArithSpace :=
  (((Real.sqrt (F.energy T i))⁻¹ * F.weight i t : ℝ) : ℂ) • basisVec (F.endpoint i)

omit [DecidableEq ι] [Countable ι] in
theorem memLp_carrierProfile (T : ℝ) (i : ι) :
    MemLp (F.carrierProfile T i) 2 (timeMeasure T) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable ?_) ((Real.sqrt (F.energy T i))⁻¹)
    (ae_of_all _ fun t => ?_)
  · exact (Complex.continuous_ofReal.comp (continuous_const.mul (F.continuous_weight i))).smul
      continuous_const
  · have hpn : 0 ≤ Real.sqrt (F.energy T i) := Real.sqrt_nonneg _
    rw [carrierProfile, norm_smul, norm_basisVec, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_inv, abs_of_nonneg hpn]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hpn) (F.abs_weight_le i t)

/-- The carrier vectors `ψ_i`. -/
def carrier (T : ℝ) (i : ι) : ResponseSpace T := (F.memLp_carrierProfile T i).toLp

omit [Countable ι] in
theorem inner_basisVec_endpoint (i j : ι) :
    ⟪basisVec (F.endpoint i), basisVec (F.endpoint j)⟫_ℂ = if i = j then 1 else 0 := by
  rw [orthonormal_iff_ite.mp orthonormal_basisVec]
  by_cases h : i = j
  · simp [h]
  · simp [h, F.endpoint_injective.ne h]

omit [Countable ι] in
/-- **The carrier is orthonormal** when every channel has positive energy. -/
theorem orthonormal_carrier {T : ℝ} (hT : 0 ≤ T) (hE : ∀ i, 0 < F.energy T i) :
    Orthonormal ℂ (F.carrier T) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [MeasureTheory.L2.inner_def]
  have h1 : ∫ t, ⟪(F.carrier T i : ℝ → ArithSpace) t, (F.carrier T j : ℝ → ArithSpace) t⟫_ℂ
        ∂(timeMeasure T) =
      ∫ t, ⟪F.carrierProfile T i t, F.carrierProfile T j t⟫_ℂ ∂(timeMeasure T) :=
    integral_congr_ae (((F.memLp_carrierProfile T i).coeFn_toLp).mp
      (((F.memLp_carrierProfile T j).coeFn_toLp).mono fun t hj hi => by
        simp only [carrier, hi, hj]))
  rw [h1]
  simp only [carrierProfile, inner_smul_left, inner_smul_right, F.inner_basisVec_endpoint,
    Complex.conj_ofReal]
  by_cases hij : i = j
  · subst hij
    simp only [if_true, mul_one]
    have he : ∀ t, ((((Real.sqrt (F.energy T i))⁻¹ * F.weight i t : ℝ) : ℂ) *
        (((Real.sqrt (F.energy T i))⁻¹ * F.weight i t : ℝ) : ℂ)) =
        (((Real.sqrt (F.energy T i))⁻¹ ^ 2 * F.weight i t ^ 2 : ℝ) : ℂ) := fun t => by
      push_cast; ring
    simp_rw [he]
    rw [integral_complex_ofReal, integral_const_mul, ← intervalIntegral.integral_of_le hT,
      ← energy, inv_pow, Real.sq_sqrt (F.energy_nonneg hT i), inv_mul_cancel₀ (hE i).ne']
    simp
  · simp [hij]

omit [Countable ι] in
/-- The carrier coefficients of a response: `⟨ψ_i, R c⟩ = √E_i c_i`. -/
theorem inner_carrier_response {T : ℝ} (hT : 0 ≤ T) (hE : ∀ i, 0 < F.energy T i) (i : ι)
    (c : Controls ι) :
    ⟪F.carrier T i, F.response T c⟫_ℂ = (Real.sqrt (F.energy T i) : ℂ) * c i := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : ∫ t, ⟪(F.carrier T i : ℝ → ArithSpace) t, (F.response T c : ℝ → ArithSpace) t⟫_ℂ
        ∂(timeMeasure T) = ∫ t, ⟪F.carrierProfile T i t, F.profile c t⟫_ℂ ∂(timeMeasure T) :=
    integral_congr_ae (((F.memLp_carrierProfile T i).coeFn_toLp).mp
      ((F.coeFn_response T c).mono fun t hc hi => by simp only [carrier, hi, hc]))
  rw [h1]
  have he : ∀ t, ⟪F.carrierProfile T i t, F.profile c t⟫_ℂ =
      (((Real.sqrt (F.energy T i))⁻¹ * F.weight i t ^ 2 : ℝ) : ℂ) * c i := fun t => by
    rw [carrierProfile, inner_smul_left, profile, F.inner_basisVec_embed, Complex.conj_ofReal]
    simp only [weightDiag, ellTwoDiagonal_apply]
    push_cast
    ring
  simp_rw [he]
  rw [integral_mul_const, integral_complex_ofReal, integral_const_mul,
    ← intervalIntegral.integral_of_le hT, ← energy]
  have hs : Real.sqrt (F.energy T i) ≠ 0 := (Real.sqrt_pos.mpr (hE i)).ne'
  have hsE : (Real.sqrt (F.energy T i))⁻¹ * F.energy T i = Real.sqrt (F.energy T i) := by
    calc (Real.sqrt (F.energy T i))⁻¹ * F.energy T i
        = (Real.sqrt (F.energy T i))⁻¹ * (Real.sqrt (F.energy T i) * Real.sqrt (F.energy T i)) := by
          rw [Real.mul_self_sqrt (F.energy_nonneg hT i)]
      _ = Real.sqrt (F.energy T i) := by field_simp
  rw [hsE]

omit [Countable ι] in
/-- **The inverse response cost** `‖c‖² = ∑_i |⟨ψ_i, R c⟩|²/E_i`. -/
theorem inverseCost {T : ℝ} (hT : 0 ≤ T) (hE : ∀ i, 0 < F.energy T i) (c : Controls ι) :
    ‖c‖ ^ 2 = ∑' i, ‖⟪F.carrier T i, F.response T c⟫_ℂ‖ ^ 2 / F.energy T i := by
  rw [lp_norm_sq]
  refine tsum_congr fun i => ?_
  rw [F.inner_carrier_response hT hE, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (F.energy_nonneg hT i)]
  field_simp [(hE i).ne']

end HistoryFamily

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
