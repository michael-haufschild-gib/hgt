import GaloisForLFunctions.HTGeometry.ArithmeticPrimeShiftSource
import GaloisForLFunctions.HTGeometry.GlobalResponseProperness
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp

/-!
# All-prime Duhamel response: raw nonproperness and commutator-normalized properness

Prime controls `c ∈ ℓ²(ℙ)` drive the vacuum through the one-letter responses:
`(R_T^com c)(t) = ∑_p c_p D̃_p(t) e_1 = -∑_p c_p (1 - p^{-t}) e_p` and
`(R_T^raw c)(t) = ∑_p c_p D_p(t) e_1 = -∑_p c_p (1 - p^{-t})/(log p) e_p` `(APS.9)`, as elements of
`L²([0,T]; ℓ²(ℕ≥1))`.  With `b_p(T)² = ∫₀ᵀ (1 - p^{-t})² dt` `(APS.10)` the energies are diagonal
`(APS.11)`; `b_2(T) ≤ b_p(T) ≤ √T` gives the two-sided bound `(APS.13)` and the closed range of the
normalized map, while `b_p(T)/log p → 0` `(APS.12)` makes the raw map compact, injective and of
dense nonclosed range in the common carrier `𝒴_T = span{ψ_p}`, `ψ_p = b_p⁻¹ (1 - p^{-t}) e_p`.
The response Laplacians are `diag(b_p²/(log p)²)` and `diag(b_p²) ≥ b_2² I` `(APS.15)`, and the
inverse cost on the range is `∑_p |y_p|²/b_p²` `(APS.14)`.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory Set Filter Topology HTGeometry RHTower

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-! ### Prime controls -/

/-- Prime controls `ℓ²(ℙ)`. -/
abbrev PrimeControls : Type := lp (fun _ : Nat.Primes => ℂ) 2

/-- A prime as a positive integer. -/
def primePNat (p : Nat.Primes) : ℕ+ := ⟨p, p.2.pos⟩

theorem primePNat_injective : Function.Injective primePNat := fun _ _ h =>
  Subtype.ext (congrArg PNat.val h)

theorem primePNat_coe (p : Nat.Primes) : ((primePNat p : ℕ) : ℝ) = ((p : ℕ) : ℝ) := rfl

/-- The prime coordinates `ℓ²(ℙ) → ℓ²(ℕ≥1)`, `δ_p ↦ e_p`; its range is the prime subspace
`H_ℙ`. -/
def primeEmbed : PrimeControls →L[ℂ] ArithSpace :=
  (lpScalarInjection primePNat primePNat_injective).toContinuousLinearMap

theorem norm_primeEmbed (x : PrimeControls) : ‖primeEmbed x‖ = ‖x‖ :=
  (lpScalarInjection primePNat primePNat_injective).norm_map x

theorem inner_primeEmbed (x y : PrimeControls) : ⟪primeEmbed x, primeEmbed y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (lpScalarInjection primePNat primePNat_injective).inner_map_map x y

theorem primeEmbed_single (p : Nat.Primes) (c : ℂ) :
    primeEmbed (lp.single 2 p c) = c • basisVec (primePNat p) := by
  rw [primeEmbed, LinearIsometry.coe_toContinuousLinearMap, lpScalarInjection_single, basisVec,
    ← lp.single_smul, smul_eq_mul, mul_one]

/-! ### The response gain -/

/-- The normalized gain `1 - p^{-t⁺}` of the prime letter at time `t`. -/
def gain (t : ℝ) (p : Nat.Primes) : ℝ := 1 - ((p : ℕ) : ℝ) ^ (-max t 0)

theorem gain_of_nonneg {t : ℝ} (ht : 0 ≤ t) (p : Nat.Primes) :
    gain t p = 1 - ((p : ℕ) : ℝ) ^ (-t) := by
  rw [gain, max_eq_left ht]

theorem one_le_prime (p : Nat.Primes) : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
  exact_mod_cast p.2.one_lt.le

theorem gain_nonneg (t : ℝ) (p : Nat.Primes) : 0 ≤ gain t p :=
  sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (one_le_prime p)
    (neg_nonpos.mpr (le_max_right _ _)))

theorem gain_le_one (t : ℝ) (p : Nat.Primes) : gain t p ≤ 1 :=
  sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem norm_neg_gain_le (t : ℝ) (p : Nat.Primes) : ‖(-(gain t p : ℂ))‖ ≤ 1 := by
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gain_nonneg t p)]
  exact gain_le_one t p

theorem gain_mono {p q : Nat.Primes} (hpq : (p : ℕ) ≤ (q : ℕ)) (t : ℝ) : gain t p ≤ gain t q := by
  have h : ((q : ℕ) : ℝ) ^ (-max t 0) ≤ ((p : ℕ) : ℝ) ^ (-max t 0) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [one_le_prime p]) (by exact_mod_cast hpq)
      (neg_nonpos.mpr (le_max_right _ _))
  simp only [gain]
  linarith

theorem continuous_gain (p : Nat.Primes) : Continuous fun t => gain t p := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith [one_le_prime p]
  exact continuous_const.sub (continuous_const.rpow (by fun_prop) fun _ => Or.inl hp.ne')

theorem gain_pos {t : ℝ} (ht : 0 < t) (p : Nat.Primes) : 0 < gain t p := by
  rw [gain_of_nonneg ht.le]
  have h1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  have : ((p : ℕ) : ℝ) ^ (-t) < 1 := Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)
  linarith

/-! ### Response profiles -/

/-- The diagonal gain operator `δ_p ↦ -(1 - p^{-t}) δ_p` on prime controls. -/
def gainDiag (t : ℝ) : PrimeControls →L[ℂ] PrimeControls :=
  ellTwoDiagonal (fun p => -(gain t p : ℂ)) (norm_neg_gain_le t)

/-- The commutator-normalized response history `t ↦ ∑_p c_p D̃_p(t) e_1`. -/
def comProfile (c : PrimeControls) (t : ℝ) : ArithSpace := primeEmbed (gainDiag t c)

theorem norm_comProfile_le (c : PrimeControls) (t : ℝ) : ‖comProfile c t‖ ≤ ‖c‖ := by
  rw [comProfile, norm_primeEmbed]
  exact ((gainDiag t).le_opNorm c).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_ellTwoDiagonal_le _ _ zero_le_one))

theorem comProfile_sub (c d : PrimeControls) (t : ℝ) :
    comProfile (c - d) t = comProfile c t - comProfile d t := by
  simp [comProfile, map_sub]

theorem comProfile_single (p : Nat.Primes) (a : ℂ) (t : ℝ) :
    comProfile (lp.single 2 p a) t = (-(gain t p : ℂ) * a) • basisVec (primePNat p) := by
  have h : gainDiag t (lp.single 2 p a) = lp.single 2 p (-(gain t p : ℂ) * a) := by
    ext q
    simp only [gainDiag, ellTwoDiagonal_apply, lp.single_apply]
    by_cases hq : q = p
    · subst hq; simp
    · simp [hq]
  rw [comProfile, h, primeEmbed_single]

/-- **`(APS.9)` on a single prime**: the profile of `δ_p` is the Duhamel response
`D̃_p(t) e_1`. -/
theorem comProfile_single_eq_duhamel (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) :
    comProfile (lp.single 2 p 1) t = duhamel (letter (primePNat p)) t (basisVec 1) := by
  rw [comProfile_single, duhamel_letter ht (m := primePNat p) p.2.two_le, neg_apply, smul_apply,
    mul_apply_eq_comp, heat_vacuum, shift_vacuum, gain_of_nonneg ht, primePNat_coe, mul_one,
    neg_smul]

theorem continuous_comProfile (c : PrimeControls) : Continuous (comProfile c) := by
  set F : Finset Nat.Primes → ℝ → ArithSpace := fun s => comProfile (∑ p ∈ s, lp.single 2 p (c p))
  have hcF : ∀ s, Continuous (F s) := fun s => by
    have hF : F s = fun t => ∑ p ∈ s, (-(gain t p : ℂ) * c p) • basisVec (primePNat p) := by
      funext t
      simp only [F, comProfile, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← comProfile, comProfile_single]
    rw [hF]
    refine continuous_finsetSum _ fun p _ => ?_
    exact ((Complex.continuous_ofReal.comp (continuous_gain p)).neg.mul continuous_const).smul
      continuous_const
  have hsum := lp.hasSum_single (E := fun _ : Nat.Primes => ℂ) (p := 2) (by norm_num) c
  have hunif : TendstoUniformly F (comProfile c) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h := (Metric.tendsto_nhds.mp hsum) ε hε
    filter_upwards [h] with s hs t
    rw [dist_eq_norm, ← comProfile_sub]
    exact (norm_comProfile_le _ t).trans_lt (by rwa [dist_eq_norm, norm_sub_rev] at hs)
  exact hunif.continuous (Frequently.of_forall hcF)

/-- Pointwise energy: `⟨R c(t), R d(t)⟩ = ∑_p (1 - p^{-t})² c̄_p d_p`. -/
theorem inner_comProfile (c d : PrimeControls) (t : ℝ) :
    ⟪comProfile c t, comProfile d t⟫_ℂ =
      ∑' p, ((gain t p ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (c p) * d p) := by
  rw [comProfile, comProfile, inner_primeEmbed, lp.inner_eq_tsum]
  refine tsum_congr fun p => ?_
  simp only [gainDiag, ellTwoDiagonal_apply, RCLike.inner_apply, map_mul, map_neg,
    Complex.conj_ofReal]
  push_cast
  ring

/-! ### The profile constants -/

/-- `b_p(T)² = ∫₀ᵀ (1 - p^{-t})² dt` `(APS.10)`. -/
def profileSq (T : ℝ) (p : Nat.Primes) : ℝ := ∫ t in (0 : ℝ)..T, gain t p ^ 2

theorem continuous_gain_sq (p : Nat.Primes) : Continuous fun t => gain t p ^ 2 :=
  (continuous_gain p).pow 2

theorem gain_sq_le_one (t : ℝ) (p : Nat.Primes) : gain t p ^ 2 ≤ 1 :=
  pow_le_one₀ (gain_nonneg t p) (gain_le_one t p)

theorem profileSq_nonneg {T : ℝ} (hT : 0 ≤ T) (p : Nat.Primes) : 0 ≤ profileSq T p :=
  intervalIntegral.integral_nonneg hT fun _ _ => sq_nonneg _

theorem profileSq_le {T : ℝ} (hT : 0 ≤ T) (p : Nat.Primes) : profileSq T p ≤ T := by
  have h := intervalIntegral.integral_mono_on hT
    ((continuous_gain_sq p).intervalIntegrable (μ := volume) 0 T)
    (continuous_const.intervalIntegrable (μ := volume) 0 T) fun t _ => gain_sq_le_one t p
  simpa [profileSq] using h

theorem profileSq_mono {T : ℝ} (hT : 0 ≤ T) {p q : Nat.Primes} (hpq : (p : ℕ) ≤ (q : ℕ)) :
    profileSq T p ≤ profileSq T q :=
  intervalIntegral.integral_mono_on hT
    ((continuous_gain_sq p).intervalIntegrable (μ := volume) 0 T)
    ((continuous_gain_sq q).intervalIntegrable (μ := volume) 0 T)
    fun t _ => pow_le_pow_left₀ (gain_nonneg t p) (gain_mono hpq t) 2

theorem profileSq_pos {T : ℝ} (hT : 0 < T) (p : Nat.Primes) : 0 < profileSq T p :=
  intervalIntegral.intervalIntegral_pos_of_pos_on ((continuous_gain_sq p).intervalIntegrable 0 T)
    (fun _ ht => pow_pos (gain_pos ht.1 p) 2) hT

/-- The smallest prime. -/
def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

theorem profileSq_two_le {T : ℝ} (hT : 0 ≤ T) (p : Nat.Primes) :
    profileSq T primeTwo ≤ profileSq T p :=
  profileSq_mono hT p.2.two_le

theorem integral_rpow_neg_mul {m : ℝ} (hm : 1 < m) {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, m ^ (-(a * t)) = (1 - m ^ (-(a * T))) / (a * Real.log m) := by
  have hm0 : 0 < m := by linarith
  have hlog : 0 < Real.log m := Real.log_pos hm
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) T, HasDerivAt (fun t => -(m ^ (-(a * t))) / (a * Real.log m))
      (m ^ (-(a * t))) t := fun t _ => by
    have h := (Real.hasStrictDerivAt_const_rpow hm0 (-(a * t))).hasDerivAt.comp t
      (((hasDerivAt_id t).const_mul a).neg)
    refine (h.neg.div_const (a * Real.log m)).congr_deriv ?_
    field_simp
  have hcont : Continuous fun t : ℝ => m ^ (-(a * t)) :=
    continuous_const.rpow (by fun_prop) fun _ => Or.inl hm0.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.rpow_zero]
  field_simp
  ring

/-- **`(APS.10)`, closed form**:
`b_p(T)² = T - 2(1 - p^{-T})/log p + (1 - p^{-2T})/(2 log p)`. -/
theorem profileSq_eq {T : ℝ} (hT : 0 ≤ T) (p : Nat.Primes) :
    profileSq T p = T - 2 * ((1 - ((p : ℕ) : ℝ) ^ (-T)) / Real.log ((p : ℕ) : ℝ)) +
      (1 - ((p : ℕ) : ℝ) ^ (-(2 * T))) / (2 * Real.log ((p : ℕ) : ℝ)) := by
  have hx : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  have hx0 : 0 < ((p : ℕ) : ℝ) := by linarith
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) T, gain t p ^ 2 =
      1 - 2 * ((p : ℕ) : ℝ) ^ (-(1 * t)) + ((p : ℕ) : ℝ) ^ (-(2 * t)) := fun t ht => by
    rw [uIcc_of_le hT] at ht
    rw [gain_of_nonneg ht.1, one_mul, show -(2 * t) = (-t) * 2 by ring,
      Real.rpow_mul hx0.le, show (((p : ℕ) : ℝ) ^ (-t)) ^ (2 : ℝ) =
        (((p : ℕ) : ℝ) ^ (-t)) ^ (2 : ℕ) from Real.rpow_natCast _ 2]
    ring
  have hc1 : Continuous fun t : ℝ => ((p : ℕ) : ℝ) ^ (-(1 * t)) :=
    continuous_const.rpow (by fun_prop) fun _ => Or.inl hx0.ne'
  have hc2 : Continuous fun t : ℝ => ((p : ℕ) : ℝ) ^ (-(2 * t)) :=
    continuous_const.rpow (by fun_prop) fun _ => Or.inl hx0.ne'
  rw [profileSq, intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_add (f := fun t => 1 - 2 * ((p : ℕ) : ℝ) ^ (-(1 * t)))
      (g := fun t => ((p : ℕ) : ℝ) ^ (-(2 * t)))
      ((continuous_const.sub (continuous_const.mul hc1)).intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f := fun _ => (1 : ℝ))
      (g := fun t => 2 * ((p : ℕ) : ℝ) ^ (-(1 * t)))
      (continuous_const.intervalIntegrable _ _) ((continuous_const.mul hc1).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_rpow_neg_mul hx one_pos,
    integral_rpow_neg_mul hx two_pos]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, one_mul]

/-! ### Square sums of controls -/

theorem summable_norm_sq (c : PrimeControls) : Summable fun p => ‖c p‖ ^ 2 := by
  have h := (lp.memℓp c).summable (p := 2) (by norm_num)
  simpa using h

theorem norm_sq_eq_tsum (c : PrimeControls) : ‖c‖ ^ 2 = ∑' p, ‖c p‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) c
  simpa using h

theorem summable_norm_mul (c d : PrimeControls) : Summable fun p => ‖c p‖ * ‖d p‖ :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun p => by nlinarith [two_mul_le_add_sq ‖c p‖ ‖d p‖, norm_nonneg (c p), norm_nonneg (d p)])
    ((summable_norm_sq c).add (summable_norm_sq d))

/-! ### The commutator-normalized response map -/

/-- Lebesgue measure on the time window `(0, T]`. -/
abbrev timeMeasure (T : ℝ) : Measure ℝ := volume.restrict (Ioc 0 T)

/-- The response space `L²((0,T]; ℓ²(ℕ≥1))`. -/
abbrev ResponseSpace (T : ℝ) : Type := Lp ArithSpace 2 (timeMeasure T)

theorem memLp_comProfile (T : ℝ) (c : PrimeControls) :
    MemLp (comProfile c) 2 (timeMeasure T) :=
  MemLp.of_bound (continuous_comProfile c).aestronglyMeasurable ‖c‖
    (ae_of_all _ fun t => norm_comProfile_le c t)

theorem comProfile_add (c d : PrimeControls) : comProfile (c + d) = comProfile c + comProfile d :=
  funext fun t => by simp [comProfile, map_add]

theorem comProfile_smul (a : ℂ) (c : PrimeControls) : comProfile (a • c) = a • comProfile c :=
  funext fun t => by simp [comProfile, map_smul]

/-- The normalized response map as a linear map into `L²`. -/
def comResponseLin (T : ℝ) : PrimeControls →ₗ[ℂ] ResponseSpace T where
  toFun c := (memLp_comProfile T c).toLp
  map_add' c d := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (EventuallyEq.of_eq (comProfile_add c d))
  map_smul' a c := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (EventuallyEq.of_eq (comProfile_smul a c))

theorem coeFn_comResponseLin (T : ℝ) (c : PrimeControls) :
    (comResponseLin T c : ℝ → ArithSpace) =ᵐ[timeMeasure T] comProfile c :=
  (memLp_comProfile T c).coeFn_toLp

/-- **`(APS.9)`, `(APS.11)`: the commutator-normalized all-prime response
`ℓ²(ℙ) → L²((0,T]; ℓ²(ℕ≥1))`. -/
def comResponse (T : ℝ) : PrimeControls →L[ℂ] ResponseSpace T :=
  LinearMap.mkContinuous (comResponseLin T)
    ((measureUnivNNReal (timeMeasure T) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹) fun c =>
    Lp.norm_le_of_ae_bound (norm_nonneg c)
      ((coeFn_comResponseLin T c).mono fun t ht => by rw [ht]; exact norm_comProfile_le c t)

theorem comResponse_apply (T : ℝ) (c : PrimeControls) : comResponse T c = comResponseLin T c :=
  rfl

theorem coeFn_comResponse (T : ℝ) (c : PrimeControls) :
    (comResponse T c : ℝ → ArithSpace) =ᵐ[timeMeasure T] comProfile c :=
  coeFn_comResponseLin T c

/-- `⟨R c, R d⟩ = ∑_p b_p(T)² c̄_p d_p`. -/
theorem inner_comResponse {T : ℝ} (hT : 0 ≤ T) (c d : PrimeControls) :
    ⟪comResponse T c, comResponse T d⟫_ℂ =
      ∑' p, (profileSq T p : ℂ) * ((starRingEnd ℂ) (c p) * d p) := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : ∫ t, ⟪(comResponse T c : ℝ → ArithSpace) t, (comResponse T d : ℝ → ArithSpace) t⟫_ℂ
        ∂(timeMeasure T) = ∫ t, ⟪comProfile c t, comProfile d t⟫_ℂ ∂(timeMeasure T) :=
    integral_congr_ae ((coeFn_comResponse T c).mp
      ((coeFn_comResponse T d).mono fun t hd hc => by simp only [hc, hd]))
  rw [h1]
  simp_rw [inner_comProfile]
  have hint : ∀ p, Integrable (fun t => ((gain t p ^ 2 : ℝ) : ℂ) *
      ((starRingEnd ℂ) (c p) * d p)) (timeMeasure T) := fun p =>
    ((Complex.continuous_ofReal.comp (continuous_gain_sq p)).mul continuous_const).integrableOn_Ioc
  have hnorm : ∀ p, ∫ t, ‖((gain t p ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (c p) * d p)‖
      ∂(timeMeasure T) = profileSq T p * (‖c p‖ * ‖d p‖) := fun p => by
    have he : ∀ t, ‖((gain t p ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (c p) * d p)‖ =
        gain t p ^ 2 * (‖c p‖ * ‖d p‖) := fun t => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul,
        RCLike.norm_conj]
    simp_rw [he]
    rw [integral_mul_const, profileSq, intervalIntegral.integral_of_le hT]
  have hsum : Summable fun p => ∫ t, ‖((gain t p ^ 2 : ℝ) : ℂ) *
      ((starRingEnd ℂ) (c p) * d p)‖ ∂(timeMeasure T) := by
    simp_rw [hnorm]
    exact Summable.of_nonneg_of_le
      (fun p => mul_nonneg (profileSq_nonneg hT p) (by positivity))
      (fun p => mul_le_mul_of_nonneg_right (profileSq_le hT p) (by positivity))
      ((summable_norm_mul c d).mul_left T)
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun p => ?_
  rw [integral_mul_const, integral_complex_ofReal, profileSq, intervalIntegral.integral_of_le hT]

/-- **`(APS.11)`, normalized energy**: `‖R^com c‖² = ∑_p b_p(T)² |c_p|²`. -/
theorem norm_comResponse_sq {T : ℝ} (hT : 0 ≤ T) (c : PrimeControls) :
    ‖comResponse T c‖ ^ 2 = ∑' p, profileSq T p * ‖c p‖ ^ 2 := by
  have h := inner_comResponse hT c c
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ∀ p, (profileSq T p : ℂ) * ((starRingEnd ℂ) (c p) * c p) =
      ((profileSq T p * ‖c p‖ ^ 2 : ℝ) : ℂ) := fun p => by
    rw [Complex.conj_mul']
    push_cast
    ring
  simp_rw [h2] at h
  rw [← Complex.ofReal_tsum] at h
  have h3 := congrArg Complex.re h
  simpa [← Complex.ofReal_pow] using h3

theorem summable_profile_mul (hT : 0 ≤ T) (c : PrimeControls) :
    Summable fun p => profileSq T p * ‖c p‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun p => mul_nonneg (profileSq_nonneg hT p) (by positivity))
    (fun p => mul_le_mul_of_nonneg_right (profileSq_le hT p) (by positivity))
    ((summable_norm_sq c).mul_left T)

/-- **`(APS.13)`, lower bound**: `b_2(T)² ‖c‖² ≤ ‖R^com c‖²`. -/
theorem lower_bound_comResponse {T : ℝ} (hT : 0 ≤ T) (c : PrimeControls) :
    profileSq T primeTwo * ‖c‖ ^ 2 ≤ ‖comResponse T c‖ ^ 2 := by
  rw [norm_comResponse_sq hT, norm_sq_eq_tsum, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun p => mul_le_mul_of_nonneg_right (profileSq_two_le hT p)
    (by positivity)) ((summable_norm_sq c).mul_left _) (summable_profile_mul hT c)

/-- **`(APS.13)`, upper bound**: `‖R^com c‖² ≤ T ‖c‖²`. -/
theorem upper_bound_comResponse {T : ℝ} (hT : 0 ≤ T) (c : PrimeControls) :
    ‖comResponse T c‖ ^ 2 ≤ T * ‖c‖ ^ 2 := by
  rw [norm_comResponse_sq hT, norm_sq_eq_tsum, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun p => mul_le_mul_of_nonneg_right (profileSq_le hT p)
    (by positivity)) (summable_profile_mul hT c) ((summable_norm_sq c).mul_left _)

/-! ### Closed range of the normalized response -/

/-- The profile norm `b_p(T)`. -/
def profile (T : ℝ) (p : Nat.Primes) : ℝ := Real.sqrt (profileSq T p)

theorem profile_pos {T : ℝ} (hT : 0 < T) (p : Nat.Primes) : 0 < profile T p :=
  Real.sqrt_pos.mpr (profileSq_pos hT p)

theorem profile_sq {T : ℝ} (hT : 0 ≤ T) (p : Nat.Primes) : profile T p ^ 2 = profileSq T p :=
  Real.sq_sqrt (profileSq_nonneg hT p)

/-- `b_2(T) ‖c‖ ≤ ‖R^com c‖`. -/
theorem profile_two_mul_le {T : ℝ} (hT : 0 ≤ T) (c : PrimeControls) :
    profile T primeTwo * ‖c‖ ≤ ‖comResponse T c‖ := by
  have h := lower_bound_comResponse hT c
  rw [← profile_sq hT, ← mul_pow] at h
  exact pow_le_pow_left₀ (by positivity) h 2 |> fun _ =>
    (pow_le_pow_iff_left₀ (by unfold profile; positivity) (norm_nonneg _) two_ne_zero).mp h

theorem comResponse_injective {T : ℝ} (hT : 0 < T) : Function.Injective (comResponse T) := by
  intro c d hcd
  have h := profile_two_mul_le hT.le (c - d)
  rw [map_sub, hcd, sub_self, norm_zero] at h
  have hb := profile_pos hT primeTwo
  have : ‖c - d‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (c - d)]) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- **Normalized phase: closed range.** -/
theorem isClosed_range_comResponse {T : ℝ} (hT : 0 < T) : IsClosed (Set.range (comResponse T)) := by
  have hb := profile_pos hT primeTwo
  have hanti : AntilipschitzWith (Real.toNNReal (profile T primeTwo)⁻¹) (comResponse T) :=
    (comResponse T).antilipschitz_of_bound fun c => by
      rw [Real.coe_toNNReal _ (inv_nonneg.mpr hb.le), inv_mul_eq_div, le_div_iff₀ hb, mul_comm]
      exact profile_two_mul_le hT.le c
  exact hanti.isClosed_range (comResponse T).uniformContinuous

/-! ### The response carrier -/

theorem inner_basisVec_primeEmbed (p : Nat.Primes) (x : PrimeControls) :
    ⟪basisVec (primePNat p), primeEmbed x⟫_ℂ = x p := by
  rw [basisVec, lp.inner_single_left, primeEmbed, LinearIsometry.coe_toContinuousLinearMap,
    lpScalarInjection_coordinate]
  simp

/-- The carrier profile `ψ_p(t) = b_p⁻¹ (1 - p^{-t}) e_p`. -/
def carrierProfile (T : ℝ) (p : Nat.Primes) (t : ℝ) : ArithSpace :=
  (((profile T p)⁻¹ * gain t p : ℝ) : ℂ) • basisVec (primePNat p)

theorem memLp_carrierProfile (T : ℝ) (p : Nat.Primes) :
    MemLp (carrierProfile T p) 2 (timeMeasure T) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable ?_) ((profile T p)⁻¹) (ae_of_all _ ?_)
  · exact (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_gain p))).smul
      continuous_const
  · intro t
    have hpn : 0 ≤ profile T p := Real.sqrt_nonneg _
    rw [carrierProfile, norm_smul, norm_basisVec, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_inv, abs_of_nonneg hpn, abs_of_nonneg (gain_nonneg t p)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hpn) (gain_le_one t p)

/-- The orthonormal carrier vectors `ψ_p ∈ L²((0,T]; ℓ²(ℕ≥1))`. -/
def carrier (T : ℝ) (p : Nat.Primes) : ResponseSpace T := (memLp_carrierProfile T p).toLp

theorem inner_basisVec_primePNat (p q : Nat.Primes) :
    ⟪basisVec (primePNat p), basisVec (primePNat q)⟫_ℂ = if p = q then 1 else 0 := by
  rw [orthonormal_iff_ite.mp orthonormal_basisVec]
  by_cases h : p = q
  · simp [h]
  · simp [h, primePNat_injective.ne h]

/-- **The carrier is orthonormal.** -/
theorem orthonormal_carrier {T : ℝ} (hT : 0 < T) : Orthonormal ℂ (carrier T) := by
  rw [orthonormal_iff_ite]
  intro p q
  rw [MeasureTheory.L2.inner_def]
  have h1 : ∫ t, ⟪(carrier T p : ℝ → ArithSpace) t, (carrier T q : ℝ → ArithSpace) t⟫_ℂ
        ∂(timeMeasure T) = ∫ t, ⟪carrierProfile T p t, carrierProfile T q t⟫_ℂ ∂(timeMeasure T) :=
    integral_congr_ae (((memLp_carrierProfile T p).coeFn_toLp).mp
      (((memLp_carrierProfile T q).coeFn_toLp).mono fun t hq hp => by simp only [carrier, hp, hq]))
  rw [h1]
  simp only [carrierProfile, inner_smul_left, inner_smul_right, inner_basisVec_primePNat,
    Complex.conj_ofReal]
  by_cases hpq : p = q
  · subst hpq
    simp only [if_true, mul_one]
    have he : ∀ t, ((((profile T p)⁻¹ * gain t p : ℝ) : ℂ) * (((profile T p)⁻¹ * gain t p : ℝ) : ℂ))
        = (((profile T p)⁻¹ ^ 2 * gain t p ^ 2 : ℝ) : ℂ) := fun t => by push_cast; ring
    simp_rw [he]
    rw [integral_complex_ofReal, integral_const_mul, ← intervalIntegral.integral_of_le hT.le,
      ← profileSq, ← profile_sq hT.le, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 (profile_pos hT p).ne')]
    simp
  · simp [hpq]

/-- The carrier coefficients of a response: `⟨ψ_p, R^com c⟩ = -b_p c_p`. -/
theorem inner_carrier_comResponse {T : ℝ} (hT : 0 < T) (p : Nat.Primes) (c : PrimeControls) :
    ⟪carrier T p, comResponse T c⟫_ℂ = -(profile T p : ℂ) * c p := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : ∫ t, ⟪(carrier T p : ℝ → ArithSpace) t, (comResponse T c : ℝ → ArithSpace) t⟫_ℂ
        ∂(timeMeasure T) = ∫ t, ⟪carrierProfile T p t, comProfile c t⟫_ℂ ∂(timeMeasure T) :=
    integral_congr_ae (((memLp_carrierProfile T p).coeFn_toLp).mp
      ((coeFn_comResponse T c).mono fun t hc hp => by simp only [carrier, hp, hc]))
  rw [h1]
  have he : ∀ t, ⟪carrierProfile T p t, comProfile c t⟫_ℂ =
      (((profile T p)⁻¹ * gain t p ^ 2 : ℝ) : ℂ) * (-(c p)) := fun t => by
    rw [carrierProfile, inner_smul_left, comProfile, inner_basisVec_primeEmbed, Complex.conj_ofReal]
    simp only [gainDiag, ellTwoDiagonal_apply]
    push_cast
    ring
  simp_rw [he]
  rw [integral_mul_const, integral_complex_ofReal, integral_const_mul,
    ← intervalIntegral.integral_of_le hT.le, ← profileSq, ← profile_sq hT.le]
  have hb := (profile_pos hT p).ne'
  push_cast
  field_simp

/-- `R^com δ_p = -b_p ψ_p`. -/
theorem comResponse_single {T : ℝ} (hT : 0 < T) (p : Nat.Primes) :
    comResponse T (lp.single 2 p 1) = (-(profile T p : ℂ)) • carrier T p := by
  rw [comResponse_apply, comResponseLin, LinearMap.coe_mk, AddHom.coe_mk, carrier,
    ← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ (EventuallyEq.of_eq (funext fun t => ?_))
  rw [comProfile_single, Pi.smul_apply, carrierProfile, smul_smul]
  congr 1
  have hb : (profile T p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (profile_pos hT p).ne'
  push_cast
  rw [mul_one, ← mul_assoc, neg_mul, mul_inv_cancel₀ hb, neg_one_mul]

theorem single_eq_smul (p : Nat.Primes) (a : ℂ) :
    (lp.single 2 p a : PrimeControls) = a • (lp.single 2 p (1 : ℂ) : PrimeControls) := by
  rw [← lp.single_smul, smul_eq_mul, mul_one]

theorem comResponse_single_smul {T : ℝ} (hT : 0 < T) (p : Nat.Primes) (a : ℂ) :
    comResponse T (lp.single 2 p a) = (a * -(profile T p : ℂ)) • carrier T p := by
  have h1 : comResponse T (lp.single 2 p a) =
      a • comResponse T (lp.single 2 p (1 : ℂ) : PrimeControls) := by
    rw [single_eq_smul p a]
    exact (comResponse T).map_smul a _
  rw [h1, comResponse_single hT, smul_smul]

/-- The response carrier `𝒴_T`, the closed span of the `ψ_p`. -/
def carrierSpace (T : ℝ) : Submodule ℂ (ResponseSpace T) :=
  (Submodule.span ℂ (Set.range (carrier T))).topologicalClosure

theorem comResponse_mem_carrierSpace {T : ℝ} (hT : 0 < T) (c : PrimeControls) :
    comResponse T c ∈ carrierSpace T := by
  have hsum := (lp.hasSum_single (E := fun _ : Nat.Primes => ℂ) (p := 2) (by norm_num) c).mapL
    (comResponse T)
  refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hsum
    (Eventually.of_forall fun s => ?_)
  refine Submodule.le_topologicalClosure _ (Submodule.sum_mem _ fun p _ => ?_)
  rw [comResponse_single_smul hT p (c p)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

theorem carrier_mem_range {T : ℝ} (hT : 0 < T) (p : Nat.Primes) :
    carrier T p = comResponse T (lp.single 2 p (-(profile T p : ℂ))⁻¹) := by
  have hb : (-(profile T p : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (profile_pos hT p).ne')
  rw [comResponse_single_smul hT, ← neg_inv, neg_mul_neg, inv_mul_cancel₀ (neg_ne_zero.mp hb),
    one_smul]

/-- **The normalized response fills the carrier exactly**: `ran R^com = 𝒴_T`. -/
theorem range_comResponse {T : ℝ} (hT : 0 < T) :
    LinearMap.range (comResponse T : PrimeControls →ₗ[ℂ] ResponseSpace T) = carrierSpace T := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    exact comResponse_mem_carrierSpace hT c
  · refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact ⟨_, (carrier_mem_range hT p).symm⟩
    · rw [LinearMap.coe_range]
      exact isClosed_range_comResponse hT

/-- **`(APS.14)`: the inverse response cost** `‖c‖² = ∑_p |⟨ψ_p, y⟩|²/b_p²` on `y = R^com c`. -/
theorem inverseCost_comResponse {T : ℝ} (hT : 0 < T) (c : PrimeControls) :
    ‖c‖ ^ 2 = ∑' p, ‖⟪carrier T p, comResponse T c⟫_ℂ‖ ^ 2 / profileSq T p := by
  rw [norm_sq_eq_tsum]
  refine tsum_congr fun p => ?_
  rw [inner_carrier_comResponse hT, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (profile_pos hT p), mul_pow, profile_sq hT.le]
  field_simp [(profileSq_pos hT p).ne']

/-- The inverse cost is bounded by `b_2(T)⁻¹`. -/
theorem norm_le_comResponse {T : ℝ} (hT : 0 < T) (c : PrimeControls) :
    ‖c‖ ≤ (profile T primeTwo)⁻¹ * ‖comResponse T c‖ := by
  rw [inv_mul_eq_div, le_div_iff₀ (profile_pos hT primeTwo), mul_comm]
  exact profile_two_mul_le hT.le c

/-- **`(APS.15)`: the normalized response Laplacian** `Q^com = diag(b_p(T)²)`. -/
theorem comLaplacian {T : ℝ} (hT : 0 ≤ T) :
    ContinuousLinearMap.adjoint (comResponse T) ∘L comResponse T =
      ellTwoDiagonal (fun p => (profileSq T p : ℂ)) (C := T) fun p => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (profileSq_nonneg hT p)]
        exact profileSq_le hT p := by
  ext1 c
  refine ext_inner_right ℂ fun d => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    inner_comResponse hT, lp.inner_eq_tsum]
  refine tsum_congr fun p => ?_
  simp only [ellTwoDiagonal_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- `(APS.15)`: `Q^com ≥ b_2(T)² I`. -/
theorem comLaplacian_ge {T : ℝ} (hT : 0 ≤ T) (c : PrimeControls) :
    profileSq T primeTwo * ‖c‖ ^ 2 ≤
      RCLike.re ⟪(ContinuousLinearMap.adjoint (comResponse T) ∘L comResponse T) c, c⟫_ℂ := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq]
  exact lower_bound_comResponse hT c

/-! ### The raw response -/

theorem log_prime_pos (p : Nat.Primes) : 0 < Real.log ((p : ℕ) : ℝ) :=
  Real.log_pos (by exact_mod_cast p.2.one_lt)

/-- The raw letter weight `1/log p`. -/
def logWeight (p : Nat.Primes) : ℂ := ((Real.log ((p : ℕ) : ℝ))⁻¹ : ℝ)

theorem norm_logWeight (p : Nat.Primes) : ‖logWeight p‖ = (Real.log ((p : ℕ) : ℝ))⁻¹ := by
  rw [logWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (log_prime_pos p))]

theorem norm_logWeight_le (p : Nat.Primes) : ‖logWeight p‖ ≤ 2 := by
  rw [norm_logWeight]
  have h2 : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
  have h3 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  calc (Real.log ((p : ℕ) : ℝ))⁻¹ ≤ (Real.log 2)⁻¹ :=
        inv_anti₀ (by linarith) h2
    _ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith

/-- The raw letter normalization `δ_p ↦ (log p)⁻¹ δ_p`. -/
def logDiag : PrimeControls →L[ℂ] PrimeControls :=
  LpDiagonal.lpDiag logWeight 2 (by norm_num) norm_logWeight_le

theorem logDiag_apply (c : PrimeControls) (p : Nat.Primes) : logDiag c p = logWeight p * c p :=
  rfl

/-- **`(APS.9)`, raw**: the raw all-prime response `R^raw = R^com ∘ diag((log p)⁻¹)`. -/
def rawResponse (T : ℝ) : PrimeControls →L[ℂ] ResponseSpace T := comResponse T ∘L logDiag

/-- The raw profile of `δ_p` is the Duhamel response `D_p(t) e_1`. -/
theorem comProfile_logDiag_single_eq_duhamel (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) :
    comProfile (logDiag (lp.single 2 p 1)) t = duhamel (shift (primePNat p)) t (basisVec 1) := by
  have h : logDiag (lp.single 2 p 1) = lp.single 2 p (logWeight p) := by
    ext q
    rw [logDiag_apply, lp.single_apply, lp.single_apply]
    by_cases hq : q = p
    · subst hq; simp
    · simp [hq]
  rw [h, comProfile_single, duhamel_shift ht (m := primePNat p) p.2.two_le, neg_apply, smul_apply,
    mul_apply_eq_comp, heat_vacuum, shift_vacuum, gain_of_nonneg ht, primePNat_coe, logWeight,
    ← neg_smul]
  congr 1
  push_cast
  ring

/-- **`(APS.11)`, raw energy**: `‖R^raw c‖² = ∑_p b_p(T)²/(log p)² |c_p|²`. -/
theorem norm_rawResponse_sq {T : ℝ} (hT : 0 ≤ T) (c : PrimeControls) :
    ‖rawResponse T c‖ ^ 2 =
      ∑' p, profileSq T p / Real.log ((p : ℕ) : ℝ) ^ 2 * ‖c p‖ ^ 2 := by
  rw [rawResponse, ContinuousLinearMap.comp_apply, norm_comResponse_sq hT]
  refine tsum_congr fun p => ?_
  rw [logDiag_apply, norm_mul, norm_logWeight, mul_pow, inv_pow]
  ring

theorem logDiag_injective : Function.Injective logDiag := by
  intro c d h
  ext p
  have hp := congrArg (fun x : PrimeControls => x p) h
  simp only [logDiag_apply] at hp
  have hw : logWeight p ≠ 0 := by
    rw [logWeight, Complex.ofReal_ne_zero]
    exact (inv_pos.mpr (log_prime_pos p)).ne'
  exact mul_left_cancel₀ hw hp

/-- **Raw phase: injective.** -/
theorem rawResponse_injective {T : ℝ} (hT : 0 < T) : Function.Injective (rawResponse T) :=
  (comResponse_injective hT).comp logDiag_injective

theorem tendsto_log_prime :
    Tendsto (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ)) cofinite atTop := by
  have h1 : Tendsto (fun p : Nat.Primes => (p : ℕ)) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact Subtype.val_injective.tendsto_cofinite
  exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp h1)

/-- **Raw phase: compact.** -/
theorem isCompactOperator_rawResponse (T : ℝ) : IsCompactOperator (rawResponse T) := by
  have hlim : Tendsto (fun p => ‖logWeight p‖) cofinite (𝓝 0) := by
    simp_rw [norm_logWeight]
    exact tendsto_inv_atTop_zero.comp tendsto_log_prime
  exact (LpDiagonal.isCompactOperator_lpDiag logWeight 2 (by norm_num) norm_logWeight_le
    hlim).clm_comp (comResponse T)

/-- **`(APS.12)`**: the raw singular values `b_p(T)/log p` tend to zero. -/
theorem tendsto_profile_div_log {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun p => profile T p / Real.log ((p : ℕ) : ℝ)) cofinite (𝓝 0) := by
  have hinv : Tendsto (fun p : Nat.Primes => (Real.log ((p : ℕ) : ℝ))⁻¹) cofinite (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_prime
  have hbound : ∀ p, profile T p / Real.log ((p : ℕ) : ℝ) ≤
      Real.sqrt T * (Real.log ((p : ℕ) : ℝ))⁻¹ := fun p => by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (profileSq_le hT p))
      (inv_nonneg.mpr (log_prime_pos p).le)
  have hnn : ∀ p, 0 ≤ profile T p / Real.log ((p : ℕ) : ℝ) := fun p =>
    div_nonneg (Real.sqrt_nonneg _) (log_prime_pos p).le
  refine squeeze_zero hnn hbound ?_
  simpa using hinv.const_mul (Real.sqrt T)

theorem norm_rawResponse_single {T : ℝ} (hT : 0 < T) (p : Nat.Primes) :
    ‖rawResponse T (lp.single 2 p 1)‖ = profile T p / Real.log ((p : ℕ) : ℝ) := by
  have hlog : logDiag (lp.single 2 p 1) = lp.single 2 p (logWeight p) := by
    ext q
    rw [logDiag_apply, lp.single_apply, lp.single_apply]
    by_cases hq : q = p
    · subst hq; simp
    · simp [hq]
  rw [rawResponse, ContinuousLinearMap.comp_apply, hlog, comResponse_single_smul hT, norm_smul,
    (orthonormal_carrier hT).1 p, mul_one, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (profile_pos hT p), norm_logWeight, div_eq_mul_inv, mul_comm]

/-- **Raw phase: unit prime interventions escape every uniform response bound.** -/
theorem tendsto_norm_rawResponse_single {T : ℝ} (hT : 0 < T) :
    Tendsto (fun p => ‖rawResponse T (lp.single 2 p 1)‖) cofinite (𝓝 0) := by
  simp_rw [norm_rawResponse_single hT]
  exact tendsto_profile_div_log hT.le

theorem norm_single_one (p : Nat.Primes) : ‖(lp.single 2 p (1 : ℂ) : PrimeControls)‖ = 1 := by
  rw [lp.norm_single (by norm_num)]
  simp

/-- **Raw phase: nonclosed range.** -/
theorem not_isClosed_range_rawResponse {T : ℝ} (hT : 0 < T) :
    ¬ IsClosed (Set.range (rawResponse T)) := by
  intro hcl
  have h4 := ((globalProperness_tfae (rawResponse T)).out 0 3).mp hcl
  apply h4
  let e : ℕ ↪ Nat.Primes := Infinite.natEmbedding Nat.Primes
  have hker : invisibleKernel (rawResponse T) = ⊥ := by
    rw [invisibleKernel, LinearMap.ker_eq_bot]
    exact rawResponse_injective hT
  refine ⟨fun n => lp.single 2 (e n) 1,
    fun n => by rw [hker, Submodule.bot_orthogonal_eq_top]; trivial,
    fun n => norm_single_one (e n), ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have he : Tendsto e atTop cofinite := by
    rw [← Nat.cofinite_eq_atTop]
    exact e.injective.tendsto_cofinite
  exact (tendsto_norm_rawResponse_single hT).comp he

/-- **Raw phase: dense range in the carrier.** -/
theorem closure_range_rawResponse {T : ℝ} (hT : 0 < T) :
    (LinearMap.range (rawResponse T : PrimeControls →ₗ[ℂ] ResponseSpace T)).topologicalClosure =
      carrierSpace T := by
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
    rintro _ ⟨c, rfl⟩
    exact comResponse_mem_carrierSpace hT (logDiag c)
  · refine Submodule.topologicalClosure_mono ?_
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have hw : logWeight p ≠ 0 := by
      rw [logWeight, Complex.ofReal_ne_zero]
      exact (inv_pos.mpr (log_prime_pos p)).ne'
    refine ⟨lp.single 2 p ((logWeight p)⁻¹ * (-(profile T p : ℂ))⁻¹), ?_⟩
    have hlog : logDiag (lp.single 2 p ((logWeight p)⁻¹ * (-(profile T p : ℂ))⁻¹)) =
        lp.single 2 p (-(profile T p : ℂ))⁻¹ := by
      ext q
      rw [logDiag_apply, lp.single_apply, lp.single_apply]
      by_cases hq : q = p
      · subst hq
        simp only [Pi.single_eq_same]
        rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
      · simp [hq]
    change comResponse T (logDiag _) = _
    rw [hlog, ← carrier_mem_range hT]

/-- `(APS.15)`, raw: the raw response Laplacian is `diag(b_p(T)²/(log p)²)`. -/
theorem rawLaplacian_inner {T : ℝ} (hT : 0 ≤ T) (c d : PrimeControls) :
    ⟪(ContinuousLinearMap.adjoint (rawResponse T) ∘L rawResponse T) c, d⟫_ℂ =
      ∑' p, ((profileSq T p / Real.log ((p : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) *
        ((starRingEnd ℂ) (c p) * d p) := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left, rawResponse,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, inner_comResponse hT]
  refine tsum_congr fun p => ?_
  rw [logDiag_apply, logDiag_apply, logWeight, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-! ### Finite controls and the profile limit -/

/-- The response values lie in the prime subspace `H_ℙ`. -/
theorem comProfile_mem_range_primeEmbed (c : PrimeControls) (t : ℝ) :
    comProfile c t ∈ LinearMap.range (primeEmbed : PrimeControls →ₗ[ℂ] ArithSpace) :=
  ⟨gainDiag t c, rfl⟩

/-- **`(APS.9)` on finite controls**: `∑_{p ∈ s} a_p D̃_p(t) e_1`. -/
theorem comProfile_finite_eq_duhamel (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) {t : ℝ}
    (ht : 0 ≤ t) :
    comProfile (∑ p ∈ s, lp.single 2 p (a p)) t =
      ∑ p ∈ s, a p • duhamel (letter (primePNat p)) t (basisVec 1) := by
  simp only [comProfile, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← comProfile, single_eq_smul, comProfile_smul, Pi.smul_apply,
    comProfile_single_eq_duhamel p ht]

/-- **`(APS.9)` on finite controls, raw**: `∑_{p ∈ s} a_p D_p(t) e_1`. -/
theorem rawProfile_finite_eq_duhamel (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) {t : ℝ}
    (ht : 0 ≤ t) :
    comProfile (logDiag (∑ p ∈ s, lp.single 2 p (a p))) t =
      ∑ p ∈ s, a p • duhamel (shift (primePNat p)) t (basisVec 1) := by
  simp only [map_sum, comProfile]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← comProfile, single_eq_smul, map_smul, comProfile_smul, Pi.smul_apply,
    comProfile_logDiag_single_eq_duhamel p ht]

/-- `b_p(T)² → T` along the primes. -/
theorem tendsto_profileSq {T : ℝ} (hT : 0 ≤ T) : Tendsto (profileSq T) cofinite (𝓝 T) := by
  have hinv : Tendsto (fun p : Nat.Primes => (Real.log ((p : ℕ) : ℝ))⁻¹) cofinite (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_prime
  have hfrac : ∀ x : ℝ, 0 ≤ x → Tendsto (fun p : Nat.Primes =>
      (1 - ((p : ℕ) : ℝ) ^ (-x)) / Real.log ((p : ℕ) : ℝ)) cofinite (𝓝 0) := fun x hx => by
    refine squeeze_zero (fun p => div_nonneg ?_ (log_prime_pos p).le) (fun p => ?_) hinv
    · exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (one_le_prime p) (by linarith))
    · rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (log_prime_pos p).le)
        (sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have h := (tendsto_const_nhds (x := T)).sub ((hfrac T hT).const_mul 2) |>.add
    ((hfrac (2 * T) (by positivity)).div_const 2)
  simp only [mul_zero, sub_zero, zero_div, add_zero] at h
  refine h.congr fun p => ?_
  rw [profileSq_eq hT]
  ring

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
