import GaloisForLFunctions.RHTower.MobiusDivisorPhysicalCutoff

/-!
# The full divisor head as the inverse-cube limit of the finite prime cores

The pointwise finite full head `H_∞(x) = ∑_{1 ≤ d ≤ x} μ(d) √d U(x/d)` agrees with the finite core
head `H_P` on `[0, X]` as soon as `P` contains every prime up to `X`: a squarefree `d ≤ x` has all
its prime factors below `X`, so it divides `∏P`, and a divisor of `∏P` above `x` contributes
nothing.  Both heads obey the core-free envelope `(3/5) x^{3/2}`, so their difference has
inverse-cube mass at most `4/√X`, and the two-scale heads differ by at most `8/√X` uniformly in the
scale `A ≥ 1`.  Along any cofinal exhaustion of finite prime sets both differences tend to zero.

Consequently the core-uniform positive moment passes to the full head, and the finite Euler moment
product `∏_{p ∈ P} (1 − p^{−3/2})` identifies the limit:
`∫_1^∞ H_∞(x)/x³ dx = (∫_1^∞ U(x)/x³ dx)/ζ(3/2) > 0`.
-/

noncomputable section
open MeasureTheory Set Finset Filter Topology
namespace RHTower

/-- The pointwise finite full divisor head `H_∞(x) = ∑_{1 ≤ d ≤ x} μ(d) √d U(x/d)`. -/
def mobiusDivisorFullHead (x : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊x⌋₊,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.sqrt d * divisorContinuousUnitHead (x / d)

/-- Any longer divisor range gives the same full head. -/
theorem mobiusDivisorFullHead_eq_sum_Icc {x : ℝ} {N : ℕ} (hN : ⌊x⌋₊ ≤ N) :
    mobiusDivisorFullHead x = ∑ d ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.sqrt d * divisorContinuousUnitHead (x / d) := by
  unfold mobiusDivisorFullHead
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hN)
  intro d hd hnd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hlt : ⌊x⌋₊ < d := by
    by_contra h
    exact hnd (Finset.mem_Icc.mpr ⟨hd1, not_lt.mp h⟩)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  rw [divisorContinuousUnitHead_eq_zero ((div_le_one hdR).mpr (Nat.lt_of_floor_lt hlt).le),
    mul_zero]

theorem measurable_mobiusDivisorFullHead : Measurable mobiusDivisorFullHead := by
  have hf : ∀ N : ℕ, Measurable (fun x : ℝ => ∑ d ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.sqrt d *
        divisorContinuousUnitHead (x / d)) := by
    intro N
    apply Finset.measurable_sum
    intro d _
    exact measurable_const.mul (measurable_divisorContinuousUnitHead.comp
      (measurable_id.div_const (d : ℝ)))
  refine measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr (fun x => ?_))
  exact tendsto_atTop_of_eventually_const (i₀ := ⌊x⌋₊)
    (fun N hN => (mobiusDivisorFullHead_eq_sum_Icc hN).symm)

/-- The full head obeys the same core-free envelope `(3/5) x^{3/2}`. -/
theorem abs_mobiusDivisorFullHead_le (x : ℝ) :
    |mobiusDivisorFullHead x| ≤ 3 / 5 * x * Real.sqrt x := by
  unfold mobiusDivisorFullHead
  refine abs_sum_dilation_unitHead_le _ (fun d hd => (Finset.mem_Icc.mp hd).1)
    (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) (fun d => ?_) x
  have h := ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [← Int.cast_abs]
  exact_mod_cast h

/-- The full head has no mass at or below one. -/
theorem mobiusDivisorFullHead_eq_zero {x : ℝ} (hx : x ≤ 1) : mobiusDivisorFullHead x = 0 := by
  unfold mobiusDivisorFullHead
  refine Finset.sum_eq_zero (fun d hd => ?_)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  rw [divisorContinuousUnitHead_eq_zero ((div_le_one (zero_lt_one.trans_le hd1)).mpr
    (hx.trans hd1)), mul_zero]

/-- **Literal agreement below the prime horizon.**  If `P` contains every prime at most `X`, then
`H_P(x) = H_∞(x)` for every `x ≤ X`. -/
theorem mobiusDivisorContinuousHead_eq_fullHead (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {X : ℝ} (hcov : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → p ∈ P) {x : ℝ} (hx : x ≤ X) :
    mobiusDivisorContinuousHead P x = mobiusDivisorFullHead x := by
  classical
  set D : ℕ := ∏ p ∈ P, p with hDdef
  have hD : 0 < D := Finset.prod_pos (fun p hp => (hP p hp).pos)
  set f : ℕ → ℝ := fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.sqrt d * divisorContinuousUnitHead (x / d)
    with hf
  have h1 : mobiusDivisorContinuousHead P x = ∑ d ∈ D.divisors ∩ Finset.Icc 1 ⌊x⌋₊, f d := by
    unfold mobiusDivisorContinuousHead
    refine (Finset.sum_subset Finset.inter_subset_left (fun d hd hnd => ?_)).symm
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hnI : d ∉ Finset.Icc 1 ⌊x⌋₊ := fun hI => hnd (Finset.mem_inter.mpr ⟨hd, hI⟩)
    have hlt : ⌊x⌋₊ < d := by
      by_contra h
      exact hnI (Finset.mem_Icc.mpr ⟨hd0, not_lt.mp h⟩)
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    show ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.sqrt d *
      divisorContinuousUnitHead (x / d) = 0
    rw [divisorContinuousUnitHead_eq_zero ((div_le_one hdR).mpr (Nat.lt_of_floor_lt hlt).le),
      mul_zero]
  have h2 : mobiusDivisorFullHead x = ∑ d ∈ D.divisors ∩ Finset.Icc 1 ⌊x⌋₊, f d := by
    unfold mobiusDivisorFullHead
    refine (Finset.sum_subset Finset.inter_subset_right (fun d hd hnd => ?_)).symm
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdx : d ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hd).2
    have hnD : d ∉ D.divisors := fun hD' => hnd (Finset.mem_inter.mpr ⟨hD', hd⟩)
    have hsq : ¬ Squarefree d := by
      intro hs
      apply hnD
      refine Nat.mem_divisors.mpr ⟨?_, hD.ne'⟩
      have hx0 : 0 ≤ x := by
        have : 0 < ⌊x⌋₊ := lt_of_lt_of_le zero_lt_one (hd1.trans hdx)
        exact zero_le_one.trans (Nat.floor_pos.mp this)
      have hdxR : (d : ℝ) ≤ x := (Nat.cast_le.mpr hdx).trans (Nat.floor_le hx0)
      have hsub : d.primeFactors ⊆ P := by
        intro q hq
        have hqd : q ≤ d := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq)
        refine hcov q (Nat.prime_of_mem_primeFactors hq) ?_
        exact ((Nat.cast_le.mpr hqd).trans hdxR).trans hx
      rw [← Nat.prod_primeFactors_of_squarefree hs]
      exact Finset.prod_dvd_prod_of_subset _ _ id hsub
    show ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.sqrt d *
      divisorContinuousUnitHead (x / d) = 0
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp
  rw [h1, h2]

/-! ### The inverse-cube completion -/

/-- The difference of the core and full heads has envelope `(6/5) x^{3/2}`. -/
theorem abs_mobiusDivisorContinuousHead_sub_fullHead_le (P : Finset ℕ) (x : ℝ) :
    |mobiusDivisorContinuousHead P x - mobiusDivisorFullHead x| ≤ 6 / 5 * x * Real.sqrt x := by
  have h1 := abs_mobiusDivisorContinuousHead_le P x
  have h2 := abs_mobiusDivisorFullHead_le x
  calc |mobiusDivisorContinuousHead P x - mobiusDivisorFullHead x|
      ≤ |mobiusDivisorContinuousHead P x| + |mobiusDivisorFullHead x| := abs_sub _ _
    _ ≤ 6 / 5 * x * Real.sqrt x := by linarith

theorem measurable_mobiusDivisorHead_sub_fullHead (P : Finset ℕ) :
    Measurable (fun x => mobiusDivisorContinuousHead P x - mobiusDivisorFullHead x) :=
  (measurable_mobiusDivisorContinuousHead P).sub measurable_mobiusDivisorFullHead

/-- **The full head obeys the same tail bound (2).** -/
theorem integral_abs_mobiusDivisorFullHead_tail_le {X : ℝ} (hX : 0 < X) :
    ∫ x in Ioi X, |mobiusDivisorFullHead x| / x ^ 3 ≤ 2 / Real.sqrt X := by
  have h := (integrableOn_abs_div_cube_Ioi_and_le measurable_mobiusDivisorFullHead
    abs_mobiusDivisorFullHead_le hX).2
  refine h.trans ?_
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  rw [div_le_div_iff_of_pos_right hs]
  norm_num

/-- **Quantitative completion (5a).**  If `P` contains every prime at most `X ≥ 1`, then
`∫_1^∞ |H_P − H_∞|/x³ ≤ 4/√X`. -/
theorem integral_abs_mobiusDivisorHead_sub_fullHead_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {X : ℝ} (hX : 1 ≤ X) (hcov : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → p ∈ P) :
    ∫ x in Ioi 1, |mobiusDivisorContinuousHead P x - mobiusDivisorFullHead x| / x ^ 3
      ≤ 4 / Real.sqrt X := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have heq : ∫ x in Ioi 1, |mobiusDivisorContinuousHead P x - mobiusDivisorFullHead x| / x ^ 3 =
      ∫ x in Ioi X, |mobiusDivisorContinuousHead P x - mobiusDivisorFullHead x| / x ^ 3 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi hX)
    intro x hx
    have hxX : x ≤ X := le_of_not_gt hx.2
    rw [mobiusDivisorContinuousHead_eq_fullHead P hP hcov hxX, sub_self, abs_zero, zero_div]
  rw [heq]
  refine ((integrableOn_abs_div_cube_Ioi_and_le (measurable_mobiusDivisorHead_sub_fullHead P)
    (abs_mobiusDivisorContinuousHead_sub_fullHead_le P) hX0).2).trans ?_
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  rw [div_le_div_iff_of_pos_right hs]
  norm_num

theorem integrableOn_abs_mobiusDivisorHead_sub_fullHead (P : Finset ℕ) :
    IntegrableOn (fun x => |mobiusDivisorContinuousHead P x - mobiusDivisorFullHead x| / x ^ 3)
      (Ioi 1) :=
  (integrableOn_abs_div_cube_Ioi_and_le (measurable_mobiusDivisorHead_sub_fullHead P)
    (abs_mobiusDivisorContinuousHead_sub_fullHead_le P) zero_lt_one).1

private lemma eventually_lt_of_cofinal {C : ℝ} (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ (N : ℝ) ∧ C / Real.sqrt N < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((C / ε) ^ 2) 1)
  have hN1 : (1 : ℝ) < N := (le_max_right _ _).trans_lt hN
  have hN2 : (C / ε) ^ 2 < N := (le_max_left _ _).trans_lt hN
  refine ⟨N, hN1.le, ?_⟩
  have hs : C / ε < Real.sqrt N :=
    (Real.lt_sqrt (div_nonneg hC hε.le)).mpr hN2
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (zero_lt_one.trans hN1)
  rw [div_lt_iff₀ hsN]
  rw [div_lt_iff₀ hε] at hs
  linarith

/-- **Cofinal completion (5a).**  Along any cofinal exhaustion of finite prime sets,
`∫_1^∞ |H_{P_n} − H_∞|/x³ → 0`. -/
theorem tendsto_integral_abs_mobiusDivisorHead_sub_fullHead (P : ℕ → Finset ℕ)
    (hP : ∀ n, ∀ p ∈ P n, p.Prime)
    (hcof : ∀ N : ℕ, ∀ᶠ n in atTop, ∀ p : ℕ, p.Prime → p ≤ N → p ∈ P n) :
    Tendsto (fun n => ∫ x in Ioi 1,
      |mobiusDivisorContinuousHead (P n) x - mobiusDivisorFullHead x| / x ^ 3) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall (fun n => ha.trans_le
      (setIntegral_nonneg measurableSet_Ioi (fun x hx => div_nonneg (abs_nonneg _)
        (pow_pos (zero_lt_one.trans hx) 3).le))), fun a ha => ?_⟩
  obtain ⟨N, hN1, hNa⟩ := eventually_lt_of_cofinal (by norm_num : (0 : ℝ) ≤ 4) ha
  filter_upwards [hcof N] with n hn
  exact lt_of_le_of_lt (integral_abs_mobiusDivisorHead_sub_fullHead_le (P n) (hP n) hN1
    (fun p hp hpN => hn p hp (by exact_mod_cast hpN))) hNa

/-! ### The two-scale completion -/

/-- The two-scale full head `g_{∞,A}(x) = H_∞(x) + A H_∞(x/A)`. -/
def mobiusDivisorFullTwoScaleHead (A x : ℝ) : ℝ :=
  mobiusDivisorFullHead x + A * mobiusDivisorFullHead (x / A)

/-- Rescaling an inverse-cube mass on `(1, ∞)` for a function vanishing at and below one. -/
theorem setIntegral_Ioi_one_comp_div {G : ℝ → ℝ} (hG : ∀ y ≤ 1, G y = 0) {A : ℝ} (hA : 1 ≤ A) :
    ∫ x in Ioi 1, G (x / A) / x ^ 3 = (A ^ 2)⁻¹ * ∫ y in Ioi 1, G y / y ^ 3 := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hpt : ∀ x : ℝ, G (x / A) / x ^ 3 = (A ^ 3)⁻¹ * (G (A⁻¹ * x) / (A⁻¹ * x) ^ 3) := by
    intro x
    rw [← div_eq_inv_mul]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · field_simp
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun y => G y / y ^ 3) 1 (inv_pos.mpr hA0),
    mul_one, inv_inv, smul_eq_mul]
  have hshift : ∫ y in Ioi A⁻¹, G y / y ^ 3 = ∫ y in Ioi 1, G y / y ^ 3 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi (inv_le_one_of_one_le₀ hA))
    intro y hy
    rw [hG y (le_of_not_gt hy.2), zero_div]
  rw [hshift]
  field_simp

/-- **Quantitative two-scale completion (5b).**  If `P` contains every prime at most `X ≥ 1`, then
for every `A ≥ 1`, `∫_1^∞ |g_{P,A} − g_{∞,A}|/x³ ≤ 8/√X`. -/
theorem integral_abs_mobiusDivisorTwoScale_sub_full_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {X : ℝ} (hX : 1 ≤ X) (hcov : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → p ∈ P) {A : ℝ} (hA : 1 ≤ A) :
    ∫ x in Ioi 1, |mobiusDivisorTwoScaleHead P A x - mobiusDivisorFullTwoScaleHead A x| / x ^ 3
      ≤ 8 / Real.sqrt X := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  set D : ℝ → ℝ := fun x => mobiusDivisorContinuousHead P x - mobiusDivisorFullHead x with hD
  have hDz : ∀ y ≤ 1, |D y| = 0 := fun y hy => by
    simp only [hD]
    rw [mobiusDivisorContinuousHead_eq_zero P hy, mobiusDivisorFullHead_eq_zero hy, sub_self,
      abs_zero]
  have hDm : Measurable D := measurable_mobiusDivisorHead_sub_fullHead P
  have hI1 : IntegrableOn (fun x => |D x| / x ^ 3) (Ioi 1) :=
    integrableOn_abs_mobiusDivisorHead_sub_fullHead P
  have hbA : ∀ x, |D (x / A)| ≤ 6 / 5 * x * Real.sqrt x := by
    intro x
    rcases le_or_gt x 0 with hx | hx
    · rw [hDz _ ((div_nonpos_of_nonpos_of_nonneg hx hA0.le).trans zero_le_one),
        Real.sqrt_eq_zero'.mpr hx]
      simp
    · refine (abs_mobiusDivisorContinuousHead_sub_fullHead_le P (x / A)).trans ?_
      have h1 : x / A ≤ x := div_le_self hx.le hA
      have h2 := Real.sqrt_le_sqrt h1
      have h0 : 0 ≤ x / A := div_nonneg hx.le hA0.le
      have := mul_le_mul h1 h2 (Real.sqrt_nonneg _) hx.le
      nlinarith
  have hI2 : IntegrableOn (fun x => |D (x / A)| / x ^ 3) (Ioi 1) :=
    (integrableOn_abs_div_cube_Ioi_and_le (hDm.comp (measurable_id.div_const A)) hbA
      zero_lt_one).1
  have hpt : ∀ x ∈ Ioi (1 : ℝ),
      |mobiusDivisorTwoScaleHead P A x - mobiusDivisorFullTwoScaleHead A x| / x ^ 3 ≤
        |D x| / x ^ 3 + A * (|D (x / A)| / x ^ 3) := by
    intro x hx
    have hx3 : 0 < x ^ 3 := pow_pos (zero_lt_one.trans hx) 3
    have heq : mobiusDivisorTwoScaleHead P A x - mobiusDivisorFullTwoScaleHead A x =
        D x + A * D (x / A) := by
      simp only [mobiusDivisorTwoScaleHead, mobiusDivisorFullTwoScaleHead, hD]
      ring
    rw [heq, ← mul_div_assoc, ← add_div]
    refine div_le_div_of_nonneg_right ?_ hx3.le
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hA0]
  have hmeas : Measurable (fun x =>
      |mobiusDivisorTwoScaleHead P A x - mobiusDivisorFullTwoScaleHead A x| / x ^ 3) := by
    have h1 := measurable_mobiusDivisorContinuousHead P
    have h2 := measurable_mobiusDivisorFullHead
    unfold mobiusDivisorTwoScaleHead mobiusDivisorFullTwoScaleHead
    fun_prop
  have hint : IntegrableOn (fun x =>
      |mobiusDivisorTwoScaleHead P A x - mobiusDivisorFullTwoScaleHead A x| / x ^ 3) (Ioi 1) := by
    refine Integrable.mono' (hI1.add (hI2.const_mul A)) hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _)
      (pow_pos (zero_lt_one.trans hx) 3).le)]
    exact hpt x hx
  have hscale : ∫ x in Ioi 1, |D (x / A)| / x ^ 3 = (A ^ 2)⁻¹ * ∫ y in Ioi 1, |D y| / y ^ 3 :=
    setIntegral_Ioi_one_comp_div (G := fun y => |D y|) hDz hA
  have hbound := integral_abs_mobiusDivisorHead_sub_fullHead_le P hP hX hcov
  have hI1v : ∫ x in Ioi 1, |D x| / x ^ 3 ≤ 4 / Real.sqrt X := hbound
  have hI1n : 0 ≤ ∫ x in Ioi 1, |D x| / x ^ 3 :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => div_nonneg (abs_nonneg _)
      (pow_pos (zero_lt_one.trans hx) 3).le)
  calc ∫ x in Ioi 1, |mobiusDivisorTwoScaleHead P A x - mobiusDivisorFullTwoScaleHead A x| / x ^ 3
      ≤ ∫ x in Ioi 1, (|D x| / x ^ 3 + A * (|D (x / A)| / x ^ 3)) :=
        setIntegral_mono_on hint (hI1.add (hI2.const_mul A)) measurableSet_Ioi hpt
    _ = (∫ x in Ioi 1, |D x| / x ^ 3) + A * ((A ^ 2)⁻¹ * ∫ y in Ioi 1, |D y| / y ^ 3) := by
        rw [integral_add hI1 (hI2.const_mul A), integral_const_mul, hscale]
    _ = (1 + A⁻¹) * ∫ x in Ioi 1, |D x| / x ^ 3 := by
        field_simp
    _ ≤ 2 * (4 / Real.sqrt X) := by
        have hAi : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
        have hAi0 : 0 ≤ A⁻¹ := inv_nonneg.mpr hA0.le
        nlinarith
    _ = 8 / Real.sqrt X := by ring

/-- **Uniform two-scale completion (5b).**  Along any cofinal exhaustion of finite prime sets,
`sup_{A ≥ 1} ∫_1^∞ |g_{P_n,A} − g_{∞,A}|/x³ → 0`. -/
theorem tendstoUniformlyOn_integral_abs_mobiusDivisorTwoScale_sub_full (P : ℕ → Finset ℕ)
    (hP : ∀ n, ∀ p ∈ P n, p.Prime)
    (hcof : ∀ N : ℕ, ∀ᶠ n in atTop, ∀ p : ℕ, p.Prime → p ≤ N → p ∈ P n) :
    TendstoUniformlyOn (fun n A => ∫ x in Ioi 1,
        |mobiusDivisorTwoScaleHead (P n) A x - mobiusDivisorFullTwoScaleHead A x| / x ^ 3)
      (fun _ => 0) atTop (Ici 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN1, hNa⟩ := eventually_lt_of_cofinal (by norm_num : (0 : ℝ) ≤ 8) hε
  filter_upwards [hcof N] with n hn
  intro A hA
  have hnn : 0 ≤ ∫ x in Ioi 1,
      |mobiusDivisorTwoScaleHead (P n) A x - mobiusDivisorFullTwoScaleHead A x| / x ^ 3 :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => div_nonneg (abs_nonneg _)
      (pow_pos (zero_lt_one.trans hx) 3).le)
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact lt_of_le_of_lt (integral_abs_mobiusDivisorTwoScale_sub_full_le (P n) (hP n) hN1
    (fun p hp hpN => hn p hp (by exact_mod_cast hpN)) hA) hNa

/-! ### The moment of the full head -/

theorem integrableOn_mobiusDivisorFullHead_moment :
    IntegrableOn (fun x => mobiusDivisorFullHead x / x ^ 3) (Ioi 1) := by
  have h := (integrableOn_abs_div_cube_Ioi_and_le measurable_mobiusDivisorFullHead
    abs_mobiusDivisorFullHead_le zero_lt_one).1
  refine Integrable.mono' h (measurable_div_cube measurable_mobiusDivisorFullHead).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun x hx => ?_)))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (zero_lt_one.trans hx) 3 : (0 : ℝ) < x ^ 3)]

/-- The finite core moments converge to the full moment along any cofinal exhaustion. -/
theorem tendsto_integral_mobiusDivisorHead_moment (P : ℕ → Finset ℕ)
    (hP : ∀ n, ∀ p ∈ P n, p.Prime)
    (hcof : ∀ N : ℕ, ∀ᶠ n in atTop, ∀ p : ℕ, p.Prime → p ≤ N → p ∈ P n) :
    Tendsto (fun n => ∫ x in Ioi 1, mobiusDivisorContinuousHead (P n) x / x ^ 3) atTop
      (𝓝 (∫ x in Ioi 1, mobiusDivisorFullHead x / x ^ 3)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (tendsto_integral_abs_mobiusDivisorHead_sub_fullHead P hP hcof)
  have hiP : IntegrableOn (fun x => mobiusDivisorContinuousHead (P n) x / x ^ 3) (Ioi 1) :=
    (integrable_mobiusDivisorContinuousHead_moment (P n)).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  rw [← integral_sub hiP integrableOn_mobiusDivisorFullHead_moment]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [← sub_div, Real.norm_eq_abs, abs_div,
    abs_of_pos (pow_pos (zero_lt_one.trans hx) 3 : (0 : ℝ) < x ^ 3)]

private lemma sqrt_div_sq_eq_rpow (n : ℕ) : Real.sqrt n / (n : ℝ) ^ 2 = (n : ℝ) ^ (-3 / 2 : ℝ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hnR]
  norm_num

/-- The cofinal exhaustion by all primes below `n`. -/
theorem primesBelow_cofinal (N : ℕ) :
    ∀ᶠ n in atTop, ∀ p : ℕ, p.Prime → p ≤ N → p ∈ Nat.primesBelow n := by
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  intro p hp hpN
  exact Nat.mem_primesBelow.mpr ⟨by omega, hp⟩

/-- **The positive moment passes to the full head.** -/
theorem mobiusDivisorUniformMoment_le_fullHead :
    mobiusDivisorUniformMoment ≤ ∫ x in Ioi 1, mobiusDivisorFullHead x / x ^ 3 := by
  have hT := tendsto_integral_mobiusDivisorHead_moment (fun n => Nat.primesBelow n)
    (fun n p hp => Nat.prime_of_mem_primesBelow hp) primesBelow_cofinal
  exact ge_of_tendsto hT (Eventually.of_forall (fun n =>
    mobiusDivisorUniformMoment_le _ (fun p hp => Nat.prime_of_mem_primesBelow hp)))

/-- **The Euler identification (5c).**
`∫_1^∞ H_∞(x)/x³ dx = (∫_1^∞ U(x)/x³ dx)/ζ(3/2)`. -/
theorem integral_mobiusDivisorFullHead_moment_eq :
    ((∫ x in Ioi 1, mobiusDivisorFullHead x / x ^ 3 : ℝ) : ℂ) =
      ((∫ x in Ioi (1 : ℝ), divisorContinuousUnitHead x / x ^ 3 : ℝ) : ℂ) /
        riemannZeta (3 / 2) := by
  have hs : 1 < (3 / 2 : ℂ).re := by norm_num
  set IU : ℝ := ∫ x in Ioi (1 : ℝ), divisorContinuousUnitHead x / x ^ 3 with hIU
  have hmom : ∀ n, ∫ x in Ioi 1, mobiusDivisorContinuousHead (Nat.primesBelow n) x / x ^ 3 =
      (∏ p ∈ Nat.primesBelow n, (1 - Real.sqrt p / (p : ℝ) ^ 2)) * IU := by
    intro n
    rw [integral_mobiusDivisorContinuousHead_moment_Ioi_one,
      integral_mobiusDivisorContinuousHead_moment _ (fun p hp => Nat.prime_of_mem_primesBelow hp),
      hIU, integral_Ioi_one_divisorContinuousUnitHead]
  have hfac : ∀ p : ℕ, (((1 - Real.sqrt p / (p : ℝ) ^ 2 : ℝ)) : ℂ) = 1 - (p : ℂ) ^ (-(3 / 2 : ℂ)) := by
    intro p
    rw [sqrt_div_sq_eq_rpow, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_cpow (Nat.cast_nonneg p)]
    push_cast
    ring_nf
  have hE : Tendsto (fun n => ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-(3 / 2 : ℂ)))) atTop
      (𝓝 (riemannZeta (3 / 2))⁻¹) := by
    have h := (riemannZeta_eulerProduct hs).inv₀ (riemannZeta_ne_zero_of_one_lt_re hs)
    refine h.congr (fun n => ?_)
    rw [Finset.prod_inv_distrib, inv_inv]
  have hC : Tendsto (fun n => ((∫ x in Ioi 1,
      mobiusDivisorContinuousHead (Nat.primesBelow n) x / x ^ 3 : ℝ) : ℂ)) atTop
      (𝓝 ((riemannZeta (3 / 2))⁻¹ * (IU : ℂ))) := by
    refine (hE.mul_const (IU : ℂ)).congr (fun n => ?_)
    rw [hmom n, Complex.ofReal_mul, Complex.ofReal_prod]
    simp_rw [hfac]
  have hR : Tendsto (fun n => ((∫ x in Ioi 1,
      mobiusDivisorContinuousHead (Nat.primesBelow n) x / x ^ 3 : ℝ) : ℂ)) atTop
      (𝓝 ((∫ x in Ioi 1, mobiusDivisorFullHead x / x ^ 3 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp
      (tendsto_integral_mobiusDivisorHead_moment (fun n => Nat.primesBelow n)
        (fun n p hp => Nat.prime_of_mem_primesBelow hp) primesBelow_cofinal)
  rw [tendsto_nhds_unique hR hC, mul_comm, ← div_eq_mul_inv]

/-- **The full signed moment is strictly positive (5c).** -/
theorem integral_mobiusDivisorFullHead_moment_pos :
    0 < ∫ x in Ioi 1, mobiusDivisorFullHead x / x ^ 3 :=
  mobiusDivisorUniformMoment_pos.trans_le mobiusDivisorUniformMoment_le_fullHead

end RHTower
