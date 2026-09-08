import GaloisForLFunctions.RHTower.MobiusDivisorContinuousHeadMoment
import GaloisForLFunctions.RHTower.MellinLinePolarization

/-!
# Physical regularity of the finite signed divisor head

Exact square-root interpolation propagates the integer ceiling to the
whole real ray. The literal complex primitive is real-valued. Finite
Mobius dilation preserves measurability and square-root growth. These
source estimates prove local integrability, Mellin holomorphy on the full
square-root half-plane, and logarithmic L1 and L2 membership for every
positive dilation on the physical pairing line.
-/

noncomputable section
open Complex Filter Set Topology MeasureTheory Finset Asymptotics
namespace RHTower

/-- The literal real-ray unit head has the same sharp square-root ceiling
as its integer samples, including every partial interval. -/
theorem divisorContinuousUnitHead_le_sqrt (x : ℝ) :
    divisorContinuousUnitHead x ≤ (3/5:ℝ)*Real.sqrt x := by
  by_cases hx : x ≤ 1
  · rw [divisorContinuousUnitHead_eq_zero hx]
    positivity
  have hx1 : 1 ≤ x := (lt_of_not_ge hx).le
  let k : ℕ := ⌊x⌋₊
  have hk : 1 ≤ k := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx1)
  have hkx : (k:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxk : x ≤ (k+1:ℕ) := by exact_mod_cast (Nat.lt_floor_add_one x).le
  have hkk : (k:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast Nat.le_succ k
  have h₀ := divisorUnsignedDilationChannel_one_le_three_fifths_sqrt k
  have h₁ := divisorUnsignedDilationChannel_one_le_three_fifths_sqrt (k+1)
  have he := divisorContinuousUnitHead_between hk hkk le_rfl
  rw [divisorContinuousUnitHead_nat] at he
  rw [he] at h₁
  rw [divisorContinuousUnitHead_between hk hkx hxk]
  have hu : 0 ≤ Real.sqrt x-Real.sqrt k := sub_nonneg.mpr (Real.sqrt_le_sqrt hkx)
  have hv : Real.sqrt x-Real.sqrt k ≤ Real.sqrt (k+1:ℕ)-Real.sqrt k :=
    sub_le_sub_right (Real.sqrt_le_sqrt hxk) _
  by_cases hD : 0 ≤ primeFreeDivisorDefect k-(3/5:ℝ)
  · have hm := mul_le_mul_of_nonneg_right hv hD
    nlinarith
  · have hm := mul_nonpos_of_nonneg_of_nonpos hu (le_of_not_ge hD)
    nlinarith

/-- Measurability follows from the exact finite-interval source formula. -/
theorem measurable_divisorContinuousUnitHead : Measurable divisorContinuousUnitHead := by
  have he : divisorContinuousUnitHead = fun x : ℝ =>
      if x ≤ 1 then 0 else divisorUnsignedDilationChannel ⌊x⌋₊ 1+
        (Real.sqrt x-Real.sqrt (⌊x⌋₊:ℝ))*primeFreeDivisorDefect ⌊x⌋₊ := by
    funext x
    by_cases hx : x ≤ 1
    · simp [hx,divisorContinuousUnitHead_eq_zero hx]
    · rw [if_neg hx]
      apply divisorContinuousUnitHead_between
      · exact (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using (lt_of_not_ge hx).le)
      · exact Nat.floor_le (by linarith)
      · exact_mod_cast (Nat.lt_floor_add_one x).le
  rw [he]
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
  have hA : Measurable (fun x : ℝ => divisorUnsignedDilationChannel ⌊x⌋₊ 1) :=
    (measurable_of_countable (fun n : ℕ => divisorUnsignedDilationChannel n 1)).comp Nat.measurable_floor
  have hD : Measurable (fun x : ℝ => primeFreeDivisorDefect ⌊x⌋₊) :=
    (measurable_of_countable (fun n : ℕ => primeFreeDivisorDefect n)).comp Nat.measurable_floor
  have hk : Measurable (fun x : ℝ => Real.sqrt (⌊x⌋₊:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => Real.sqrt (n:ℝ))).comp Nat.measurable_floor
  exact hA.add ((Real.continuous_sqrt.measurable.sub hk).mul hD)

/-- The complex primitive of the real coefficients has no discarded imaginary part. -/
theorem squareRootSummatoryPrimitive_divisor_eq_real (x : ℝ) :
    squareRootSummatoryPrimitive (fun n => (primeFreeDivisorIncrement n:ℂ)) x =
      (divisorContinuousUnitHead x:ℂ) := by
  have hN (N : ℕ) :
      squareRootSummatoryPrimitive (fun n => (primeFreeDivisorIncrement n:ℂ)) N =
        (divisorContinuousUnitHead N:ℂ) := by
    rw [squareRootSummatoryPrimitive_nat,divisorContinuousUnitHead_nat]
    simp only [← Complex.ofReal_sum,← Complex.ofReal_mul,sum_primeFreeDivisorIncrement,
      divisorUnsignedDilationChannel,Nat.div_one]
  by_cases hx : x ≤ 1
  · rw [divisorContinuousUnitHead_eq_zero hx,squareRootSummatoryPrimitive_eq_integral]
    simp [Ioo_eq_empty_of_le hx]
  · have hk : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr
      (by simpa using (lt_of_not_ge hx).le)
    have hlo := Nat.floor_le (by linarith : 0 ≤ x)
    have hhi : x ≤ (⌊x⌋₊+1:ℕ) := by exact_mod_cast (Nat.lt_floor_add_one x).le
    rw [squareRootSummatoryPrimitive_between _ hk hlo hhi,hN,
      divisorContinuousUnitHead_between hk hlo hhi]
    rw [← Complex.ofReal_sum,sum_primeFreeDivisorIncrement,divisorContinuousUnitHead_nat]
    push_cast
    rfl

/-- The literal processed head is a measurable real source. -/
theorem measurable_mobiusDivisorContinuousHead (P : Finset ℕ) :
    Measurable (mobiusDivisorContinuousHead P) := by
  apply Finset.measurable_sum
  intro d hd
  exact measurable_const.mul (measurable_divisorContinuousUnitHead.comp
    (measurable_id.div_const (d:ℝ)))

/-- Every finite processed source retains square-root real-ray growth. -/
theorem exists_bound_mobiusDivisorContinuousHead (P : Finset ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀x : ℝ, |mobiusDivisorContinuousHead P x| ≤ C*Real.sqrt x := by
  let D : Finset ℕ := (∏p∈P,p).divisors
  let C : ℝ := ∑d∈D, |((ArithmeticFunction.moebius d:ℤ):ℝ)| *Real.sqrt d*(3/5)/Real.sqrt d
  have hC : 0 ≤ C := sum_nonneg (fun d hd => by positivity)
  refine ⟨C,hC,?_⟩
  intro x
  by_cases hx : x ≤ 0
  · rw [mobiusDivisorContinuousHead_eq_zero P (by linarith)]
    simp only [abs_zero]
    positivity
  have hx0 : 0 ≤ x := (lt_of_not_ge hx).le
  rw [mobiusDivisorContinuousHead]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑d∈D, |((ArithmeticFunction.moebius d:ℤ):ℝ)| *Real.sqrt d*
        ((3/5:ℝ)*Real.sqrt (x/d)) := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (divisorContinuousUnitHead_nonneg _)]
      exact mul_le_mul_of_nonneg_left (divisorContinuousUnitHead_le_sqrt _)
        (by positivity)
    _ = C*Real.sqrt x := by
      dsimp [C]
      rw [Finset.sum_mul]
      apply sum_congr rfl
      intro d hd
      rw [Real.sqrt_div hx0]
      ring


/-- Local integrability is proved for the actual source on the whole real line. -/
theorem locallyIntegrable_mobiusDivisorContinuousHead (P : Finset ℕ) :
    LocallyIntegrable (fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ)) := by
  obtain ⟨C,hC,hb⟩ := exists_bound_mobiusDivisorContinuousHead P
  have hc : Continuous (fun x : ℝ => C*Real.sqrt x) := continuous_const.mul Real.continuous_sqrt
  apply hc.locallyIntegrable.mono
    (Complex.continuous_ofReal.measurable.comp (measurable_mobiusDivisorContinuousHead P)).aestronglyMeasurable
  filter_upwards with x
  simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC (Real.sqrt_nonneg x))] using hb x

private lemma head_top_bound (P : Finset ℕ) :
    (fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ)) =O[atTop] (fun x : ℝ => x^(1/2:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := exists_bound_mobiusDivisorContinuousHead P
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C,Filter.Eventually.of_forall fun x => ?_⟩
  simpa only [Complex.norm_real,Real.norm_eq_abs,← Real.sqrt_eq_rpow,
    abs_of_nonneg (Real.sqrt_nonneg x)] using hb x

private lemma head_bottom_bound (P : Finset ℕ) (b : ℝ) :
    (fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ)) =O[𝓝[>] 0] (fun x : ℝ => x^(-b)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨0,?_⟩
  have hn : ∀ᶠ x : ℝ in 𝓝[>] 0, x<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn] with x hx
  rw [mobiusDivisorContinuousHead_eq_zero P hx.le]
  simp

/-- Absolute physical Mellin convergence reaches every line to the right
of the square-root growth threshold. -/
theorem mellinConvergent_mobiusDivisorContinuousHead (P : Finset ℕ) {s : ℂ} (hs : 1/2 < s.re) :
    MellinConvergent (fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ)) (-s) := by
  apply mellinConvergent_of_isBigO_rpow
    ((locallyIntegrable_mobiusDivisorContinuousHead P).locallyIntegrableOn (Ioi 0))
    (a := -1/2) (b := -s.re-1)
  · simpa only [neg_div,neg_neg] using head_top_bound P
  · simp only [neg_re]; linarith
  · exact head_bottom_bound P _
  · simp only [neg_re]; linarith

/-- The physical Mellin transform is holomorphic on its square-root half-plane. -/
theorem differentiableAt_mellin_mobiusDivisorContinuousHead
    (P : Finset ℕ) {s : ℂ} (hs : 1/2 < s.re) :
    DifferentiableAt ℂ (fun z => mellin (fun x : ℝ =>
      (mobiusDivisorContinuousHead P x:ℂ)) (-z)) s := by
  have hd : DifferentiableAt ℂ (mellin (fun x : ℝ =>
      (mobiusDivisorContinuousHead P x:ℂ))) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      ((locallyIntegrable_mobiusDivisorContinuousHead P).locallyIntegrableOn (Ioi 0))
      (a := -1/2) (b := -s.re-1)
    · simpa only [neg_div,neg_neg] using head_top_bound P
    · simp only [neg_re]; linarith
    · exact head_bottom_bound P _
    · simp only [neg_re]; linarith
  exact hd.comp s differentiableAt_id.neg

private lemma log_head_measurable (P : Finset ℕ) (Y : ℝ) :
    Measurable (logMellinLineSource (fun x => (mobiusDivisorContinuousHead P (Y*x):ℂ)) (-1)) := by
  unfold logMellinLineSource
  exact (by fun_prop : Measurable (fun u : ℝ => Real.exp (-(-1)*u))).smul
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_mobiusDivisorContinuousHead P).comp (by fun_prop)))

private lemma log_head_zero (P : Finset ℕ) {Y : ℝ} (hY : 0 < Y) {u : ℝ}
    (hu : Real.log Y ≤ u) :
    logMellinLineSource (fun x => (mobiusDivisorContinuousHead P (Y*x):ℂ)) (-1) u=0 := by
  have hx : Y*Real.exp (-u) ≤ 1 := by
    rw [← Real.exp_log hY,← Real.exp_add,← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    linarith
  simp [logMellinLineSource,mobiusDivisorContinuousHead_eq_zero P hx]

private lemma log_head_bound (P : Finset ℕ) {Y : ℝ} (hY : 0 < Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀u : ℝ,
      ‖logMellinLineSource (fun x => (mobiusDivisorContinuousHead P (Y*x):ℂ)) (-1) u‖ ≤
        C*Real.exp ((1/2)*u) := by
  obtain ⟨C,hC,hb⟩ := exists_bound_mobiusDivisorContinuousHead P
  refine ⟨C*Real.sqrt Y,by positivity,?_⟩
  intro u
  have he : Real.sqrt (Real.exp (-u))=Real.exp (-(u/2)) := by
    rw [Real.sqrt_eq_rpow,← Real.exp_mul]
    congr 1
    ring
  have ht : Real.exp u*Real.sqrt (Real.exp (-u))=Real.exp ((1/2)*u) := by
    rw [he,← Real.exp_add]
    congr 1
    ring
  simp only [logMellinLineSource,neg_neg,one_mul,norm_smul,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),Complex.norm_real]
  calc
    _ ≤ Real.exp u*(C*Real.sqrt (Y*Real.exp (-u))) :=
      mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos u).le
    _ = (C*Real.sqrt Y)*(Real.exp u*Real.sqrt (Real.exp (-u))) := by
      rw [Real.sqrt_mul hY.le]
      ring
    _ = _ := by rw [ht]

/-- Every positive dilation of the literal head has an integrable logarithmic
source on the physical pairing line. -/
theorem integrable_log_mobiusDivisorContinuousHead (P : Finset ℕ) {Y : ℝ} (hY : 0 < Y) :
    Integrable (logMellinLineSource (fun x => (mobiusDivisorContinuousHead P (Y*x):ℂ)) (-1)) := by
  obtain ⟨C,hC,hb⟩ := log_head_bound P hY
  have hi : Integrable ((Iic (Real.log Y)).indicator (fun u : ℝ => C*Real.exp ((1/2)*u))) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    exact (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<1/2) _).const_mul C
  apply hi.mono' (log_head_measurable P Y).aestronglyMeasurable
  filter_upwards with u
  by_cases hu : u ≤ Real.log Y
  · simpa [hu] using hb u
  · rw [log_head_zero P hY (le_of_not_ge hu)]
    simp [hu]

/-- Every positive dilation has a square-integrable logarithmic source too;
no Mellin-Plancherel domain assumption remains for these literal heads. -/
theorem memLp_log_mobiusDivisorContinuousHead (P : Finset ℕ) {Y : ℝ} (hY : 0 < Y) :
    MemLp (logMellinLineSource (fun x => (mobiusDivisorContinuousHead P (Y*x):ℂ)) (-1)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (log_head_measurable P Y).aestronglyMeasurable).mpr
  obtain ⟨C,hC,hb⟩ := log_head_bound P hY
  have hi : Integrable ((Iic (Real.log Y)).indicator (fun u : ℝ => C^2*Real.exp u)) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    exact (integrableOn_exp_Iic _).const_mul (C^2)
  apply hi.mono' ((log_head_measurable P Y).norm.pow_const 2).aestronglyMeasurable
  filter_upwards with u
  by_cases hu : u ≤ Real.log Y
  · rw [Set.indicator_of_mem (show u ∈ Set.Iic (Real.log Y) from hu),
      Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hb u) 2
    have he : (Real.exp ((1/2)*u))^2=Real.exp u := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rwa [mul_pow,he] at hsq
  · rw [log_head_zero P hY (le_of_not_ge hu)]
    simp [hu]

end RHTower
