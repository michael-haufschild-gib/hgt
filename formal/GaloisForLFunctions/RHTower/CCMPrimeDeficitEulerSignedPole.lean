import GaloisForLFunctions.RHTower.CCMPrimeDeficitDilationSourceBounds
import GaloisForLFunctions.RHTower.CCMPrimeDeficitEulerRenewal
import GaloisForLFunctions.RHTower.SqrtTelescopeSums

/-!
# The actual signed Euler renewal has a harmonic pole

Fixed finite Euler completion does not absorb the signed Chebyshev deficit.
The unchanged renewal of that deficit has leading term
`(1 + gamma) (totient P / P)^2 T exp T` for every positive fixed modulus.
In particular, even an `O(exp T)` bound is impossible.

The positive survivor is an exact classification: the complete finite
shifted divisor-source quadratic form has a rank-one leading pole, and its
nullspace consists precisely of directions with zero signed exponential
moment (the harmonic moment for logarithmic integer shifts). Every pair
term is retained. The elementary source estimate and a square-root sum
prove the pole law without a prime-error estimate or an RH premise.

This does not bound the native prime-polar cumulative energy. Moving Euler
moduli require uniform signed control after retaining the harmonic correction.
-/

noncomputable section
open MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower

private def pole : ℝ := Real.eulerMascheroniConstant + 1
private def stirling : ℝ := Real.log (2 * Real.pi) / 2
private def envelope : ℝ := 6 + |pole| + 2 * |stirling|

private theorem source_envelope {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDilationSource T - pole * Real.exp T| ≤
      envelope * Real.exp (T / 2) := by
  have hrem := abs_ccmPrimeDeficitDilationRemainder_le hT
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ T/2 by positivity)
  have he1 : 1 ≤ Real.exp (T/2) := Real.one_le_exp (by positivity)
  have hlin : T ≤ 2 * Real.exp (T/2) := by nlinarith only [he, sq_nonneg (T/2), hT]
  have hquad : T^2/4 ≤ 2 * Real.exp (T/2) := by nlinarith only [he, hT]
  have hc := mul_le_mul_of_nonneg_left he1 (abs_nonneg pole)
  have hd := mul_le_mul_of_nonneg_left hlin (abs_nonneg stirling)
  calc
    _ = |ccmPrimeDeficitDilationRemainder T - pole - stirling*T| := by
      congr 1
      unfold ccmPrimeDeficitDilationRemainder pole stirling
      ring
    _ ≤ |ccmPrimeDeficitDilationRemainder T| + |pole| + |stirling| * T := by
      calc
        _ ≤ |ccmPrimeDeficitDilationRemainder T - pole| + |stirling*T| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul, abs_of_nonneg hT]
          gcongr
          exact abs_sub _ _
    _ ≤ envelope * Real.exp (T/2) := by dsimp [envelope]; nlinarith only [hrem,hlin,hquad,hc,hd]

private theorem delayed_exp_half (T : ℝ) {n : ℕ} (hn : 0 < n) :
    Real.exp ((T - Real.log n)/2) = Real.exp (T/2) / Real.sqrt n := by
  rw [sub_div, Real.exp_sub]
  congr 1
  rw [← Real.log_sqrt (show (0:ℝ) ≤ n by positivity),
    Real.exp_log (Real.sqrt_pos.mpr (by exact_mod_cast hn))]

private theorem divisor_harmonic_envelope {T : ℝ} (_hT : 0 ≤ T) :
    |ccmPrimeDeficitDivisorSource T -
      pole * Real.exp T * (∑ n ∈ Icc 1 ⌊Real.exp T⌋₊, (n:ℝ)⁻¹)| ≤
      (2*envelope)*Real.exp T := by
  have hK : 0 ≤ envelope := by unfold envelope; positivity
  rw [← logarithmicDilationSum_dilationSource_eq_divisorSource]
  unfold logarithmicDilationSum logarithmicWeightedDilation
  simp only [one_mul]
  have hmain : pole * Real.exp T * (∑ n ∈ Icc 1 ⌊Real.exp T⌋₊, (n:ℝ)⁻¹) =
      ∑ n ∈ Icc 1 ⌊Real.exp T⌋₊, pole * Real.exp (T - Real.log n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [Real.exp_sub, Real.exp_log hnpos]
    ring
  rw [hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Icc 1 ⌊Real.exp T⌋₊,
        |ccmPrimeDeficitDilationSource (T - Real.log n) - pole * Real.exp (T - Real.log n)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 ⌊Real.exp T⌋₊, envelope * Real.exp ((T-Real.log n)/2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0:ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hl : Real.log n ≤ T := (Real.log_le_iff_le_exp hnpos).mpr
        ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2)
      exact source_envelope (sub_nonneg.mpr hl)
    _ = (envelope * Real.exp (T/2)) * (∑ n ∈ Icc 1 ⌊Real.exp T⌋₊, 1/Real.sqrt n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [delayed_exp_half T (Finset.mem_Icc.mp hn).1]
      ring
    _ ≤ (envelope * Real.exp (T/2)) * (2*Real.sqrt ⌊Real.exp T⌋₊) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt_le _) (mul_nonneg hK (Real.exp_pos _).le)
    _ ≤ (envelope * Real.exp (T/2)) * (2*Real.exp (T/2)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (Real.exp_pos _).le)
      gcongr
      calc
        Real.sqrt (⌊Real.exp T⌋₊:ℝ) ≤ Real.sqrt (Real.exp T) :=
          Real.sqrt_le_sqrt (Nat.floor_le (Real.exp_pos T).le)
        _ = _ := (Real.exp_half T).symm
    _ = _ := by rw [mul_mul_mul_comm, ← Real.exp_add, add_halves]; ring

private def harmonicEnvelope : ℝ := |Real.eulerMascheroniConstant| + Real.log 2 + 1
private def divisorEnvelope : ℝ := 2*envelope + |pole| * harmonicEnvelope

private theorem harmonic_envelope {T : ℝ} (hT : 0 ≤ T) :
    |(∑ n ∈ Icc 1 ⌊Real.exp T⌋₊, (n:ℝ)⁻¹)-T| ≤ harmonicEnvelope := by
  let N := ⌊Real.exp T⌋₊
  have hN : 1 ≤ N := (Nat.le_floor_iff (Real.exp_pos T).le).mpr
    (by simpa using Real.one_le_exp hT)
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0:ℝ) < N := lt_of_lt_of_le zero_lt_one hNR
  have hx : (N:ℝ) ≤ Real.exp T := Nat.floor_le (Real.exp_pos T).le
  have hx' : Real.exp T < (N:ℝ)+1 := Nat.lt_floor_add_one (Real.exp T)
  have hlog : Real.log N ≤ T := (Real.log_le_iff_le_exp hpos).mpr hx
  have hlog' : T ≤ Real.log 2 + Real.log N := by
    have h := Real.log_le_log (Real.exp_pos T) (show Real.exp T ≤ 2*(N:ℝ) by linarith)
    rwa [Real.log_exp, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hpos.ne'] at h
  have hH := harmonic_mascheroni_half_bounds hN
  have hH0 : 0 ≤ ((harmonic N:ℚ):ℝ)-Real.log N-Real.eulerMascheroniConstant :=
    (by positivity : (0:ℝ) ≤ 1/(2*((N:ℝ)+1))).trans hH.1
  have hH1 : ((harmonic N:ℚ):ℝ)-Real.log N-Real.eulerMascheroniConstant ≤ 1 :=
    hH.2.trans ((div_le_one (by positivity : (0:ℝ)<2*N)).mpr (by linarith))
  have hsum : (∑ n ∈ Icc 1 N, (n:ℝ)⁻¹) = ((harmonic N:ℚ):ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast]
  change |(∑ n ∈ Icc 1 N, (n:ℝ)⁻¹)-T| ≤ harmonicEnvelope
  rw [hsum, abs_le]
  dsimp [harmonicEnvelope]
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  constructor <;> linarith [le_abs_self Real.eulerMascheroniConstant,
    neg_abs_le Real.eulerMascheroniConstant]

private theorem divisor_envelope {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDivisorSource T - pole*T*Real.exp T| ≤
      divisorEnvelope * Real.exp T := by
  let H : ℝ := ∑ n ∈ Icc 1 ⌊Real.exp T⌋₊, (n:ℝ)⁻¹
  have h1 := divisor_harmonic_envelope hT
  have h2 := mul_le_mul_of_nonneg_left (harmonic_envelope hT)
    (mul_nonneg (abs_nonneg pole) (Real.exp_pos T).le)
  calc
    _ = |(ccmPrimeDeficitDivisorSource T - pole*Real.exp T*H) +
        pole*Real.exp T*(H-T)| := by congr 1; ring
    _ ≤ |ccmPrimeDeficitDivisorSource T - pole*Real.exp T*H| +
        |pole| * Real.exp T*|H-T| := by
      simpa only [abs_mul, abs_of_pos (Real.exp_pos T)] using abs_add_le
        (ccmPrimeDeficitDivisorSource T - pole*Real.exp T*H) (pole*Real.exp T*(H-T))
    _ ≤ divisorEnvelope * Real.exp T := by
      dsimp [divisorEnvelope]
      change |ccmPrimeDeficitDivisorSource T - pole*Real.exp T*H| ≤ _ at h1
      change |pole| * Real.exp T*|H-T| ≤ _ at h2
      nlinarith only [h1,h2]

/-- The complete doubled source has a nonzero logarithmic exponential pole. -/
theorem ccmPrimeDeficitDivisorSource_pole_limit :
    Tendsto (fun T : ℝ => ccmPrimeDeficitDivisorSource T / (T*Real.exp T))
      atTop (𝓝 (Real.eulerMascheroniConstant+1)) := by
  change Tendsto _ _ (𝓝 pole)
  rw [tendsto_iff_dist_tendsto_zero]
  have hmaj : Tendsto (fun T : ℝ => divisorEnvelope/T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun T => dist_nonneg) ?_ hmaj
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  rw [Real.dist_eq]
  calc
    _ = |ccmPrimeDeficitDivisorSource T-pole*T*Real.exp T|/(T*Real.exp T) := by
      rw [show ccmPrimeDeficitDivisorSource T/(T*Real.exp T)-pole =
        (ccmPrimeDeficitDivisorSource T-pole*T*Real.exp T)/(T*Real.exp T) by
          field_simp, abs_div, abs_of_pos (mul_pos hT (Real.exp_pos T))]
    _ ≤ (divisorEnvelope*Real.exp T)/(T*Real.exp T) :=
      div_le_div_of_nonneg_right (divisor_envelope hT.le) (by positivity)
    _ = divisorEnvelope/T := by field_simp

private theorem shift_pole_limit {f : ℝ → ℝ} {c : ℝ}
    (hf : Tendsto (fun T => f T/(T*Real.exp T)) atTop (𝓝 c)) (u : ℝ) :
    Tendsto (fun T => f (T-u)/(T*Real.exp T)) atTop (𝓝 (c*Real.exp (-u))) := by
  have hshift : Tendsto (fun T : ℝ => T-u) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    exact eventually_atTop.2 ⟨B+u, fun T hT => by linarith⟩
  have hratio : Tendsto (fun T : ℝ => (T-u)/T) atTop (𝓝 1) := by
    have h : Tendsto (fun T : ℝ => 1-u/T) atTop (𝓝 (1-0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    field_simp
  have h := ((hf.comp hshift).mul hratio).mul_const (Real.exp (-u))
  simp only [mul_one, Function.comp_def] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (max (0:ℝ) u)] with T hT
  have hT0 : T ≠ 0 := ne_of_gt (lt_of_le_of_lt (le_max_left _ _) hT)
  have hTu : T-u ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt (le_max_right _ _) hT))
  rw [show Real.exp (T-u) = Real.exp T*Real.exp (-u) by rw [sub_eq_add_neg,Real.exp_add]]
  field_simp

/-- The complete finite two-label Hessian retains its leading rank-one pole. -/
theorem ccmPrimeDeficitDivisorSource_finite_pair_pole_limit
    {ι : Type*} (S : Finset ι) (v u : ι → ℝ) :
    Tendsto (fun T : ℝ =>
      (∑ i ∈ S, ∑ j ∈ S, v i*v j*
        ccmPrimeDeficitDivisorSource (T-u i-u j))/(T*Real.exp T))
      atTop (𝓝 ((Real.eulerMascheroniConstant+1) *
        (∑ i ∈ S, v i*Real.exp (-u i))^2)) := by
  have h (i j : ι) :=
    (shift_pole_limit ccmPrimeDeficitDivisorSource_pole_limit (u i+u j)).const_mul (v i*v j)
  have hs := tendsto_finsetSum S (fun i _ => tendsto_finsetSum S (fun j _ => h i j))
  have he : (∑ i ∈ S, ∑ j ∈ S,
      (v i*v j)*((Real.eulerMascheroniConstant+1)*Real.exp (-(u i+u j)))) =
      (Real.eulerMascheroniConstant+1)*(∑ i ∈ S, v i*Real.exp (-u i))^2 := by
    rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [neg_add, Real.exp_add]
    ring
  rw [he] at hs
  convert hs using 1
  ext T
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sub_sub]
  ring

/-- Precisely harmonic-neutral finite directions remove the leading pole. -/
theorem ccmPrimeDeficitDivisorSource_finite_pair_pole_vanishes_iff
    {ι : Type*} (S : Finset ι) (v u : ι → ℝ) :
    Tendsto (fun T : ℝ =>
      (∑ i ∈ S, ∑ j ∈ S, v i*v j*
        ccmPrimeDeficitDivisorSource (T-u i-u j))/(T*Real.exp T)) atTop (𝓝 0) ↔
      ∑ i ∈ S, v i*Real.exp (-u i) = 0 := by
  have hc : Real.eulerMascheroniConstant+1 ≠ 0 := by
    have := Real.one_half_lt_eulerMascheroniConstant
    linarith
  constructor
  · intro h
    have he := tendsto_nhds_unique (ccmPrimeDeficitDivisorSource_finite_pair_pole_limit S v u) h
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left hc)
  · intro h
    simpa only [h, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero] using
      ccmPrimeDeficitDivisorSource_finite_pair_pole_limit S v u

private theorem zero_pole_of_exponential_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ T : ℝ, 0 ≤ T → |f T| ≤ C*Real.exp T) :
    Tendsto (fun T : ℝ => f T/(T*Real.exp T)) atTop (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => dist_nonneg) ?_
    (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun T : ℝ => C/T) atTop (𝓝 0))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (mul_pos hT (Real.exp_pos T))]
  calc
    _ ≤ (C*Real.exp T)/(T*Real.exp T) :=
      div_le_div_of_nonneg_right (hf T hT.le) (by positivity)
    _ = C/T := by field_simp

private theorem source_zero_pole :
    Tendsto (fun T : ℝ => ccmPrimeDeficitDilationSource T/(T*Real.exp T)) atTop (𝓝 0) := by
  apply zero_pole_of_exponential_bound (C := envelope+|pole|)
  intro T hT
  have he := source_envelope hT
  have hK : 0 ≤ envelope := by unfold envelope; positivity
  have hhalf := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (show T/2 ≤ T by linarith)) hK
  calc
    _ = |(ccmPrimeDeficitDilationSource T-pole*Real.exp T)+pole*Real.exp T| := by congr 1; ring
    _ ≤ |ccmPrimeDeficitDilationSource T-pole*Real.exp T|+|pole*Real.exp T| := abs_add_le _ _
    _ ≤ (envelope+|pole|)*Real.exp T := by
      rw [abs_mul,abs_of_pos (Real.exp_pos T)]
      nlinarith only [he,hhalf]

private theorem euler_dilation_eq {P : ℕ} (hP : 0 < P) (f : ℝ → ℝ)
    {T : ℝ} (hT : Real.log P ≤ T) :
    logarithmicWeightedDilation (ccmEulerMobius P) f T =
      ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d:ℝ)*f (T-Real.log d) := by
  have hPR : (0:ℝ) < P := by exact_mod_cast hP
  have hsub : P.divisors ⊆ Icc 1 ⌊Real.exp T⌋₊ := by
    intro d hd
    refine Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, ?_⟩
    apply (Nat.le_floor_iff (Real.exp_pos T).le).mpr
    have hdP : (d:ℝ) ≤ P := by exact_mod_cast Nat.le_of_dvd hP (Nat.dvd_of_mem_divisors hd)
    exact hdP.trans ((Real.log_le_iff_le_exp hPR).mp hT)
  unfold logarithmicWeightedDilation
  calc
    _ = ∑ d ∈ P.divisors, ccmEulerMobius P d*f (T-Real.log d) := by
      symm
      apply Finset.sum_subset hsub
      intro n hn hnot
      have hnd : ¬ n ∣ P := fun hd => hnot (Nat.mem_divisors.mpr ⟨hd,hP.ne'⟩)
      simp [ccmEulerMobius,hnd]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [ccmEulerMobius, ArithmeticFunction.coe_mk, if_pos (Nat.dvd_of_mem_divisors hd)]

private theorem euler_action_eq {P : ℕ} (hP : 0 < P)
    {T : ℝ} (hT : 2*Real.log P ≤ T) :
    ccmPrimeDeficitEulerAction P T =
      2*(∑ d ∈ P.divisors, (ArithmeticFunction.moebius d:ℝ)*
        ccmPrimeDeficitDilationSource (T-Real.log d)) -
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        (ArithmeticFunction.moebius d:ℝ)*(ArithmeticFunction.moebius e:ℝ)*
          ccmPrimeDeficitDivisorSource (T-Real.log d-Real.log e) := by
  have hPR : (0:ℝ) < P := by exact_mod_cast hP
  have hlog0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast hP)
  have hlogT : Real.log P ≤ T := by linarith
  unfold ccmPrimeDeficitEulerAction ccmPrimeDeficitCoefficientAction logarithmicReconstructionAction
  rw [funext logarithmicDilationSum_dilationSource_eq_divisorSource,
    euler_dilation_eq hP _ hlogT, euler_dilation_eq hP _ hlogT]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hlogd : Real.log d ≤ Real.log P :=
    Real.log_le_log hdR (by exact_mod_cast Nat.le_of_dvd hP (Nat.dvd_of_mem_divisors hd))
  rw [euler_dilation_eq hP _ (by linarith), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

private theorem exp_neg_log_nat {n : ℕ} (hn : 0 < n) :
    Real.exp (-Real.log n) = (n:ℝ)⁻¹ := by
  rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hn)]

/-- Fixed finite Euler completion has a negative, noncritical source pole. -/
theorem ccmPrimeDeficitEulerAction_pole_limit {P : ℕ} (hP : 0 < P) :
    Tendsto (fun T : ℝ => ccmPrimeDeficitEulerAction P T/(T*Real.exp T)) atTop
      (𝓝 (-(Real.eulerMascheroniConstant+1)*
        (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d:ℝ)/(d:ℝ))^2)) := by
  have hlin := tendsto_finsetSum P.divisors (fun d _ =>
    (shift_pole_limit source_zero_pole (Real.log d)).const_mul (ArithmeticFunction.moebius d:ℝ))
  simp only [zero_mul, mul_zero, Finset.sum_const_zero] at hlin
  have hquad := ccmPrimeDeficitDivisorSource_finite_pair_pole_limit P.divisors
    (fun d => (ArithmeticFunction.moebius d:ℝ)) (fun d => Real.log d)
  have hmoment : (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d:ℝ)*Real.exp (-Real.log d)) =
      ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d:ℝ)/(d:ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [exp_neg_log_nat (Nat.pos_of_mem_divisors hd), div_eq_mul_inv]
  rw [hmoment] at hquad
  have h := (hlin.const_mul 2).sub hquad
  simp only [mul_zero, zero_sub, neg_mul] at h ⊢
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2*Real.log (P:ℝ))] with T hT
  rw [euler_action_eq hP hT]
  simp only [sub_div, mul_div_assoc, Finset.sum_div]

private theorem euler_moment_eq_totient {P : ℕ} (hP : 0 < P) :
    (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d:ℝ)/(d:ℝ)) =
      (P.totient:ℝ)/(P:ℝ) := by
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n => (n.totient:ℝ)) (g := fun n => (n:ℝ))).mp
      (fun n hn => by exact_mod_cast Nat.sum_totient n) P hP
  rw [Nat.sum_divisorsAntidiagonal (fun d e => (ArithmeticFunction.moebius d:ℝ)*(e:ℝ))] at hi
  have hPR : (P:ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  rw [← hi, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hdR]
  field_simp

/-- The obstruction is strictly present at every positive fixed Euler modulus. -/
theorem ccmPrimeDeficitEulerAction_not_exponential_bound {P : ℕ} (hP : 0 < P) :
    ¬ ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → |ccmPrimeDeficitEulerAction P T| ≤ C*Real.exp T := by
  rintro ⟨C,hC⟩
  have hzero := tendsto_nhds_unique (ccmPrimeDeficitEulerAction_pole_limit hP)
    (zero_pole_of_exponential_bound hC)
  rw [euler_moment_eq_totient hP] at hzero
  have hc : 0 < Real.eulerMascheroniConstant+1 := by
    have := Real.one_half_lt_eulerMascheroniConstant
    linarith
  have hm : 0 < (P.totient:ℝ)/(P:ℝ) := div_pos
    (by exact_mod_cast Nat.totient_pos.mpr hP) (by exact_mod_cast hP)
  have hneg : -(Real.eulerMascheroniConstant+1)*((P.totient:ℝ)/(P:ℝ))^2 < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos hc) (sq_pos_of_pos hm)
  linarith

private theorem deficit_exp_bound (T : ℝ) (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T| ≤ (Real.log 4+5)*Real.exp T := by
  have hc : 0 ≤ Real.log 4+5 := by have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); linarith
  have hpoint (t : ℝ) : |Real.exp t-Chebyshev.psi (Real.exp t)| ≤ (Real.log 4+5)*Real.exp t := by
    have hp := Chebyshev.psi_le_const_mul_self (Real.exp_pos t).le
    have h0 := Chebyshev.psi_nonneg (Real.exp t)
    have he := Real.exp_pos t
    have hl := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    apply abs_le.mpr
    constructor <;> nlinarith
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun t : ℝ => Real.exp t-Chebyshev.psi (Real.exp t))
    (g := fun t : ℝ => (Real.log 4+5)*Real.exp t) hT
    (Eventually.of_forall fun t _ => by rw [Real.norm_eq_abs]; exact hpoint t)
    ((Real.continuous_exp.const_mul _).intervalIntegrable 0 T)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero] at hb
  change |ccmLogChebyshevDeficitPrimitive T| ≤ _ at hb
  linarith

/-- The unchanged signed source itself excites the fixed Euler renewal pole. -/
theorem ccmPrimeDeficitEulerSignedRenewal_pole_limit {P : ℕ} (hP : 0 < P) :
    Tendsto (fun T : ℝ =>
      logarithmicWeightedDilation (ccmEulerRough P)
        (logarithmicWeightedDilation (ccmEulerRough P) ccmLogChebyshevDeficitPrimitive) T /
          (T*Real.exp T)) atTop
      (𝓝 ((Real.eulerMascheroniConstant+1)*((P.totient:ℝ)/(P:ℝ))^2)) := by
  have h := (zero_pole_of_exponential_bound deficit_exp_bound).sub
    (ccmPrimeDeficitEulerAction_pole_limit hP)
  rw [euler_moment_eq_totient hP] at h
  simp only [zero_sub, neg_mul, neg_neg] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  rw [← ccmLogChebyshevDeficitPrimitive_sub_eulerAction_eq_renewal P hT, sub_div]

/-- No fixed positive Euler modulus gives an exponential budget for its actual signed renewal. -/
theorem ccmPrimeDeficitEulerSignedRenewal_not_exponential_bound (P : ℕ) :
    ¬ ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
      |logarithmicWeightedDilation (ccmEulerRough (P+1))
        (logarithmicWeightedDilation (ccmEulerRough (P+1)) ccmLogChebyshevDeficitPrimitive) T| ≤
          C*Real.exp T := by
  rintro ⟨C,hC⟩
  have hzero := tendsto_nhds_unique
    (ccmPrimeDeficitEulerSignedRenewal_pole_limit (Nat.succ_pos P))
    (zero_pole_of_exponential_bound hC)
  have hc : 0 < Real.eulerMascheroniConstant+1 := by
    have := Real.one_half_lt_eulerMascheroniConstant
    linarith
  have hm : 0 < ((P+1).totient:ℝ)/(P+1:ℕ) := div_pos
    (by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos P)) (by positivity)
  exact (ne_of_gt (mul_pos hc (sq_pos_of_pos hm))) hzero

end RHTower
