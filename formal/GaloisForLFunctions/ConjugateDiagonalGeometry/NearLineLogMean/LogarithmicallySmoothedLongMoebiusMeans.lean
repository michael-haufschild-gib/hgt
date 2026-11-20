import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.RecoveringLogMultipliersByShortVerticalTranslations
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MaximalPrefixesOfTheLongMoebiusSection
import GaloisForLFunctions.RHTower.FirstMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Undoing logarithmic smoothing of long Möbius polynomials

On the nonconstant terms the normalized inverse logarithm has multiplier
log(2)/log(n). Vertical differentiation removes one power exactly. Finite
one-sided differences estimate that derivative on the original height
interval, including when the Dirichlet cutoff is much larger than the height.
-/

noncomputable section
open Finset Filter Topology Complex MeasureTheory
open _root_.HTGeometry
open GaloisForLFunctions.MultiscaleMollifiedZetaField
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def logRatio (n : ℕ) := Real.log 2/Real.log (max 2 n : ℕ)

private theorem logRatio_antitone : Antitone logRatio := by
  intro a b hab
  have htwo : (1:ℝ)<(max 2 a:ℕ) := by exact_mod_cast (show 1 < max 2 a by omega)
  exact div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (Real.log_pos htwo)
    (Real.log_le_log (by positivity) (Nat.cast_le.mpr (max_le_max_left _ hab)))

private theorem logRatio_one : logRatio 1=1 := by
  simp [logRatio,div_self (Real.log_pos (by norm_num : (1:ℝ)<2)).ne']

private theorem logRatio_nonneg (n : ℕ) : 0 ≤ logRatio n :=
  div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ max 2 n by omega)))

private theorem logRatio_le_one {n : ℕ} (hn : 1 ≤ n) : logRatio n ≤ 1 :=
  (logRatio_antitone hn).trans_eq logRatio_one

/-- All orders retain the constant mode. At n≥2 each integration divides
the coefficient by log(n)/log(2). -/
def logDampedMoebius (m N : ℕ) (t : ℝ) := _root_.RHTower.edPoly
  (fun n => ((logRatio n:ℂ)^m)*_root_.RHTower.mobCoeff n) (Icc 1 N) (linePoint t)

theorem logDampedMoebius_zero (N : ℕ) (t : ℝ) :
    logDampedMoebius 0 N t = moebiusPoly N (linePoint t) := by
  simp only [logDampedMoebius,pow_zero,one_mul,moebiusPoly]

private def dampedAmplitude (m n : ℕ) : ℂ :=
  (logRatio n:ℂ)^m*_root_.RHTower.mobCoeff n*((n:ℝ)^(-(1/2:ℝ)):ℝ)

private theorem damped_packet (m N : ℕ) : logDampedMoebius m N =
    genPoly (dampedAmplitude m) (fun n => -Real.log n) (Icc 1 N) := by
  funext t
  unfold logDampedMoebius _root_.RHTower.edPoly genPoly
  apply sum_congr rfl
  intro n hn
  have hz : linePoint t = _root_.RHTower.linePt t := by
    norm_num [linePoint,_root_.RHTower.linePt]
  change ((logRatio n:ℂ)^m*_root_.RHTower.mobCoeff n)*((n:ℝ):ℂ)^(-linePoint t) = _
  rw [hz,Complex.ofReal_natCast,_root_.RHTower.natCast_cpow_neg_linePt n (mem_Icc.mp hn).1 t]
  have he : -(I*(Real.log n:ℂ))*(t:ℂ) = I*((-Real.log n:ℝ)*t) := by push_cast; ring
  simp only [he,dampedAmplitude,Complex.ofReal_neg,mul_assoc]

private theorem dampedAmplitude_le_weight (m n : ℕ) (hn1 : 1 ≤ n) :
    ‖dampedAmplitude m n‖ ≤ logRatio n^m := by
  have hmu := _root_.RHTower.norm_mobCoeff_le n
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr hn1) (by norm_num : -(1/2:ℝ) ≤ 0)
  rw [dampedAmplitude,norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (logRatio_nonneg n),Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact (mul_le_of_le_one_right (mul_nonneg (pow_nonneg (logRatio_nonneg n) _) (norm_nonneg _)) hpow).trans
    (mul_le_of_le_one_right (pow_nonneg (logRatio_nonneg n) _) hmu)

private theorem damped_mass (m N : ℕ) : (∑ n ∈ Icc 1 N, ‖dampedAmplitude m n‖) ≤ N := by
  have h (n : ℕ) (hn : n ∈ Icc 1 N) : ‖dampedAmplitude m n‖ ≤ 1 :=
    (dampedAmplitude_le_weight m n (mem_Icc.mp hn).1).trans
      (pow_le_one₀ (logRatio_nonneg n) (logRatio_le_one (mem_Icc.mp hn).1))
  simpa [Nat.card_Icc] using sum_le_sum h

/-- All orders have the same vertical frequencies. Their coefficient masses
are bounded by the cutoff uniformly in the smoothing order. -/
theorem exists_logDampedMoebius_packet (m N : ℕ) :
    ∃ a : ℕ → ℂ, logDampedMoebius m N = genPoly a (fun n => -Real.log n) (Icc 1 N) ∧
      (∑ n ∈ Icc 1 N, ‖a n‖) ≤ N :=
  ⟨dampedAmplitude m,damped_packet m N,damped_mass m N⟩

theorem logDampedMoebius_le_prefix_maximum (m N : ℕ) (t : ℝ) :
    ‖logDampedMoebius m N t‖ ≤ moebiusPrefixMaximum N t := by
  let w (n : ℕ) := logRatio n^m
  have H := (moebius_prefix_maximum_iff_taper_bound N t _).mp le_rfl w
    (fun n => pow_nonneg (logRatio_nonneg n) _) (fun i j hij =>
      pow_le_pow_left₀ (logRatio_nonneg j) (logRatio_antitone hij) _)
    (by simp [w,logRatio_one])
  have hi : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc,mem_Icc]; omega
  simpa only [hi,w,Complex.ofReal_pow,logDampedMoebius,_root_.RHTower.edPoly] using H

/-- Exact differentiation of the smoothed section, including its missing
constant coefficient. -/
theorem deriv_logDampedMoebius (m : ℕ) {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    deriv (logDampedMoebius (m+1) N) t =
      (-(Real.log 2:ℂ)*I)*(logDampedMoebius m N t-1) := by
  rw [damped_packet,deriv_genPoly_as_packet,damped_packet]
  have h1 : (∑ n ∈ Icc 1 N, if n=1 then (1:ℂ) else 0) = 1 := by simp [hN]
  unfold genPoly
  conv_rhs => arg 2; rhs; rw [←h1]
  rw [←sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro n hn
  by_cases he : n=1
  · subst n; simp [dampedAmplitude,logRatio_one,_root_.RHTower.mobCoeff]
  have hn2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  have hc : (logRatio n:ℂ)*(Real.log n:ℂ)=(Real.log 2:ℂ) := by
    unfold logRatio
    rw [max_eq_right hn2,Complex.ofReal_div,div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hlog)]
  rw [if_neg he,sub_zero]
  simp only [dampedAmplitude,pow_succ,Complex.ofReal_neg]
  linear_combination -I*((logRatio n:ℂ)^m*_root_.RHTower.mobCoeff n*
    ((n:ℝ)^(-(1/2:ℝ)):ℝ)*cexp (I*(-(Real.log n:ℂ)*(t:ℂ))))*hc

/-- Every fixed polynomial cutoff length admits a subpower comparison
on the very same window, uniformly in the logarithmic smoothing order. -/
theorem eventually_logDamped_derivative_energy {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ m : ℕ,
    (∫ t in (1:ℝ)..T, ‖deriv (logDampedMoebius m ⌊T^θ⌋₊) t‖^2) ≤
      C*T^η*(∫ t in (1:ℝ)..T, ‖logDampedMoebius m ⌊T^θ⌋₊ t‖^2)+8 := by
  let r := η/4
  have hr : 0 < r := div_pos hη (by norm_num)
  obtain ⟨d,hd⟩ := exists_nat_ge (θ/r)
  obtain ⟨l,hl⟩ := exists_nat_ge (1/r)
  let P := translationLog (d+l+1)
  refine ⟨4*P.support.card*(∑ j ∈ P.support, ‖P.coeff j‖^2),by positivity,?_⟩
  have hlog := (isLittleO_log_rpow_atTop hr).bound (inv_pos.mpr hθ)
  filter_upwards [eventually_ge_atTop (1:ℝ), (tendsto_rpow_atTop hr).eventually_ge_atTop 2,
    eventually_ge_atTop (2*(P.natDegree:ℝ)+1),hlog] with T hT hx hfit hlogT
  intro m
  let X := T^r
  let N := ⌊T^θ⌋₊
  have hT0 := zero_lt_one.trans_le hT
  have hN : (N:ℝ) ≤ T^θ := Nat.floor_le (by positivity)
  have hpower (i : ℕ) : X^i=T^(r*(i:ℝ)) := by rw [Real.rpow_mul hT0.le,Real.rpow_natCast]
  have hmass : (∑ n ∈ Icc 1 N, ‖dampedAmplitude m n‖) ≤ X^d := by
    rw [hpower]
    exact (damped_mass m N).trans (hN.trans (Real.rpow_le_rpow_of_exponent_le hT
      (by simpa only [mul_comm] using (div_le_iff₀ hr).mp hd)))
  have hTsize : T ≤ X^l := by
    rw [hpower]
    calc T = T^(1:ℝ) := (Real.rpow_one T).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by
        simpa only [mul_comm] using (div_le_iff₀ hr).mp hl)
  have hf (n : ℕ) (hn : n ∈ Icc 1 N) : |-Real.log n| ≤ X := by
    have hn1 : (1:ℝ) ≤ n := Nat.one_le_cast.mpr (mem_Icc.mp hn).1
    rw [abs_neg,abs_of_nonneg (Real.log_nonneg hn1)]
    have hh := Real.log_le_log (zero_lt_one.trans_le hn1) ((Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hN)
    rw [Real.log_rpow hT0] at hh
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hT),abs_of_nonneg (Real.rpow_nonneg hT0.le _)] at hlogT
    exact hh.trans (by calc θ*Real.log T ≤ θ*(θ⁻¹*X) := mul_le_mul_of_nonneg_left hlogT hθ.le
                            _ = X := by field_simp)
  have hfour : X^4=T^η := by rw [hpower]; congr 1; dsimp [r]; ring
  have H := derivative_energy_of_polynomial_size d l (dampedAmplitude m) (fun n => -Real.log n)
    (Icc 1 N) (X:=X) hx hT hTsize hf hmass (fun j hj => by
      have hj' : (j:ℝ) ≤ P.natDegree := by exact_mod_cast Polynomial.le_natDegree_of_mem_supp j hj
      linarith only [hj',hfit])
  rw [hfour] at H
  simpa only [P,N,damped_packet] using H

private theorem damped_cont (m N : ℕ) : Continuous (logDampedMoebius m N) := by
  rw [damped_packet]; unfold genPoly; fun_prop

private theorem damped_deriv_cont (m N : ℕ) : Continuous (deriv (logDampedMoebius m N)) := by
  rw [damped_packet,deriv_genPoly_as_packet]; unfold genPoly; fun_prop

/-- Removing one inverse logarithm replaces it by the actual derivative
plus the stationary mode. -/
theorem logDamped_energy_le_derivative (m : ℕ) {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in (1:ℝ)..T, ‖logDampedMoebius m N t‖^2) ≤ 2*(T-1)+
      (2/(Real.log 2)^2)*(∫ t in (1:ℝ)..T, ‖deriv (logDampedMoebius (m+1) N) t‖^2) := by
  have hL := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hpt (t : ℝ) : ‖logDampedMoebius m N t‖^2 ≤ 2+
      (2/(Real.log 2)^2)*‖deriv (logDampedMoebius (m+1) N) t‖^2 := by
    let z := logDampedMoebius m N t
    have hz : ‖z‖ ≤ ‖z-1‖+1 := by simpa only [norm_one] using norm_le_norm_sub_add z 1
    have H := pow_le_pow_left₀ (norm_nonneg _) hz 2
    calc ‖z‖^2 ≤ 2+2*‖z-1‖^2 := by nlinarith only [H,sq_nonneg (‖z-1‖-1)]
      _ = _ := by
        rw [deriv_logDampedMoebius m hN,norm_mul,norm_mul,norm_neg,norm_I,mul_one,
          Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL,mul_pow]
        dsimp only [z]
        field_simp
  have hc := (damped_deriv_cont (m+1) N).norm.pow 2
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hT
    (f:=fun t => ‖logDampedMoebius m N t‖^2)
    (g:=fun t => 2+(2/(Real.log 2)^2)*‖deriv (logDampedMoebius (m+1) N) t‖^2)
    (((damped_cont m N).norm.pow 2).intervalIntegrable _ _)
    ((continuous_const.add (hc.const_mul (2/(Real.log 2)^2))).intervalIntegrable _ _)
    (fun t _ => hpt t)
  rw [intervalIntegral.integral_add (f:=fun _ : ℝ => (2:ℝ))
    (g:=fun t => (2/(Real.log 2)^2)*‖deriv (logDampedMoebius (m+1) N) t‖^2)
    intervalIntegrable_const ((hc.const_mul _).intervalIntegrable _ _),intervalIntegral.integral_const,
    smul_eq_mul,intervalIntegral.integral_const_mul,mul_comm (T-1)] at hi
  exact hi

/-- The length and the interval of observation are fixed before taking
the mean; the polynomial inside the integral has that single cutoff. -/
def logDampedMoment (m : ℕ) (θ T : ℝ) :=
  ∫ t in (1:ℝ)..T, ‖logDampedMoebius m ⌊T^θ⌋₊ t‖^2

private theorem moment_nonneg (m : ℕ) (θ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    0 ≤ logDampedMoment m θ T :=
  intervalIntegral.integral_nonneg hT fun _ _ => sq_nonneg _

/-- Removing one inverse logarithm costs an arbitrarily small power of
the observation height. All orders share the same constants and heights. -/
theorem adjacent_logDamped_moments {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ T : ℝ in atTop, ∀ m : ℕ,
      logDampedMoment m θ T ≤ A*(T+T^η*logDampedMoment (m+1) θ T) := by
  obtain ⟨C,hC,H⟩ := eventually_logDamped_derivative_energy hθ hη
  let D : ℝ := 2/(Real.log 2)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨2+8*D+D*C,by positivity,?_⟩
  filter_upwards [H,eventually_ge_atTop (1:ℝ)] with T hder hT
  intro m
  have hN := (Nat.one_le_floor_iff (T^θ)).mpr (Real.one_le_rpow hT hθ.le)
  let Y := T^η*logDampedMoment (m+1) θ T
  have hY : 0 ≤ Y := mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hT) _) (moment_nonneg _ _ hT)
  calc logDampedMoment m θ T ≤ 2*(T-1)+D*(C*Y+8) := by
         apply (logDamped_energy_le_derivative m hN hT).trans
         exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
           (by simpa only [Y,logDampedMoment,mul_assoc] using hder (m+1)) hD)
    _ ≤ (2+8*D)*T+D*C*Y := by nlinarith only [mul_nonneg hD (sub_nonneg.mpr hT)]
    _ ≤ _ := by
      change _ ≤ (2+8*D+D*C)*(T+Y)
      nlinarith only [mul_nonneg (by positivity : 0 ≤ 2+8*D) hY,
        mul_nonneg (mul_nonneg hD hC) (zero_le_one.trans hT)]

/-- Cofinal polynomial bounds with length slope 2β. Heights may depend
on the length exponent. -/
def cofinalLogDampedBound (m : ℕ) (β : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∃ᶠ T : ℝ in atTop, logDampedMoment m θ T ≤ C*T^(K+2*β*θ)

/-- Iterating a one-step energy comparison over consecutive orders. -/
theorem iterate_energy_step (J : ℕ → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hs : ∀ m, J m ≤ a*J (m+1)) (m : ℕ) : J 0 ≤ a^m*J m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc J 0 ≤ a^m*J m := ih
      _ ≤ a^m*(a*J (m+1)) := mul_le_mul_of_nonneg_left (hs m) (pow_nonneg ha _)
      _ = _ := by rw [pow_succ,mul_assoc]

/-- Any bounded number of integrations can be undone on one fixed
observation interval. The power of T is independent of the order cap. -/
theorem bounded_logDamped_recovery {θ : ℝ} (hθ : 0 < θ) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ m ≤ M,
      logDampedMoment 0 θ T ≤ C*T*(T+logDampedMoment m θ T) := by
  let η : ℝ := 1/((M:ℝ)+1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A,hA,H⟩ := adjacent_logDamped_moments hθ hη
  refine ⟨(1+A)^M,by positivity,?_⟩
  filter_upwards [H,eventually_ge_atTop (1:ℝ)] with T hstep hT
  let U := T^η
  let J (m : ℕ) := T+logDampedMoment m θ T
  have hT0 := zero_le_one.trans hT
  have hU : 1 ≤ U := Real.one_le_rpow hT hη.le
  have hJ (m : ℕ) : 0 ≤ J m := add_nonneg hT0 (moment_nonneg _ _ hT)
  have hB : 1 ≤ (1+A)*U := one_le_mul_of_one_le_of_one_le (by linarith only [hA]) hU
  have huT : T ≤ U*T := le_mul_of_one_le_left hT0 hU
  have hs (m : ℕ) : J m ≤ ((1+A)*U)*J (m+1) := by
    have h1 : T ≤ U*J (m+1) := huT.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (moment_nonneg _ _ hT)) (zero_le_one.trans hU))
    have h2 : T+U*logDampedMoment (m+1) θ T ≤ U*J (m+1) := by
      dsimp only [J]; rw [mul_add]; exact add_le_add huT le_rfl
    calc J m ≤ T+A*(T+U*logDampedMoment (m+1) θ T) := add_le_add le_rfl (hstep m)
      _ ≤ U*J (m+1)+A*(U*J (m+1)) := add_le_add h1 (mul_le_mul_of_nonneg_left h2 hA)
      _ = _ := by ring
  have huM : U^M ≤ T := by
    rw [show U^M=T^(η*(M:ℝ)) by rw [Real.rpow_mul hT0,Real.rpow_natCast]]
    refine (Real.rpow_le_rpow_of_exponent_le hT (z:=(1:ℝ)) ?_).trans_eq (Real.rpow_one T)
    dsimp [η]
    rw [one_div,mul_comm,←div_eq_mul_inv,div_le_one (by positivity)]
    linarith
  intro m hm
  calc logDampedMoment 0 θ T ≤ J 0 := le_add_of_nonneg_left hT0
    _ ≤ ((1+A)*U)^m*J m := iterate_energy_step J (zero_le_one.trans hB) hs m
    _ ≤ ((1+A)*U)^M*J m := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hm) (hJ m)
    _ ≤ (1+A)^M*T*J m := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huM (by positivity)) (hJ m)

/-- Each length exponent may choose its own arbitrary finite cap.
Within that cap the smoothing order can be selected anew at each height. -/
theorem adaptive_logDamped_iff_zero_width (cap : ℝ → ℕ) (order : ∀ θ : ℝ, ℝ → Fin (cap θ+1))
    {β : ℝ} (hβ : 0 ≤ β) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∃ᶠ T : ℝ in atTop, logDampedMoment (order θ T).val θ T ≤ B*T^(K+2*β*θ)) ↔
    GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth ≤ β := by
  constructor
  · rintro ⟨K,hK,H⟩
    apply zetaZeroWidth_le_of_cofinal_pure_moebius_slope hβ (show 0 ≤ K+2 by positivity)
    intro θ₀ hθ₀
    obtain ⟨θ,hθ,B,hB,h⟩ := H θ₀ hθ₀
    have hθpos := hθ₀.trans_le hθ
    obtain ⟨C,hC,hrec⟩ := bounded_logDamped_recovery hθpos (cap θ)
    refine ⟨θ,hθ,C*(1+B),by positivity,(h.and_eventually (hrec.and (eventually_ge_atTop (1:ℝ)))).mono ?_⟩
    rintro T ⟨hb,hstep,hT⟩
    let V := T^(K+2*β*θ)
    have hV : 1 ≤ V := Real.one_le_rpow hT (by positivity)
    have ht := zero_le_one.trans hT
    have hpow : T^(K+2+2*β*θ)=T^2*V := by
      rw [show K+2+2*β*θ=2+(K+2*β*θ) by ring,Real.rpow_add (zero_lt_one.trans_le hT),Real.rpow_two]
    simp_rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly,←logDampedMoebius_zero]
    calc logDampedMoment 0 θ T ≤ C*T*(T+logDampedMoment (order θ T).val θ T) :=
           hstep _ (Nat.le_of_lt_succ (order θ T).isLt)
      _ ≤ C*T*(T*V+B*(T*V)) := mul_le_mul_of_nonneg_left (add_le_add
        (le_mul_of_one_le_right ht hV) (hb.trans (mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_left (zero_le_one.trans hV) hT) hB))) (mul_nonneg hC ht)
      _ = _ := by rw [hpow]; ring
  · intro hwidth
    obtain ⟨K,hK,H⟩ := (zetaZeroWidth_iff_cofinal_maximal_moebius_slope hβ).mp hwidth
    refine ⟨K,hK,fun θ₀ hθ₀ => ?_⟩
    obtain ⟨θ,hθ,B,hB,h⟩ := H θ₀ hθ₀
    refine ⟨θ,hθ,B,hB,(h.and_eventually (eventually_ge_atTop (1:ℝ))).mono fun T ⟨hb,hT⟩ => ?_⟩
    exact (intervalIntegral.integral_mono_on hT (((damped_cont _ _).norm.pow 2).intervalIntegrable _ _)
      (((continuous_moebiusPrefixMaximum _).pow 2).intervalIntegrable _ _) fun t _ =>
        pow_le_pow_left₀ (norm_nonneg _) (logDampedMoebius_le_prefix_maximum _ _ t) 2).trans hb

/-- Every fixed integral order of logarithmic smoothing preserves the
exact length slope in the sparse-height Möbius criterion. -/
theorem cofinal_logDamped_iff_zero_width (m : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    cofinalLogDampedBound m β ↔ GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth ≤ β :=
  adaptive_logDamped_iff_zero_width (fun _ => m) (fun _ _ => ⟨m,Nat.lt_succ_self m⟩) hβ

theorem cofinal_logDamped_iff_riemannHypothesis (m : ℕ) :
    cofinalLogDampedBound m 0 ↔ RiemannHypothesis := by
  rw [cofinal_logDamped_iff_zero_width m le_rfl,
    RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ←GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl]

private theorem norm_mode (a : ℂ) (n : ℕ) (t : ℝ) :
    ‖a*cexp (I*((-Real.log n:ℝ)*t))‖ = ‖a‖ := by
  have he : I*((-Real.log n:ℝ)*t) = (((-Real.log n*t:ℝ):ℂ)*I) := by push_cast; ring
  rw [he,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]

private theorem norm_damped_le_length (m N : ℕ) (t : ℝ) : ‖logDampedMoebius m N t‖ ≤ N := by
  rw [damped_packet]; unfold genPoly
  refine (norm_sum_le _ _).trans ?_
  simpa only [norm_mode] using damped_mass m N

private theorem logDamped_difference_at_two (m : ℕ) {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    logDampedMoebius m N t-moebiusPoly 2 (linePoint t) =
      ∑ n ∈ Icc 3 N, dampedAmplitude m n*cexp (I*((-Real.log n:ℝ)*t)) := by
  have htwo : logDampedMoebius m 2 t = moebiusPoly 2 (linePoint t) := by
    unfold logDampedMoebius moebiusPoly _root_.RHTower.edPoly
    apply sum_congr rfl
    intro n hn
    have hw : logRatio n = 1 := by
      rw [logRatio,max_eq_left (mem_Icc.mp hn).2,Nat.cast_ofNat,div_self (Real.log_pos (by norm_num)).ne']
    simp only [hw,Complex.ofReal_one,one_pow,one_mul]
  rw [←htwo,damped_packet,damped_packet]
  have hsub : Icc 1 2 ⊆ Icc 1 N := fun n hn => mem_Icc.mpr ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans hN⟩
  let f (n : ℕ) := dampedAmplitude m n*cexp (I*((-Real.log n:ℝ)*t))
  change (∑ n ∈ Icc 1 N, f n)-(∑ n ∈ Icc 1 2, f n) = _
  rw [←sum_sdiff_eq_sub hsub]
  have hi : Icc 1 N \ Icc 1 2 = Icc 3 N := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_sdiff,Finset.mem_Icc]
    omega
  rw [hi]

/-- Absolute coefficient mass outside the two stationary-size modes. -/
def logDampedTailMass (m N : ℕ) := ∑ n ∈ Icc 3 N, ‖dampedAmplitude m n‖

theorem logDamped_tail_mass_formula (m N : ℕ) :
    logDampedTailMass m N = ∑ n ∈ Icc 3 N, ((ArithmeticFunction.moebius n:ℤ):ℝ)^2 *
      (n:ℝ)^(-(1/2:ℝ))*(Real.log 2/Real.log n)^m := by
  unfold logDampedTailMass
  apply sum_congr rfl
  intro n hn
  have hn2 : 2 ≤ n := (by have := (mem_Icc.mp hn).1; omega)
  have hmu : |(ArithmeticFunction.moebius n:ℤ)| = (ArithmeticFunction.moebius n:ℤ)^2 := by
    rw [ArithmeticFunction.abs_moebius,ArithmeticFunction.moebius_sq]
  rw [dampedAmplitude,norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (logRatio_nonneg n),_root_.RHTower.mobCoeff,Complex.norm_intCast,←Int.cast_abs,hmu,Int.cast_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    logRatio,max_eq_right hn2]
  ring

theorem logDamped_two_mode_le_tail_mass (m : ℕ) {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    ‖logDampedMoebius m N t-moebiusPoly 2 (linePoint t)‖ ≤ logDampedTailMass m N := by
  rw [logDamped_difference_at_two m hN]
  simpa only [logDampedTailMass,norm_mode] using norm_sum_le (Icc 3 N)
    (fun n => dampedAmplitude m n*cexp (I*((-Real.log n:ℝ)*t)))

/-- The actual observed moment after the tail has absolute mass at most b. -/
theorem logDampedMoment_le_of_tail_mass (m : ℕ) {θ T b : ℝ} (hT : 1 ≤ T)
    (hN : 2 ≤ ⌊T^θ⌋₊) (hb : logDampedTailMass m ⌊T^θ⌋₊ ≤ b) :
    logDampedMoment m θ T ≤ (2+b)^2*(T-1) := by
  let N := ⌊T^θ⌋₊
  have hpt (t : ℝ) : ‖logDampedMoebius m N t‖^2 ≤ (2+b)^2 := by
    have htwo : ‖moebiusPoly 2 (linePoint t)‖ ≤ 2 := by
      simpa only [logDampedMoebius_zero,Nat.cast_ofNat] using norm_damped_le_length 0 2 t
    apply pow_le_pow_left₀ (norm_nonneg _)
    have H := (norm_le_norm_sub_add (logDampedMoebius m N t) (moebiusPoly 2 (linePoint t))).trans
      (add_le_add ((logDamped_two_mode_le_tail_mass m hN t).trans hb) htwo)
    linarith only [H]
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hT
    (f:=fun t => ‖logDampedMoebius m N t‖^2) (g:=fun _ => (2+b)^2)
    (((damped_cont m N).norm.pow 2).intervalIntegrable _ _) intervalIntegrable_const (fun t _ => hpt t)
  simpa only [logDampedMoment,intervalIntegral.integral_const,smul_eq_mul,mul_comm (T-1)] using hi

/-- When the order can grow with the cutoff, only the first two modes
survive. The approximation is uniform over the entire vertical line. -/
theorem logDamped_two_mode_error (m : ℕ) {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    ‖logDampedMoebius m N t-moebiusPoly 2 (linePoint t)‖ ≤
      (N:ℝ)*(Real.log 2/Real.log 3)^m := by
  apply (logDamped_two_mode_le_tail_mass m hN t).trans
  have H (n : ℕ) (hn : n ∈ Icc 3 N) : ‖dampedAmplitude m n‖ ≤ logRatio 3^m := by
    have h3 := (mem_Icc.mp hn).1
    exact (dampedAmplitude_le_weight m n (by omega)).trans
      (pow_le_pow_left₀ (logRatio_nonneg n) (logRatio_antitone h3) _)
  have hcard : ((Icc 3 N).card:ℝ) ≤ N := by
    exact_mod_cast (show (Icc 3 N).card ≤ N by rw [Nat.card_Icc]; omega)
  calc logDampedTailMass m N ≤ ∑ _n ∈ Icc 3 N, logRatio 3^m := sum_le_sum H
    _ = (Icc 3 N).card*logRatio 3^m := by simp
    _ ≤ _ := by simpa [logRatio] using mul_le_mul_of_nonneg_right hcard (pow_nonneg (logRatio_nonneg 3) m)

/-- A logarithmically growing order can force a uniform moment bound for
every cutoff, without any input about zeta zeros. -/
theorem logarithmic_order_moment_bound (m : ℕ) {θ T : ℝ} (hT : 1 ≤ T) (hN : 2 ≤ ⌊T^θ⌋₊)
    (hm : Real.log (⌊T^θ⌋₊:ℕ) ≤ (m:ℝ)*(-Real.log (Real.log 2/Real.log 3))) :
    logDampedMoment m θ T ≤ 9*(T-1) := by
  let N := ⌊T^θ⌋₊
  let q := Real.log 2/Real.log 3
  have hq : 0 < q := div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  have hNp : (0:ℝ)<N := Nat.cast_pos.mpr (by dsimp [N]; omega)
  have hsmall : (N:ℝ)*q^m ≤ 1 := by
    rw [←Real.exp_log hNp,←Real.rpow_natCast q m,Real.rpow_def_of_pos hq,←Real.exp_add,Real.exp_le_one_iff]
    change Real.log N ≤ (m:ℝ)*(-Real.log q) at hm
    linarith only [hm]
  have htwo (t : ℝ) : ‖moebiusPoly 2 (linePoint t)‖ ≤ 2 := by
    simpa only [logDampedMoebius_zero,Nat.cast_ofNat] using norm_damped_le_length 0 2 t
  have hpt (t : ℝ) : ‖logDampedMoebius m N t‖^2 ≤ 9 := by
    have h := (norm_le_norm_sub_add (logDampedMoebius m N t) (moebiusPoly 2 (linePoint t))).trans
      (add_le_add ((logDamped_two_mode_error m hN t).trans hsmall) (htwo t))
    exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (by norm_num)
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hT
    (f:=fun t => ‖logDampedMoebius m N t‖^2) (g:=fun _ => (9:ℝ))
    (((damped_cont m N).norm.pow 2).intervalIntegrable _ _) intervalIntegrable_const (fun t _ => hpt t)
  simpa only [logDampedMoment,intervalIntegral.integral_const,smul_eq_mul,mul_comm (T-1)] using hi

/-- Explicit order at which the moment is bounded by nine times the
window length for every length exponent and every height. -/
theorem cutoff_selected_log_order_bound (θ T : ℝ) (hT : 1 ≤ T) :
    let N := ⌊T^θ⌋₊
    let m := ⌈Real.log N/(-Real.log (Real.log 2/Real.log 3))⌉₊
    logDampedMoment m θ T ≤ 9*(T-1) := by
  intro N m
  by_cases hN : 2 ≤ N
  · apply logarithmic_order_moment_bound m hT hN
    have h0 : 0 < Real.log 2/Real.log 3 :=
      div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
    have h1 : Real.log 2/Real.log 3 < 1 := (div_lt_one (Real.log_pos (by norm_num))).mpr
      (Real.log_lt_log (by norm_num) (by norm_num))
    exact (div_le_iff₀ (neg_pos.mpr (Real.log_neg h0 h1))).mp (Nat.le_ceil _)
  · have hlen : (N:ℝ) ≤ 1 := by exact_mod_cast (show N ≤ 1 by omega)
    have hpt (t : ℝ) : ‖logDampedMoebius m N t‖^2 ≤ 9 := by
      have hh := pow_le_pow_left₀ (norm_nonneg _) ((norm_damped_le_length m N t).trans hlen) 2
      exact hh.trans (by norm_num)
    have hi := intervalIntegral.integral_mono_on (μ:=volume) hT
      (f:=fun t => ‖logDampedMoebius m N t‖^2) (g:=fun _ => (9:ℝ))
      (((damped_cont m N).norm.pow 2).intervalIntegrable _ _) intervalIntegrable_const (fun t _ => hpt t)
    simpa only [logDampedMoment,intervalIntegral.integral_const,smul_eq_mul,mul_comm (T-1)] using hi

#print axioms logDamped_tail_mass_formula
#print axioms logDamped_two_mode_le_tail_mass
#print axioms logDamped_two_mode_error
#print axioms logarithmic_order_moment_bound
#print axioms cutoff_selected_log_order_bound
#print axioms logDampedMoebius_le_prefix_maximum
#print axioms deriv_logDampedMoebius
#print axioms eventually_logDamped_derivative_energy
#print axioms adjacent_logDamped_moments
#print axioms bounded_logDamped_recovery
#print axioms adaptive_logDamped_iff_zero_width
#print axioms cofinal_logDamped_iff_zero_width
#print axioms cofinal_logDamped_iff_riemannHypothesis

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
