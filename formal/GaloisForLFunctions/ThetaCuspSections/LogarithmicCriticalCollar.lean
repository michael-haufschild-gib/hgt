import GaloisForLFunctions.ThetaCuspSections.QuantitativeCriticalCollar
import GaloisForLFunctions.RHTower.XiHadamardSharpRegion

/-!
# Logarithmic critical collars for all finite theta ranks

The zero-free logarithmic region makes the Fourier current nonnegative on a
finite frequency window. A fixed positive core controls polynomial squares;
uniform exponential decay pays the remaining signed tail. A cubic frequency
cutoff turns this comparison into an aperture collar of logarithmic width.
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Matrix Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar
open _root_.RHTower CriticalCollar QuantitativeCollar

/-- The zero-free logarithmic boundary gives a nonnegative current on a finite frequency window. -/
theorem current_nonneg_on_frequency_window {a T b : ℝ} (ha : 0 < a)
    (hregion : 1/2-1/58/Real.log (T+1/2) ≤ a) (hb : |b| ≤ T) :
    0 ≤ current a b := by
  let z : ℂ := (b:ℂ)-(a:ℂ)*I
  by_cases hXi : XiC z = 0
  · change 0 ≤ 2*((starRingEnd ℂ) (XiC z)*(-I*deriv XiC z)).re
    simp only [hXi,map_zero,zero_mul,Complex.zero_re,mul_zero,le_refl]
  have hre : (1/2+z*I).re = 1/2+a := by norm_num [z,Complex.mul_re,Complex.mul_im]
  have him : (1/2+z*I).im = b := by norm_num [z,Complex.mul_re,Complex.mul_im]
  have hx : 1/2 < (1/2+z*I).re := by rw [hre]; linarith only [ha]
  have hlog : 0 ≤ (logDeriv xi (1/2+z*I)).re := by
    rcases le_or_gt |b| 4 with hlo | hhi
    · exact re_logDeriv_xi_nonneg_of_abs_im_le_four hx (by rwa [him])
    · apply re_logDeriv_xi_nonneg_of_zeroFree_sharp hx (by rwa [him])
      rw [him,hre]
      have hbpos : 0 < |b|+1/2 := by positivity
      have hLb : 0 < Real.log (|b|+1/2) := Real.log_pos (by linarith only [hhi])
      have hlogs : Real.log (|b|+1/2) ≤ Real.log (T+1/2) :=
        Real.log_le_log hbpos (by linarith only [hb])
      have hLT : 0 < Real.log (T+1/2) := hLb.trans_le hlogs
      have hfrac : 1/58/Real.log (T+1/2) ≤ 1/58/Real.log (|b|+1/2) := by
        apply (div_le_div_iff₀ hLT hLb).mpr
        nlinarith only [hlogs]
      linarith only [hregion,hfrac]
  have hlogXi : 0 ≤ (logDeriv XiC z).im := by
    rw [logDeriv_XiC_eq_mul_I_logDeriv_xi]
    simpa using hlog
  change 0 ≤ 2*((starRingEnd ℂ) (XiC z)*(-I*deriv XiC z)).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im _ _ hXi,← logDeriv_apply]
  exact mul_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) hlogXi


/-- Uniform Xi and Xi-derivative strip bounds give exponential decay of the current. -/
private theorem current_uniform_exp : ∃ C : ℝ, 0 < C ∧
    ∀ a : ℝ, |a| ≤ 3/4 → ∀ b : ℝ,
      |current a b| ≤ C*Real.exp (-((Real.pi/4)*|b|)) := by
  let δ : ℝ := Real.pi/8
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδpi : 2*δ < Real.pi/2 := by dsimp only [δ]; linarith only [Real.pi_pos]
  obtain ⟨C₀,hC₀,h₀⟩ := exists_norm_XiC_horizontal_le
    (A:=3/4) (δ:=δ) (by norm_num) hδ hδpi
  obtain ⟨C₁,hC₁,h₁⟩ := exists_norm_XiC_deriv_horizontal_le
    (A:=3/4) (δ:=δ) (by norm_num) hδ hδpi
  refine ⟨2*C₀*C₁+1,by positivity,fun a ha b => ?_⟩
  let z : ℂ := (b:ℂ)-(a:ℂ)*I
  have hu : ‖XiC z‖ ≤ C₀*Real.exp (-(δ*|b|)) := by
    simpa only [z,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
      h₀ b (-a) (by simpa only [abs_neg] using ha)
  have hv : ‖deriv XiC z‖ ≤ C₁*Real.exp (-(δ*|b|)) := by
    simpa only [z,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
      h₁ b (-a) (by simpa only [abs_neg] using ha)
  have hprod := mul_le_mul hu hv (norm_nonneg _) (by positivity)
  have hcur : |current a b| ≤ 2*(‖XiC z‖*‖deriv XiC z‖) := by
    unfold current
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [norm_mul,Complex.norm_conj,norm_neg,Complex.norm_I,one_mul] using
      Complex.abs_re_le_norm ((starRingEnd ℂ) (XiC z)*(-I*deriv XiC z))
  calc |current a b| ≤ 2*(‖XiC z‖*‖deriv XiC z‖) := hcur
    _ ≤ 2*((C₀*Real.exp (-(δ*|b|)))*(C₁*Real.exp (-(δ*|b|)))) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (2*C₀*C₁)*Real.exp (-((Real.pi/4)*|b|)) := by
      rw [show -((Real.pi/4)*|b|)=-(δ*|b|)+-(δ*|b|) by dsimp only [δ]; ring,
        Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.exp_pos _).le

/-- The part of a raw moment outside a symmetric frequency window. -/
private def tailMoment (a T : ℝ) (k : ℕ) : ℝ :=
  ∫ b : ℝ, {b : ℝ | T < |b|}.indicator (fun b => b^k*current a b) b

/-- One exponential tail estimate controls every moment order with factorial growth. -/
private theorem tailMoment_factorial_exp : ∃ M K : ℝ, 0 < M ∧ 1 ≤ K ∧
    ∀ a : ℝ, |a| ≤ 3/4 → ∀ T : ℝ, 0 ≤ T → ∀ k : ℕ,
      |tailMoment a T k| ≤ M*K^k*(k.factorial:ℝ)*Real.exp (-((Real.pi/8)*T)) := by
  obtain ⟨C,hC,hcurrent⟩ := current_uniform_exp
  let E : ℝ→ℝ := fun b => Real.exp (-((Real.pi/16)*|b|))
  have hE : Integrable E :=
    integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic (by positivity)
  let I₀ : ℝ := ∫ b : ℝ, E b
  have hI₀ : 0 ≤ I₀ := integral_nonneg fun b => (Real.exp_pos _).le
  let M : ℝ := C*(I₀+1)
  let K : ℝ := max 1 (16/Real.pi)
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨M,K,hM,le_max_left _ _,fun a ha T _hT k => ?_⟩
  let S : Set ℝ := {b : ℝ | T < |b|}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hi : Integrable (S.indicator (fun b : ℝ => b^k*current a b)) :=
    (raw_integrable a (ha.trans_lt (by norm_num)) k).indicator hS
  let B : ℝ := C*Real.exp (-((Real.pi/8)*T))*(16/Real.pi)^k*(k.factorial:ℝ)
  have hmajor (b : ℝ) : |S.indicator (fun b : ℝ => b^k*current a b) b| ≤ B*E b := by
    by_cases hb : b∈S
    · rw [Set.indicator_of_mem hb,abs_mul,abs_pow]
      have hbT : T ≤ |b| := hb.le
      have hexp : Real.exp (-((Real.pi/8)*|b|)) ≤ Real.exp (-((Real.pi/8)*T)) :=
        Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos,hbT])
      have h := mul_le_mul_of_nonneg_left (hcurrent a ha b) (pow_nonneg (abs_nonneg b) k)
      have hpow := pow_abs_mul_exp_neg_le (by positivity : (0:ℝ) < Real.pi/8) k b
      calc |b|^k*|current a b| ≤ |b|^k*(C*Real.exp (-((Real.pi/4)*|b|))) := h
        _ = C*Real.exp (-((Real.pi/8)*|b|))*(|b|^k*Real.exp (-((Real.pi/8)*|b|))) := by
          rw [show -((Real.pi/4)*|b|)=-((Real.pi/8)*|b|)+-((Real.pi/8)*|b|) by ring,
            Real.exp_add]
          ring
        _ ≤ (C*Real.exp (-((Real.pi/8)*T)))*
            ((2/(Real.pi/8))^k*(k.factorial:ℝ)*Real.exp (-(((Real.pi/8)/2)*|b|))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp hC.le) hpow (by positivity) (by positivity)
        _ = B*E b := by
          dsimp only [B,E]
          rw [show (2:ℝ)/(Real.pi/8)=16/Real.pi by ring,
            show (Real.pi/8)/2=Real.pi/16 by ring]
          ring
    · rw [Set.indicator_of_notMem hb,abs_zero]
      positivity
  have hnorm : Integrable (fun b : ℝ => |S.indicator (fun b : ℝ => b^k*current a b) b|) := by
    simpa only [Real.norm_eq_abs] using hi.norm
  have hle := integral_mono hnorm (hE.const_mul B) hmajor
  rw [integral_const_mul] at hle
  have hn : |tailMoment a T k| ≤ B*I₀ := by
    change |∫ b : ℝ, S.indicator (fun b : ℝ => b^k*current a b) b| ≤ _
    exact abs_integral_le_integral_abs.trans hle
  have hK : (16/Real.pi)^k ≤ K^k := pow_le_pow_left₀ (by positivity) (le_max_right _ _) k
  calc |tailMoment a T k| ≤ B*I₀ := hn
    _ ≤ C*(I₀+1)*(16/Real.pi)^k*(k.factorial:ℝ)*Real.exp (-((Real.pi/8)*T)) := by
      dsimp only [B]
      nlinarith only [show 0 ≤ C*Real.exp (-((Real.pi/8)*T))*(16/Real.pi)^k*(k.factorial:ℝ) by positivity]
    _ ≤ _ := by dsimp only [M]; gcongr


private theorem self_le_exp (x : ℝ) : x ≤ Real.exp x := by
  have h := Real.add_one_le_exp x
  linarith only [h]

/-- A coarse induction bound suffices to compare factorial costs with cubic exponential decay. -/
private theorem factorial_le_exp_sq (n : ℕ) : (n.factorial:ℝ) ≤ Real.exp ((n:ℝ)^2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    calc ((n:ℝ)+1)*(n.factorial:ℝ) ≤ Real.exp n*Real.exp ((n:ℝ)^2) :=
        mul_le_mul (Real.add_one_le_exp (n:ℝ)) ih (by positivity) (Real.exp_pos _).le
      _ = Real.exp ((n:ℝ)+(n:ℝ)^2) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (((n:ℝ)+1)^2) := Real.exp_le_exp.mpr (by nlinarith only [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n])

private theorem polynomial_exponent_bound {S : ℝ} (hS : 0 ≤ S) (N : ℕ) :
    ((4*(N:ℝ)+3)*S+(N:ℝ)+(N:ℝ)^2+4*(N:ℝ)^2*((N:ℝ)+1)) ≤
      (4*S+6)*((N:ℝ)+1)^3 := by
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hS0 : 0 ≤ S*(N:ℝ)^3 := mul_nonneg hS (pow_nonneg hN _)
  have hS1 : 0 ≤ S*(N:ℝ)^2 := mul_nonneg hS (sq_nonneg _)
  have hS2 : 0 ≤ S*(N:ℝ) := mul_nonneg hS hN
  have hN3 : 0 ≤ (N:ℝ)^3 := pow_nonneg hN _
  nlinarith only [hS,hN,hS0,hS1,hS2,hN3,sq_nonneg (N:ℝ)]

private theorem factorial_tail_cost_le_exp {M m r K S : ℝ}
    (hM : 0 < M) (_hm : 0 < m) (hr : 0 < r) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hMbound : M ≤ Real.exp S) (hmbound : 2/m ≤ Real.exp S)
    (hrbound : r⁻¹ ≤ Real.exp S) (hKbound : K ≤ Real.exp S) (N : ℕ) :
    (2/m)*r⁻¹^(2*N+1)*(N:ℝ)*M*K^(2*N)*(N.factorial:ℝ)*
      (Nat.factorial (2*N):ℝ)^(N+1) ≤ Real.exp ((4*S+6)*((N:ℝ)+1)^3) := by
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hbound := mul_le_mul
    (mul_le_mul
      (mul_le_mul
        (mul_le_mul
          (mul_le_mul
            (mul_le_mul hmbound (pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hrbound (2*N+1))
              (by positivity) (Real.exp_pos _).le)
            (self_le_exp (N:ℝ)) hN (by positivity))
          hMbound hM.le (by positivity))
        (pow_le_pow_left₀ hK hKbound (2*N)) (by positivity) (by positivity))
      (factorial_le_exp_sq N) (by positivity) (by positivity))
    (pow_le_pow_left₀ (by positivity) (factorial_le_exp_sq (2*N)) (N+1))
    (by positivity) (by positivity)
  have he : Real.exp S*(Real.exp S)^(2*N+1)*Real.exp (N:ℝ)*Real.exp S*
      (Real.exp S)^(2*N)*Real.exp ((N:ℝ)^2)*
      (Real.exp (((2*N:ℕ):ℝ)^2))^(N+1) =
      Real.exp ((4*(N:ℝ)+3)*S+(N:ℝ)+(N:ℝ)^2+4*(N:ℝ)^2*((N:ℝ)+1)) := by
    simp only [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    push_cast
    ring
  exact hbound.trans (he.le.trans (Real.exp_le_exp.mpr (polynomial_exponent_bound hS N)))

/-- A fixed cubic cutoff pays half the compact moment floor at every rank. -/
private theorem exists_cubic_tail_payment {M m r K κ : ℝ}
    (hM : 0 < M) (hm : 0 < m) (hr : 0 < r) (hK : 1 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 4 ≤ D ∧ ∀ N : ℕ,
      ((N.factorial:ℝ)*(Nat.factorial (2*N):ℝ)^N)*
        ((N:ℝ)*M*K^(2*N)*(Nat.factorial (2*N):ℝ))*
          Real.exp (-(κ*(D*((N:ℝ)+1)^3))) ≤ m*r^(2*N+1)/2 := by
  let S : ℝ := 1+M+2/m+r⁻¹+K
  have hm0 : 0 < 2/m := by positivity
  have hr0 : 0 < r⁻¹ := inv_pos.mpr hr
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hMbound : M ≤ Real.exp S := by
    apply le_trans _ (self_le_exp S)
    dsimp only [S]
    linarith only [hm0,hr0,hK0]
  have hmbound : 2/m ≤ Real.exp S := by
    apply le_trans _ (self_le_exp S)
    dsimp only [S]
    linarith only [hM,hr0,hK0]
  have hrbound : r⁻¹ ≤ Real.exp S := by
    apply le_trans _ (self_le_exp S)
    dsimp only [S]
    linarith only [hM,hm0,hK0]
  have hKbound : K ≤ Real.exp S := by
    apply le_trans _ (self_le_exp S)
    dsimp only [S]
    linarith only [hM,hm0,hr0]
  let D : ℝ := 4+(4*S+7)/κ
  have hD : 4 ≤ D := le_add_of_nonneg_right (by positivity)
  have hpay : 4*S+6 ≤ κ*D := by
    have he : κ*D=4*κ+(4*S+7) := by dsimp only [D]; field_simp [hκ.ne']
    rw [he]
    linarith only [hκ]
  refine ⟨D,hD,fun N => ?_⟩
  have hcost := factorial_tail_cost_le_exp hM hm hr hK0.le hS hMbound hmbound hrbound hKbound N
  have hmul := mul_le_mul_of_nonneg_right hcost
    (Real.exp_pos (-(κ*(D*((N:ℝ)+1)^3)))).le
  have hexp : Real.exp ((4*S+6)*((N:ℝ)+1)^3)*
      Real.exp (-(κ*(D*((N:ℝ)+1)^3))) ≤ 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have h := mul_le_mul_of_nonneg_right hpay (by positivity : 0 ≤ ((N:ℝ)+1)^3)
    nlinarith only [h]
  have hnorm := hmul.trans hexp
  have h := mul_le_mul_of_nonneg_left hnorm (mul_pos hm (pow_pos hr (2*N+1))).le
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
  convert h using 1 <;> simp only [pow_succ,inv_pow] <;> field_simp [hr.ne',hm.ne']


private theorem cubic_window_log_bound {D : ℝ} (hD : 4 ≤ D) (N : ℕ) :
    0 < Real.log (D*((N:ℝ)+1)^3+1/2) ∧
    Real.log (D*((N:ℝ)+1)^3+1/2) ≤
      (Real.log (D+1)+3)*(1+Real.log ((N:ℝ)+1)) := by
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hn : 1 ≤ (N:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hn0 : 0 < (N:ℝ)+1 := zero_lt_one.trans_le hn
  have hp : 1 ≤ ((N:ℝ)+1)^3 := one_le_pow₀ hn
  have hT : 4 ≤ D*((N:ℝ)+1)^3 := hD.trans (le_mul_of_one_le_right hD0.le hp)
  have hlT : 0 < Real.log (D*((N:ℝ)+1)^3+1/2) := Real.log_pos (by linarith only [hT])
  have hlN : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg hn
  have hlD : 0 ≤ Real.log (D+1) := Real.log_nonneg (by linarith only [hD])
  refine ⟨hlT,?_⟩
  have harg : D*((N:ℝ)+1)^3+1/2 ≤ (D+1)*((N:ℝ)+1)^3 := by nlinarith only [hp]
  have h := Real.log_le_log (by positivity : 0 < D*((N:ℝ)+1)^3+1/2) harg
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  nlinarith only [h,mul_nonneg hlD hlN]

/-- The cubic frequency window fits inside the zero-free sign region on one logarithmic collar. -/
private theorem exists_logarithmic_window_width {D ε : ℝ} (hD : 4 ≤ D) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∀ a : ℝ,
      |a-1/2| < c/(1+Real.log ((N:ℝ)+1)) →
        |a-1/2| ≤ ε ∧ 0 < a ∧ |a| ≤ 3/4 ∧
          1/2-1/58/Real.log (D*((N:ℝ)+1)^3+1/2) ≤ a := by
  let Q : ℝ := Real.log (D+1)+3
  have hlogD : 0 ≤ Real.log (D+1) := Real.log_nonneg (by linarith only [hD])
  have hQ : 0 < Q := by dsimp only [Q]; linarith only [hlogD]
  let c : ℝ := min ε (min (1/8) (1/(58*Q)))
  have hc : 0 < c := lt_min hε (lt_min (by norm_num) (by positivity))
  have hcε : c ≤ ε := min_le_left _ _
  have hcsmall : c ≤ 1/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hcQ : c ≤ 1/(58*Q) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c,hc,fun N a ha => ?_⟩
  let L : ℝ := 1+Real.log ((N:ℝ)+1)
  have hlogN : 0 ≤ Real.log ((N:ℝ)+1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hL : 1 ≤ L := le_add_of_nonneg_right hlogN
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hdist : |a-1/2| ≤ c := ha.le.trans (div_le_self hc.le hL)
  have hsmall : |a-1/2| ≤ 1/8 := hdist.trans hcsmall
  obtain ⟨hlo,hhi⟩ := abs_le.mp hsmall
  have ha0 : 0 < a := by linarith only [hlo]
  have habs : |a| ≤ 3/4 := abs_le.mpr ⟨by linarith only [hlo],by linarith only [hhi]⟩
  refine ⟨hdist.trans hcε,ha0,habs,?_⟩
  obtain ⟨hlogT,hlogbound⟩ := cubic_window_log_bound hD N
  have hfrac : c/L ≤ 1/58/Real.log (D*((N:ℝ)+1)^3+1/2) := by
    rw [div_div]
    apply (div_le_div_iff₀ hL0 (by positivity : 0 < 58*Real.log (D*((N:ℝ)+1)^3+1/2))).mpr
    have h₁ := mul_le_mul_of_nonneg_left hlogbound (by positivity : 0 ≤ 58*c)
    have h₂ := mul_le_mul_of_nonneg_right ((le_div_iff₀ (by positivity : 0 < 58*Q)).mp hcQ) hL0.le
    change _ ≤ Q*L at hlogbound
    change (58*c)*Real.log (D*((N:ℝ)+1)^3+1/2) ≤ (58*c)*(Q*L) at h₁
    nlinarith only [h₁,h₂]
  have hlow := (abs_le.mp (ha.le.trans hfrac)).1
  linarith only [hlow]


/-- A compact positive boundary interval stays uniformly positive under small aperture shifts. -/
private theorem fixed_current_core : ∃ m r ε : ℝ, 0 < m ∧ 0 < r ∧ r ≤ 1 ∧
    0 < ε ∧ ε ≤ 1/8 ∧ ∀ a : ℝ, |a-1/2| ≤ ε → ∀ b∈Icc 0 r, m ≤ current a b := by
  obtain ⟨m,r,hm,hr,hr1,hfloor⟩ := current_boundary_floor
  obtain ⟨C,hC,hLip⟩ := current_lipschitz_exp
  refine ⟨m/2,r,min (1/8) (m/(2*C)),by positivity,hr,hr1,
    lt_min (by norm_num) (by positivity),min_le_left _ _,fun a ha b hb => ?_⟩
  have hsmall : |a-1/2| ≤ 1/8 := ha.trans (min_le_left _ _)
  have hCpay : C*|a-1/2| ≤ m/2 := by
    have hp := (le_div_iff₀ (by positivity : (0:ℝ) < 2*C)).mp (ha.trans (min_le_right _ _))
    nlinarith only [hp]
  have hexp : Real.exp (-((Real.pi/4)*|b|)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg (by positivity) (abs_nonneg b))
  have hdiff := (hLip a hsmall b).trans
    (mul_le_of_le_one_right (by positivity) hexp)
  have hlow := (abs_le.mp (hdiff.trans hCpay)).1
  linarith only [hlow,hfloor b hb]

private theorem nonnegative_current_compact_comparison {g : ℝ→ℝ} {m r : ℝ}
    (hr : 0 < r) (hpos : ∀ b : ℝ, 0 ≤ g b)
    (hfloor : ∀ b : ℝ, b∈Icc 0 r → m ≤ g b)
    (hintg : ∀ k : ℕ, Integrable (fun b : ℝ => b^k*g b))
    (N : ℕ) (v : Fin N → ℝ) :
    m*(v ⬝ᵥ compactMomentMatrix r N*ᵥv) ≤
      v ⬝ᵥ HTGeometry.momentHankelMatrix (weightedMoment volume g) N*ᵥv := by
  let p := Polynomial.ofFn N v
  have hraw : v ⬝ᵥ HTGeometry.momentHankelMatrix (weightedMoment volume g) N*ᵥv =
      ∫ b : ℝ, (p.eval b)^2*g b := by
    rw [HTGeometry.dotProduct_mulVec_momentHankelMatrix,momentFunctional_rawMoment_eq_integral hintg]
    simp only [Polynomial.eval_pow,p]
  have hint : Integrable (fun b : ℝ => (p.eval b)^2*g b) := by
    have h := integrable_polynomial_mul_of_rawMoments hintg (p^2)
    convert h using 1
    funext b
    rw [Polynomial.eval_pow]
  have hsq : IntegrableOn (fun b : ℝ => (p.eval b)^2) (Ioc 0 r) :=
    (p.continuous.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hcmp : (∫ b : ℝ in Ioc 0 r, m*(p.eval b)^2) ≤
      ∫ b : ℝ in Ioc 0 r, (p.eval b)^2*g b := by
    apply integral_mono_ae (hsq.const_mul m) hint.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with b hb
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hfloor b ⟨hb.1.le,hb.2⟩) (sq_nonneg (p.eval b))
  have hwhole : (∫ b : ℝ in Ioc 0 r, (p.eval b)^2*g b) ≤
      ∫ b : ℝ, (p.eval b)^2*g b := by
    have hc : 0 ≤ ∫ b : ℝ in (Ioc 0 r)ᶜ, (p.eval b)^2*g b :=
      integral_nonneg fun b => mul_nonneg (sq_nonneg _) (hpos b)
    have he := integral_add_compl (s:=Ioc (0:ℝ) r) measurableSet_Ioc hint
    linarith only [he,hc]
  rw [compactMomentMatrix_quad r hr,hraw,← integral_const_mul]
  exact hcmp.trans hwhole

/-- A nonnegative current with a compact positive core inherits factorial moment coercivity. -/
private theorem nonnegative_current_factorial_floor {g : ℝ→ℝ} {m r : ℝ}
    (hm : 0 < m) (hr : 0 < r) (hr1 : r ≤ 1) (hpos : ∀ b : ℝ, 0 ≤ g b)
    (hfloor : ∀ b : ℝ, b∈Icc 0 r → m ≤ g b)
    (hintg : ∀ k : ℕ, Integrable (fun b : ℝ => b^k*g b))
    (n : ℕ) (v : Fin (n+1) → ℝ) :
    m*r^(2*(n+1)+1)*(v ⬝ᵥ v) ≤
      ((Nat.factorial (n+1):ℝ)*(Nat.factorial (2*(n+1)):ℝ)^(n+1))*
        (v ⬝ᵥ HTGeometry.momentHankelMatrix (weightedMoment volume g) (n+1)*ᵥv) := by
  let w : Fin (n+1) → ℝ := fun i => r^i.val*v i
  let B : ℝ := (Nat.factorial (n+1):ℝ)*(Nat.factorial (2*(n+1)):ℝ)^(n+1)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hnorm := scaled_vector_floor hr hr1 (n+1) v
  have hunit := unitMomentMatrix_coercive n w
  have hcmp := nonnegative_current_compact_comparison hr hpos hfloor hintg (n+1) v
  calc m*r^(2*(n+1)+1)*(v ⬝ᵥ v) = (m*r)*(r^(2*(n+1))*(v ⬝ᵥ v)) := by rw [pow_succ]; ring
    _ ≤ (m*r)*(w ⬝ᵥ w) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ (m*r)*(B*(w ⬝ᵥ unitMomentMatrix (n+1)*ᵥw)) :=
      mul_le_mul_of_nonneg_left hunit (by positivity)
    _ = B*(m*(v ⬝ᵥ compactMomentMatrix r (n+1)*ᵥv)) := by
      rw [compactMomentMatrix_scale]
      dsimp only [w]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcmp hB

private def truncatedCurrent (a T b : ℝ) : ℝ :=
  {b : ℝ | |b| ≤ T}.indicator (current a) b

private def truncatedHankel (a T : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  HTGeometry.momentHankelMatrix (weightedMoment volume (truncatedCurrent a T)) N

private def tailHankel (a T : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => tailMoment a T (i.val+j.val)

private theorem truncated_integrable (a T : ℝ) (ha : |a| < 1) (k : ℕ) :
    Integrable (fun b : ℝ => b^k*truncatedCurrent a T b) := by
  have h := (raw_integrable a ha k).indicator
    ((isClosed_le continuous_abs continuous_const).measurableSet :
      MeasurableSet {b : ℝ | |b| ≤ T})
  have he : (fun b : ℝ => b^k*truncatedCurrent a T b) =
      {b : ℝ | |b| ≤ T}.indicator (fun b : ℝ => b^k*current a b) := by
    funext b
    by_cases hb : |b| ≤ T
    · simp only [truncatedCurrent,Set.indicator_of_mem (show b∈{b : ℝ | |b| ≤ T} from hb)]
    · simp only [truncatedCurrent,Set.indicator_of_notMem (show b∉{b : ℝ | |b| ≤ T} from hb),mul_zero]
  rw [he]
  exact h

private theorem tail_integrable (a T : ℝ) (ha : |a| < 1) (k : ℕ) :
    Integrable ({b : ℝ | T < |b|}.indicator (fun b : ℝ => b^k*current a b)) :=
  (raw_integrable a ha k).indicator (isOpen_lt continuous_const continuous_abs).measurableSet

/-- Frequency truncation and its tail partition each actual moment exactly. -/
private theorem raw_eq_truncated_add_tail (a T : ℝ) (ha : |a| < 1) (N : ℕ) :
    rawHankel a N = truncatedHankel a T N+tailHankel a T N := by
  ext i j
  change (∫ b : ℝ, b^(i.val+j.val)*current a b) =
    (∫ b : ℝ, b^(i.val+j.val)*truncatedCurrent a T b)+
      ∫ b : ℝ, {b : ℝ | T < |b|}.indicator (fun b => b^(i.val+j.val)*current a b) b
  rw [← integral_add (truncated_integrable a T ha _) (tail_integrable a T ha _)]
  congr 1
  funext b
  by_cases hb : |b| ≤ T
  · simp only [truncatedCurrent,Set.indicator_of_mem (show b∈{b : ℝ | |b| ≤ T} from hb),
      Set.indicator_of_notMem (show b∉{b : ℝ | T < |b|} from not_lt.mpr hb),add_zero]
  · simp only [truncatedCurrent,Set.indicator_of_notMem (show b∉{b : ℝ | |b| ≤ T} from hb),
      Set.indicator_of_mem (show b∈{b : ℝ | T < |b|} from lt_of_not_ge hb),mul_zero,zero_add]

private theorem truncated_current_factorial_floor {a T m r : ℝ}
    (ha : |a| < 1) (hm : 0 < m) (hr : 0 < r) (hr1 : r ≤ 1) (hrT : r ≤ T)
    (hpos : ∀ b : ℝ, |b| ≤ T → 0 ≤ current a b)
    (hfloor : ∀ b : ℝ, b∈Icc 0 r → m ≤ current a b)
    (n : ℕ) (v : Fin (n+1) → ℝ) :
    m*r^(2*(n+1)+1)*(v ⬝ᵥ v) ≤
      ((Nat.factorial (n+1):ℝ)*(Nat.factorial (2*(n+1)):ℝ)^(n+1))*
        (v ⬝ᵥ truncatedHankel a T (n+1)*ᵥv) := by
  apply nonnegative_current_factorial_floor hm hr hr1
  · intro b
    by_cases hb : |b| ≤ T
    · simpa only [truncatedCurrent,Set.indicator_of_mem (show b∈{b : ℝ | |b| ≤ T} from hb)] using hpos b hb
    · simp only [truncatedCurrent,Set.indicator_of_notMem (show b∉{b : ℝ | |b| ≤ T} from hb),le_refl]
  · intro b hb
    have hbt : |b| ≤ T := by rw [abs_of_nonneg hb.1]; exact hb.2.trans hrT
    simpa only [truncatedCurrent,Set.indicator_of_mem (show b∈{b : ℝ | |b| ≤ T} from hbt)] using hfloor b hb
  · exact truncated_integrable a T ha

/-- The uniform moment estimate bounds every entry of the finite tail matrix. -/
private theorem tail_entry_bound {M K : ℝ} (hM : 0 < M) (hK : 1 ≤ K)
    (htail : ∀ a : ℝ, |a| ≤ 3/4 → ∀ T : ℝ, 0 ≤ T → ∀ k : ℕ,
      |tailMoment a T k| ≤ M*K^k*(k.factorial:ℝ)*Real.exp (-((Real.pi/8)*T)))
    (N : ℕ) (a T : ℝ) (ha : |a| ≤ 3/4) (hT : 0 ≤ T) (i j : Fin N) :
    |tailHankel a T N i j| ≤
      M*K^(2*N)*(Nat.factorial (2*N):ℝ)*Real.exp (-((Real.pi/8)*T)) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hij : i.val+j.val ≤ 2*N := by omega
  have hp := pow_le_pow_right₀ hK hij
  have hf : (Nat.factorial (i.val+j.val):ℝ) ≤ (Nat.factorial (2*N):ℝ) := by
    exact_mod_cast Nat.factorial_le hij
  have hprod := mul_le_mul hp hf (by positivity) (by positivity)
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprod hM.le) (Real.exp_pos (-((Real.pi/8)*T))).le
  have h := (htail a ha T hT (i.val+j.val)).trans (by simpa only [mul_assoc] using hbound)
  simpa only [tailHankel,mul_assoc] using h

/-- Every finite actual theta rank is strict in a critical collar of logarithmic width. -/
theorem signedHankel_posDef_logarithmic_collar : ∃ c : ℝ, 0 < c ∧
    ∀ N : ℕ, ∀ a : ℝ,
      |a-1/2| < c/(1+Real.log ((N:ℝ)+1)) →
        (thetaCuspCenterMixedSignedHankel a N).PosDef := by
  obtain ⟨m,r,ε,hm,hr,hr1,hε,hεsmall,hcore⟩ := fixed_current_core
  obtain ⟨M,K,hM,hK,htail⟩ := tailMoment_factorial_exp
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨D,hD,hpayment⟩ := exists_cubic_tail_payment hM hm hr hK
    (by positivity : (0:ℝ) < Real.pi/8)
  obtain ⟨c,hc,hwidth⟩ := exists_logarithmic_window_width hD hε
  refine ⟨c,hc,fun N a ha => ?_⟩
  obtain ⟨hsmall,ha0,habs,hregion⟩ := hwidth N a ha
  have ha1 : |a| < 1 := habs.trans_lt (by norm_num)
  apply signed_posDef_of_raw ha1 N
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨raw_hermitian a N,fun v hv => ?_⟩
  rw [star_trivial]
  cases N with
  | zero => exact False.elim (hv (Subsingleton.elim v 0))
  | succ n =>
    let T : ℝ := D*(((n+1:ℕ):ℝ)+1)^3
    have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hD
    have hT : 4 ≤ T := by
      apply hD.trans
      apply le_mul_of_one_le_right hD0.le
      apply one_le_pow₀
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hT0 : 0 ≤ T := (by norm_num : (0:ℝ) ≤ 4).trans hT
    have hrT : r ≤ T := hr1.trans ((by norm_num : (1:ℝ) ≤ 4).trans hT)
    have hpos (b : ℝ) (hb : |b| ≤ T) : 0 ≤ current a b :=
      current_nonneg_on_frequency_window ha0 hregion hb
    let B : ℝ := (Nat.factorial (n+1):ℝ)*(Nat.factorial (2*(n+1)):ℝ)^(n+1)
    let E : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := tailHankel a T (n+1)
    let P : ℝ := (n+1:ℕ)*M*K^(2*(n+1))*(Nat.factorial (2*(n+1)):ℝ)*
      Real.exp (-((Real.pi/8)*T))
    have hB : 0 < B := by dsimp only [B]; positivity
    have hpay : B*P ≤ m*r^(2*(n+1)+1)/2 := by
      simpa only [B,P,T,mul_assoc] using hpayment (n+1)
    have hentry := tail_entry_bound hM hK htail (n+1) a T habs hT0
    have he := GaloisForLFunctions.HTGeometry.abs_dotProduct_mulVec_le E (by positivity) hentry v
    have he' : |v ⬝ᵥ E*ᵥv| ≤ P*(v ⬝ᵥ v) := by
      convert he using 1
      dsimp only [P]
      ring
    have hnorm : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (by rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
        (Ne.symm (fun h => hv ((dotProduct_self_eq_zero).mp h)))
    have hsplit : v ⬝ᵥ rawHankel a (n+1)*ᵥv =
        v ⬝ᵥ truncatedHankel a T (n+1)*ᵥv+v ⬝ᵥ E*ᵥv := by
      rw [raw_eq_truncated_add_tail a T ha1,Matrix.add_mulVec,dotProduct_add]
    have hsplitB := congrArg (fun q : ℝ => B*q) hsplit
    have hlow := mul_le_mul_of_nonneg_left (abs_le.mp he').1 hB.le
    have hpaid := mul_le_mul_of_nonneg_right hpay hnorm.le
    have hzero := truncated_current_factorial_floor ha1 hm hr hr1 hrT hpos (hcore a hsmall) n v
    change m*r^(2*(n+1)+1)*(v ⬝ᵥ v) ≤
      B*(v ⬝ᵥ truncatedHankel a T (n+1)*ᵥv) at hzero
    have hfinal : (m*r^(2*(n+1)+1)/2)*(v ⬝ᵥ v) ≤ B*(v ⬝ᵥ rawHankel a (n+1)*ᵥv) := by
      nlinarith only [hzero,hlow,hpaid,hsplitB]
    have hpositive : 0 < (m*r^(2*(n+1)+1)/2)*(v ⬝ᵥ v) := by positivity
    exact (mul_pos_iff_of_pos_left hB).mp (hpositive.trans_le hfinal)

/-- The logarithmic collar at rank `N` applies simultaneously to all smaller sections. -/
theorem signedHankel_posDef_logarithmic_collar_upto : ∃ c : ℝ, 0 < c ∧
    ∀ N : ℕ, ∀ n ≤ N, ∀ a : ℝ,
      |a-1/2| < c/(1+Real.log ((N:ℝ)+1)) →
        (thetaCuspCenterMixedSignedHankel a n).PosDef := by
  obtain ⟨c,hc,hp⟩ := signedHankel_posDef_logarithmic_collar
  refine ⟨c,hc,fun N n hn a ha => ?_⟩
  have hinj : Function.Injective (Fin.castLE hn) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin N => k.val) hij
  have he : (thetaCuspCenterMixedSignedHankel a N).submatrix (Fin.castLE hn) (Fin.castLE hn) =
      thetaCuspCenterMixedSignedHankel a n := by ext i j; rfl
  simpa only [he] using (hp N a ha).submatrix hinj

end GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar
