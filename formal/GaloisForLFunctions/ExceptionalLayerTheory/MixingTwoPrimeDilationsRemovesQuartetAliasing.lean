import GaloisForLFunctions.ExceptionalLayerTheory.TwoAndThreeDilationRecurrencesAndSingleQuartetStratum
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock
import GaloisForLFunctions.ExceptionalLayerTheory.EveryRightZeroForcesBothSignsOfThePrimeError
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing

/-!
# Identifying the quartet by mixed prime dilations

Agreement of two cosines permits opposite phase orientations at the two
primes. An extra reading at their product enforces a common orientation.
The two prime logarithms then identify the frequency up to sign.
-/

noncomputable section

open Complex Filter Topology
open GaloisForLFunctions.ZeroConfigurationGeometry GaloisForLFunctions.ExclusionOfTheCriticalState

namespace GaloisForLFunctions.ExceptionalLayerTheory

private def fullTurn (r t : ℝ) : Prop := ∃ m : ℤ, r*t=(m:ℝ)*(2*Real.pi)

private theorem fullTurn_other {a b t : ℝ} (hab : fullTurn (a+b) t) (ha : fullTurn a t) :
    fullTurn b t := by
  obtain ⟨m,hm⟩ := hab
  obtain ⟨n,hn⟩ := ha
  refine ⟨m-n,?_⟩
  push_cast
  linarith only [hm,hn]

private theorem fullTurn_or_of_cos {a u v : ℝ} (hc : Real.cos (u*a)=Real.cos (v*a)) :
    fullTurn a (u-v) ∨ fullTurn a (u+v) := by
  obtain ⟨m,hm | hm⟩ := (cos_eq_cos_iff_exists_int _ _).mp hc
  · exact Or.inl ⟨m,by linarith only [hm]⟩
  · exact Or.inr ⟨m,by linarith only [hm]⟩

private theorem time_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) {t : ℝ}
    (htp : fullTurn (Real.log p) t) (htq : fullTurn (Real.log q) t) : t=0 := by
  obtain ⟨m,hm⟩ := htp
  obtain ⟨n,hn⟩ := htq
  exact _root_.RHTower.primeLogPhaseClockPair_injective hp hq hpq (Prod.ext
    (HTGeometry.phaseClockValue_eq_zero_of_rate_mul_time_eq_int_two_pi _ _ m hm)
    (HTGeometry.phaseClockValue_eq_zero_of_rate_mul_time_eq_int_two_pi _ _ n hn))

/-- The cosines at two distinct primes and their product determine the
absolute frequency. The assertion includes a vanishing sine at either prime. -/
theorem abs_eq_of_two_prime_and_product_cos {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    {u v : ℝ} (h₁ : Real.cos (u*Real.log p)=Real.cos (v*Real.log p))
    (h₂ : Real.cos (u*Real.log q)=Real.cos (v*Real.log q))
    (h₃ : Real.cos (u*Real.log ((p:ℝ)*q))=Real.cos (v*Real.log ((p:ℝ)*q))) :
    |u|=|v| := by
  rw [Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)] at h₃
  have pair (t : ℝ) (h : fullTurn (Real.log p+Real.log q) t)
      (h' : fullTurn (Real.log p) t ∨ fullTurn (Real.log q) t) : t=0 := by
    rcases h' with ha | hb
    · exact time_zero hp hq hpq ha (fullTurn_other h ha)
    · rw [add_comm] at h
      exact time_zero hp hq hpq (fullTurn_other h hb) hb
  have he : u-v=0 ∨ u+v=0 := by
    rcases fullTurn_or_of_cos h₁ with hp' | hp' <;> rcases fullTurn_or_of_cos h₂ with hq' | hq'
    · exact Or.inl (time_zero hp hq hpq hp' hq')
    · exact (fullTurn_or_of_cos h₃).imp (fun h => pair _ h (Or.inl hp')) (fun h => pair _ h (Or.inr hq'))
    · exact (fullTurn_or_of_cos h₃).imp (fun h => pair _ h (Or.inr hq')) (fun h => pair _ h (Or.inl hp'))
    · exact Or.inr (time_zero hp hq hpq hp' hq')
  rcases he with e | e
  · rw [sub_eq_zero.mp e]
  · rw [show u= -v by linarith only [e],abs_neg]

/-- The prime-error recurrences at two, three and six, together with a
nonzero leading error, characterize exactly one off-line quartet. -/
theorem two_prime_product_recurrences_iff_singleQuartet {β γ : ℝ}
    (hβ : 1/2<β) (hβ' : β<1) (hγ : 0<γ) :
    (HasPositivePowerLimsup primeError β ∧
      ¬IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∧
      ¬IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ) ∧
      ¬IsSqrtLogSqUnbounded (primeDilationResidual 6 β γ)) ↔
      HasSingleOffLineQuartet ((β:ℂ)+I*γ) := by
  constructor
  · rintro ⟨hl,h₂,h₃,h₆⟩
    rcases (twoClock_bounded_and_limsup_iff hβ hβ' hγ).mp ⟨hl,h₂,h₃⟩ with
      h | ⟨ω,_,hr,h⟩
    · exact h
    exfalso
    have hz : riemannZeta ((β:ℂ)+I*ω)=0 := h.elim (fun hq => hq.2.1.1) (fun hq => hq.2.2.2.2.1.1)
    have hne : (β:ℂ)+I*ω≠1 := by
      intro e
      have he := congrArg Complex.re e
      simp at he
      exact hβ'.ne he
    have hcos := (re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1:ℝ)<6)
      h₆ (by simpa using hβ) hne hz).2
    have he := abs_eq_of_two_prime_and_product_cos Nat.prime_two Nat.prime_three (by decide)
      hr.2.2.1 hr.2.2.2 (by simpa using hcos)
    exact hr.2.1 (by simpa only [abs_of_pos hr.1,abs_of_pos hγ] using he)
  · intro h
    obtain ⟨_,_,_,hl,ha⟩ := singleQuartet_obeys_all_dilation_recurrences hγ h
    exact ⟨hl,ha 2 (by norm_num),ha 3 (by norm_num),ha 6 (by norm_num)⟩

private theorem positive_power_limsup_of_right_zero {ρ : ℂ} (hh : 1/2<ρ.re)
    (h1 : ρ.re<1) (hz : riemannZeta ρ=0) : HasPositivePowerLimsup primeError ρ.re := by
  obtain ⟨c,hc,h⟩ := both_prime_error_peaks_at_every_large_cutoff hh h1 hz
  refine ⟨c,hc,fun X => ?_⟩
  obtain ⟨M,hM⟩ := exists_nat_ge X
  obtain ⟨N,hs,hN⟩ := (h.and (eventually_ge_atTop (M^2))).exists
  obtain ⟨n,_,hn,he⟩ := hs 1 abs_one
  have hm : (M:ℝ)≤Real.sqrt N := by
    have ht := Real.sqrt_le_sqrt (show ((M^2:ℕ):ℝ)≤N by exact_mod_cast hN)
    simpa only [Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg M)] using ht
  have hp : c*(n:ℝ)^ρ.re≤primeError n := by simpa only [one_mul] using he.le
  exact ⟨n,hM.trans (hm.trans hn.le),hp.trans (le_abs_self _)⟩

private theorem bounded_residual_of_rh (h : RiemannHypothesis) {a β γ : ℝ} (ha : 1≤a) :
    ¬IsSqrtLogSqUnbounded (primeDilationResidual a β γ) := by
  let K := 200*(_root_.RHTower.xiLineTwoLogDerivConstant+2)
  have hb (x : ℝ) (hx : 16≤x) : |primeError x|≤|K|*Real.sqrt x*Real.log x^2 :=
    (_root_.RHTower.abs_chebyshevPsi_sub_le_of_riemannHypothesis h hx).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)) (sq_nonneg _))
  obtain ⟨C,X,_,hC⟩ := abs_dilationRecurrenceOp_le_of_sqrt_log_sq (β := β) (γ := γ) ha (abs_nonneg K) hb
  exact fun hu => (isSqrtLogSqUnbounded_iff_not_eventually_le _).mp hu ⟨C,X,hC⟩

/-- Without a lower amplitude assumption, the three bounded recurrences
allow precisely RH or the prescribed quartet. -/
theorem two_prime_product_recurrences_iff_rh_or_singleQuartet {β γ : ℝ}
    (hβ : 1/2<β) (hβ' : β<1) (hγ : 0<γ) :
    (¬IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∧
      ¬IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ) ∧
      ¬IsSqrtLogSqUnbounded (primeDilationResidual 6 β γ)) ↔
      RiemannHypothesis ∨ HasSingleOffLineQuartet ((β:ℂ)+I*γ) := by
  constructor
  · intro hr
    by_cases h : RiemannHypothesis
    · exact Or.inl h
    rw [_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip] at h
    push Not at h
    obtain ⟨ρ,hh,h1,hz⟩ := h
    have hn : ρ≠1 := fun e => h1.ne (by rw [e,Complex.one_re])
    have he := (re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1:ℝ)<2)
      hr.1 hh hn hz).1
    exact Or.inr ((two_prime_product_recurrences_iff_singleQuartet hβ hβ' hγ).mp
      ⟨he ▸ positive_power_limsup_of_right_zero hh h1 hz,hr⟩)
  · rintro (h | h)
    · exact ⟨bounded_residual_of_rh h (by norm_num),bounded_residual_of_rh h (by norm_num),
        bounded_residual_of_rh h (by norm_num)⟩
    · exact ((two_prime_product_recurrences_iff_singleQuartet hβ hβ' hγ).mpr h).2

/-- The forward dilation residual for the logarithmic count of ordinary
primes, with every prime counted once. -/
def ordinaryThetaDilationResidual (a β γ : ℝ) :=
  dilationRecurrenceOp a β γ (fun x => Chebyshev.theta x-x)

private theorem bounded_congr_of_bounded_difference {f g : ℝ → ℝ}
    (hd : ∃ B X : ℝ, ∀ x, X≤x → |f x-g x|≤B*Real.sqrt x*Real.log x^2) :
    (¬IsSqrtLogSqUnbounded f) ↔ ¬IsSqrtLogSqUnbounded g := by
  obtain ⟨B,X,hB⟩ := hd
  simp only [isSqrtLogSqUnbounded_iff_not_eventually_le,not_not]
  constructor <;> rintro ⟨C,Y,hC⟩ <;> refine ⟨C+B,max X Y,fun x hx => ?_⟩
  · have he := abs_sub (f x) (f x-g x)
    rw [sub_sub_cancel] at he
    linarith only [he,hB x ((le_max_left _ _).trans hx),hC x ((le_max_right _ _).trans hx)]
  · have he := abs_add_le (g x) (f x-g x)
    rw [show g x+(f x-g x)=f x by ring] at he
    linarith only [he,hB x ((le_max_left _ _).trans hx),hC x ((le_max_right _ _).trans hx)]

private theorem theta_residual_iff {a β γ : ℝ} (ha : 1≤a) :
    (¬IsSqrtLogSqUnbounded (primeDilationResidual a β γ)) ↔
      ¬IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual a β γ) := by
  let δ (x : ℝ) := Chebyshev.psi x-Chebyshev.theta x
  let K := 3*(Real.log 4+4)
  have hK : 0≤K := by dsimp only [K]; positivity
  have hd (x : ℝ) (hx : Real.exp 1≤x) : |δ x|≤K*Real.sqrt x*Real.log x^2 := by
    have hxpos := (Real.exp_pos 1).trans_le hx
    have hl : 1≤Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
    have hδ := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt x
    change |Chebyshev.psi x-Chebyshev.theta x|≤_
    rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
    exact hδ.trans (le_mul_of_one_le_right (mul_nonneg hK (Real.sqrt_nonneg _))
      (by nlinarith only [hl,sq_nonneg (Real.log x-1)]))
  obtain ⟨B,X,_,hb⟩ := abs_dilationRecurrenceOp_le_of_sqrt_log_sq (β := β) (γ := γ) ha hK hd
  refine bounded_congr_of_bounded_difference ⟨B,X,fun x hx => ?_⟩
  have he : δ=fun t => primeError t-(Chebyshev.theta t-t) := by
    funext t; dsimp [δ,primeError]; ring
  have h := hb x hx
  rwa [he,dilationRecurrenceOp_sub] at h

/-- Three recurrences on actual ordinary prime counts allow precisely RH
or a single quartet at the specified point, without any amplitude input. -/
theorem ordinary_prime_recurrences_iff_rh_or_singleQuartet {β γ : ℝ}
    (hβ : 1/2<β) (hβ' : β<1) (hγ : 0<γ) :
    (¬IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 2 β γ) ∧
      ¬IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 3 β γ) ∧
      ¬IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 6 β γ)) ↔
      RiemannHypothesis ∨ HasSingleOffLineQuartet ((β:ℂ)+I*γ) := by
  simpa only [← theta_residual_iff (by norm_num : (1:ℝ)≤2),
    ← theta_residual_iff (by norm_num : (1:ℝ)≤3),← theta_residual_iff (by norm_num : (1:ℝ)≤6)]
    using two_prime_product_recurrences_iff_rh_or_singleQuartet hβ hβ' hγ

#print axioms ordinary_prime_recurrences_iff_rh_or_singleQuartet
#print axioms abs_eq_of_two_prime_and_product_cos
#print axioms two_prime_product_recurrences_iff_singleQuartet

end GaloisForLFunctions.ExceptionalLayerTheory
