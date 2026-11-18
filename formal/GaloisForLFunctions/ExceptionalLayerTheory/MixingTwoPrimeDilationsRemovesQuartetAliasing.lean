import GaloisForLFunctions.ExceptionalLayerTheory.TwoAndThreeDilationRecurrencesAndSingleQuartetStratum
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock

/-!
# Identifying the quartet by mixed prime dilations

Agreement of two cosines permits opposite phase orientations at the two
primes. An extra reading at their product enforces a common orientation.
The two prime logarithms then identify the frequency up to sign.
-/

noncomputable section

open Complex
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
      hr.2.2.1 hr.2.2.2 (by norm_num at hcos ⊢; exact hcos)
    exact hr.2.1 (by simpa only [abs_of_pos hr.1,abs_of_pos hγ] using he)
  · intro h
    obtain ⟨_,_,_,hl,ha⟩ := singleQuartet_obeys_all_dilation_recurrences hγ h
    exact ⟨hl,ha 2 (by norm_num),ha 3 (by norm_num),ha 6 (by norm_num)⟩

#print axioms abs_eq_of_two_prime_and_product_cos
#print axioms two_prime_product_recurrences_iff_singleQuartet

end GaloisForLFunctions.ExceptionalLayerTheory
