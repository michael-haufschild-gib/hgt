import GaloisForLFunctions.RHTower.XiLogDerivNonholonomic
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.XiWeilDivisorHilbert
import GaloisForLFunctions.RHTower.SuzukiTorqueContinuationAnalytic

/-!
# The torque continuation has a double pole above every Xi zero

`(16)` divides a difference of two completed curvatures by `2s²`.  Above a zero `ρ` of `ξ` in the
open strip the first curvature has an exact double pole, the second is evaluated at `ρ+2` where the
Euler product forbids a zero, and the denominator does not vanish.  So the continuation has exact
meromorphic order `-2` at `p = ρ + 1/2`, which no convergent Laplace transform can have.
-/

open Complex

noncomputable section

namespace RHTower

/-- The zero set of `ξ` is countable. -/
theorem xi_zeroSet_countable : {s : ℂ | xi s = 0}.Countable := by
  have hinj : Function.Injective (fun s : ℂ => -Complex.I * (s - 1 / 2)) := by
    intro a b hab
    simp only at hab
    have hI : (-Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
    have h := mul_left_cancel₀ hI hab
    exact sub_left_inj.mp h
  refine (XiC_zeroSet_countable.preimage hinj).mono ?_
  intro s hs
  have hval : XiC (-Complex.I * (s - 1 / 2)) = xi s := by
    rw [XiC]
    congr 1
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  exact Set.mem_preimage.mpr (by rw [Set.mem_setOf_eq, hval]; exact hs)

/-- A nontrivial zero of `ξ` in the open critical strip. -/
theorem exists_xi_zero_openStrip : ∃ ρ : ℂ, 0 < ρ.re ∧ ρ.re < 1 ∧ xi ρ = 0 := by
  obtain ⟨ρ, h0, h1, hz⟩ := exists_riemannZeta_zero_mem_openStrip
  refine ⟨ρ, h0, h1, ?_⟩
  have hne1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at h1
    linarith
  rw [xi_eq_zero_iff h0 hne1]
  exact hz

theorem meromorphicAt_deriv_logDeriv_xi (z : ℂ) : MeromorphicAt (deriv (logDeriv xi)) z :=
  (meromorphicAt_logDeriv_xi z).deriv

/-- **The curvature has an exact double pole at every Xi zero.** -/
theorem meromorphicOrderAt_deriv_logDeriv_xi_eq_neg_two {ρ : ℂ} (hz : xi ρ = 0) :
    meromorphicOrderAt (deriv (logDeriv xi)) ρ = ((-2 : ℤ) : WithTop ℤ) := by
  have hn : (((-1 : ℤ) : ℂ)) ≠ 0 := by norm_num
  have h := meromorphicOrderAt_deriv_eq_sub_one hn (meromorphicOrderAt_logDeriv_xi_eq_neg_one hz)
  simpa using h

/-- A nonnegative-order germ is not of order `-2`. -/
theorem analytic_meromorphicOrderAt_ne_neg_two {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    meromorphicOrderAt f p ≠ ((-2 : ℤ) : WithTop ℤ) := by
  rw [hf.meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f p) ⊤ with htop | hne
  · rw [htop]
    simp only [ENat.map_top]
    exact WithTop.top_ne_coe
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hm]
    simp only [ENat.map_coe]
    intro hcon
    have : (m : ℤ) = -2 := by exact_mod_cast hcon
    omega

/-- A nonnegative-order germ has order at least `-2`. -/
theorem analytic_neg_two_le_meromorphicOrderAt {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    ((-2 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p := by
  rw [hf.meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f p) ⊤ with htop | hne
  · rw [htop]
    simp
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hm]
    simp only [ENat.map_coe]
    have hle : ((-2 : ℤ)) ≤ (m : ℤ) := by omega
    exact_mod_cast WithTop.coe_le_coe.mpr hle

/-- **The continuation has exact order `-2` above a strip zero of `ξ`.** -/
theorem meromorphicOrderAt_continuation_eq_neg_two {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hz : xi ρ = 0) :
    meromorphicOrderAt suzukiPositionTorqueLaplaceContinuation (ρ + 1 / 2)
      = ((-2 : ℤ) : WithTop ℤ) := by
  set p : ℂ := ρ + 1 / 2 with hpdef
  have hpre : p.re = ρ.re + 1 / 2 := by
    rw [hpdef, Complex.add_re]
    norm_num
  have hshift : p - 1 / 2 = ρ := by rw [hpdef]; ring
  have hshift' : p + 3 / 2 = ρ + 2 := by rw [hpdef]; ring
  have hpne : p ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hpre
    linarith
  have hfar : xi (ρ + 2) ≠ 0 := by
    refine xi_ne_zero_of_one_lt_re ?_
    rw [Complex.add_re]
    norm_num
    linarith
  have hRan : AnalyticAt ℂ (fun s : ℂ => deriv (logDeriv xi) (s + 3 / 2)) p := by
    have hin : AnalyticAt ℂ (fun s : ℂ => s + 3 / 2) p := analyticAt_id.add analyticAt_const
    have hout : AnalyticAt ℂ (deriv (logDeriv xi)) ((fun s : ℂ => s + 3 / 2) p) := by
      rw [show ((fun s : ℂ => s + 3 / 2) p) = ρ + 2 from hshift']
      exact analyticAt_deriv_logDeriv_xi hfar
    exact AnalyticAt.comp (x := p) (g := deriv (logDeriv xi)) (f := fun s : ℂ => s + 3 / 2)
      hout hin
  have hLord : meromorphicOrderAt (fun s : ℂ => deriv (logDeriv xi) (s - 1 / 2)) p
      = ((-2 : ℤ) : WithTop ℤ) := by
    have hg : AnalyticAt ℂ (fun s : ℂ => s - 1 / 2) p := analyticAt_id.sub analyticAt_const
    have hg' : deriv (fun s : ℂ => s - 1 / 2) p ≠ 0 := by
      have hd : deriv (fun s : ℂ => s - 1 / 2) p = 1 :=
        ((hasDerivAt_id p).sub_const (1 / 2 : ℂ)).deriv
      rw [hd]
      exact one_ne_zero
    have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := deriv (logDeriv xi))
      (g := fun s : ℂ => s - 1 / 2) (x := p) hg hg'
    have h2 : meromorphicOrderAt (deriv (logDeriv xi)) ((fun s : ℂ => s - 1 / 2) p)
        = ((-2 : ℤ) : WithTop ℤ) := by
      rw [show ((fun s : ℂ => s - 1 / 2) p) = ρ from hshift]
      exact meromorphicOrderAt_deriv_logDeriv_xi_eq_neg_two hz
    rw [h2] at h
    exact h
  have hm1 : MeromorphicAt (fun s : ℂ => deriv (logDeriv xi) (s - 1 / 2)) p := by
    have hg : AnalyticAt ℂ (fun s : ℂ => s - 1 / 2) p := analyticAt_id.sub analyticAt_const
    have hf : MeromorphicAt (deriv (logDeriv xi)) ((fun s : ℂ => s - 1 / 2) p) := by
      rw [show ((fun s : ℂ => s - 1 / 2) p) = ρ from hshift]
      exact meromorphicAt_deriv_logDeriv_xi ρ
    exact MeromorphicAt.comp_analyticAt (f := deriv (logDeriv xi))
      (g := fun s : ℂ => s - 1 / 2) hf hg
  have hm2b : MeromorphicAt (fun s : ℂ => deriv (logDeriv xi) (s + 3 / 2)) p :=
    hRan.meromorphicAt
  have hm2 : MeromorphicAt (fun s : ℂ => -deriv (logDeriv xi) (s + 3 / 2)) p := hm2b.neg
  have hRneg : meromorphicOrderAt (fun s : ℂ => -deriv (logDeriv xi) (s + 3 / 2)) p
      = meromorphicOrderAt (fun s : ℂ => deriv (logDeriv xi) (s + 3 / 2)) p :=
    (meromorphicOrderAt_fun_neg (f := fun s : ℂ => deriv (logDeriv xi) (s + 3 / 2))).symm
  have hnumMero : MeromorphicAt
      (fun s : ℂ => deriv (logDeriv xi) (s - 1 / 2) - deriv (logDeriv xi) (s + 3 / 2)) p :=
    hm1.sub hm2b
  have hnum : meromorphicOrderAt
      (fun s : ℂ => deriv (logDeriv xi) (s - 1 / 2) - deriv (logDeriv xi) (s + 3 / 2)) p
      = ((-2 : ℤ) : WithTop ℤ) := by
    have hsum : ((fun s : ℂ => deriv (logDeriv xi) (s - 1 / 2))
        + (fun s : ℂ => -deriv (logDeriv xi) (s + 3 / 2)))
        = fun s : ℂ => deriv (logDeriv xi) (s - 1 / 2) - deriv (logDeriv xi) (s + 3 / 2) := by
      funext s
      simp only [Pi.add_apply]
      ring
    have hne : meromorphicOrderAt (fun s : ℂ => deriv (logDeriv xi) (s - 1 / 2)) p
        ≠ meromorphicOrderAt (fun s : ℂ => -deriv (logDeriv xi) (s + 3 / 2)) p := by
      rw [hLord, hRneg]
      exact fun h => analytic_meromorphicOrderAt_ne_neg_two hRan h.symm
    have h := meromorphicOrderAt_add_of_ne hm1 hm2 hne
    rw [hsum, hLord, hRneg] at h
    rw [h]
    exact min_eq_left (analytic_neg_two_le_meromorphicOrderAt hRan)
  have hdenMero : MeromorphicAt (fun s : ℂ => 2 * s ^ (2 : ℕ)) p :=
    (analyticAt_const.mul (analyticAt_id.pow 2)).meromorphicAt
  have hden : meromorphicOrderAt (fun s : ℂ => 2 * s ^ (2 : ℕ)) p = 0 := by
    have han : AnalyticAt ℂ (fun s : ℂ => 2 * s ^ (2 : ℕ)) p :=
      analyticAt_const.mul (analyticAt_id.pow 2)
    have hval : (fun s : ℂ => 2 * s ^ (2 : ℕ)) p ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hpne)
    rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr hval]
    simp
  have hdiv : suzukiPositionTorqueLaplaceContinuation
      = (fun s : ℂ => deriv (logDeriv xi) (s - 1 / 2) - deriv (logDeriv xi) (s + 3 / 2))
        / (fun s : ℂ => 2 * s ^ (2 : ℕ)) := by
    funext s
    rw [suzukiPositionTorqueLaplaceContinuation]
    rfl
  rw [hdiv, meromorphicOrderAt_div hnumMero hdenMero, hnum, hden, sub_zero]

end RHTower
