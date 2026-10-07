import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorThetaDefect
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorResiduePolynomial

/-!
# Exact interior deficit poles

Every clearing root lies in the strict critical strip. Its pole order is exactly
the missing multiplicity below one copy of xi, so its logarithmic residue
polynomial cannot vanish. No RH or simple-zero hypothesis is used.
-/

noncomputable section

open Complex Set Filter Topology Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

/-- Every zero of xi lies strictly between the two boundary lines Re=0 and Re=1. -/
theorem xi_zero_re_mem_Ioo {ρ : ℂ} (hρ : xi ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  have hupper : ∀ s : ℂ, xi s = 0 → s.re < 1 := by
    intro s hz
    by_contra h
    have hre : 1 ≤ s.re := le_of_not_gt h
    have hspos : 0 < s.re := by linarith
    have hs0 : s ≠ 0 := by intro h0; norm_num [h0] at hre
    have hs1 : s ≠ 1 := by intro h1; norm_num [h1, xi_one] at hz
    have he := MaassZetaSquaredConverse.two_xi_eq hspos hs1
    rw [hz, mul_zero] at he
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
      (Complex.Gammaℝ_ne_zero_of_re_pos hspos)) (riemannZeta_ne_zero_of_one_le_re hre)) he.symm
  refine ⟨?_, hupper ρ hρ⟩
  have h := hupper (1 - ρ) (by simpa only [xi_one_sub] using hρ)
  simp only [sub_re, one_re] at h
  linarith

/-- The exact deficit polynomial has no roots away from xi's zero divisor. -/
theorem deficitPolynomial_root_xi_zero {E : ℂ → ℂ} (P : Polynomial ℂ)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {ρ : ℂ} (hρ : P.eval ρ = 0) : xi ρ = 0 := by
  by_contra hx
  have hxiord : analyticOrderAt xi ρ = 0 :=
    (xi_analyticOnNhd_univ ρ (mem_univ _)).analyticOrderAt_eq_zero.mpr hx
  have hd : xiDeficit E ρ = 0 := by simp [xiDeficit, analyticOrderNatAt, hxiord]
  have hPA : AnalyticAt ℂ (fun w => P.eval w) ρ :=
    P.differentiable.differentiableOn.analyticAt Filter.univ_mem
  have hp : P.eval ρ ≠ 0 := hPA.analyticOrderAt_eq_zero.mp (by rw [hord, hd, Nat.cast_zero])
  exact hp hρ

/-- Every actual interior pole belongs to the strip required by the Poisson modes. -/
theorem deficitPolynomial_root_re_mem_Ioo {E : ℂ → ℂ} (P : Polynomial ℂ)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {ρ : ℂ} (hρ : P.eval ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 :=
  xi_zero_re_mem_Ioo (deficitPolynomial_root_xi_zero P hord hρ)

/-- A root records a strictly positive missing multiplicity. -/
theorem deficitPolynomial_root_deficit_pos {E : ℂ → ℂ} (P : Polynomial ℂ)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {ρ : ℂ} (hρ : P.eval ρ = 0) : 0 < xiDeficit E ρ := by
  apply Nat.pos_of_ne_zero
  intro hd
  have hPA : AnalyticAt ℂ (fun w => P.eval w) ρ :=
    P.differentiable.differentiableOn.analyticAt Filter.univ_mem
  have hp : P.eval ρ ≠ 0 := hPA.analyticOrderAt_eq_zero.mp (by rw [hord, hd, Nat.cast_zero])
  exact hp hρ

private lemma entire_order_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf1 : f 1 ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro ht
  have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
    (fun w => hf.differentiableOn.analyticAt Filter.univ_mem)).mp ht
  exact hf1 (congrFun hz 1)

/-- Exact pole clearing cannot leave a common zero of its numerator and its polynomial. -/
theorem poleClearedNumerator_ne_zero_at_root {E H : ℂ → ℂ}
    (hE : Differentiable ℂ E) (hE1 : E 1 ≠ 0)
    (hH : Differentiable ℂ H) (hH1 : H 1 ≠ 0) (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {ρ : ℂ} (hρ : P.eval ρ = 0) : H ρ ≠ 0 := by
  have hPA : AnalyticAt ℂ (fun w => P.eval w) ρ :=
    P.differentiable.differentiableOn.analyticAt Filter.univ_mem
  have hEA : AnalyticAt ℂ E ρ := hE.differentiableOn.analyticAt Filter.univ_mem
  have hHA : AnalyticAt ℂ H ρ := hH.differentiableOn.analyticAt Filter.univ_mem
  have hXA : AnalyticAt ℂ xi ρ := xi_analyticOnNhd_univ ρ (mem_univ _)
  have hPf : analyticOrderAt (fun w => P.eval w) ρ ≠ ⊤ := by rw [hord]; simp
  have hEf := entire_order_ne_top hE hE1 ρ
  have hHf := entire_order_ne_top hH hH1 ρ
  have hXf := entire_order_ne_top xi_differentiable (by rw [xi_one]; norm_num) ρ
  have hpn : analyticOrderNatAt (fun w => P.eval w) ρ = xiDeficit E ρ := by
    simp only [analyticOrderNatAt, hord, ENat.toNat_coe]
  have heq : (fun w => P.eval w) * E = H * xi := funext hfac
  have ho := congrArg (fun f : ℂ → ℂ => analyticOrderNatAt f ρ) heq
  rw [analyticOrderNatAt_mul hPA hEA hPf hEf, analyticOrderNatAt_mul hHA hXA hHf hXf,
    hpn] at ho
  have hd := deficitPolynomial_root_deficit_pos P hord hρ
  have hn : analyticOrderNatAt H ρ = 0 := by unfold xiDeficit at ho hd; omega
  apply hHA.analyticOrderAt_eq_zero.mp
  rw [← Nat.cast_analyticOrderNatAt hHf, hn, Nat.cast_zero]

/-- The pole order equals exactly the deficit, with every multiplicity retained. -/
theorem poleClearedDegreeTwoCompletion_order_at_root {E H : ℂ → ℂ}
    (hE : Differentiable ℂ E) (hE1 : E 1 ≠ 0)
    (hH : Differentiable ℂ H) (hH1 : H 1 ≠ 0) (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {ρ : ℂ} (hρ : P.eval ρ = 0) :
    meromorphicOrderAt (poleClearedDegreeTwoCompletion P H) ρ = (-(xiDeficit E ρ : ℤ) : WithTop ℤ) := by
  have hr := deficitPolynomial_root_re_mem_Ioo P hord hρ
  have h0 : ρ ≠ 0 := by intro hz; norm_num [hz] at hr
  have h1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr (by intro hz; norm_num [hz] at hr)
  have hn := poleClearedNumerator_ne_zero_at_root hE hE1 hH hH1 P hfac hord hρ
  have hPA : AnalyticAt ℂ (fun w => P.eval w) ρ :=
    P.differentiable.differentiableOn.analyticAt Filter.univ_mem
  have hden : AnalyticAt ℂ (fun s : ℂ => 2 * s ^ 2 * (s - 1) ^ 2) ρ := by fun_prop
  have hden0 : (2 : ℂ) * ρ ^ 2 * (ρ - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ h0)) (pow_ne_zero _ h1)
  have hA : AnalyticAt ℂ (fun s : ℂ => H s / (2 * s ^ 2 * (s - 1) ^ 2)) ρ :=
    (hH.differentiableOn.analyticAt Filter.univ_mem).div hden hden0
  have hA0 : H ρ / (2 * ρ ^ 2 * (ρ - 1) ^ 2) ≠ 0 := div_ne_zero hn hden0
  have heq : poleClearedDegreeTwoCompletion P H =
      (fun s : ℂ => H s / (2 * s ^ 2 * (s - 1) ^ 2)) / (fun s => P.eval s) := by
    funext s
    dsimp only [poleClearedDegreeTwoCompletion, Pi.div_apply]
    rw [div_div]
    congr 1
    ring
  rw [heq, meromorphicOrderAt_div hA.meromorphicAt hPA.meromorphicAt,
    hA.meromorphicOrderAt_eq, hA.analyticOrderAt_eq_zero.mpr hA0,
    hPA.meromorphicOrderAt_eq, hord]
  simp

/-- Every genuine deficit produces a nonremovable pole of the actual completion. -/
theorem poleClearedDegreeTwoCompletion_order_neg_at_root {E H : ℂ → ℂ}
    (hE : Differentiable ℂ E) (hE1 : E 1 ≠ 0)
    (hH : Differentiable ℂ H) (hH1 : H 1 ≠ 0) (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {ρ : ℂ} (hρ : P.eval ρ = 0) : meromorphicOrderAt (poleClearedDegreeTwoCompletion P H) ρ < 0 := by
  rw [poleClearedDegreeTwoCompletion_order_at_root hE hE1 hH hH1 P hfac hord hρ]
  have hd := deficitPolynomial_root_deficit_pos P hord hρ
  norm_cast
  omega

end RHTower.WeilHigherDenominator
