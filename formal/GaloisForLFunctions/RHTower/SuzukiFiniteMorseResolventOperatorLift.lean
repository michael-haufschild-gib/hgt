import GaloisForLFunctions.RHTower.SuzukiFiniteMorseResolventJetCompletion
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Operator lift of the finite-Morse resolvent completion

The finite-Morse theorem is stated for the below-spectrum resolvent `R = (A - rho)⁻¹` of a
lower-bounded self-adjoint operator.  Its scalar core — the zero-constant Lagrange interpolant,
the exact negative debts, and the infinite-positive-tail no-go — is already algebra.  This module
lifts the statement to the operator level.

The lift is carried by the continuous functional calculus of the bounded self-adjoint operator
`R`, not by a spectral decomposition of `A`.  Reading the affine Krein weight in the resolvent
coordinate `x = 1/(t - rho)` turns

`d(t) = alpha*beta / (t (t - alpha) (t - beta))`

into the rational function

`w(x) = alpha*beta*x^3 / ((rho x + 1)((rho - alpha) x + 1)((rho - beta) x + 1))`,

which is regular at `x = 0` and vanishes there.  Hence `d(A)` is a genuine continuous function of
`R` even though `A` is unbounded, and the completion inequality `D + q(R)^2 >= 0` becomes exactly
the pointwise inequality `w + q^2 >= 0` on the spectrum of `R`.

Zero constant term of the interpolant is what makes its operator realization compact, and the
same zero constant term makes `w(0) + q(0)^2 = 0`, so the accumulation point `0` of the spectrum
of a compact resolvent costs nothing.

Everything is unconditional: no RH premise, no Xi divisor, no estimate, and no computation.
-/

open Polynomial ContinuousLinearMap

namespace RHTower

noncomputable section

/-! ## The affine Krein weight in the resolvent coordinate -/

/-- The affine Krein weight read in the resolvent coordinate `x = 1 / (t - rho)`.  The cubic
numerator makes it regular, and zero, at the spectral accumulation point `x = 0`. -/
def suzukiKreinResolventWeight (alpha beta rho x : ℝ) : ℝ :=
  alpha * beta * x ^ 3 /
    ((rho * x + 1) * ((rho - alpha) * x + 1) * ((rho - beta) * x + 1))

@[simp] theorem suzukiKreinResolventWeight_zero (alpha beta rho : ℝ) :
    suzukiKreinResolventWeight alpha beta rho 0 = 0 := by
  simp [suzukiKreinResolventWeight]

/-- **Spectral bridge.**  In the resolvent coordinate the weight is the affine Krein defect. -/
theorem suzukiKreinResolventWeight_resolventNode
    {alpha beta rho t : ℝ} (hab : alpha ≠ beta) (ht0 : t ≠ 0) (hta : t ≠ alpha)
    (htb : t ≠ beta) (htr : t ≠ rho) :
    suzukiKreinResolventWeight alpha beta rho (suzukiFiniteMorseResolventNode rho t)
      = suzukiAffineResolventKreinDefect alpha beta t := by
  have hd : t - rho ≠ 0 := sub_ne_zero.mpr htr
  have hta' : t - alpha ≠ 0 := sub_ne_zero.mpr hta
  have htb' : t - beta ≠ 0 := sub_ne_zero.mpr htb
  have h1 : rho * (t - rho)⁻¹ + 1 = t / (t - rho) := by
    field_simp
    ring
  have h2 : (rho - alpha) * (t - rho)⁻¹ + 1 = (t - alpha) / (t - rho) := by
    field_simp
    ring
  have h3 : (rho - beta) * (t - rho)⁻¹ + 1 = (t - beta) / (t - rho) := by
    field_simp
    ring
  have key : t / (t - rho) * ((t - alpha) / (t - rho)) * ((t - beta) / (t - rho))
      = t * (t - alpha) * (t - beta) / (t - rho) ^ 3 := by
    field_simp
  rw [suzukiAffineResolventKreinDefect_eq hab ht0 hta htb, suzukiFiniteMorseResolventNode,
    suzukiKreinResolventWeight, h1, h2, h3, key, div_div_eq_mul_div]
  congr 1
  field_simp

/-- The weight is continuous wherever its three linear factors are nonzero. -/
theorem continuousOn_suzukiKreinResolventWeight (alpha beta rho : ℝ) {s : Set ℝ}
    (hs : ∀ x ∈ s,
      (rho * x + 1) * ((rho - alpha) * x + 1) * ((rho - beta) * x + 1) ≠ 0) :
    ContinuousOn (suzukiKreinResolventWeight alpha beta rho) s := by
  unfold suzukiKreinResolventWeight
  exact ContinuousOn.div (by fun_prop) (by fun_prop) hs

/-! ## The operator completion -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The affine Krein defect operator `d(A)`, realized as a continuous function of the
below-spectrum resolvent. -/
def suzukiOperatorKreinDefect (alpha beta rho : ℝ) (R : H →L[ℂ] H) : H →L[ℂ] H :=
  cfc (suzukiKreinResolventWeight alpha beta rho) R

/-- The finite resolvent-jet square `q(R)^2`. -/
def suzukiResolventJetSquare (q : ℝ[X]) (R : H →L[ℂ] H) : H →L[ℂ] H :=
  (Polynomial.aeval R q) ^ 2

theorem suzukiResolventJet_isSelfAdjoint (q : ℝ[X]) {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) :
    IsSelfAdjoint (Polynomial.aeval R q) := by
  rw [← cfc_polynomial q R]
  exact cfc_predicate _ _

/-- **The jet square is a positive operator.** -/
theorem suzukiResolventJetSquare_nonneg (q : ℝ[X]) {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) :
    0 ≤ suzukiResolventJetSquare q R := by
  have hsa : IsSelfAdjoint (Polynomial.aeval R q) := suzukiResolventJet_isSelfAdjoint q hR
  have : suzukiResolventJetSquare q R
      = star (Polynomial.aeval R q) * (Polynomial.aeval R q) := by
    rw [suzukiResolventJetSquare, hsa.star_eq, sq]
  rw [this]
  exact star_mul_self_nonneg _

omit [CompleteSpace H] in
/-- Powers of a compact operator are compact. -/
theorem isCompactOperator_pow {R : H →L[ℂ] H} (hR : IsCompactOperator ⇑R) :
    ∀ n : ℕ, IsCompactOperator ⇑(R ^ (n + 1)) := by
  intro n
  induction n with
  | zero => simpa using hR
  | succ k ih =>
      have hmul : ⇑(R ^ (k + 1 + 1)) = ⇑(R ^ (k + 1)) ∘ ⇑R := by
        ext x
        simp [pow_succ]
      rw [hmul]
      exact ih.comp_clm R

omit [CompleteSpace H] in
/-- **Compactness of the resolvent jet.**  Zero constant term is exactly what removes the
identity component, so the jet inherits compactness of the resolvent. -/
theorem isCompactOperator_suzukiResolventJet {q : ℝ[X]} (hq : q.coeff 0 = 0)
    {R : H →L[ℂ] H} (hR : IsCompactOperator ⇑R) :
    IsCompactOperator ⇑(Polynomial.aeval R q) := by
  classical
  have hsum : Polynomial.aeval R q
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • R ^ i :=
    Polynomial.aeval_eq_sum_range R
  rw [hsum]
  have hcoe : ⇑(∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • R ^ i)
      = ∑ i ∈ Finset.range (q.natDegree + 1), ⇑(q.coeff i • R ^ i) := by
    ext x
    simp
  rw [hcoe]
  refine Finset.sum_induction _ IsCompactOperator (fun f g hf hg => hf.add hg)
    isCompactOperator_zero ?_
  intro i _
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have : (q.coeff 0 • R ^ 0 : H →L[ℂ] H) = 0 := by rw [hq]; simp
    rw [this]
    exact isCompactOperator_zero
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hcoe2 : ⇑(q.coeff (k + 1) • R ^ (k + 1)) = q.coeff (k + 1) • ⇑(R ^ (k + 1)) := by
      ext x; simp
    rw [hcoe2]
    exact (isCompactOperator_pow hR k).smul _

/-- The completion operator is the functional calculus of the pointwise completion. -/
theorem suzukiOperatorCompletion_eq_cfc
    {alpha beta rho : ℝ} {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) (q : ℝ[X])
    (hcont : ContinuousOn (suzukiKreinResolventWeight alpha beta rho) (spectrum ℝ R)) :
    suzukiOperatorKreinDefect alpha beta rho R + suzukiResolventJetSquare q R
      = cfc (fun x => suzukiKreinResolventWeight alpha beta rho x + (q.eval x) ^ 2) R := by
  have hpoly : ContinuousOn (fun x : ℝ => q.eval x) (spectrum ℝ R) :=
    (Polynomial.continuous_aeval q).continuousOn
  have hsq : cfc (fun x : ℝ => (q.eval x) ^ 2) R = suzukiResolventJetSquare q R := by
    rw [cfc_pow (fun x : ℝ => q.eval x) 2 R hpoly, suzukiResolventJetSquare, cfc_polynomial q R]
  rw [cfc_add R _ _ hcont (by exact hpoly.pow 2), hsq, suzukiOperatorKreinDefect]

/-- **`(T2)` at operator level.**  The finite resolvent-jet square completes the affine Krein
defect to a positive operator exactly when it dominates the pointwise debt on the spectrum of the
resolvent. -/
theorem suzukiOperatorCompletion_nonneg_iff
    {alpha beta rho : ℝ} {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) (q : ℝ[X])
    (hden : ∀ x ∈ spectrum ℝ R,
      (rho * x + 1) * ((rho - alpha) * x + 1) * ((rho - beta) * x + 1) ≠ 0) :
    0 ≤ suzukiOperatorKreinDefect alpha beta rho R + suzukiResolventJetSquare q R ↔
      ∀ x ∈ spectrum ℝ R, 0 ≤ suzukiKreinResolventWeight alpha beta rho x + (q.eval x) ^ 2 := by
  have hcont : ContinuousOn (suzukiKreinResolventWeight alpha beta rho) (spectrum ℝ R) :=
    continuousOn_suzukiKreinResolventWeight alpha beta rho hden
  have hpoly : ContinuousOn (fun x : ℝ => q.eval x) (spectrum ℝ R) :=
    (Polynomial.continuous_aeval q).continuousOn
  rw [suzukiOperatorCompletion_eq_cfc hR q hcont]
  exact cfc_nonneg_iff _ R (hcont.add (hpoly.pow 2)) hR

end

end RHTower
