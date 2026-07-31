import GaloisForLFunctions.RHTower.SuzukiFiniteMorseResolventJetCompletion
import GaloisForLFunctions.HTGeometry.ResolventFamilyJet
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

/-! ## The finite-Morse completion at operator level -/

/-- **`(T1)` at operator level.**  The finite-Morse interpolant completes the affine Krein defect
of the below-spectrum resolvent to a positive operator, whenever the spectrum of the resolvent
consists of the compactification point together with resolvent coordinates of the finitely many
negative spectral levels and of positive spectral levels. -/
theorem suzukiFiniteMorse_operatorCompletion_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {alpha beta rho : ℝ} {negativeLevel : ι → ℝ} {R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hab : alpha < beta) (hb0 : beta < 0) (hrho0 : rho < 0)
    (hbt : ∀ i, beta < negativeLevel i) (hnegative : ∀ i, negativeLevel i < 0)
    (hrho : ∀ i, rho < negativeLevel i) (hinjective : Function.Injective negativeLevel)
    (hden : ∀ x ∈ spectrum ℝ R,
      (rho * x + 1) * ((rho - alpha) * x + 1) * ((rho - beta) * x + 1) ≠ 0)
    (hspectrum : ∀ x ∈ spectrum ℝ R, x = 0 ∨
      (∃ i, x = suzukiFiniteMorseResolventNode rho (negativeLevel i)) ∨
      (∃ t : ℝ, 0 < t ∧ x = suzukiFiniteMorseResolventNode rho t)) :
    0 ≤ suzukiOperatorKreinDefect alpha beta rho R
      + suzukiResolventJetSquare
          (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel) R := by
  rw [suzukiOperatorCompletion_nonneg_iff hR _ hden]
  intro x hx
  rcases hspectrum x hx with h0 | ⟨i, hi⟩ | ⟨t, htpos, hti⟩
  · subst h0
    rw [suzukiKreinResolventWeight_zero, suzukiFiniteMorseKreinInterpolant,
      suzukiFiniteMorseInterpolant_eval_zero]
    norm_num
  · subst hi
    have hlevel := hnegative i
    rw [suzukiKreinResolventWeight_resolventNode (ne_of_lt hab) (ne_of_lt hlevel)
      (ne_of_gt (lt_trans hab (hbt i))) (ne_of_gt (hbt i)) (ne_of_gt (hrho i)),
      suzukiFiniteMorseKreinInterpolant_cancels_negativeDefect
        hab hb0 hbt hnegative hrho hinjective i]
  · subst hti
    have hta : t ≠ alpha := ne_of_gt (lt_trans (lt_trans hab hb0) htpos)
    have htb : t ≠ beta := ne_of_gt (lt_trans hb0 htpos)
    have htr : t ≠ rho := ne_of_gt (lt_trans hrho0 htpos)
    rw [suzukiKreinResolventWeight_resolventNode (ne_of_lt hab) (ne_of_gt htpos) hta htb htr]
    exact suzukiPolynomialResolventSquare_preserves_positiveDefect
      (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel) hab hb0 htpos

/-- The completed operator has nonnegative energy on every state. -/
theorem suzukiFiniteMorse_operatorCompletion_re_inner_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {alpha beta rho : ℝ} {negativeLevel : ι → ℝ} {R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hab : alpha < beta) (hb0 : beta < 0) (hrho0 : rho < 0)
    (hbt : ∀ i, beta < negativeLevel i) (hnegative : ∀ i, negativeLevel i < 0)
    (hrho : ∀ i, rho < negativeLevel i) (hinjective : Function.Injective negativeLevel)
    (hden : ∀ x ∈ spectrum ℝ R,
      (rho * x + 1) * ((rho - alpha) * x + 1) * ((rho - beta) * x + 1) ≠ 0)
    (hspectrum : ∀ x ∈ spectrum ℝ R, x = 0 ∨
      (∃ i, x = suzukiFiniteMorseResolventNode rho (negativeLevel i)) ∨
      (∃ t : ℝ, 0 < t ∧ x = suzukiFiniteMorseResolventNode rho t)) (v : H) :
    0 ≤ RCLike.re (inner ℂ ((suzukiOperatorKreinDefect alpha beta rho R
      + suzukiResolventJetSquare
          (suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel) R) v) v) :=
  ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (suzukiFiniteMorse_operatorCompletion_nonneg hR hab hb0 hrho0 hbt hnegative hrho hinjective
      hden hspectrum)).re_inner_nonneg_left v

/-! ## Eigenvector evaluation and the exact-projector no-go -/

omit [CompleteSpace H] in
/-- Powers act on an eigenvector by powers of the eigenvalue. -/
theorem pow_apply_of_eigenvector {R : H →L[ℂ] H} {x : ℝ} {v : H}
    (hv : R v = ((x : ℝ) : ℂ) • v) (n : ℕ) : (R ^ n) v = (((x ^ n : ℝ)) : ℂ) • v := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hstep : (R ^ (k + 1)) v = (R ^ k) (R v) := by
        rw [pow_succ]
        rfl
      rw [hstep, hv, ContinuousLinearMap.map_smul, ih, smul_smul]
      push_cast
      ring_nf

omit [CompleteSpace H] in
/-- Real scalars act on a complex space through the coercion. -/
theorem real_smul_complex_smul (c : ℝ) (z : ℂ) (v : H) :
    c • (z • v) = ((c : ℂ) * z) • v := by
  have h : ((c : ℂ)) • (z • v) = c • (z • v) := by
    simp
  rw [← h, smul_smul]

omit [CompleteSpace H] in
/-- A real polynomial in an operator acts on an eigenvector by its value at the eigenvalue. -/
theorem aeval_apply_of_eigenvector {q : ℝ[X]} {R : H →L[ℂ] H} {x : ℝ} {v : H}
    (hv : R v = ((x : ℝ) : ℂ) • v) :
    (Polynomial.aeval R q) v = ((q.eval x : ℝ) : ℂ) • v := by
  classical
  have hsum : Polynomial.aeval R q
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • R ^ i :=
    Polynomial.aeval_eq_sum_range R
  have hev : q.eval x = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * x ^ i :=
    Polynomial.eval_eq_sum_range x
  have hstep : ∀ i : ℕ, (q.coeff i • R ^ i : H →L[ℂ] H) v
      = (((q.coeff i * x ^ i : ℝ)) : ℂ) • v := by
    intro i
    have hpow : (R ^ i) v = (((x ^ i : ℝ)) : ℂ) • v := pow_apply_of_eigenvector hv i
    have h1 : (q.coeff i • R ^ i : H →L[ℂ] H) v = q.coeff i • ((R ^ i) v) := rfl
    rw [h1, hpow, real_smul_complex_smul]
    push_cast
    ring_nf
  have hsumapp : (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • R ^ i : H →L[ℂ] H) v
      = ∑ i ∈ Finset.range (q.natDegree + 1), (q.coeff i • R ^ i : H →L[ℂ] H) v := by
    simp
  rw [hsum, hsumapp, hev, Complex.ofReal_sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => hstep i

omit [CompleteSpace H] in
/-- The jet square acts on an eigenvector by the squared polynomial value. -/
theorem suzukiResolventJetSquare_apply_of_eigenvector {q : ℝ[X]} {R : H →L[ℂ] H} {x : ℝ} {v : H}
    (hv : R v = ((x : ℝ) : ℂ) • v) :
    suzukiResolventJetSquare q R v = (((q.eval x ^ 2 : ℝ)) : ℂ) • v := by
  have hstep : suzukiResolventJetSquare q R v
      = (Polynomial.aeval R q) ((Polynomial.aeval R q) v) := by
    rw [suzukiResolventJetSquare, pow_two]
    rfl
  rw [hstep, aeval_apply_of_eigenvector hv, ContinuousLinearMap.map_smul,
    aeval_apply_of_eigenvector hv, smul_smul]
  push_cast
  ring_nf

omit [CompleteSpace H] in
theorem real_smul_left_cancel {c d : ℝ} {v : H} (hv : v ≠ 0)
    (h : ((c : ℝ) : ℂ) • v = ((d : ℝ) : ℂ) • v) : c = d := by
  have hsub : (((c - d : ℝ)) : ℂ) • v = 0 := by
    push_cast
    rw [sub_smul, h]
    simp
  rcases smul_eq_zero.mp hsub with hz | hz
  · have : (c : ℝ) - d = 0 := by exact_mod_cast hz
    linarith
  · exact absurd hz hv

omit [CompleteSpace H] in
/-- **`(5)` at operator level.**  No finite resolvent-jet square is the exact minimal projector
completion.  Vanishing on an infinite tail of positive eigenvectors forces the polynomial to
vanish identically, after which no strictly positive negative-level debt can be paid. -/
theorem suzukiOperatorResolventJetSquare_exactProjector_impossible
    {q : ℝ[X]} {R : H →L[ℂ] H} {positiveNodes : Set ℝ} {negativeNode debt : ℝ}
    (hinfinite : positiveNodes.Infinite)
    (hpositive : ∀ x ∈ positiveNodes, ∃ v : H, v ≠ 0 ∧ R v = ((x : ℝ) : ℂ) • v ∧
      suzukiResolventJetSquare q R v = 0)
    (hnegative : ∃ v : H, v ≠ 0 ∧ R v = ((negativeNode : ℝ) : ℂ) • v ∧
      suzukiResolventJetSquare q R v = ((debt : ℝ) : ℂ) • v)
    (hdebt : 0 < debt) : False := by
  have htail : ∀ x ∈ positiveNodes, q.eval x ^ 2 = 0 := by
    intro x hx
    obtain ⟨v, hv0, hveig, hvzero⟩ := hpositive x hx
    rw [suzukiResolventJetSquare_apply_of_eigenvector hveig] at hvzero
    have : ((q.eval x ^ 2 : ℝ) : ℂ) • v = ((0 : ℝ) : ℂ) • v := by
      rw [hvzero]
      simp
    exact real_smul_left_cancel hv0 this
  obtain ⟨v, hv0, hveig, hvdebt⟩ := hnegative
  rw [suzukiResolventJetSquare_apply_of_eigenvector hveig] at hvdebt
  have hmatch : q.eval negativeNode ^ 2 = debt := real_smul_left_cancel hv0 hvdebt
  exact suzukiFiniteResolventPolynomial_exactProjector_impossible q hinfinite htail hdebt hmatch

/-! ## `(T3)`: the interpolant is a finite shift jet of the resolvent family -/

omit [CompleteSpace H] in
/-- The finite-Morse interpolant of a compact resolvent is a compact operator: its zero constant
term removes the identity component. -/
theorem isCompactOperator_suzukiFiniteMorseInterpolant
    {ι : Type*} [Fintype ι] [DecidableEq ι] (alpha beta rho : ℝ) (t : ι → ℝ)
    {R : H →L[ℂ] H} (hR : IsCompactOperator ⇑R) :
    IsCompactOperator
      ⇑(Polynomial.aeval R (suzukiFiniteMorseKreinInterpolant alpha beta rho t)) := by
  refine isCompactOperator_suzukiResolventJet ?_ hR
  rw [Polynomial.coeff_zero_eq_eval_zero, suzukiFiniteMorseKreinInterpolant,
    suzukiFiniteMorseInterpolant_eval_zero]

/-- **`(T3)`.**  Evaluated at one below-spectrum resolvent, the finite-Morse interpolant is
exactly a finite combination of normalized shift derivatives of the resolvent family: the `n`-th
normalized jet is `n! R^{n+1}`, and each differentiates to the next. -/
theorem suzukiFiniteMorseInterpolant_eq_resolventShiftJetSum
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] (S : ℝ → A) (v : ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (alpha beta rho : ℝ) (t : ι → ℝ) :
    Polynomial.aeval (S v) (suzukiFiniteMorseKreinInterpolant alpha beta rho t)
      = ∑ n ∈ Finset.range (suzukiFiniteMorseKreinInterpolant alpha beta rho t).natDegree,
          ((suzukiFiniteMorseKreinInterpolant alpha beta rho t).coeff (n + 1)
              / (Nat.factorial n : ℝ))
            • GaloisForLFunctions.HTGeometry.resolventShiftJet S n v := by
  refine GaloisForLFunctions.HTGeometry.aeval_eq_resolventShiftJet_sum S v _ ?_
  rw [Polynomial.coeff_zero_eq_eval_zero, suzukiFiniteMorseKreinInterpolant,
    suzukiFiniteMorseInterpolant_eval_zero]

/-! ## `(3)`: the block behaviour in the resolvent coordinate -/

/-- **`(3)`, negative block.**  Read in the resolvent coordinate, the completed Krein weight
vanishes identically at every negative spectral level: there the jet square is exactly the
negative of the affine Krein defect. -/
theorem suzukiFiniteMorse_completedWeight_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {alpha beta rho : ℝ} {negativeLevel : ι → ℝ}
    (hab : alpha < beta) (hb0 : beta < 0)
    (hbt : ∀ i, beta < negativeLevel i) (hnegative : ∀ i, negativeLevel i < 0)
    (hrho : ∀ i, rho < negativeLevel i) (hinjective : Function.Injective negativeLevel) (i : ι) :
    suzukiKreinResolventWeight alpha beta rho
        (suzukiFiniteMorseResolventNode rho (negativeLevel i))
      + ((suzukiFiniteMorseKreinInterpolant alpha beta rho negativeLevel).eval
          (suzukiFiniteMorseResolventNode rho (negativeLevel i))) ^ 2 = 0 := by
  rw [suzukiKreinResolventWeight_resolventNode (ne_of_lt hab) (ne_of_lt (hnegative i))
    (ne_of_gt (lt_trans hab (hbt i))) (ne_of_gt (hbt i)) (ne_of_gt (hrho i))]
  exact suzukiFiniteMorseKreinInterpolant_cancels_negativeDefect
    hab hb0 hbt hnegative hrho hinjective i

/-- **`(3)`, positive block.**  At every positive spectral level the bare affine Krein weight is
already strictly positive in the resolvent coordinate, so any added jet square only overpays. -/
theorem suzukiFiniteMorse_kreinResolventWeight_pos
    {alpha beta rho t : ℝ} (hab : alpha < beta) (hb0 : beta < 0) (hrho0 : rho < 0)
    (htpos : 0 < t) :
    0 < suzukiKreinResolventWeight alpha beta rho (suzukiFiniteMorseResolventNode rho t) := by
  have hta : t ≠ alpha := ne_of_gt (lt_trans (lt_trans hab hb0) htpos)
  have htb : t ≠ beta := ne_of_gt (lt_trans hb0 htpos)
  have htr : t ≠ rho := ne_of_gt (lt_trans hrho0 htpos)
  rw [suzukiKreinResolventWeight_resolventNode (ne_of_lt hab) (ne_of_gt htpos) hta htb htr]
  exact (suzukiAffineResolventKreinDefect_pos_iff hab hb0 (lt_trans hb0 htpos)
    (ne_of_gt htpos)).2 htpos

end

end RHTower
