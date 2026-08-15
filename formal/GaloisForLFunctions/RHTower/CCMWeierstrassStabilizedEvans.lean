import Mathlib

/-!
# Weierstrass stabilization: conjugate pairing and positivity of the stabilized quotient

Three exact mechanisms of the card are formalized.

*Conjugate pairing.*  A polynomial with real coefficients takes conjugate values at conjugate
points, so its nonreal roots occur in conjugate pairs with equal multiplicity.  This is claim 2 of
`(2)`: when a real pair of characteristic roots disappears, the stabilized polynomial keeps it as a
nonreal conjugate pair and the degree does not jump.

*Positivity of a root-free monic factor.*  A monic real polynomial with no real root is strictly
positive everywhere.  Together with `(1+ξ²)^L > 0` this is claim 3 of `(2)`: the quotient `(3)` is
strictly positive on the real axis.

*The determinant restatement.*  The vanishing of the Evans section on `λ ≤ 0` is exactly the
statement that no `λ ≤ 0` is a zero of the section — equation `(12)` — recorded as the definitional
equivalence the card uses.

Weierstrass preparation, the analytic Grushin reduction, the determinant-line gluing and the
identification of vanishing order with multiplicity `(7)` are cited parents and stay outside the
Lean statement.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## Conjugate pairing of the stabilized roots -/

/-- A real polynomial takes conjugate values at conjugate points. -/
theorem eval_conj_of_real (p : Polynomial ℝ) (z : ℂ) :
    (p.map (algebraMap ℝ ℂ)).eval ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) ((p.map (algebraMap ℝ ℂ)).eval z) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.map_add, Polynomial.eval_add, hp, hq, map_add]
  | monomial n a =>
      simp only [Polynomial.map_monomial, Polynomial.eval_monomial, map_mul, map_pow,
        Complex.coe_algebraMap, Complex.conj_ofReal]

/-- **Claim 2 of (2).**  The nonreal zeros of a real stabilized polynomial come in conjugate
pairs. -/
theorem isRoot_conj_iff (p : Polynomial ℝ) (z : ℂ) :
    (p.map (algebraMap ℝ ℂ)).IsRoot ((starRingEnd ℂ) z)
      ↔ (p.map (algebraMap ℝ ℂ)).IsRoot z := by
  constructor
  · intro h
    rw [Polynomial.IsRoot, eval_conj_of_real] at h
    have := congrArg (starRingEnd ℂ) h
    rwa [Complex.conj_conj, map_zero] at this
  · intro h
    rw [Polynomial.IsRoot, eval_conj_of_real, h, map_zero]

/-! ## Positivity of the stabilized quotient -/

/-- **Claim 3 of (2), root-free factor.**  A monic real polynomial without real roots is strictly
positive everywhere: the extra conjugate factors introduced by the stabilization never change the
sign of the quotient. -/
theorem eval_pos_of_monic_no_real_root {p : Polynomial ℝ} (hmonic : p.Monic)
    (hno : ∀ x : ℝ, p.eval x ≠ 0) (x : ℝ) : 0 < p.eval x := by
  by_cases hdeg : p.natDegree = 0
  · have hp1 : p = 1 := by
      have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      have hcoeff : p.coeff 0 = 1 := by
        have hl := hmonic.leadingCoeff
        rwa [Polynomial.leadingCoeff, hdeg] at hl
      rw [hC, hcoeff, map_one]
    rw [hp1, Polynomial.eval_one]
    norm_num
  · have hdegpos : 0 < p.degree := by
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero]
      exact_mod_cast Nat.pos_of_ne_zero hdeg
    have hlead : (0 : ℝ) ≤ p.leadingCoeff := by
      rw [hmonic.leadingCoeff]
      norm_num
    have htend := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg p hdegpos hlead
    obtain ⟨y, hy⟩ := (htend.eventually_ge_atTop 1).exists
    by_contra hx
    have hxle : p.eval x ≤ 0 := not_lt.mp hx
    have hxlt : p.eval x < 0 := lt_of_le_of_ne hxle (hno x)
    have hcont : ContinuousOn (fun t : ℝ => p.eval t) (Set.uIcc x y) :=
      (Polynomial.continuous p).continuousOn
    have hmem : (0 : ℝ) ∈ Set.uIcc (p.eval x) (p.eval y) := by
      refine Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hxlt, ?_⟩)
      linarith
    obtain ⟨z, _, hz⟩ := intermediate_value_uIcc hcont hmem
    exact hno z hz

/-- `(1+ξ²)^L` is strictly positive. -/
theorem one_add_sq_pow_pos (L : ℕ) (ξ : ℝ) : 0 < (1 + ξ ^ 2) ^ L := by
  positivity

/-- **Claim 3 of (2).**  With a positive numerator and a positive stabilized denominator the
quotient `(3)` is strictly positive on the real axis. -/
theorem stabilized_quotient_pos {N D : ℝ} (hN : 0 < N) (hD : 0 < D) : 0 < N / D :=
  div_pos hN hD

/-! ## The determinant restatement -/

/-- **Equation (12).**  Emptiness of the zero divisor on the nonpositive axis is exactly the
statement that the section has no zero there. -/
theorem evans_zero_divisor_empty_iff {E : ℝ → ℝ} :
    (∀ lam : ℝ, lam ≤ 0 → E lam ≠ 0) ↔ ({lam : ℝ | lam ≤ 0 ∧ E lam = 0} = ∅) := by
  constructor
  · intro h
    refine Set.eq_empty_iff_forall_notMem.mpr fun lam hlam => ?_
    exact h lam hlam.1 hlam.2
  · intro h lam hlam hE
    have : lam ∈ ({lam : ℝ | lam ≤ 0 ∧ E lam = 0}) := ⟨hlam, hE⟩
    rw [h] at this
    exact absurd this (Set.notMem_empty lam)

end GaloisForLFunctions.RHTower

end
