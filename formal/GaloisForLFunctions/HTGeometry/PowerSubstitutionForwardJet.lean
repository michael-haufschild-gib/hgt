import GaloisForLFunctions.HTGeometry.PowerSubstitutionJet

/-!
# Inverting the `q`-th power chain rule

The chain rule for `z ↦ z^q` expresses the jets of the pullback `g(z) = f(z^q)` as a triangular
combination of the pulled-back jets of `f`.  This file inverts that relation: writing
`s = q X^{q-1}` for the pullback multiplier, one has

`s(z)^{2j} · f^{(j)}(z^q) = ∑_{i ≤ j} n_{j,i}(z) · g^{(i)}(z)`

with polynomial coefficients obeying `n_{0,0} = 1` and

`n_{j+1,i} = (n_{j,i}' + n_{j,i-1}) s − 2j · n_{j,i} s'`.

The inversion is division-free: it follows by differentiating the previous identity and using
`s · f^{(j+1)}(z^q) = (f^{(j)}(·^q))'`, so no denominator is ever introduced.  The transition matrix
`n` is again lower triangular, with diagonal `n_{j,j} = s^j`.
-/

namespace HTGeometry

open Polynomial

/-- The pullback multiplier `s = q X^{q-1}` of the substitution `z ↦ z^q`. -/
noncomputable def powScale (q : ℕ) : Polynomial ℂ := Polynomial.C (q : ℂ) * Polynomial.X ^ (q - 1)

@[simp] theorem eval_powScale (q : ℕ) (z : ℂ) :
    (powScale q).eval z = (q : ℂ) * z ^ (q - 1) := by
  simp [powScale]

/-- Coefficients inverting the `q`-th power chain rule. -/
noncomputable def powInvCoeff (q : ℕ) : ℕ → ℕ → Polynomial ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, 0 =>
      (powInvCoeff q j 0).derivative * powScale q
        - Polynomial.C ((2 * j : ℕ) : ℂ) * (powInvCoeff q j 0) * (powScale q).derivative
  | j + 1, i + 1 =>
      ((powInvCoeff q j (i + 1)).derivative + powInvCoeff q j i) * powScale q
        - Polynomial.C ((2 * j : ℕ) : ℂ) * (powInvCoeff q j (i + 1)) * (powScale q).derivative

@[simp] theorem powInvCoeff_zero_zero (q : ℕ) : powInvCoeff q 0 0 = 1 := rfl

@[simp] theorem powInvCoeff_zero_succ (q i : ℕ) : powInvCoeff q 0 (i + 1) = 0 := rfl

theorem powInvCoeff_succ_zero (q j : ℕ) :
    powInvCoeff q (j + 1) 0
      = (powInvCoeff q j 0).derivative * powScale q
        - Polynomial.C ((2 * j : ℕ) : ℂ) * (powInvCoeff q j 0) * (powScale q).derivative := rfl

theorem powInvCoeff_succ_succ (q j i : ℕ) :
    powInvCoeff q (j + 1) (i + 1)
      = ((powInvCoeff q j (i + 1)).derivative + powInvCoeff q j i) * powScale q
        - Polynomial.C ((2 * j : ℕ) : ℂ) * (powInvCoeff q j (i + 1))
            * (powScale q).derivative := rfl

/-- The inverse transition matrix is lower triangular. -/
theorem powInvCoeff_eq_zero_of_lt (q : ℕ) {j i : ℕ} (h : j < i) : powInvCoeff q j i = 0 := by
  induction j generalizing i with
  | zero =>
    obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp
  | succ j ih =>
    obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [powInvCoeff_succ_succ, ih (by omega), ih (by omega)]
    simp

/-- The diagonal of the inverse transition matrix is `s^j`. -/
theorem powInvCoeff_self (q j : ℕ) : powInvCoeff q j j = powScale q ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [powInvCoeff_succ_succ, powInvCoeff_eq_zero_of_lt q (Nat.lt_succ_self j), ih]
    simp [pow_succ, mul_comm]

/-- **Inverted chain rule.**  The pulled-back jets of `f` are recovered from the jets of
`z ↦ f(z^q)` after multiplication by a power of the pullback multiplier.  No division occurs. -/
theorem pow_mul_iteratedDeriv_comp_pow {f : ℂ → ℂ} {q : ℕ}
    (hf : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m f))
    (hg : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m (fun w : ℂ => f (w ^ q))))
    (j : ℕ) (z : ℂ) :
    ((powScale q).eval z) ^ (2 * j) * iteratedDeriv j f (z ^ q)
      = ∑ i ∈ Finset.range (j + 1),
          (powInvCoeff q j i).eval z * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z := by
  have hu : ∀ (m : ℕ) (x : ℂ),
      HasDerivAt (fun y : ℂ => iteratedDeriv m f (y ^ q))
        ((powScale q).eval x * iteratedDeriv (m + 1) f (x ^ q)) x := by
    intro m x
    have houter : HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f (x ^ q)) (x ^ q) := by
      have h := (hf m (x ^ q)).hasDerivAt
      rwa [← iteratedDeriv_succ] at h
    have hinner : HasDerivAt (fun y : ℂ => y ^ q) ((q : ℂ) * x ^ (q - 1)) x := hasDerivAt_pow q x
    have hcomp := houter.comp x hinner
    have hval : (powScale q).eval x * iteratedDeriv (m + 1) f (x ^ q)
        = iteratedDeriv (m + 1) f (x ^ q) * ((q : ℂ) * x ^ (q - 1)) := by
      rw [eval_powScale]; ring
    rw [hval]
    exact hcomp
  have hG : ∀ (i : ℕ) (x : ℂ),
      HasDerivAt (iteratedDeriv i (fun w : ℂ => f (w ^ q)))
        (iteratedDeriv (i + 1) (fun w : ℂ => f (w ^ q)) x) x := by
    intro i x
    have h := (hg i x).hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  induction j generalizing z with
  | zero => simp
  | succ j ih =>
    set S : ℂ := (powScale q).eval z with hS
    set S' : ℂ := (powScale q).derivative.eval z with hS'
    -- the two sides of the inductive hypothesis, as functions
    have hIHfun : (fun y : ℂ => ((powScale q).eval y) ^ (2 * j) * iteratedDeriv j f (y ^ q))
        = fun y : ℂ => ∑ i ∈ Finset.range (j + 1),
            (powInvCoeff q j i).eval y * iteratedDeriv i (fun w : ℂ => f (w ^ q)) y :=
      funext fun y => ih y
    have hLeft : HasDerivAt
        (fun y : ℂ => ((powScale q).eval y) ^ (2 * j) * iteratedDeriv j f (y ^ q))
        (((2 * j : ℕ) : ℂ) * S ^ (2 * j - 1) * S' * iteratedDeriv j f (z ^ q)
          + S ^ (2 * j) * (S * iteratedDeriv (j + 1) f (z ^ q))) z := by
      have hpowS : HasDerivAt (fun y : ℂ => ((powScale q).eval y) ^ (2 * j))
          (((2 * j : ℕ) : ℂ) * S ^ (2 * j - 1) * S') z := by
        have hbase : HasDerivAt (fun y : ℂ => (powScale q).eval y) S' z :=
          (powScale q).hasDerivAt z
        exact hbase.pow (2 * j)
      exact hpowS.mul (hu j z)
    have hRight : HasDerivAt
        (fun y : ℂ => ∑ i ∈ Finset.range (j + 1),
          (powInvCoeff q j i).eval y * iteratedDeriv i (fun w : ℂ => f (w ^ q)) y)
        (∑ i ∈ Finset.range (j + 1),
          ((powInvCoeff q j i).derivative.eval z
              * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z
            + (powInvCoeff q j i).eval z
              * iteratedDeriv (i + 1) (fun w : ℂ => f (w ^ q)) z)) z :=
      HasDerivAt.fun_sum fun i _ => ((powInvCoeff q j i).hasDerivAt z).mul (hG i z)
    rw [hIHfun] at hLeft
    have hderiv := hLeft.unique hRight
    -- multiply the differentiated identity by `S` and use the inductive hypothesis again
    have hcoeff : ((2 * j : ℕ) : ℂ) * S ^ (2 * j - 1) * S
        = ((2 * j : ℕ) : ℂ) * S ^ (2 * j) := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp
      · have h2 : 2 * j - 1 + 1 = 2 * j := by omega
        rw [mul_assoc, ← pow_succ, h2]
    have hmul : S * (((2 * j : ℕ) : ℂ) * S ^ (2 * j - 1) * S' * iteratedDeriv j f (z ^ q)
          + S ^ (2 * j) * (S * iteratedDeriv (j + 1) f (z ^ q)))
        = S * (∑ i ∈ Finset.range (j + 1),
            ((powInvCoeff q j i).derivative.eval z
                * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z
              + (powInvCoeff q j i).eval z
                * iteratedDeriv (i + 1) (fun w : ℂ => f (w ^ q)) z)) := by
      rw [hderiv]
    have hIHz := ih z
    have hkey : S ^ (2 * (j + 1)) * iteratedDeriv (j + 1) f (z ^ q)
        = ∑ i ∈ Finset.range (j + 1),
            (((powInvCoeff q j i).derivative.eval z * S
                - ((2 * j : ℕ) : ℂ) * (powInvCoeff q j i).eval z * S')
              * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z
            + (powInvCoeff q j i).eval z * S
              * iteratedDeriv (i + 1) (fun w : ℂ => f (w ^ q)) z) := by
      have hexpand : S * (((2 * j : ℕ) : ℂ) * S ^ (2 * j - 1) * S'
            * iteratedDeriv j f (z ^ q)
          + S ^ (2 * j) * (S * iteratedDeriv (j + 1) f (z ^ q)))
          = ((2 * j : ℕ) : ℂ) * S' * (S ^ (2 * j) * iteratedDeriv j f (z ^ q))
            + S ^ (2 * (j + 1)) * iteratedDeriv (j + 1) f (z ^ q) := by
        have hpow : S ^ (2 * (j + 1)) = S ^ (2 * j) * S ^ 2 := by
          rw [show (2 * (j + 1)) = 2 * j + 2 by ring, pow_add]
        rw [hpow]
        linear_combination (S' * iteratedDeriv j f (z ^ q)) * hcoeff
      rw [hexpand, hIHz, Finset.mul_sum, Finset.mul_sum] at hmul
      have hfinal : S ^ (2 * (j + 1)) * iteratedDeriv (j + 1) f (z ^ q)
          = (∑ i ∈ Finset.range (j + 1),
              S * ((powInvCoeff q j i).derivative.eval z
                    * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z
                  + (powInvCoeff q j i).eval z
                    * iteratedDeriv (i + 1) (fun w : ℂ => f (w ^ q)) z))
            - ∑ i ∈ Finset.range (j + 1), ((2 * j : ℕ) : ℂ) * S'
                * ((powInvCoeff q j i).eval z * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z) := by
        linear_combination hmul
      rw [hfinal, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hkey, Finset.sum_add_distrib]
    -- reindex the target sum
    have hdrop : ∑ i ∈ Finset.range (j + 1 + 1),
          ((powInvCoeff q j i).derivative.eval z * S
              - ((2 * j : ℕ) : ℂ) * (powInvCoeff q j i).eval z * S')
            * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z
        = ∑ i ∈ Finset.range (j + 1),
          ((powInvCoeff q j i).derivative.eval z * S
              - ((2 * j : ℕ) : ℂ) * (powInvCoeff q j i).eval z * S')
            * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z := by
      rw [Finset.sum_range_succ, powInvCoeff_eq_zero_of_lt q (Nat.lt_succ_self j)]
      simp
    have hshiftA := Finset.sum_range_succ'
      (fun i => ((powInvCoeff q j i).derivative.eval z * S
          - ((2 * j : ℕ) : ℂ) * (powInvCoeff q j i).eval z * S')
        * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z) (j + 1)
    have hshiftT := Finset.sum_range_succ'
      (fun i => (powInvCoeff q (j + 1) i).eval z
        * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z) (j + 1)
    rw [hshiftT]
    have hsucc2 : ∀ i ∈ Finset.range (j + 1),
        (powInvCoeff q (j + 1) (i + 1)).eval z
            * iteratedDeriv (i + 1) (fun w : ℂ => f (w ^ q)) z
          = ((powInvCoeff q j (i + 1)).derivative.eval z * S
              - ((2 * j : ℕ) : ℂ) * (powInvCoeff q j (i + 1)).eval z * S')
              * iteratedDeriv (i + 1) (fun w : ℂ => f (w ^ q)) z
            + (powInvCoeff q j i).eval z * S
              * iteratedDeriv (i + 1) (fun w : ℂ => f (w ^ q)) z := by
      intro i _
      rw [powInvCoeff_succ_succ]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_C, hS, hS']
      ring
    have hzero : (powInvCoeff q (j + 1) 0).eval z
          * iteratedDeriv 0 (fun w : ℂ => f (w ^ q)) z
        = ((powInvCoeff q j 0).derivative.eval z * S
            - ((2 * j : ℕ) : ℂ) * (powInvCoeff q j 0).eval z * S')
            * iteratedDeriv 0 (fun w : ℂ => f (w ^ q)) z := by
      rw [powInvCoeff_succ_zero]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hS, hS']
    rw [Finset.sum_congr rfl hsucc2, hzero, Finset.sum_add_distrib, ← hdrop, hshiftA]
    ring

end HTGeometry
