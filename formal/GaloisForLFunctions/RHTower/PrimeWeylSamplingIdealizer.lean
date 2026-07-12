import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Complex.Basic

/-!
# Finite shift--Weyl collapse on an infinite sampling nullspace

This is the algebraic separation core of the prime-modulated Weyl idealizer theorem. A finite
shift--differential operator is encoded by polynomial coefficient fields acting on freely
prescribable finite jets. If it preserves the nullspace of an infinite sampling set, then every
coefficient attached to a shift with infinitely many sampling failures vanishes. Every positive
jet coefficient at the zero shift also vanishes. Only the zero-shift, zero-jet polynomial
multiplier can remain.

The analytic paper theorem obtains the freely prescribable jets from compactly supported smooth
functions and obtains infinite shift-failure sets from symmetry plus superlinear sampling density.
-/

open scoped BigOperators

noncomputable section
namespace RHTower

/-- A field of independently prescribable jets of orders `0,...,m` on the spectral line. -/
abbrev SamplingJetField (m : ℕ) := Fin (m + 1) → ℂ → ℂ

/-- Evaluation of a finite shift--jet operator with polynomial coefficient fields. -/
def finiteShiftJetAction (m : ℕ) (F : Finset ℂ)
    (a : ℂ → Fin (m + 1) → Polynomial ℂ)
    (phi : SamplingJetField m) (x : ℂ) : ℂ :=
  ∑ h ∈ F, ∑ j : Fin (m + 1), (a h j).eval x * phi j (x + h)

/-- The operator sends every jet field whose value component vanishes on `S` to another value
component vanishing on `S`. This is the sampling-nullspace idealizer condition. -/
def PreservesSamplingNull (m : ℕ) (S : Set ℂ) (F : Finset ℂ)
    (a : ℂ → Fin (m + 1) → Polynomial ℂ) : Prop :=
  ∀ phi : SamplingJetField m,
    (∀ x ∈ S, phi 0 x = 0) →
      ∀ x ∈ S, finiteShiftJetAction m F a phi x = 0

/-- The jet field with one prescribed unit jet at one spectral point. -/
def isolatedJetField (m : ℕ) (j : Fin (m + 1)) (y : ℂ) : SamplingJetField m :=
  fun k z => if k = j ∧ z = y then 1 else 0

theorem isolatedJetField_apply_self (m : ℕ) (j : Fin (m + 1)) (y : ℂ) :
    isolatedJetField m j y j y = 1 := by
  simp [isolatedJetField]

theorem isolatedJetField_apply_of_ne
    (m : ℕ) (j k : Fin (m + 1)) (y z : ℂ)
    (h : k ≠ j ∨ z ≠ y) :
    isolatedJetField m j y k z = 0 := by
  have hne : ¬ (k = j ∧ z = y) := by
    intro hkz
    exact h.elim (fun hk => hk hkz.1) (fun hz => hz hkz.2)
  simp [isolatedJetField, hne]

/-- If one shift misses the sampling set at infinitely many points, every polynomial coefficient
attached to that shift is zero. -/
theorem shiftPolynomial_eq_zero_of_infinite_failure
    {m : ℕ} {S : Set ℂ} {F : Finset ℂ}
    {a : ℂ → Fin (m + 1) → Polynomial ℂ}
    (hpres : PreservesSamplingNull m S F a)
    {h : ℂ} (hhF : h ∈ F) (j : Fin (m + 1))
    (hfail : Set.Infinite {x : ℂ | x ∈ S ∧ x + h ∉ S}) :
    a h j = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply hfail.mono
  intro x hx
  have hnull : ∀ y ∈ S, isolatedJetField m j (x + h) 0 y = 0 := by
    intro y hy
    apply isolatedJetField_apply_of_ne
    by_cases hj : (0 : Fin (m + 1)) = j
    · right
      intro hyx
      exact hx.2 (hyx ▸ hy)
    · exact Or.inl hj
  have hzero := hpres (isolatedJetField m j (x + h)) hnull x hx.1
  rw [finiteShiftJetAction] at hzero
  have hsum :
      (∑ h' ∈ F, ∑ k : Fin (m + 1),
          (a h' k).eval x * isolatedJetField m j (x + h) k (x + h')) =
        (a h j).eval x := by
    rw [Finset.sum_eq_single h]
    · rw [Finset.sum_eq_single j]
      · simp [isolatedJetField]
      · intro k _ hkj
        simp [isolatedJetField, hkj]
      · simp
    · intro h' hh' hhne
      have hpoint : x + h' ≠ x + h := by
        intro heq
        exact hhne (add_left_cancel heq)
      simp [isolatedJetField, hpoint]
    · intro hhnot
      exact (hhnot hhF).elim
  rw [hsum] at hzero
  exact hzero

/-- On an infinite sampling set, every positive-order zero-shift jet coefficient is zero. -/
theorem derivativePolynomial_eq_zero_of_infinite_samples
    {m : ℕ} {S : Set ℂ} {F : Finset ℂ}
    {a : ℂ → Fin (m + 1) → Polynomial ℂ}
    (hpres : PreservesSamplingNull m S F a)
    (hzeroF : (0 : ℂ) ∈ F) (hS : S.Infinite)
    (j : Fin (m + 1)) (hj : j ≠ 0) :
    a 0 j = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply hS.mono
  intro x hx
  have hnull : ∀ y ∈ S, isolatedJetField m j x 0 y = 0 := by
    intro y hy
    exact isolatedJetField_apply_of_ne m j 0 x y (Or.inl (Ne.symm hj))
  have hzero := hpres (isolatedJetField m j x) hnull x hx
  rw [finiteShiftJetAction] at hzero
  have hsum :
      (∑ h ∈ F, ∑ k : Fin (m + 1),
          (a h k).eval x * isolatedJetField m j x k (x + h)) =
        (a 0 j).eval x := by
    rw [Finset.sum_eq_single 0]
    · rw [Finset.sum_eq_single j]
      · simp [isolatedJetField]
      · intro k _ hkj
        simp [isolatedJetField, hkj]
      · simp
    · intro h hh hne
      have hpoint : x + h ≠ x := by
        simpa [add_eq_left] using hne
      simp [isolatedJetField, hpoint]
    · intro hnot
      exact (hnot hzeroF).elim
  rw [hsum] at hzero
  exact hzero

/-- **Finite prime--Weyl coefficient collapse.** Under infinite failure of every nonzero shift,
sampling-nullspace preservation kills every coefficient except the zero-shift, zero-jet
polynomial multiplier. -/
theorem primeWeylSampling_coeff_collapse
    {m : ℕ} {S : Set ℂ} {F : Finset ℂ}
    {a : ℂ → Fin (m + 1) → Polynomial ℂ}
    (hpres : PreservesSamplingNull m S F a)
    (hzeroF : (0 : ℂ) ∈ F) (hS : S.Infinite)
    (hfail : ∀ h ∈ F, h ≠ 0 →
      Set.Infinite {x : ℂ | x ∈ S ∧ x + h ∉ S}) :
    ∀ h ∈ F, ∀ j : Fin (m + 1), h ≠ 0 ∨ j ≠ 0 → a h j = 0 := by
  intro h hhF j hhj
  rcases hhj with hh | hj
  · exact shiftPolynomial_eq_zero_of_infinite_failure hpres hhF j (hfail h hhF hh)
  · by_cases hh : h = 0
    · subst h
      exact derivativePolynomial_eq_zero_of_infinite_samples hpres hzeroF hS j hj
    · exact shiftPolynomial_eq_zero_of_infinite_failure hpres hhF j (hfail h hhF hh)

end RHTower
