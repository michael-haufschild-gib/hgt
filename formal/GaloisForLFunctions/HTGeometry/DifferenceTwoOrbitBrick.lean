import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

/-!
# Two-orbit difference brick

The unit shift `X ↦ X + 1` on rational functions cannot produce a prescribed pole part supported on
a single `ℤ`-orbit.  This file proves the two-orbit form: if `w = p/q` satisfies

  `w(X+1) - w(X) = A / ((X - c₀)^(n+1) (X - c₁)^(k+1))`

with `c₀ - c₁ ∉ ℤ` and `natDegree A ≤ n + k + 1`, then `A = 0`.

The mechanism is the same pinch as in the single-orbit case, applied once to each orbit: evaluating
the cross-multiplied identity at the largest root of `q` in an orbit forces that root to be the
orbit's base point, and evaluating one step below the smallest root forces the smallest root to be
one step past it — incompatible unless `q` has no root in the orbit at all.  With `q` and its shift
free of roots at both base points, the denominator is coprime to them and must divide `A`, whose
degree is too small.

Separating the two orbits is what makes the archimedean factor's parity modes independent: the poles
of `ψ(s/2)` and of `ψ((s+1)/2)` lie in `ℤ`-orbits that differ by a half-integer.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **Orbit pinch.** If the cross-multiplied shift-difference identity has a numerator factor `B`
vanishing on the orbit `t + ℤ` only at `t` itself, then `q` has no root in that orbit. -/
theorem q_eval_ne_zero_of_orbit {p q A B : Polynomial ℂ} (hq : q ≠ 0)
    (hpz : ∀ z : ℂ, q.eval z = 0 → p.eval z ≠ 0)
    (h : B * (p.comp (X + C 1) * q - p * q.comp (X + C 1))
      = A * (q * q.comp (X + C 1)))
    (t : ℂ) (hB : ∀ m : ℤ, B.eval (t + (m : ℂ)) = 0 → m = 0) :
    ∀ m : ℤ, q.eval (t + (m : ℂ)) ≠ 0 := by
  by_contra hcon
  simp only [not_forall, ne_eq, not_not] at hcon
  obtain ⟨m₀, hm₀⟩ := hcon
  have hfin : {m : ℤ | q.eval (t + (m : ℂ)) = 0}.Finite := by
    have hroots : {x : ℂ | q.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hq
    have hinj : Function.Injective (fun m : ℤ => t + (m : ℂ)) := by
      intro a b hab
      have : ((a : ℂ)) = ((b : ℂ)) := by
        have := hab
        simpa using this
      exact_mod_cast this
    exact Set.Finite.preimage hinj.injOn hroots
  have hne : hfin.toFinset.Nonempty := ⟨m₀, by simpa using hm₀⟩
  set M : ℤ := hfin.toFinset.max' hne with hM_def
  set μ : ℤ := hfin.toFinset.min' hne with hμ_def
  have hMroot : q.eval (t + (M : ℂ)) = 0 := by
    have := hfin.toFinset.max'_mem hne
    simpa using this
  have hμroot : q.eval (t + (μ : ℂ)) = 0 := by
    have := hfin.toFinset.min'_mem hne
    simpa using this
  have hM1 : q.eval (t + ((M + 1 : ℤ) : ℂ)) ≠ 0 := by
    intro hr
    have hmem : (M + 1 : ℤ) ∈ hfin.toFinset := by simpa using hr
    have := hfin.toFinset.le_max' _ hmem
    omega
  have hμ1 : q.eval (t + ((μ - 1 : ℤ) : ℂ)) ≠ 0 := by
    intro hr
    have hmem : (μ - 1 : ℤ) ∈ hfin.toFinset := by simpa using hr
    have := hfin.toFinset.min'_le _ hmem
    omega
  have hMzero : M = 0 := by
    have hM := congrArg (Polynomial.eval (t + (M : ℂ))) h
    simp only [eval_mul, eval_sub, eval_comp, eval_add, eval_X, eval_C] at hM
    rw [hMroot] at hM
    rw [show t + (M : ℂ) + 1 = t + ((M + 1 : ℤ) : ℂ) by push_cast; ring] at hM
    simp only [mul_zero, zero_mul, zero_sub, mul_neg] at hM
    have hBz : B.eval (t + (M : ℂ)) = 0 := by
      rcases mul_eq_zero.mp (neg_eq_zero.mp hM) with h' | h'
      · exact h'
      · exact absurd h' (mul_ne_zero (hpz _ hMroot) hM1)
    exact hB M hBz
  have hμone : μ = 1 := by
    have hm := congrArg (Polynomial.eval (t + ((μ - 1 : ℤ) : ℂ))) h
    simp only [eval_mul, eval_sub, eval_comp, eval_add, eval_X, eval_C] at hm
    rw [show t + ((μ - 1 : ℤ) : ℂ) + 1 = t + (μ : ℂ) by push_cast; ring] at hm
    rw [hμroot] at hm
    simp only [mul_zero, sub_zero] at hm
    have hBz : B.eval (t + ((μ - 1 : ℤ) : ℂ)) = 0 := by
      rcases mul_eq_zero.mp hm with h' | h'
      · exact h'
      · exact absurd h' (mul_ne_zero (hpz _ hμroot) hμ1)
    have := hB (μ - 1) hBz
    omega
  have hle := hfin.toFinset.min'_le _ (hfin.toFinset.max'_mem hne)
  omega

/-- Coprimality of a linear factor with a polynomial that does not vanish at its root. -/
theorem isCoprime_X_sub_C_of_eval_ne_zero {a : ℂ} {q : Polynomial ℂ} (h : q.eval a ≠ 0) :
    IsCoprime (X - C a) q := by
  refine ((Polynomial.prime_X_sub_C a).irreducible.coprime_iff_not_dvd).mpr ?_
  intro hdvd
  exact h (Polynomial.dvd_iff_isRoot.mp hdvd)

/-- **Two-orbit difference brick.** A rational function cannot have a unit-shift difference whose
pole part is supported on two `ℤ`-orbits with incommensurable base points. -/
theorem difference_two_orbit_pole_free {p q A : Polynomial ℂ} {c₀ c₁ : ℂ} {n k : ℕ}
    (hq : q ≠ 0) (hco : IsCoprime p q)
    (hsep : ∀ m : ℤ, c₀ - c₁ ≠ (m : ℂ))
    (hdeg : A.natDegree ≤ n + k + 1)
    (h : (X - C c₀) ^ (n + 1) * (X - C c₁) ^ (k + 1) *
          (p.comp (X + C 1) * q - p * q.comp (X + C 1))
        = A * (q * q.comp (X + C 1))) :
    A = 0 := by
  have hpz : ∀ z : ℂ, q.eval z = 0 → p.eval z ≠ 0 := by
    intro z hqz hpz
    obtain ⟨a, b, hab⟩ := hco
    have := congrArg (Polynomial.eval z) hab
    simp only [eval_add, eval_mul, eval_one, hpz, hqz, mul_zero, add_zero] at this
    exact one_ne_zero this.symm
  set B : Polynomial ℂ := (X - C c₀) ^ (n + 1) * (X - C c₁) ^ (k + 1) with hB_def
  have hBeval : ∀ z : ℂ, B.eval z = (z - c₀) ^ (n + 1) * (z - c₁) ^ (k + 1) := by
    intro z
    simp [hB_def]
  have horb0 : ∀ m : ℤ, q.eval (c₀ + (m : ℂ)) ≠ 0 := by
    refine q_eval_ne_zero_of_orbit hq hpz h c₀ ?_
    intro m hm
    rw [hBeval] at hm
    rcases mul_eq_zero.mp hm with h' | h'
    · have hz : c₀ + (m : ℂ) - c₀ = 0 := pow_eq_zero_iff (by omega : n + 1 ≠ 0) |>.mp h'
      have : ((m : ℂ)) = 0 := by linear_combination hz
      exact_mod_cast this
    · have hz : c₀ + (m : ℂ) - c₁ = 0 := pow_eq_zero_iff (by omega : k + 1 ≠ 0) |>.mp h'
      exact absurd (show c₀ - c₁ = ((-m : ℤ) : ℂ) by push_cast; linear_combination hz)
        (hsep (-m))
  have horb1 : ∀ m : ℤ, q.eval (c₁ + (m : ℂ)) ≠ 0 := by
    refine q_eval_ne_zero_of_orbit hq hpz h c₁ ?_
    intro m hm
    rw [hBeval] at hm
    rcases mul_eq_zero.mp hm with h' | h'
    · have hz : c₁ + (m : ℂ) - c₀ = 0 := pow_eq_zero_iff (by omega : n + 1 ≠ 0) |>.mp h'
      exact absurd (show c₀ - c₁ = ((m : ℤ) : ℂ) by linear_combination -hz) (hsep m)
    · have hz : c₁ + (m : ℂ) - c₁ = 0 := pow_eq_zero_iff (by omega : k + 1 ≠ 0) |>.mp h'
      have : ((m : ℂ)) = 0 := by linear_combination hz
      exact_mod_cast this
  have hshiftEval : ∀ z : ℂ, (q.comp (X + C 1)).eval z = q.eval (z + 1) := by
    intro z
    simp [eval_comp]
  have hq0 : q.eval c₀ ≠ 0 := by simpa using horb0 0
  have hq0' : (q.comp (X + C 1)).eval c₀ ≠ 0 := by
    rw [hshiftEval]
    have := horb0 1
    simpa using this
  have hq1 : q.eval c₁ ≠ 0 := by simpa using horb1 0
  have hq1' : (q.comp (X + C 1)).eval c₁ ≠ 0 := by
    rw [hshiftEval]
    have := horb1 1
    simpa using this
  have hcop0 : IsCoprime ((X - C c₀) ^ (n + 1)) (q * q.comp (X + C 1)) :=
    IsCoprime.pow_left
      ((isCoprime_X_sub_C_of_eval_ne_zero hq0).mul_right
        (isCoprime_X_sub_C_of_eval_ne_zero hq0'))
  have hcop1 : IsCoprime ((X - C c₁) ^ (k + 1)) (q * q.comp (X + C 1)) :=
    IsCoprime.pow_left
      ((isCoprime_X_sub_C_of_eval_ne_zero hq1).mul_right
        (isCoprime_X_sub_C_of_eval_ne_zero hq1'))
  have hcopB : IsCoprime B (q * q.comp (X + C 1)) := hcop0.mul_left hcop1
  have hdvd : B ∣ A * (q * q.comp (X + C 1)) := ⟨_, h.symm⟩
  have hBA : B ∣ A := hcopB.dvd_of_dvd_mul_right hdvd
  by_contra hA
  have hdegB : B.natDegree = n + k + 2 := by
    rw [hB_def, Polynomial.natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero c₀))
      (pow_ne_zero _ (X_sub_C_ne_zero c₁)), Polynomial.natDegree_pow,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
    ring
  have := Polynomial.natDegree_le_of_dvd hBA hA
  omega

/-- **Two-orbit brick from a pointwise identity.** An analytic shift-difference relation holding on
any infinite set of complex numbers already forces the pole-part numerator to vanish. -/
theorem difference_two_orbit_pole_free_of_eval {p q A : Polynomial ℂ} {c₀ c₁ : ℂ} {n k : ℕ}
    (hq : q ≠ 0) (hco : IsCoprime p q)
    (hsep : ∀ m : ℤ, c₀ - c₁ ≠ (m : ℂ))
    (hdeg : A.natDegree ≤ n + k + 1)
    {S : Set ℂ} (hS : S.Infinite)
    (heval : ∀ z ∈ S,
      (z - c₀) ^ (n + 1) * (z - c₁) ^ (k + 1) *
          (p.eval (z + 1) * q.eval z - p.eval z * q.eval (z + 1))
        = A.eval z * (q.eval z * q.eval (z + 1))) :
    A = 0 := by
  refine difference_two_orbit_pole_free hq hco hsep hdeg ?_
  have hpoly : (X - C c₀) ^ (n + 1) * (X - C c₁) ^ (k + 1) *
        (p.comp (X + C 1) * q - p * q.comp (X + C 1))
      - A * (q * q.comp (X + C 1)) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine hS.mono ?_
    intro z hz
    have hval := heval z hz
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, eval_sub, eval_mul, eval_pow, eval_comp,
      eval_add, eval_X, eval_C]
    linear_combination hval
  linear_combination hpoly

end GaloisForLFunctions.HTGeometry
