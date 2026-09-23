import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic

/-!
# The scaled logarithmic derivative and its degeneracy

The leading behaviour of a product law's bordered determinant is governed by the *scaled logarithmic
derivative* `T = v·Q'/Q`, whose numerator-cleared derivative is

`Q²·T' = (v'Q' + v·Q'')·Q − v·(Q')²`.

Two facts make this the right object.  It is additive in `Q` — the Wronskian obeys a product rule
`W(P·R) = R²·W(P) + P²·W(R)`, because `T` is a logarithmic derivative — and it **vanishes exactly on
the powers of `v`**: for `Q = K·v^k` with `v` linear, `T = k·v'` is constant.

That is the degenerate locus of the general product law, and the exponential tower sits on it
(`Q = v = X`).  So the tower's determinant argument is the argument at the one place where the scaled
logarithmic derivative carries no information, which is why it does not generalise.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- The cleared derivative of the scaled logarithmic derivative `v·Q'/Q`. -/
noncomputable def scaledLogWronskian (Q v : Polynomial ℂ) : Polynomial ℂ :=
  (v.derivative * Q.derivative + v * Q.derivative.derivative) * Q - v * Q.derivative ^ (2 : ℕ)

/-- **The product rule.**  The scaled logarithmic derivative is additive, so its Wronskian is a
weighted sum. -/
theorem scaledLogWronskian_mul (P R v : Polynomial ℂ) :
    scaledLogWronskian (P * R) v
      = R ^ (2 : ℕ) * scaledLogWronskian P v + P ^ (2 : ℕ) * scaledLogWronskian R v := by
  simp only [scaledLogWronskian, derivative_mul, derivative_add]
  ring

@[simp] theorem scaledLogWronskian_C (K : ℂ) (v : Polynomial ℂ) :
    scaledLogWronskian (Polynomial.C K) v = 0 := by
  simp [scaledLogWronskian]

/-- On `v` itself the Wronskian is the curvature of `v`. -/
theorem scaledLogWronskian_self (v : Polynomial ℂ) :
    scaledLogWronskian v v = v ^ (2 : ℕ) * v.derivative.derivative := by
  simp only [scaledLogWronskian]
  ring

/-- **The powers of a linear `v` are the degenerate locus.** -/
theorem scaledLogWronskian_pow {v : Polynomial ℂ} (hv : v.derivative.derivative = 0) (k : ℕ) :
    scaledLogWronskian (v ^ k) v = 0 := by
  induction k with
  | zero => simpa using scaledLogWronskian_C 1 v
  | succ k ih =>
      rw [pow_succ, scaledLogWronskian_mul, ih, scaledLogWronskian_self, hv]
      simp

theorem scaledLogWronskian_C_mul_pow {v : Polynomial ℂ} (hv : v.derivative.derivative = 0)
    (K : ℂ) (k : ℕ) : scaledLogWronskian (Polynomial.C K * v ^ k) v = 0 := by
  rw [scaledLogWronskian_mul, scaledLogWronskian_C, scaledLogWronskian_pow hv]
  simp

/-! ## The cross term dominates -/

/-- A crude degree bound for the Wronskian: no cancellation is needed. -/
theorem natDegree_scaledLogWronskian_le {Q v : Polynomial ℂ} (hv : v.natDegree ≤ 1) :
    (scaledLogWronskian Q v).natDegree ≤ 2 * Q.natDegree - 1 := by
  rcases Nat.eq_zero_or_pos Q.natDegree with hq0 | hq1
  · have hzero : Q.derivative = 0 := by
      rw [Polynomial.derivative_eq_zero]
      exact hq0
    rw [scaledLogWronskian, hzero]
    simp
  have hQ' : Q.derivative.natDegree ≤ Q.natDegree - 1 := Polynomial.natDegree_derivative_le Q
  have hQ'' : Q.derivative.derivative.natDegree ≤ Q.derivative.natDegree - 1 :=
    Polynomial.natDegree_derivative_le Q.derivative
  have hv' : v.derivative.natDegree ≤ v.natDegree - 1 := Polynomial.natDegree_derivative_le v
  have hmid : (v.derivative * Q.derivative + v * Q.derivative.derivative).natDegree
      ≤ Q.natDegree - 1 := by
    rcases Nat.lt_or_ge Q.natDegree 2 with hq | hq
    · have hzero : Q.derivative.derivative = 0 := by
        rw [Polynomial.derivative_eq_zero]
        omega
      rw [hzero, mul_zero, add_zero]
      have h1 : (v.derivative * Q.derivative).natDegree
          ≤ v.derivative.natDegree + Q.derivative.natDegree := Polynomial.natDegree_mul_le
      omega
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · have h1 : (v.derivative * Q.derivative).natDegree
            ≤ v.derivative.natDegree + Q.derivative.natDegree := Polynomial.natDegree_mul_le
        omega
      · have h2 : (v * Q.derivative.derivative).natDegree
            ≤ v.natDegree + Q.derivative.derivative.natDegree := Polynomial.natDegree_mul_le
        omega
  have hlast : (v * Q.derivative ^ (2 : ℕ)).natDegree ≤ 2 * Q.natDegree - 1 := by
    have hE : (Q.derivative ^ (2 : ℕ)).natDegree ≤ 2 * Q.derivative.natDegree :=
      Polynomial.natDegree_pow_le
    have h1 : (v * Q.derivative ^ (2 : ℕ)).natDegree ≤ v.natDegree + (Q.derivative ^ (2 : ℕ)).natDegree :=
      Polynomial.natDegree_mul_le
    omega
  rw [scaledLogWronskian]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · have h3 : ((v.derivative * Q.derivative + v * Q.derivative.derivative) * Q).natDegree
        ≤ (v.derivative * Q.derivative + v * Q.derivative.derivative).natDegree + Q.natDegree :=
      Polynomial.natDegree_mul_le
    omega
  · exact hlast

/-- **The cross term dominates the Wronskian.**  For a nonconstant `Q`, a linear `v` and a nonzero
constant, the combination `W(Q,v) + c·Q²·Q'` is nonzero, because the second term has degree
`3·deg Q − 1` while the first has degree at most `2·deg Q − 1`.

This is the combination that governs the height induction of a product law: at each level the newest
cross term outweighs the Wronskian left by the level below. -/
theorem scaledLogWronskian_add_cross_ne_zero {Q v : Polynomial ℂ} {c : ℂ}
    (hc : c ≠ 0) (hQ : 1 ≤ Q.natDegree) (hv : v.natDegree ≤ 1) :
    scaledLogWronskian Q v + Polynomial.C c * Q ^ (2 : ℕ) * Q.derivative ≠ 0 := by
  have hQ0 : Q ≠ 0 := fun h => by simp [h] at hQ
  have hQ'0 : Q.derivative ≠ 0 := by
    intro h
    rw [Polynomial.derivative_eq_zero] at h
    omega
  have hcross : (Polynomial.C c * Q ^ (2 : ℕ) * Q.derivative).degree
      = ((3 * Q.natDegree - 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul, Polynomial.degree_C hc, zero_add,
      Polynomial.degree_pow, Polynomial.degree_eq_natDegree hQ0,
      Polynomial.degree_derivative (p := Q) (by omega)]
    have h2 : (2 : ℕ) • (Q.natDegree : WithBot ℕ) = ((2 * Q.natDegree : ℕ) : WithBot ℕ) := by
      push_cast
      ring
    rw [h2, ← Nat.cast_add]
    congr 1
    omega
  have hW : (scaledLogWronskian Q v).degree ≤ ((2 * Q.natDegree - 1 : ℕ) : WithBot ℕ) :=
    Polynomial.natDegree_le_iff_degree_le.mp (natDegree_scaledLogWronskian_le hv)
  have hlt : ((2 * Q.natDegree - 1 : ℕ) : WithBot ℕ)
      < ((3 * Q.natDegree - 1 : ℕ) : WithBot ℕ) := by
    exact_mod_cast Nat.cast_lt.mpr (by omega : 2 * Q.natDegree - 1 < 3 * Q.natDegree - 1)
  intro h0
  have hdeg := Polynomial.degree_add_eq_right_of_degree_lt
    (p := scaledLogWronskian Q v) (q := Polynomial.C c * Q ^ (2 : ℕ) * Q.derivative)
    (by rw [hcross]; exact lt_of_le_of_lt hW hlt)
  rw [h0, Polynomial.degree_zero, hcross] at hdeg
  exact absurd hdeg.symm (by simp)

/-! ## The sharp degree bound

Subtracting the right multiple of `Q` from `v·Q'` turns the Wronskian into a Wronskian of a
lower-degree pair, which gives the sharp bound with no coefficient extraction. -/

/-- **The Wronskian is a Wronskian of the reduced numerator.**  Subtracting any constant multiple of
`Q` from `v·Q'` leaves the Wronskian unchanged. -/
theorem scaledLogWronskian_eq_reduced (Q v : Polynomial ℂ) (c : ℂ) :
    scaledLogWronskian Q v
      = (v * Q.derivative - Polynomial.C c * Q).derivative * Q
        - (v * Q.derivative - Polynomial.C c * Q) * Q.derivative := by
  simp only [scaledLogWronskian, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_C]
  ring

/-- **The sharp degree bound**, given that the reduced numerator drops a degree. -/
theorem natDegree_scaledLogWronskian_le_of_reduced {Q v : Polynomial ℂ} {c : ℂ}
    (hQ : 1 ≤ Q.natDegree)
    (hR : (v * Q.derivative - Polynomial.C c * Q).natDegree ≤ Q.natDegree - 1) :
    (scaledLogWronskian Q v).natDegree ≤ 2 * Q.natDegree - 2 := by
  set R : Polynomial ℂ := v * Q.derivative - Polynomial.C c * Q with hRdef
  have hQ' : Q.derivative.natDegree ≤ Q.natDegree - 1 := Polynomial.natDegree_derivative_le Q
  have hR' : R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
  have h1 : (R.derivative * Q).natDegree ≤ R.derivative.natDegree + Q.natDegree :=
    Polynomial.natDegree_mul_le
  have h2 : (R * Q.derivative).natDegree ≤ R.natDegree + Q.derivative.natDegree :=
    Polynomial.natDegree_mul_le
  have hq : 1 ≤ Q.natDegree := hQ
  have hRn : R.natDegree ≤ Q.natDegree - 1 := hR
  have hRd : R.derivative.natDegree ≤ Q.natDegree - 2 := by
    have := hR'
    omega
  rcases Nat.lt_or_ge Q.natDegree 2 with hq2 | hq2
  · have hR0 : R.derivative = 0 := by
      rw [Polynomial.derivative_eq_zero]
      omega
    rw [scaledLogWronskian_eq_reduced Q v c, ← hRdef, hR0, zero_mul, zero_sub,
      Polynomial.natDegree_neg]
    omega
  · rw [scaledLogWronskian_eq_reduced Q v c, ← hRdef]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · omega
    · omega

/-- **The canonical constant reduces the degree.**  Subtracting `deg Q · lead v` times `Q` from
`v·Q'` kills the top coefficient. -/
theorem natDegree_reduced_le {Q v : Polynomial ℂ} (hQ : 1 ≤ Q.natDegree) (hv : v.natDegree = 1) :
    (v * Q.derivative
        - Polynomial.C ((Q.natDegree : ℂ) * v.leadingCoeff) * Q).natDegree
      ≤ Q.natDegree - 1 := by
  set R : Polynomial ℂ :=
    v * Q.derivative - Polynomial.C ((Q.natDegree : ℂ) * v.leadingCoeff) * Q with hRdef
  have hQ0 : Q ≠ 0 := fun h => by simp [h] at hQ
  have hQ'0 : Q.derivative ≠ 0 := by
    intro h
    rw [Polynomial.derivative_eq_zero] at h
    omega
  have hdQ' : Q.derivative.natDegree = Q.natDegree - 1 := by
    have h := Polynomial.degree_derivative (p := Q) (by omega)
    exact Polynomial.natDegree_eq_of_degree_eq_some h
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  -- the top coefficients agree
  have hprod : (v * Q.derivative).coeff (1 + (Q.natDegree - 1))
      = v.leadingCoeff * Q.derivative.leadingCoeff := by
    have := Polynomial.coeff_mul_degree_add_degree v Q.derivative
    rwa [hv, hdQ'] at this
  have hidx : 1 + (Q.natDegree - 1) = Q.natDegree := by omega
  have hderivlead : Q.derivative.leadingCoeff = (Q.natDegree : ℂ) * Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hdQ', Polynomial.coeff_derivative, Polynomial.leadingCoeff]
    have hsub : Q.natDegree - 1 + 1 = Q.natDegree := by omega
    rw [hsub]
    push_cast [Nat.cast_sub hQ]
    ring
  have hC : (Polynomial.C ((Q.natDegree : ℂ) * v.leadingCoeff) * Q).coeff Q.natDegree
      = (Q.natDegree : ℂ) * v.leadingCoeff * Q.leadingCoeff := by
    rw [Polynomial.coeff_C_mul]
    rfl
  have hzero : R.coeff Q.natDegree = 0 := by
    rw [hRdef, Polynomial.coeff_sub, ← hidx, hprod, hidx, hC, hderivlead]
    ring
  -- and the degree is at most `Q.natDegree`
  have hle : R.natDegree ≤ Q.natDegree := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans Polynomial.natDegree_mul_le ?_
      omega
    · refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C]
      omega
  rcases eq_or_ne R 0 with hR0 | hR0
  · rw [hR0]
    simp
  · have hne : R.natDegree ≠ Q.natDegree := by
      intro heq
      have hlead : R.leadingCoeff = 0 := by
        rw [Polynomial.leadingCoeff, heq]
        exact hzero
      exact hR0 (Polynomial.leadingCoeff_eq_zero.mp hlead)
    omega

/-- **The sharp degree bound, unconditionally.** -/
theorem natDegree_scaledLogWronskian_le_sub_two {Q v : Polynomial ℂ}
    (hQ : 1 ≤ Q.natDegree) (hv : v.natDegree = 1) :
    (scaledLogWronskian Q v).natDegree ≤ 2 * Q.natDegree - 2 :=
  natDegree_scaledLogWronskian_le_of_reduced hQ (natDegree_reduced_le hQ hv)

end GaloisForLFunctions.HTGeometry
