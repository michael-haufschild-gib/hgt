import Mathlib

/-!
# Trailing degree kills a low product modulo the horizon

Two facts about polynomials over a domain, both used to show that a syzygy between two states over
the same branch value forces the states to coincide.

The first is the multiplicativity of trailing degree: a nonzero factor of degree below `m` times a
factor with a nonzero coefficient at `n` has a nonzero coefficient strictly below `m + n`, so the
product is not divisible by `X^(m+n)`.  This is what converts "the two states differ" into a
contradiction with the compatibility equation, and it needs no hypothesis on the second factor
beyond one nonvanishing coefficient.

The second is Euclid's lemma in the shape a syzygy produces it: `D V + E U = 0` with `U, V` coprime
forces `D = C U` and `E = −C V` for a single cofactor `C`.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Trailing degree obstructs divisibility by the horizon.**  A nonzero polynomial of degree below
`m` multiplied by one with a nonzero coefficient at `n` has a nonzero coefficient strictly below
`m + n`. -/
theorem not_X_pow_dvd_mul_of_trailing {f g : R[X]} {m n : ℕ}
    (hf : f ≠ 0) (hfdeg : f.natDegree < m) (hg : g.coeff n ≠ 0) :
    ¬ (X : R[X]) ^ (m + n) ∣ f * g := by
  intro hdvd
  have hg0 : g ≠ 0 := by
    intro h
    rw [h] at hg
    simp at hg
  have htf : f.natTrailingDegree ≤ f.natDegree := natTrailingDegree_le_natDegree f
  have htg : g.natTrailingDegree ≤ n := natTrailingDegree_le_of_ne_zero hg
  have hlt : f.natTrailingDegree + g.natTrailingDegree < m + n := by omega
  have hne : (f * g).trailingCoeff ≠ 0 :=
    trailingCoeff_nonzero_iff_nonzero.2 (mul_ne_zero hf hg0)
  have hval : (f * g).trailingCoeff
      = (f * g).coeff (f.natTrailingDegree + g.natTrailingDegree) := by
    rw [Polynomial.trailingCoeff, natTrailingDegree_mul hf hg0]
  rw [hval] at hne
  exact hne ((X_pow_dvd_iff.1 hdvd) _ hlt)

/-- **The low factor of a horizon-divisible product vanishes.**  Contrapositive of the previous
statement: if the product *is* divisible by the horizon, the low factor is zero. -/
theorem eq_zero_of_X_pow_dvd_mul {f g : R[X]} {m n : ℕ}
    (hfdeg : f.natDegree < m) (hg : g.coeff n ≠ 0)
    (hdvd : (X : R[X]) ^ (m + n) ∣ f * g) : f = 0 := by
  by_contra hf
  exact not_X_pow_dvd_mul_of_trailing hf hfdeg hg hdvd

/-- **Euclid's lemma in syzygy form.**  A syzygy between coprime polynomials has a single
cofactor. -/
private theorem exists_cofactor_of_syzygy {U V D E : R[X]}
    (huv : IsCoprime U V) (hU : U ≠ 0) (h : D * V + E * U = 0) :
    ∃ C : R[X], D = C * U ∧ E = -(C * V) := by
  have hdvd : U ∣ D * V := ⟨-E, by linear_combination h⟩
  obtain ⟨C, hC⟩ := huv.dvd_of_dvd_mul_right hdvd
  refine ⟨C, by rw [hC]; ring, ?_⟩
  have hcancel : E * U = -(C * V) * U := by
    rw [hC] at h
    linear_combination h
  exact mul_right_cancel₀ hU hcancel

/-- **Two low states over the same value coincide.**  If the difference of the two states is low and
the marked tail has a nonzero coefficient at the second depth, the difference vanishes. -/
theorem eq_of_low_difference {A A' T : R[X]} {m n : ℕ}
    (hdeg : (A' - A).natDegree < m) (hT : T.coeff n ≠ 0)
    (hdvd : (X : R[X]) ^ (m + n) ∣ (A' - A) * T) : A' = A :=
  sub_eq_zero.1 (eq_zero_of_X_pow_dvd_mul hdeg hT hdvd)

/-- **The two states over a branch value coincide.**  Given the tangent syzygy `D V + E U = 0`, a
low difference `D` of degree below `m`, a marked tail with a nonzero coefficient at `n`, and the
compatibility equation `X^(m+n) ∣ D T`, both differences vanish.  This is the whole content of the
generic-fold rigidity: the ramification-to-branch degree is one. -/
theorem eq_zero_of_tangent_syzygy {U V D E T : R[X]} {m n : ℕ}
    (hU : U ≠ 0) (hsyz : D * V + E * U = 0)
    (hDdeg : D.natDegree < m) (hT : T.coeff n ≠ 0)
    (hdvd : (X : R[X]) ^ (m + n) ∣ D * T) :
    D = 0 ∧ E = 0 := by
  have hD : D = 0 := eq_zero_of_X_pow_dvd_mul hDdeg hT hdvd
  refine ⟨hD, ?_⟩
  have hEU : E * U = 0 := by
    rw [hD] at hsyz
    linear_combination hsyz
  rcases mul_eq_zero.1 hEU with h | h
  · exact h
  · exact absurd h hU

/-! ## The generic fold has one state -/

omit [IsDomain R] in
/-- A polynomial divisible by the horizon and of degree below it is zero. -/
private theorem eq_zero_of_X_pow_dvd_of_natDegree_lt {f : R[X]} {k : ℕ}
    (hdvd : (X : R[X]) ^ k ∣ f) (hdeg : f.natDegree < k) : f = 0 := by
  by_contra hf
  have hlead : f.coeff f.natDegree ≠ 0 := by
    rw [← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.2 hf
  exact hlead ((X_pow_dvd_iff.1 hdvd) _ hdeg)

omit [IsDomain R] in
/-- **The tangent syzygy of two states sharing a vertical tangent.**  Subtracting the two tangent
equations leaves a polynomial of degree below the horizon that the horizon divides, hence zero. -/
theorem syzygy_of_shared_tangent {P Q P' Q' U V : R[X]} {m n : ℕ}
    (hUdeg : U.natDegree < m) (hVdeg : V.natDegree < n)
    (hDdeg : (P' - P).natDegree < m) (hEdeg : (Q' - Q).natDegree < n)
    (t1 : (X : R[X]) ^ (m + n) ∣ (U * Q + P * V))
    (t2 : (X : R[X]) ^ (m + n) ∣ (U * Q' + P' * V)) :
    (P' - P) * V + (Q' - Q) * U = 0 := by
  have hdvd : (X : R[X]) ^ (m + n) ∣ ((P' - P) * V + (Q' - Q) * U) := by
    have hid : (P' - P) * V + (Q' - Q) * U
        = (U * Q' + P' * V) - (U * Q + P * V) := by ring
    rw [hid]
    exact dvd_sub t2 t1
  refine eq_zero_of_X_pow_dvd_of_natDegree_lt hdvd ?_
  have h1 : ((P' - P) * V).natDegree ≤ (P' - P).natDegree + V.natDegree :=
    Polynomial.natDegree_mul_le
  have h2 : ((Q' - Q) * U).natDegree ≤ (Q' - Q).natDegree + U.natDegree :=
    Polynomial.natDegree_mul_le
  have h3 : ((P' - P) * V + (Q' - Q) * U).natDegree
      ≤ max ((P' - P) * V).natDegree ((Q' - Q) * U).natDegree := Polynomial.natDegree_add_le _ _
  omega

/-- **A generic branch value carries only one state.**  Two states of the same fibre sharing a
vertical tangent, with a marked jet tail, coincide. -/
theorem criticalState_eq_of_shared_tangent {P Q P' Q' U V : R[X]} {m n : ℕ}
    (hU : U ≠ 0) (hV : V ≠ 0) (huv : IsCoprime U V)
    (hUdeg : U.natDegree < m) (hVdeg : V.natDegree < n)
    (hDdeg : (P' - P).natDegree < m) (hEdeg : (Q' - Q).natDegree < n)
    (hfib : (X : R[X]) ^ (m + n) ∣ (P * Q - 1))
    (hfib' : (X : R[X]) ^ (m + n) ∣ (P' * Q' - 1))
    (t1 : (X : R[X]) ^ (m + n) ∣ (U * Q + P * V))
    (t2 : (X : R[X]) ^ (m + n) ∣ (U * Q' + P' * V))
    (hmark : (P + P').coeff m ≠ 0) :
    P' = P ∧ Q' = Q := by
  have hsyz := syzygy_of_shared_tangent hUdeg hVdeg hDdeg hEdeg t1 t2
  obtain ⟨C, hDC, hEC⟩ := exists_cofactor_of_syzygy huv hU hsyz
  have hprod : (X : R[X]) ^ (m + n) ∣ (Q' - Q) * (P + P') := by
    have hsub : (X : R[X]) ^ (m + n) ∣ (P' * Q' - 1) - (P * Q - 1) := dvd_sub hfib' hfib
    have hmul : (X : R[X]) ^ (m + n) ∣ C * (U * Q + P * V) := Dvd.dvd.mul_left t1 C
    have hP'e : P' = C * U + P := sub_eq_iff_eq_add.1 hDC
    have hQ'e : Q' = -(C * V) + Q := sub_eq_iff_eq_add.1 hEC
    have hid : (Q' - Q) * (P + P')
        = ((P' * Q' - 1) - (P * Q - 1)) - C * (U * Q + P * V) := by
      rw [hP'e, hQ'e]
      ring
    rw [hid]
    exact dvd_sub hsub hmul
  have hQ : Q' - Q = 0 := by
    refine eq_zero_of_X_pow_dvd_mul (m := n) (n := m) hEdeg hmark ?_
    rwa [Nat.add_comm n m]
  have hQ' : Q' = Q := sub_eq_zero.1 hQ
  refine ⟨?_, hQ'⟩
  have hPV : (P' - P) * V = 0 := by
    rw [hQ] at hsyz
    linear_combination hsyz
  rcases mul_eq_zero.1 hPV with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hV

/-! ## The conormal pairing is perfect -/

omit [IsDomain R] in
/-- **The branch conormal determines the tangent pair.**  The coefficients of `U` pair in reverse
order with the tail coefficients of the reciprocal jet, and those of `V` with the tail coefficients
of the jet, so a low pair annihilating every tail variation is zero. -/
theorem eq_zero_of_conormal_vanishing {U V : R[X]} {m n : ℕ}
    (hU : U.natDegree < m) (hV : V.natDegree < n)
    (h : ∀ dP dQ : R[X], (X : R[X]) ^ m ∣ dP → (X : R[X]) ^ n ∣ dQ →
      (U * dQ - dP * V).coeff (m + n - 1) = 0) :
    U = 0 ∧ V = 0 := by
  have hm : 0 < m := Nat.pos_of_ne_zero fun h0 => by omega
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by omega
  constructor
  · refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_zero]
    by_cases hk : k < m
    · have hdQ : (X : R[X]) ^ n ∣ (X : R[X]) ^ (n + (m - 1 - k)) := by
        exact pow_dvd_pow _ (by omega)
      have hval := h 0 ((X : R[X]) ^ (n + (m - 1 - k))) (dvd_zero _) hdQ
      have hzero : ((0 : R[X]) * V) = 0 := by ring
      rw [hzero, sub_zero] at hval
      rw [Polynomial.coeff_mul_X_pow'] at hval
      have hle : n + (m - 1 - k) ≤ m + n - 1 := by omega
      rw [if_pos hle] at hval
      have hidx : m + n - 1 - (n + (m - 1 - k)) = k := by omega
      rwa [hidx] at hval
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_zero]
    by_cases hk : k < n
    · have hdP : (X : R[X]) ^ m ∣ (X : R[X]) ^ (m + (n - 1 - k)) := by
        exact pow_dvd_pow _ (by omega)
      have hval := h ((X : R[X]) ^ (m + (n - 1 - k))) 0 hdP (dvd_zero _)
      have hzero : (U * (0 : R[X])) = 0 := by ring
      rw [hzero, zero_sub, Polynomial.coeff_neg, neg_eq_zero] at hval
      rw [mul_comm, Polynomial.coeff_mul_X_pow'] at hval
      have hle : m + (n - 1 - k) ≤ m + n - 1 := by omega
      rw [if_pos hle] at hval
      have hidx : m + n - 1 - (m + (n - 1 - k)) = k := by omega
      rwa [hidx] at hval
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end GaloisForLFunctions.HTGeometry

end
