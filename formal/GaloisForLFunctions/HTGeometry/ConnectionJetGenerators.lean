import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.LinearCombination

/-!
# Infinitesimal coordinate changes acting on the jets of an affine connection

An affine connection `u dz` changes under the vector field `v ∂` by `δu = (v u)' + v''`.  For the
vector field `z^{k+1}∂` and the derivative coordinates `x_j = u^{(j)}(0)`, `j < N`, this is the
affine derivation

`ξ_k(x_j) = C(j+1, k+1)·x_{j−k} + [j + 1 = k]`

of the polynomial ring in the jets (`x_i = 0` beyond the truncation order).

* **Bracket law.**  `[ξ₁, ξ_k] = ((1−k)(k+2)/2)·ξ_{k+1}`, a binomial identity on the linear part
  and `1 − C(k+1,2)` on the constant part.
* **Generation.**  In characteristic zero a polynomial killed by `ξ₁` and `ξ₂` is killed by every
  `ξ_k`, `k ≥ 1`, since the bracket coefficient vanishes only at `k = 1`.
* **Transversality.**  `ξ_N` is the partial derivative in the top jet `x_{N−1}`.  So a jet equation
  solved for its top derivative, `x_{N−1} = F(x_0,…,x_{N−2})`, is never infinitesimally invariant
  under both `z²∂` and `z³∂`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (K : Type*) [Field K] (N : ℕ)

/-- The jet coordinate `x_i`, and `0` beyond the truncation order. -/
def connectionJetVar (i : ℕ) : MvPolynomial (Fin N) K :=
  if h : i < N then X ⟨i, h⟩ else 0

/-- The value of the generator `z^{k+1}∂` on the jet coordinate `x_j`. -/
def connectionGenValue (k j : ℕ) : MvPolynomial (Fin N) K :=
  (if k ≤ j then C (((j + 1).choose (k + 1) : ℕ) : K) * connectionJetVar K N (j - k) else 0)
    + if j + 1 = k then 1 else 0

/-- The infinitesimal action of `z^{k+1}∂` on the jets of an affine connection. -/
def connectionGen (k : ℕ) : Derivation K (MvPolynomial (Fin N) K) (MvPolynomial (Fin N) K) :=
  mkDerivation K fun j : Fin N => connectionGenValue K N k j

variable {K N}

theorem connectionGen_X (k : ℕ) (j : Fin N) :
    connectionGen K N k (X j) = connectionGenValue K N k j :=
  mkDerivation_X K _ j

theorem connectionGen_jetVar (k : ℕ) {i : ℕ} (hi : i < N) :
    connectionGen K N k (connectionJetVar K N i) = connectionGenValue K N k i := by
  rw [connectionJetVar, dif_pos hi, connectionGen_X]

theorem derivation_C_mul_eq (D : Derivation K (MvPolynomial (Fin N) K) (MvPolynomial (Fin N) K))
    (c : K) (p : MvPolynomial (Fin N) K) : D (C c * p) = C c * D p := by
  rw [C_mul', D.map_smul, smul_eq_C_mul]

theorem connectionGenValue_of_le {k j : ℕ} (h : k ≤ j) :
    connectionGenValue K N k j
      = C (((j + 1).choose (k + 1) : ℕ) : K) * connectionJetVar K N (j - k) := by
  rw [connectionGenValue, if_pos h, if_neg (by omega), add_zero]

theorem connectionGenValue_of_succ_eq {k j : ℕ} (h : j + 1 = k) :
    connectionGenValue K N k j = 1 := by
  rw [connectionGenValue, if_neg (by omega), if_pos h, zero_add]

theorem connectionGenValue_of_lt {k j : ℕ} (h : j + 1 < k) :
    connectionGenValue K N k j = 0 := by
  rw [connectionGenValue, if_neg (by omega), if_neg (by omega), add_zero]

/-- The binomial identity behind the bracket law, on the linear part. -/
theorem choose_bracket_identity [CharZero K] {k j : ℕ} (h : k + 1 ≤ j) :
    (((j + 1).choose (k + 1) : ℕ) : K) * (((j - k + 1).choose 2 : ℕ) : K)
        - (((j + 1).choose 2 : ℕ) : K) * ((j.choose (k + 1) : ℕ) : K)
      = ((1 - k : K) * (k + 2) / 2) * (((j + 1).choose (k + 2) : ℕ) : K) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have e1 : k + 1 + m - k + 1 = m + 2 := by omega
  have e2 : k + 1 + m + 1 = k + m + 2 := by omega
  rw [e1, e2, show k + 1 + m = k + m + 1 by omega]
  have h1 : (k + m + 2).choose (k + 2) * (k + 2) = (k + m + 2).choose (k + 1) * (m + 1) := by
    have := Nat.choose_succ_right_eq (k + m + 2) (k + 1)
    rw [show k + m + 2 - (k + 1) = m + 1 by omega] at this
    exact this
  have h2 : (k + m + 2) * (k + m + 1).choose (k + 1) = (k + m + 2).choose (k + 2) * (k + 2) :=
    Nat.add_one_mul_choose_eq (k + m + 1) (k + 1)
  have h1' := congrArg (Nat.cast : ℕ → K) h1
  have h2' := congrArg (Nat.cast : ℕ → K) h2
  push_cast at h1' h2'
  rw [Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  linear_combination -((m : K) + 2) / 2 * h1' - ((k : K) + m + 1) / 2 * h2'

/-- **The bracket law** `[ξ₁, ξ_k] = ((1−k)(k+2)/2)·ξ_{k+1}`. -/
theorem connectionGen_bracket_one [CharZero K] {k : ℕ} (hk : 1 ≤ k) :
    ⁅connectionGen K N 1, connectionGen K N k⁆
      = ((1 - k : K) * (k + 2) / 2) • connectionGen K N (k + 1) := by
  refine derivation_ext fun j => ?_
  have hj : (j : ℕ) < N := j.isLt
  rw [Derivation.commutator_apply, Derivation.smul_apply, connectionGen_X, connectionGen_X,
    connectionGen_X]
  rcases lt_trichotomy (j : ℕ) k with hlt | heq | hgt
  · -- below the diagonal both sides vanish
    rw [connectionGenValue_of_lt (k := k + 1) (by omega)]
    rcases Nat.lt_or_ge ((j : ℕ) + 1) k with h1 | h1
    · rw [connectionGenValue_of_lt (k := k) h1, map_zero]
      rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
      · rw [connectionGenValue_of_succ_eq (k := 1) (by omega), Derivation.map_one_eq_zero, sub_zero,
          smul_zero]
      · rw [connectionGenValue_of_le (k := 1) (by omega), derivation_C_mul_eq,
          connectionGen_jetVar _ (by omega), connectionGenValue_of_lt (k := k) (by omega),
          mul_zero, sub_zero, smul_zero]
    · rw [connectionGenValue_of_succ_eq (k := k) (by omega), Derivation.map_one_eq_zero, zero_sub,
        smul_zero, neg_eq_zero]
      rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
      · rw [connectionGenValue_of_succ_eq (k := 1) (by omega), Derivation.map_one_eq_zero]
      · rw [connectionGenValue_of_le (k := 1) (by omega), derivation_C_mul_eq,
          connectionGen_jetVar _ (by omega), connectionGenValue_of_lt (k := k) (by omega),
          mul_zero]
  · -- on the diagonal only the constant parts meet
    subst heq
    rw [connectionGenValue_of_le (k := (j : ℕ)) le_rfl, connectionGenValue_of_le (k := 1) hk,
      connectionGenValue_of_succ_eq (k := (j : ℕ) + 1) rfl, derivation_C_mul_eq,
      derivation_C_mul_eq,
      connectionGen_jetVar _ (by omega), connectionGen_jetVar _ (by omega), Nat.sub_self,
      connectionGenValue_of_succ_eq (k := 1) (by omega),
      connectionGenValue_of_succ_eq (k := (j : ℕ)) (by omega), Nat.choose_self]
    simp only [smul_eq_C_mul, mul_one]
    rw [← map_sub]
    congr 1
    rw [show (1 + 1 : ℕ) = 2 from rfl, Nat.cast_choose_two]
    push_cast
    ring
  · -- above the diagonal only the linear parts survive
    rw [connectionGenValue_of_le (k := k) (by omega), connectionGenValue_of_le (k := 1) (by omega),
      connectionGenValue_of_le (k := k + 1) (by omega), derivation_C_mul_eq, derivation_C_mul_eq,
      connectionGen_jetVar _ (by omega), connectionGen_jetVar _ (by omega),
      connectionGenValue_of_le (k := 1) (by omega), connectionGenValue_of_le (k := k) (by omega),
      show (j : ℕ) - k - 1 = (j : ℕ) - (k + 1) by omega,
      show (j : ℕ) - 1 - k = (j : ℕ) - (k + 1) by omega,
      show (j : ℕ) - 1 + 1 = (j : ℕ) by omega, smul_eq_C_mul]
    have key := choose_bracket_identity (K := K) (k := k) (j := (j : ℕ)) hgt
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, ← C_mul, ← sub_mul, ← map_sub,
      show (1 + 1 : ℕ) = 2 from rfl, show k + 1 + 1 = k + 2 from rfl, key]

/-- The generator `z^{N+1}∂` of index `N` (one past the top jet) is the partial derivative in the
top jet `x_N`. -/
theorem connectionGen_top (n : ℕ) :
    connectionGen K (n + 1) (n + 1) = pderiv (Fin.last n) := by
  classical
  refine derivation_ext fun j => ?_
  rw [connectionGen_X, pderiv_X]
  by_cases hj : j = Fin.last n
  · subst hj
    rw [connectionGenValue_of_succ_eq (by simp), Pi.single_eq_same]
  · have hlt : (j : ℕ) < n := by
      have := j.isLt
      have hne : (j : ℕ) ≠ n := fun h => hj (Fin.ext (by simpa using h))
      omega
    rw [connectionGenValue_of_lt (by omega), Pi.single_eq_of_ne hj]

/-- **Generation.**  A polynomial killed by `ξ₁` and `ξ₂` is killed by every `ξ_k`, `k ≥ 1`. -/
theorem connectionGen_eq_zero_of_one_two [CharZero K] {Φ : MvPolynomial (Fin N) K}
    (h1 : connectionGen K N 1 Φ = 0) (h2 : connectionGen K N 2 Φ = 0) :
    ∀ k : ℕ, 1 ≤ k → connectionGen K N k Φ = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h1
  | succ k hk ih =>
      rcases Nat.eq_or_lt_of_le hk with rfl | hk2
      · exact h2
      have hbr := congrArg (fun D => D Φ) (connectionGen_bracket_one (K := K) (N := N) hk)
      simp only [Derivation.commutator_apply, Derivation.smul_apply, ih, h1, map_zero,
        sub_zero] at hbr
      have hc : ((1 - k : K) * (k + 2) / 2) ≠ 0 := by
        have hk1 : (1 - k : K) ≠ 0 := by
          rw [sub_ne_zero]
          exact_mod_cast (show (1 : ℕ) ≠ k by omega)
        have hk2' : (k : K) + 2 ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
        exact div_ne_zero (mul_ne_zero hk1 hk2') two_ne_zero
      exact (smul_eq_zero.mp hbr.symm).resolve_left hc

/-- **Transversality.**  A polynomial killed by the infinitesimal changes `z²∂` and `z³∂` does not
depend on the top jet. -/
theorem pderiv_last_eq_zero_of_connectionGen [CharZero K] {n : ℕ} {Φ : MvPolynomial (Fin (n + 1)) K}
    (h1 : connectionGen K (n + 1) 1 Φ = 0) (h2 : connectionGen K (n + 1) 2 Φ = 0) :
    pderiv (Fin.last n) Φ = 0 := by
  rw [← connectionGen_top]
  exact connectionGen_eq_zero_of_one_two h1 h2 (n + 1) (by omega)

/-- **No jet equation solved for its top derivative is invariant under `z²∂` and `z³∂`.** -/
theorem not_connectionGen_invariant_graph [CharZero K] {n : ℕ} (F : MvPolynomial (Fin n) K) :
    ¬ (connectionGen K (n + 1) 1 (X (Fin.last n) - rename Fin.castSucc F) = 0 ∧
      connectionGen K (n + 1) 2 (X (Fin.last n) - rename Fin.castSucc F) = 0) := by
  classical
  rintro ⟨h1, h2⟩
  have h := pderiv_last_eq_zero_of_connectionGen h1 h2
  have hF : pderiv (Fin.last n) (rename Fin.castSucc F : MvPolynomial (Fin (n + 1)) K) = 0 := by
    refine pderiv_eq_zero_of_notMem_vars fun hmem => ?_
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (vars_rename Fin.castSucc F hmem)
    exact Fin.castSucc_ne_last i hi
  rw [map_sub, hF, sub_zero, pderiv_X, Pi.single_eq_same] at h
  exact one_ne_zero h

end

end GaloisForLFunctions.HTGeometry
