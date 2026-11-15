import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheCubicStepanovCount
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheDegreeTwoCharacterOfTheCubeRootsOfTwoHasItsHodgeIndex

/-!
# The cubic curve count without Weil

Let `|E| = p^n = s² = 3N + 1` and `h` squarefree of degree `D ≥ 1` with `s ≥ 3D + 10`.

* **Stepanov's bound** (`cubic_stepanov_bound`): the choice `ℓ = s`, `K = ⌊(s² − 2D)/3⌋`,
  `J = ⌊(s + 3D + 6)/3⌋` meets the dimension condition of `cubic_stepanov_count`, so
  `3·#{x : h(x) ≠ 0, h(x)^N = ε} ≤ s² + (5D + 4)s` for every `ε`.
* **Equidistribution** (`abs_three_mul_card_sub_le`): `h(x)^N` is a cube root of unity, and the three
  classes share the `s² − #{h = 0}` nonroots; the upper bound for two of them is a lower bound for
  the third: `|3·#{h(x)^N = 1} − s²| ≤ 2(5D + 4)s + 3D`.
* **The curve** (`abs_card_cubicCurve_sub_le`): `#{(x, y) : y³ = h(x)} = #{h = 0} + 3·#{h(x)^N = 1}`,
  a nonzero cube having three cube roots; hence `|#{y³ = h(x)} − s²| ≤ 2(5D + 4)s + 4D`. This is the
  Hasse–Weil bound for the cubic curve `y³ = h(x)` over the even-degree extensions, by counting.
-/

open Polynomial Finset

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open RHTower.Stepanov

variable {E : Type*} [Field E]

/-- **Stepanov's bound for a character of order three.** -/
theorem cubic_stepanov_bound [Fintype E] [DecidableEq E] {p n : ℕ} [Fact p.Prime] [CharP E p]
    (hcard : Fintype.card E = p ^ n) {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {N s : ℕ} (hQ : p ^ n = 3 * N + 1) (hs : p ^ n = s ^ 2) (hsD : 3 * h.natDegree + 10 ≤ s)
    (ε : E) :
    3 * (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)).card ≤
      s ^ 2 + (5 * h.natDegree + 4) * s := by
  set D := h.natDegree
  set K := (s ^ 2 - 2 * D) / 3
  set J := (s + 3 * D + 6) / 3
  have hsq2 : 2 * D + 2 ≤ s ^ 2 := by nlinarith
  have hK1 : s ^ 2 - 2 * D - 2 ≤ 3 * K := by omega
  have hK2 : 3 * K ≤ s ^ 2 - 2 * D := by omega
  have hJ1 : s + 3 * D + 4 ≤ 3 * J := by omega
  have hJ2 : 3 * J ≤ s + 3 * D + 6 := by omega
  have hN : 3 * N + 1 = s ^ 2 := by rw [← hQ, hs]
  have hsN : s ≤ N := by nlinarith
  have hK0 : 0 < K := by
    have : 100 ≤ s ^ 2 := by nlinarith
    omega
  have hKQ : 3 * (K - 1) + 2 * D < p ^ n := by rw [hs]; omega
  have hdim : ∑ k : Fin s, (K + (k : ℕ) * D + J) < 3 * (J * K) := by
    have hsum := sum_fin_linear s K J D
    set S := ∑ k : Fin s, (K + (k : ℕ) * D + J)
    have hs1 : 1 ≤ s := by omega
    have hsumZ : (2 * S : ℤ) = 2 * s * (K + J) + D * (s * (s - 1)) := by
      have := hsum
      zify [hs1] at this
      exact this
    have hA1 : ((s : ℤ) ^ 2 - 2 * D - 2) ≤ 3 * K := by
      have e : ((s ^ 2 - 2 * D - 2 : ℕ) : ℤ) = (s : ℤ) ^ 2 - 2 * D - 2 := by
        rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
      have h' : ((s ^ 2 - 2 * D - 2 : ℕ) : ℤ) ≤ ((3 * K : ℕ) : ℤ) := by exact_mod_cast hK1
      rw [e] at h'; push_cast at h'; exact h'
    have hB1 : ((s : ℤ) + 3 * D + 4) ≤ 3 * J := by exact_mod_cast hJ1
    have hB2 : (3 * (J : ℤ)) ≤ s + 3 * D + 6 := by exact_mod_cast hJ2
    have hsD' : ((3 : ℤ) * D + 10) ≤ s := by exact_mod_cast hsD
    have hD0 : (0 : ℤ) ≤ D := by positivity
    have hA0 : (0 : ℤ) ≤ (s : ℤ) ^ 2 - 2 * D - 2 := by
      have : ((2 * D + 2 : ℕ) : ℤ) ≤ ((s ^ 2 : ℕ) : ℤ) := by exact_mod_cast hsq2
      push_cast at this; linarith
    have p1 : ((s : ℤ) ^ 2 - 2 * D - 2) * (3 * D + 4) ≤ (3 * K) * (3 * J - s) :=
      mul_le_mul hA1 (by linarith) (by positivity) (by linarith)
    have p2 : (s : ℤ) * (3 * J) ≤ s * (s + 3 * D + 6) :=
      mul_le_mul_of_nonneg_left hB2 (by positivity)
    have p3 : ((3 : ℤ) * D + 6) * (3 * D + 10) ≤ (3 * D + 6) * s :=
      mul_le_mul_of_nonneg_left hsD' (by positivity)
    have p4 : (s : ℤ) * ((3 * D + 6) * (3 * D + 10)) ≤ s * ((3 * D + 6) * s) :=
      mul_le_mul_of_nonneg_left p3 (by positivity)
    have p5 : ((3 : ℤ) * D + 10) * (9 * D ^ 2 + 45 * D + 48) ≤ s * (9 * D ^ 2 + 45 * D + 48) :=
      mul_le_mul_of_nonneg_right hsD' (by positivity)
    have : (3 * (2 * S) : ℤ) < 2 * (3 * K) * (3 * J) := by nlinarith
    have : (S : ℤ) < 3 * (J * K) := by nlinarith
    exact_mod_cast this
  have hc := cubic_stepanov_count hcard hsq hdeg hQ hsN hK0 hKQ hdim ε
  set T := (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)).card
  have hs0 : 0 < s := by omega
  have hZ : (3 * (s * T) : ℤ) ≤ s * (s ^ 2 + (5 * D + 4) * s) := by
    have hc' : ((s * T : ℕ) : ℤ) ≤ (((K - 1) + 2 * (N * D) + p ^ n * (J - 1) : ℕ) : ℤ) := by
      exact_mod_cast hc
    have hK1' : 1 ≤ K := hK0
    have hJ1' : 1 ≤ J := by omega
    push_cast [Nat.cast_sub hK1', Nat.cast_sub hJ1'] at hc'
    rw [hs] at hc'
    push_cast at hc'
    have hNZ : (3 * (N : ℤ)) = (s : ℤ) ^ 2 - 1 := by
      have : ((3 * N + 1 : ℕ) : ℤ) = ((s ^ 2 : ℕ) : ℤ) := by exact_mod_cast hN
      push_cast at this; linarith
    have hK2' : (3 * (K : ℤ)) ≤ (s : ℤ) ^ 2 - 2 * D := by
      have h' : ((3 * K : ℕ) : ℤ) ≤ ((s ^ 2 - 2 * D : ℕ) : ℤ) := by exact_mod_cast hK2
      rw [Nat.cast_sub (by omega)] at h'; push_cast at h'; exact h'
    have hJ2' : (3 * (J : ℤ)) ≤ s + 3 * D + 6 := by exact_mod_cast hJ2
    have hD0 : (0 : ℤ) ≤ D := by positivity
    have q1 : (3 : ℤ) * ((s : ℤ) ^ 2 * (J - 1)) ≤ (s : ℤ) ^ 2 * (s + 3 * D + 3) := by
      have := mul_le_mul_of_nonneg_left (show (3 * ((J : ℤ) - 1)) ≤ s + 3 * D + 3 by linarith)
        (show (0 : ℤ) ≤ (s : ℤ) ^ 2 by positivity)
      linarith
    have q2 : (3 : ℤ) * (2 * (N * D)) = 2 * D * ((s : ℤ) ^ 2 - 1) := by
      rw [← hNZ]; ring
    nlinarith
  have hT : (3 * T : ℤ) ≤ s ^ 2 + (5 * D + 4) * s := by
    have hsZ : (0 : ℤ) < s := by exact_mod_cast hs0
    have : (s : ℤ) * (3 * T) ≤ s * (s ^ 2 + (5 * D + 4) * s) := by linarith
    exact le_of_mul_le_mul_left this hsZ
  exact_mod_cast hT

/-- A finite field with `3 ∣ |E| − 1` has a primitive cube root of unity. -/
theorem exists_cube_root_of_unity [Fintype E] (h3 : 3 ∣ Fintype.card E - 1) :
    ∃ ω : E, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcu : 3 ∣ Fintype.card Eˣ := by rw [Fintype.card_units]; exact h3
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hcu
  refine ⟨u, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  · intro h1
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    norm_num at hu

theorem eq_of_pow_three_eq_one {ω y : E} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hy : y ^ 3 = 1) :
    y = 1 ∨ y = ω ∨ y = ω ^ 2 := by
  have hsum : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1)
  have : (y - 1) * (y - ω) * (y - ω ^ 2) = 0 := by
    linear_combination hy - y * hsum + (y - 1) * 0 - hω + y ^ 2 * 0 + (1 - y) * 0 + 0 * hsum
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
