import Mathlib

/-!
# The dual exponent and the degree-two barrier

Duality for nonlinear twists of an `L`-function of degree `d` acts on the leading exponent of the phase
by

```text
κ ↦ κ / (d κ - 1) ,
```

an involution whose unique non-zero fixed point is `κ = 2/d`.  A phase contributes a trivial
exponential — so that the twist is the plain standard twist — exactly when its exponents are positive
integers with integer coefficients, apart from the resonating term of exponent `1/d`.  The mechanism
that produces self-referential twist identities therefore needs the leading exponent `1` to survive
duality, which happens only when `2/d = 1`.

Two arithmetic facts record the barrier.

* The fixed point of `κ ↦ κ/(dκ-1)` is `2/d`, which is a positive integer only for `d ∈ {1,2}`.
* Starting from the phase `c ξ + γ ξ^{1/d}`, duality sends the exponent gap `(d-1)/d` to `1/d` and the
  leading exponent `1` to `1/(d-1)`, so the dual exponents are `1/(d-1) - j/d`.  The resonating
  exponent `1/d` reappears among them exactly when `(j+1)(d-1) = d` for some `j`, i.e. only when
  `d = 2`.
-/

namespace HTGeometry

/-- The action of duality on the leading exponent of a phase, in degree `d`. -/
def dualExp (d κ : ℚ) : ℚ := κ / (d * κ - 1)

/-- **Duality is an involution on exponents.** -/
theorem dualExp_dualExp (d κ : ℚ) (h : d * κ - 1 ≠ 0) : dualExp d (dualExp d κ) = κ := by
  have hinner : d * (κ / (d * κ - 1)) - 1 = 1 / (d * κ - 1) := by
    field_simp
    ring
  have h' : κ * d - 1 ≠ 0 := by
    intro hc; apply h; linarith [hc]
  unfold dualExp
  rw [hinner]
  field_simp

/-- **The unique non-zero fixed exponent is `2/d`.** -/
theorem dualExp_eq_self_iff (d κ : ℚ) (hκ : κ ≠ 0) (h : d * κ - 1 ≠ 0) :
    dualExp d κ = κ ↔ d * κ = 2 := by
  unfold dualExp
  rw [div_eq_iff h]
  constructor
  · intro hmain
    have : κ * (d * κ - 2) = 0 := by ring_nf; ring_nf at hmain; linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hκ
    · linarith
  · intro hmain
    have : d * κ - 1 = 1 := by linarith
    rw [this, mul_one]

/-- **The degree-two barrier.**  For `d ≥ 2` the resonating exponent `1/d` is recovered among the dual
exponents `1/(d-1) - j/d` only when `d = 2`. -/
theorem exponent_return_iff (d : ℕ) (hd : 2 ≤ d) :
    (∃ j : ℕ, (j + 1) * (d - 1) = d) ↔ d = 2 := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have he : 1 ≤ e := by omega
    have hj' : (j + 1) * e = e + 1 := by simpa using hj
    have hje : j * e = 1 := by nlinarith [hj']
    have hj1 : j = 1 := Nat.eq_one_of_mul_eq_one_right hje
    have he1 : e = 1 := Nat.eq_one_of_mul_eq_one_left hje
    omega
  · rintro rfl
    exact ⟨1, by norm_num⟩

/-- The fixed exponent `2/d` is a positive integer only in degrees `1` and `2`. -/
theorem fixedExp_isInt_iff (d : ℕ) (hd : 0 < d) :
    (∃ m : ℕ, 0 < m ∧ d * m = 2) ↔ d = 1 ∨ d = 2 := by
  constructor
  · rintro ⟨m, hm, hdm⟩
    have hdvd : d ∣ 2 := ⟨m, hdm.symm⟩
    have hle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases d <;> omega
  · rintro (rfl | rfl)
    · exact ⟨2, by norm_num⟩
    · exact ⟨1, by norm_num⟩

end HTGeometry
