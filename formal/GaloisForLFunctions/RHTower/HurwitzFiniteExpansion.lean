import GaloisForLFunctions.RHTower.EstermannPrincipalPart

/-!
# The finite additive expansion of the Hurwitz zeta at rational arguments

Fourier inversion on `ZMod q` turns the indicator of a residue class into a character sum, so the
Hurwitz zeta at `c/q` is a finite combination of exponential zetas:

```text
ζ(s, c/q) = q^{s-1} ∑_{j mod q} e(cj/q) · expZeta(-j/q, s).
```

The `j = 0` term is `q^{s-1} ζ(s)`; the remaining terms are exponential zetas at nonzero
arguments, which are entire.  The expansion therefore isolates the pole of `ζ(s, c/q)` and reduces
every growth question for `ζ(·, c/q)` to one for `expZeta` at nonzero arguments.
-/

open Complex HurwitzZeta

namespace RHTower

noncomputable section

variable {q : ℕ} [NeZero q]

/-- **Orthogonality of the standard additive character.** -/
theorem sum_stdAddChar_mul (q : ℕ) [NeZero q] (b : ZMod q) :
    ∑ j : ZMod q, ZMod.stdAddChar (j * b) = if b = 0 then (q : ℂ) else 0 := by
  classical
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar q)]
  simp [ZMod.card]

/-- The inverse Fourier transform of the indicator of `c`. -/
theorem dft_inv_indicator (q : ℕ) [NeZero q] (c : ZMod q) :
    ZMod.dft (fun k : ZMod q => (q : ℂ)⁻¹ * ZMod.stdAddChar (c * k))
      = fun k => if k = c then (1 : ℂ) else 0 := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  funext k
  rw [ZMod.dft_apply]
  have hterm : ∀ j : ZMod q,
      ZMod.stdAddChar (-(j * k)) • ((q : ℂ)⁻¹ * ZMod.stdAddChar (c * j))
        = (q : ℂ)⁻¹ * ZMod.stdAddChar (j * (c - k)) := by
    intro j
    rw [smul_eq_mul, show j * (c - k) = c * j + -(j * k) by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, sum_stdAddChar_mul]
  by_cases h : k = c
  · rw [if_pos h, if_pos (by rw [h]; ring), inv_mul_cancel₀ hq0]
  · have hne : c - k ≠ 0 := fun hcon => h (by linear_combination -hcon)
    rw [if_neg h, if_neg hne, mul_zero]

/-- **The finite additive expansion of the Hurwitz zeta at a rational argument.** -/
theorem hurwitzZeta_eq_sum_expZeta (c : ZMod q) {s : ℂ} (hs : s ≠ 1) :
    hurwitzZeta (ZMod.toAddCircle c) s
      = (q : ℂ) ^ (s - 1) *
        ∑ j : ZMod q, ZMod.stdAddChar (c * j) * expZeta (ZMod.toAddCircle (-j)) s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  set Ψ : ZMod q → ℂ := fun k => (q : ℂ)⁻¹ * ZMod.stdAddChar (c * k) with hΨ
  have hΨ0 : Ψ 0 ≠ 0 := by
    rw [hΨ]
    simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact inv_ne_zero hq0
  have h := ZMod.LFunction_dft (N := q) Ψ (Or.inr hs)
  rw [dft_inv_indicator] at h
  have hL : ZMod.LFunction (fun k : ZMod q => if k = c then (1 : ℂ) else 0) s
      = (q : ℂ) ^ (-s) * hurwitzZeta (ZMod.toAddCircle c) s := by
    rw [ZMod.LFunction, Finset.sum_eq_single c]
    · rw [if_pos rfl, one_mul]
    · intro b _ hb; rw [if_neg hb, zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ _) hcon
  rw [hL] at h
  have hsum : ∑ j : ZMod q, Ψ j * expZeta (ZMod.toAddCircle (-j)) s
      = (q : ℂ)⁻¹ * ∑ j : ZMod q,
          ZMod.stdAddChar (c * j) * expZeta (ZMod.toAddCircle (-j)) s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [hΨ]; ring)
  rw [hsum] at h
  have hcp : (q : ℂ) ^ s * (q : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hq0]; simp
  have hcp2 : (q : ℂ) ^ (s - 1) = (q : ℂ) ^ s * (q : ℂ)⁻¹ := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hq0, Complex.cpow_neg_one]
  rw [hcp2, mul_assoc, ← h, ← mul_assoc, hcp, one_mul]

end

end RHTower
