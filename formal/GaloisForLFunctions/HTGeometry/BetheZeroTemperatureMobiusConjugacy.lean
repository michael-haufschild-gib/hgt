import GaloisForLFunctions.HTGeometry.BetheHolographicIsingRG

/-!
# Zero-temperature Möbius conjugacy of the Bethe holographic RG map

At the noiseless zero-temperature endpoint `a = 1`, the Bethe holographic Ising RG map is exactly the
`p`-th power map conjugated by the Cayley--Möbius chart `M(w) = (w-1)/(w+1)`:
`F_{p,1} = M ∘ (·^p) ∘ M⁻¹` (equation (17) of the card).  This is the Ritt-integrable boundary where
the edge attenuation disappears; the conjugacy is an exact rational identity.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Polynomial

/-- The Cayley--Möbius chart `M(w) = (w-1)/(w+1)` conjugating the zero-temperature RG map. -/
def betheMobiusM (w : ℚ) : ℚ := (w - 1) / (w + 1)

/-- Its inverse chart `M⁻¹(w) = (1+w)/(1-w)`. -/
def betheMobiusMinv (w : ℚ) : ℚ := (1 + w) / (1 - w)

theorem betheMobiusM_betheMobiusMinv {y : ℚ} (h : y ≠ 1) : betheMobiusM (betheMobiusMinv y) = y := by
  have h1 : (1 : ℚ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [betheMobiusM, betheMobiusMinv]
  field_simp
  ring

/-- **Zero-temperature Möbius conjugacy (equation (17)).**  `M ∘ (·^p) ∘ M⁻¹` equals the
zero-temperature Bethe RG rational map `((1+y)^p - (1-y)^p)/((1+y)^p + (1-y)^p)`. -/
theorem betheMobius_conjugacy (p : ℕ) {y : ℚ} (h1 : y ≠ 1)
    (h2 : (1 + y) ^ p + (1 - y) ^ p ≠ 0) :
    betheMobiusM ((betheMobiusMinv y) ^ p) =
      ((1 + y) ^ p - (1 - y) ^ p) / ((1 + y) ^ p + (1 - y) ^ p) := by
  have hne : (1 : ℚ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hp : (1 - y) ^ p ≠ 0 := pow_ne_zero p hne
  rw [betheMobiusMinv, div_pow, betheMobiusM]
  field_simp

/-- The zero-temperature Bethe RG map is the Möbius conjugate of the `p`-th power map. -/
theorem betheHolographicIsingRG_one_eq_mobius_conjugacy (p : ℕ) {y : ℚ} (h1 : y ≠ 1)
    (h2 : (1 + y) ^ p + (1 - y) ^ p ≠ 0) :
    (betheHolographicIsingNumerator p 1).eval y / (betheHolographicIsingDenominator p 1).eval y
      = betheMobiusM ((betheMobiusMinv y) ^ p) := by
  rw [betheMobius_conjugacy p h1 h2]
  simp only [betheHolographicIsingNumerator, betheHolographicIsingDenominator,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, one_mul]

end
end HTGeometry
