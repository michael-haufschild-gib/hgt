import GaloisForLFunctions.HTGeometry.RittSubleadingSlice

/-!
# The ratio of the two top coefficients solves the affine connection

When the coprime representation of a solution has trivial denominator the numerator identity reads
`P^Φ(aX + b) = c·P + (αX + β)`, and its two top coefficients say

`Φ(P_D)·a^D = c·P_D`,   `Φ(P_{D−1})·a^{D−1} + Φ(P_D)·D·a^{D−1}·b = c·P_{D−1} + α·[D = 2]`.

Dividing the second by the first eliminates the eigenvalue completely: the ratio
`Z = P_{D−1}/P_D` satisfies

`Φ(Z) + D·b = a·Z`

as soon as the `α` term is absent, that is whenever `D ≥ 3` or the linear part of the inhomogeneity
vanishes.  That is exactly the affine connection of the coordinate — the same relation a
positive-degree denominator produces — so a numerator of degree at least two is no worse than a
denominator: it too hands back the connection, and the descent's homogeneous branch survives only in
the single configuration `D = 2` with `α ≠ 0`.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- **The ratio of the two top coefficients solves the affine connection.** -/
theorem ratio_connection_of_polynomial_cross (Φ : K →+* K) {a b c α β : K} (ha : a ≠ 0)
    {P : K[X]} (hD : 2 ≤ P.natDegree) (hα : P.natDegree = 2 → α = 0)
    (hnum : twistComp Φ (C a * X + C b) P = C c * P + (C α * X + C β)) :
    Φ (P.coeff (P.natDegree - 1) / P.leadingCoeff)
      + (P.natDegree : K) * b = a * (P.coeff (P.natDegree - 1) / P.leadingCoeff) := by
  classical
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hD
    omega
  have hlcdef : P.leadingCoeff = P.coeff P.natDegree := rfl
  have hlc : P.coeff P.natDegree ≠ 0 := by
    rw [← hlcdef]
    exact leadingCoeff_ne_zero.mpr hP0
  set D : ℕ := P.natDegree with hDdef
  have hmapdeg : ∀ n : ℕ, D ≤ n → (P.map Φ).natDegree ≤ n := by
    intro n hn
    exact le_trans (natDegree_map_le (f := Φ) (p := P)) (by omega)
  have hRHS : ∀ k : ℕ, (C c * P + (C α * X + C β)).coeff k
      = c * P.coeff k + (α * (if 1 = k then 1 else 0) + (if k = 0 then β else 0)) := by
    intro k
    rw [coeff_add, coeff_C_mul, coeff_add, coeff_C_mul, coeff_X, coeff_C, mul_ite, mul_one,
      mul_zero]
  have hidx : (D - 1) + 1 = D := by omega
  have hcast : ((D - 1 : ℕ) : K) + 1 = (D : K) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → K) hidx
  -- the top coefficient
  have hlead : Φ (P.coeff D) * a ^ D = c * P.coeff D := by
    have h := congrArg (fun R : K[X] => R.coeff D) hnum
    simp only [twistComp] at h
    rw [coeff_comp_linear_of_natDegree_le ha (hmapdeg D le_rfl), coeff_map, hRHS D,
      if_neg (by omega : ¬ (1 : ℕ) = D), if_neg (by omega : ¬ D = 0)] at h
    linear_combination h
  -- the subleading coefficient
  have hsub : Φ (P.coeff (D - 1)) * a ^ (D - 1)
      + Φ (P.coeff D) * (D : K) * a ^ (D - 1) * b = c * P.coeff (D - 1) := by
    have h := congrArg (fun R : K[X] => R.coeff (D - 1)) hnum
    simp only [twistComp] at h
    rw [coeff_comp_linear_sub_one ha (hmapdeg ((D - 1) + 1) (by omega)), coeff_map, coeff_map,
      hidx, hRHS (D - 1), if_neg (by omega : ¬ (D - 1) = 0)] at h
    by_cases hD2 : D = 2
    · rw [hα hD2] at h
      rw [← hcast]
      linear_combination h
    · rw [if_neg (by omega : ¬ (1 : ℕ) = D - 1)] at h
      rw [← hcast]
      linear_combination h
  -- clear denominators
  have hΦlc : Φ (P.coeff D) ≠ 0 := fun h => hlc ((RingHom.injective Φ) (by rw [h, map_zero]))
  have hA1 : (a : K) ^ (D - 1) ≠ 0 := pow_ne_zero _ ha
  have hapow : (a : K) ^ D = a ^ (D - 1) * a := by
    conv_lhs => rw [← hidx]
    rw [pow_succ]
  rw [hapow] at hlead
  have key : Φ (P.coeff (D - 1)) * P.coeff D
      = a * P.coeff (D - 1) * Φ (P.coeff D) - (D : K) * b * P.coeff D * Φ (P.coeff D) := by
    refine mul_left_cancel₀ (mul_ne_zero hA1 ha) ?_
    linear_combination (a * P.coeff D) * hsub - (a * P.coeff (D - 1)) * hlead
  rw [hlcdef, map_div₀]
  field_simp
  linear_combination key

end GaloisForLFunctions.HTGeometry
