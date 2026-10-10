import GaloisForLFunctions.RHTower.PhotonicLosslessTemporalStackRealZeros

/-!
# Impedance scale is invisible to the lossless receiver

Scaling every impedance of a lossless temporal stack by `λ ≠ 0` conjugates its transfer matrix by
`diag(1, λ)` (`ptrLosslessSlab_scale`, `ptrLosslessStack_scale`). So the displacement entry, which
is the receiver's only datum, does not change (`ptrLosslessStackEntry_scale`). It depends only on
the durations and the impedance ratios.

For the PTR prime pair, impedances `c·log p` and `4c·log p` with a common duration `τ`, the entry is

  `cos²(kτ) − 4 sin²(kτ) = −3/2 + (5/2) cos(2kτ)`,

independent of the prime `p` and of `c` (`ptrPrimePairEntry_eq`). Its zeros are exactly the
wavenumbers with `cos(2kτ) = 3/5`. That is the rational phase datum `cos = 3/5`, `sin = 4/5` of the
PTR prime cyclic transfer, so the cyclic transfer sits on a resonance of the pair
(`ptrPrimePairEntry_eq_zero_iff`). Prime data carried by impedance magnitudes never reaches a
lossless product port. Any arithmetic must enter through the durations, which the clock laws
(integer density, half-rate exclusion, thin slabs) already constrain.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Scaling the impedance conjugates a slab by `diag(1, λ)`. -/
theorem ptrLosslessSlab_scale {lam : ℝ} (hlam : lam ≠ 0) (κ τ : ℝ) (k : ℂ) :
    ptrLosslessSlab (lam * κ) τ k =
      !![1, 0; 0, (lam : ℂ)] * ptrLosslessSlab κ τ k * !![1, 0; 0, (lam : ℂ)⁻¹] := by
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptrLosslessSlab, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem diag_lam_mul_inv {lam : ℝ} (hlam : lam ≠ 0) :
    !![1, 0; 0, (lam : ℂ)⁻¹] * !![1, 0; 0, (lam : ℂ)] = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hl]

/-- Scaling every impedance conjugates the whole stack by `diag(1, λ)`. -/
theorem ptrLosslessStack_scale {lam : ℝ} (hlam : lam ≠ 0) (L : List (ℝ × ℝ)) (k : ℂ) :
    ptrLosslessStack (L.map fun x => (lam * x.1, x.2)) k =
      !![1, 0; 0, (lam : ℂ)] * ptrLosslessStack L k * !![1, 0; 0, (lam : ℂ)⁻¹] := by
  induction L with
  | nil =>
    simp only [ptrLosslessStack, List.map_nil, List.prod_nil, Matrix.mul_one]
    exact (diag_lam_mul_inv hlam).symm.trans (by
      ext i j
      have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hl])
  | cons x L ih =>
    simp only [ptrLosslessStack, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, ptrLosslessSlab_scale hlam]
    simp only [Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc (!![1, 0; 0, (lam : ℂ)⁻¹]), diag_lam_mul_inv hlam, Matrix.one_mul]

/-- **Scale invisibility.** The displacement entry does not see a common impedance scale. -/
theorem ptrLosslessStackEntry_scale {lam : ℝ} (hlam : lam ≠ 0) (L : List (ℝ × ℝ)) (k : ℂ) :
    ptrLosslessStackEntry (L.map fun x => (lam * x.1, x.2)) k = ptrLosslessStackEntry L k := by
  unfold ptrLosslessStackEntry
  rw [ptrLosslessStack_scale hlam]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- The PTR prime pair: impedances `c log p` and `4c log p`, common duration `τ`. -/
def ptrPrimePair (c : ℝ) (p : ℕ) (τ : ℝ) : List (ℝ × ℝ) :=
  [(c * Real.log p, τ), (4 * (c * Real.log p), τ)]

/-- **The prime pair's entry is prime-blind.** For `p ≥ 2` and `c ≠ 0`,
`A(k) = −3/2 + (5/2) cos(2kτ)`. -/
theorem ptrPrimePairEntry_eq {c : ℝ} (hc : c ≠ 0) {p : ℕ} (hp : 2 ≤ p) (τ : ℝ) (k : ℂ) :
    ptrLosslessStackEntry (ptrPrimePair c p τ) k = -3 / 2 + 5 / 2 * Complex.cos (2 * (k * τ)) := by
  have hlog : Real.log p ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp
    exact (Real.log_pos this).ne'
  have hlam : c * Real.log p ≠ 0 := mul_ne_zero hc hlog
  have hpair : ptrPrimePair c p τ = [(1, τ), (4, τ)].map fun x => ((c * Real.log p) * x.1, x.2) := by
    simp [ptrPrimePair, mul_comm]
  rw [hpair, ptrLosslessStackEntry_scale hlam]
  simp only [ptrLosslessStackEntry, ptrLosslessStack, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Matrix.mul_one, ptrLosslessSlab, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  rw [Complex.cos_two_mul]
  linear_combination (-4 : ℂ) * Complex.sin_sq_add_cos_sq (k * τ)

/-- **The PTR phase datum is a resonance.** The prime pair's entry vanishes exactly when
`cos(2kτ) = 3/5`. -/
theorem ptrPrimePairEntry_eq_zero_iff {c : ℝ} (hc : c ≠ 0) {p : ℕ} (hp : 2 ≤ p) (τ : ℝ)
    (k : ℂ) :
    ptrLosslessStackEntry (ptrPrimePair c p τ) k = 0 ↔ Complex.cos (2 * (k * τ)) = 3 / 5 := by
  rw [ptrPrimePairEntry_eq hc hp]
  constructor
  · intro h; linear_combination (2 / 5 : ℂ) * h
  · intro h; rw [h]; norm_num

end

end RHTower
