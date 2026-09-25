import GaloisForLFunctions.RHTower.GL3Plucker

open Matrix

/-!
# The Plücker parametrisation of `U(R)\SL₃(R)`

Over any commutative ring `R`, the map `γ ↦ (botRow γ, plk γ)` identifies the left cosets
`U(R)\SL₃(R)` with the pairs `(v, p)` of unimodular vectors (`∃ w, w · v = 1`) satisfying `v · p = 0`:
- fibres are exactly the left unipotent cosets (`plucker_eq_iff`);
- the image is exactly the unimodular orthogonal pairs (`plucker_range`), using the explicit
  completion `r₁ = w × p` (`w · v = 1`), `r₀ · p = 1` (`exists_det_one_of_plucker`).
For `R = ℤ` this is the parametrisation of `U(ℤ)\SL₃(ℤ)` by coprime Plücker pairs used in the
Poincaré series and Kloosterman sums of `SL₃(ℤ)` (Bump–Friedberg–Goldfeld).
-/

namespace GaloisForLFunctions.RHTower.GL3

variable {R : Type*} [CommRing R]

/-- A vector is unimodular if some integral vector pairs with it to `1` (for `R = ℤ`: coprime
entries). -/
def IsUnimodular (v : Fin 3 → R) : Prop := ∃ w : Fin 3 → R, w ⬝ᵥ v = 1

/-- The bottom row of a determinant-one matrix is unimodular (paired with the last column of the
adjugate). -/
theorem botRow_isUnimodular {M : Matrix (Fin 3) (Fin 3) R} (hM : M.det = 1) :
    IsUnimodular (botRow M) := by
  refine ⟨![adjugate M 0 2, adjugate M 1 2, adjugate M 2 2], ?_⟩
  have h := congrFun (congrFun (mul_adjugate M) 2) 2
  rw [hM] at h
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at h
  simp only [botRow, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination h

/-- The Plücker vector of a determinant-one matrix is unimodular (paired with the top row). -/
theorem plk_isUnimodular {M : Matrix (Fin 3) (Fin 3) R} (hM : M.det = 1) :
    IsUnimodular (plk M) := ⟨M 0, by rw [← det_eq_row0_dot_plk, hM]⟩

/-- The matrix with rows `r₀, r₁, r₂`. -/
def ofRows (r0 r1 r2 : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R := Matrix.of ![r0, r1, r2]

/-- The explicit cross product `a × b`. -/
def cross3 (a b : Fin 3 → R) : Fin 3 → R :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- **Existence (Bump–Friedberg–Goldfeld).** Every pair `(v, p)` of unimodular vectors with
`v · p = 0` is the (bottom row, Plücker vector) of a determinant-one matrix: take `r₁ = w × p` with
`w · v = 1` and `r₀` with `r₀ · p = 1`. -/
theorem exists_det_one_of_plucker {v p : Fin 3 → R} (hv : IsUnimodular v) (hp : IsUnimodular p)
    (hvp : v ⬝ᵥ p = 0) :
    ∃ M : Matrix (Fin 3) (Fin 3) R, M.det = 1 ∧ botRow M = v ∧ plk M = p := by
  obtain ⟨w, hw⟩ := hv
  obtain ⟨r0, hr0⟩ := hp
  simp only [dotProduct, Fin.sum_univ_three] at hw hr0 hvp
  -- `r₁ × v = p` for `r₁ = w × p`
  have hplk : plk (ofRows r0 (cross3 w p) v) = p := by
    ext i
    fin_cases i
    · simp [plk, ofRows, cross3]; linear_combination (p 0) * hw - (w 0) * hvp
    · simp [plk, ofRows, cross3]; linear_combination (p 1) * hw - (w 1) * hvp
    · simp [plk, ofRows, cross3]; linear_combination (p 2) * hw - (w 2) * hvp
  refine ⟨ofRows r0 (cross3 w p) v, ?_, ?_, hplk⟩
  · rw [det_eq_row0_dot_plk, hplk]
    simp only [ofRows, Matrix.of_apply, Matrix.cons_val_zero, dotProduct, Fin.sum_univ_three]
    exact hr0
  · ext i; fin_cases i <;> simp [botRow, ofRows]

/-- **The fibres of the Plücker map on `SL₃(R)` are the left `U(R)`-cosets.** -/
theorem plucker_eq_iff (γ γ' : Matrix.SpecialLinearGroup (Fin 3) R) :
    (botRow (γ' : Matrix (Fin 3) (Fin 3) R) = botRow γ ∧ plk (γ' : Matrix (Fin 3) (Fin 3) R) = plk γ) ↔
      ∃ a1 a2 a3 : R, (γ' : Matrix (Fin 3) (Fin 3) R) = unip a1 a2 a3 * γ := by
  constructor
  · rintro ⟨hb, hp⟩
    exact exists_unip_of_plucker_det_one γ.2 γ'.2 hb hp
  · rintro ⟨a1, a2, a3, h⟩
    rw [h]
    exact ⟨botRow_unip_mul _ _ _ _, plk_unip_mul _ _ _ _⟩

/-- **The image of the Plücker map on `SL₃(R)`**: exactly the pairs of unimodular vectors `(v, p)`
with `v · p = 0`. For `R = ℤ` these are the coprime pairs `(A₁,B₁,C₁), (A₂,B₂,C₂)` with
`A₁A₂' + B₁B₂' + C₁C₂' = 0` in the cross-product ordering. -/
theorem plucker_range (v p : Fin 3 → R) :
    (∃ γ : Matrix.SpecialLinearGroup (Fin 3) R,
        botRow (γ : Matrix (Fin 3) (Fin 3) R) = v ∧ plk (γ : Matrix (Fin 3) (Fin 3) R) = p) ↔
      IsUnimodular v ∧ IsUnimodular p ∧ v ⬝ᵥ p = 0 := by
  constructor
  · rintro ⟨γ, rfl, rfl⟩
    exact ⟨botRow_isUnimodular γ.2, plk_isUnimodular γ.2, botRow_dot_plk _⟩
  · rintro ⟨hv, hp, hvp⟩
    obtain ⟨M, hdet, hb, hpl⟩ := exists_det_one_of_plucker hv hp hvp
    exact ⟨⟨M, hdet⟩, hb, hpl⟩

end GaloisForLFunctions.RHTower.GL3
