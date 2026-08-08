import GaloisForLFunctions.HTGeometry.LogJetRowTail

/-!
# The newest coordinate commutes with the product law up to one multiplier

Only the newest jet of a product law involves the newest coordinate, so on the low subalgebra the
coordinate derivation and the law satisfy the exact commutation

`∂_m ∘ δ = δ ∘ ∂_m + A · ∂_m`,   `A = ∂_m (δ X_m)`.

The proof is structural rather than computational: the difference of the two sides is itself a
derivation, it kills every coordinate of index at most `m`, and a derivation vanishing on a
generating set vanishes on the generated subalgebra.  The inverse generators need no separate
computation — a derivation carries inverses by its own quotient rule.

Iterating gives the newest column of the logarithmic Jacobian **at every order**: it is the shifted
operator `G ↦ δG + A·G` applied repeatedly to the single entry `∂_m (logSum)`, which the model
already computes in closed form.  This is the column the height induction peels.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-! ## The newest response -/

/-- The response of the newest jet to the newest coordinate. -/
noncomputable def topResponse (Q v : ℕ → Polynomial ℂ) (m : ℕ) : CascadeField :=
  fpderiv m (prodJet Q v m)

/-- The response is the head product times the derivative of the terminal factor. -/
theorem topResponse_eq (m : ℕ) :
    topResponse Q v m = prodHead Q m * fact (v m).derivative m := by
  rw [topResponse, prodJet_eq, Derivation.leibniz, fpderiv_prodHead_of_le Q (le_refl m),
    derivation_fact, fpderiv_fx_self]
  simp

/-- Every jet below the newest is invisible to the newest coordinate, and the newest one responds by
exactly the multiplier. -/
theorem fpderiv_top_prodJet {m j : ℕ} (hj : j ≤ m) :
    fpderiv m (prodJet Q v j) = topResponse Q v m * fpderiv m (fx j) := by
  rcases eq_or_lt_of_le hj with rfl | hlt
  · rw [fpderiv_fx_self, topResponse, mul_one]
  · rw [fpderiv_eq_zero_of_mem_lowSub Q v hlt (prodJet_mem_lowSub Q v (le_refl j)),
      fpderiv_fx_of_ne (by omega : j ≠ m), mul_zero]

/-! ## The commutator is a derivation -/

/-- The commutator of the newest coordinate derivation with the product law, as a linear map. -/
noncomputable def topCommutatorLin (Q v : ℕ → Polynomial ℂ) (m : ℕ) :
    CascadeField →ₗ[ℂ] CascadeField where
  toFun F := fpderiv m (prodDerivation Q v F) - prodDerivation Q v (fpderiv m F)
      - topResponse Q v m * fpderiv m F
  map_add' x y := by
    simp only [map_add]
    ring
  map_smul' c x := by
    have key : ∀ (D : Derivation ℂ CascadeField CascadeField) (y : CascadeField),
        D (algebraMap ℂ CascadeField c * y) = algebraMap ℂ CascadeField c * D y := by
      intro D y
      rw [Derivation.leibniz, D.map_algebraMap]
      simp
    simp only [Algebra.smul_def, RingHom.id_apply]
    rw [key (prodDerivation Q v) x, key (fpderiv m) x,
      key (fpderiv m) (prodDerivation Q v x), key (prodDerivation Q v) (fpderiv m x)]
    ring

theorem topCommutatorLin_apply (m : ℕ) (F : CascadeField) :
    topCommutatorLin Q v m F
      = fpderiv m (prodDerivation Q v F) - prodDerivation Q v (fpderiv m F)
        - topResponse Q v m * fpderiv m F := rfl

/-- **The commutator is itself a derivation.**  Both `∂δ` and `δ∂ + A∂` fail the Leibniz rule, but
their difference satisfies it exactly. -/
noncomputable def topCommutator (Q v : ℕ → Polynomial ℂ) (m : ℕ) :
    Derivation ℂ CascadeField CascadeField :=
  Derivation.mk' (topCommutatorLin Q v m) (by
    intro a b
    simp only [topCommutatorLin_apply, smul_eq_mul, Derivation.leibniz, map_add, smul_eq_mul]
    ring)

theorem topCommutator_apply (m : ℕ) (F : CascadeField) :
    topCommutator Q v m F
      = fpderiv m (prodDerivation Q v F) - prodDerivation Q v (fpderiv m F)
        - topResponse Q v m * fpderiv m F := rfl

/-! ## It vanishes on the low subalgebra -/

theorem topCommutator_fx {m j : ℕ} (hj : j ≤ m) : topCommutator Q v m (fx j) = 0 := by
  rw [topCommutator_apply, prodDerivation_fx, fpderiv_top_prodJet Q v hj]
  rcases eq_or_lt_of_le hj with rfl | hlt
  · rw [fpderiv_fx_self]
    simp
  · rw [fpderiv_fx_of_ne (by omega : j ≠ m)]
    simp

theorem topCommutator_fact {m j : ℕ} (hj : j ≤ m) (p : Polynomial ℂ) :
    topCommutator Q v m (fact p j) = 0 := by
  rw [derivation_fact, topCommutator_fx Q v hj]
  simp

theorem topCommutator_inv_fact {m j : ℕ} (hj : j ≤ m) (p : Polynomial ℂ) :
    topCommutator Q v m ((fact p j)⁻¹) = 0 := by
  rw [Derivation.leibniz_inv, topCommutator_fact Q v hj]
  simp

/-- **The commutator vanishes on the low subalgebra.**  A derivation agreeing with zero on the
generators agrees with zero on everything they generate. -/
theorem topCommutator_eq_zero {m : ℕ} {F : CascadeField} (h : F ∈ lowSub Q v m) :
    topCommutator Q v m F = 0 := by
  have hgen : Set.EqOn (⇑(topCommutator Q v m))
      (⇑(0 : Derivation ℂ CascadeField CascadeField))
      ({z : CascadeField | ∃ j, j ≤ m ∧ z = fx j}
        ∪ {z : CascadeField | ∃ j, j ≤ m ∧ z = (fact (Q j) j)⁻¹}
        ∪ {z : CascadeField | ∃ j, j ≤ m ∧ z = (fact (v j) j)⁻¹}) := by
    rintro x ((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩)
    · simpa using topCommutator_fx Q v hj
    · simpa using topCommutator_inv_fact Q v hj (Q j)
    · simpa using topCommutator_inv_fact Q v hj (v j)
  have hmem : F ∈ (lowSub Q v m : Set CascadeField) := h
  rw [lowSub] at hmem
  simpa using Derivation.eqOn_adjoin hgen hmem

/-- **The exact commutation law.** -/
theorem fpderiv_prodDerivation_top {m : ℕ} {F : CascadeField} (h : F ∈ lowSub Q v m) :
    fpderiv m (prodDerivation Q v F)
      = prodDerivation Q v (fpderiv m F) + topResponse Q v m * fpderiv m F := by
  have h0 := topCommutator_eq_zero Q v h
  rw [topCommutator_apply] at h0
  linear_combination h0

/-! ## The shifted operator, and the newest column at every order -/

/-- The operator the newest coordinate turns the product law into. -/
noncomputable def topShift (Q v : ℕ → Polynomial ℂ) (m : ℕ) : CascadeField → CascadeField :=
  fun G => prodDerivation Q v G + topResponse Q v m * G

/-- **The newest coordinate of an iterate is an iterate of the shifted operator.** -/
theorem fpderiv_iterate_prodDerivation_top {m : ℕ} (r : ℕ) {F : CascadeField}
    (h : F ∈ lowSub Q v m) :
    fpderiv m (((prodDerivation Q v : CascadeField → CascadeField)^[r]) F)
      = ((topShift Q v m)^[r]) (fpderiv m F) := by
  induction r generalizing F with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply, ih (prodDerivation_mem_lowSub Q v h),
        fpderiv_prodDerivation_top Q v h, Function.iterate_succ_apply]
      rfl

/-- **The newest column of the logarithmic Jacobian, at every order, in closed form.**  Only the
Wronskian entry of the newest level enters; the shifted operator generates the rest of the column. -/
theorem fpderiv_iterate_logSum_top_closed {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ)
    (hQ : ∀ j, Q j ≠ 0) (n r : ℕ) :
    fpderiv (n + 1)
        (((prodDerivation Q v : CascadeField → CascadeField)^[r]) (logSum Q v (n + 2)))
      = ((topShift Q v (n + 1))^[r])
          (prodHead Q (n + 1)
            * (fact (scaledLogWronskian (Q (n + 1)) (v (n + 1))) (n + 1)
                / fact (Q (n + 1)) (n + 1) ^ 2)) := by
  rw [fpderiv_iterate_prodDerivation_top Q v r
      (logSum_mem_lowSub_succ Q v (le_refl (n + 2))),
    fpderiv_logSum_top Q v (hQ (n + 1))]

end GaloisForLFunctions.HTGeometry
