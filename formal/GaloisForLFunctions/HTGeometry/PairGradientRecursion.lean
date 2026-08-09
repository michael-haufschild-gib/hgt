import GaloisForLFunctions.HTGeometry.PairLowSubalgebra

/-!
# The gradient recursion of a two-coordinate product law

The commutator argument transports unchanged: the difference of `∂_k ∘ δ` and `δ ∘ ∂_k`, corrected
by the finite first-order term `∑_l ∂_k(δX_l)·∂_l`, is a derivation, and a derivation vanishing on
the generators of the low subalgebra vanishes on all of it.

The only new step is that a generator of the low subalgebra is now a *two-variable* polynomial in two
consecutive coordinates rather than one variable in one; an induction on that polynomial reduces its
vanishing to the coordinates', which the `fx` case already gives.

So the gradient of a derivative is again the shifted gradient, with the same upper-triangular mixing
matrix — the shape the whole peel runs on.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ}

/-! ## A derivation killing the coordinates kills the factors -/

/-- **A derivation vanishing on the coordinates vanishes on every two-coordinate factor.** -/
theorem derivation_algebraMap_pairPoly_eq_zero
    (D : Derivation ℂ CascadeField CascadeField) {j m : ℕ} (h : j + 1 ≤ m)
    (hD : ∀ i, i ≤ m → D (fx i) = 0) (q : MvPolynomial (Fin 2) ℂ) :
    D (algebraMap (MvPolynomial ℕ ℂ) CascadeField (pairPoly q j)) = 0 := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      rw [pairPoly_C]
      have hc : algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.C a)
          = algebraMap ℂ CascadeField a := rfl
      rw [hc, D.map_algebraMap]
  | add q r hq hr =>
      rw [pairPoly_add, map_add, map_add, hq, hr, add_zero]
  | mul_X q i hq =>
      rw [pairPoly_mul_X, map_mul]
      have hxi : algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X (j + (i : ℕ)))
          = fx (j + (i : ℕ)) := rfl
      have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
      rw [hxi, Derivation.leibniz, hq, hD (j + (i : ℕ)) (by rcases hi with hi | hi <;> omega)]
      simp

/-! ## The mixing correction -/

/-- The first-order correction of the two-coordinate law. -/
noncomputable def pairJetMix (p : ℕ → MvPolynomial (Fin 2) ℂ) (m k : ℕ) (F : CascadeField) :
    CascadeField :=
  ∑ l ∈ Finset.range (m + 1), pairResponse p k l * fpderiv l F

theorem pairJetMix_add (m k : ℕ) (a b : CascadeField) :
    pairJetMix p m k (a + b) = pairJetMix p m k a + pairJetMix p m k b := by
  rw [pairJetMix, pairJetMix, pairJetMix, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_add]
  ring

theorem pairJetMix_mul (m k : ℕ) (a b : CascadeField) :
    pairJetMix p m k (a * b) = a * pairJetMix p m k b + b * pairJetMix p m k a := by
  rw [pairJetMix, pairJetMix, pairJetMix, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem pairJetMix_algebraMap_mul (m k : ℕ) (c : ℂ) (a : CascadeField) :
    pairJetMix p m k (algebraMap ℂ CascadeField c * a)
      = algebraMap ℂ CascadeField c * pairJetMix p m k a := by
  rw [pairJetMix, pairJetMix, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : fpderiv l (algebraMap ℂ CascadeField c * a)
      = algebraMap ℂ CascadeField c * fpderiv l a := by
    rw [Derivation.leibniz, (fpderiv l).map_algebraMap]
    simp
  rw [h]
  ring

/-! ## The commutator -/

/-- The corrected commutator of a coordinate derivation with the two-coordinate law. -/
noncomputable def pairMixCommutatorLin (p : ℕ → MvPolynomial (Fin 2) ℂ) (m k : ℕ) :
    CascadeField →ₗ[ℂ] CascadeField where
  toFun F := fpderiv k (pairDerivation p F) - pairDerivation p (fpderiv k F)
      - pairJetMix p m k F
  map_add' x y := by
    simp only [map_add, pairJetMix_add]
    ring
  map_smul' c x := by
    have key : ∀ (D : Derivation ℂ CascadeField CascadeField) (y : CascadeField),
        D (algebraMap ℂ CascadeField c * y) = algebraMap ℂ CascadeField c * D y := by
      intro D y
      rw [Derivation.leibniz, D.map_algebraMap]
      simp
    simp only [Algebra.smul_def, RingHom.id_apply]
    rw [key (pairDerivation p) x, key (fpderiv k) x,
      key (fpderiv k) (pairDerivation p x), key (pairDerivation p) (fpderiv k x),
      pairJetMix_algebraMap_mul]
    ring

theorem pairMixCommutatorLin_apply (m k : ℕ) (F : CascadeField) :
    pairMixCommutatorLin p m k F
      = fpderiv k (pairDerivation p F) - pairDerivation p (fpderiv k F)
        - pairJetMix p m k F := rfl

/-- **The corrected commutator is a derivation.** -/
noncomputable def pairMixCommutator (p : ℕ → MvPolynomial (Fin 2) ℂ) (m k : ℕ) :
    Derivation ℂ CascadeField CascadeField :=
  Derivation.mk' (pairMixCommutatorLin p m k) (by
    intro a b
    simp only [pairMixCommutatorLin_apply, smul_eq_mul, Derivation.leibniz, map_add, smul_eq_mul,
      pairJetMix_mul]
    ring)

theorem pairMixCommutator_apply (m k : ℕ) (F : CascadeField) :
    pairMixCommutator p m k F
      = fpderiv k (pairDerivation p F) - pairDerivation p (fpderiv k F)
        - pairJetMix p m k F := rfl

theorem pairMixCommutator_fx {m k j : ℕ} (hj : j ≤ m) :
    pairMixCommutator p m k (fx j) = 0 := by
  classical
  have hD : pairDerivation p (fpderiv k (fx j)) = 0 := by
    by_cases hjk : j = k
    · rw [hjk, fpderiv_fx_self]
      simp
    · rw [fpderiv_fx_of_ne hjk]
      simp
  have hmix : pairJetMix p m k (fx j) = pairResponse p k j := by
    rw [pairJetMix, Finset.sum_eq_single j]
    · rw [fpderiv_fx_self, mul_one]
    · intro l _ hlj
      rw [fpderiv_fx_of_ne (fun h => hlj h.symm), mul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega : j < m + 1)) hnot
  rw [pairMixCommutator_apply, pairDerivation_fx, hD, hmix, ← pairResponse]
  ring

theorem pairMixCommutator_inv_pairFactor {m k j : ℕ} (hj : j + 1 ≤ m) :
    pairMixCommutator p m k ((pairFactor (p j) j)⁻¹) = 0 := by
  have hfac : pairMixCommutator p m k (pairFactor (p j) j) = 0 :=
    derivation_algebraMap_pairPoly_eq_zero (pairMixCommutator p m k) hj
      (fun i hi => pairMixCommutator_fx hi) (p j)
  rw [Derivation.leibniz_inv, hfac]
  simp

/-- **The commutator vanishes on the low subalgebra.** -/
theorem pairMixCommutator_eq_zero {m k : ℕ} {F : CascadeField} (h : F ∈ pairLowSub p m) :
    pairMixCommutator p m k F = 0 := by
  have hgen : Set.EqOn (⇑(pairMixCommutator p m k))
      (⇑(0 : Derivation ℂ CascadeField CascadeField))
      ({z : CascadeField | ∃ j, j ≤ m ∧ z = fx j}
        ∪ {z : CascadeField | ∃ j, j + 1 ≤ m ∧ z = (pairFactor (p j) j)⁻¹}) := by
    rintro x (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · simpa using pairMixCommutator_fx hj
    · simpa using pairMixCommutator_inv_pairFactor hj
  have hmem : F ∈ (pairLowSub p m : Set CascadeField) := h
  rw [pairLowSub] at hmem
  simpa using Derivation.eqOn_adjoin hgen hmem

/-- **The exact mixed commutation law of the two-coordinate product law.** -/
theorem fpderiv_pairDerivation_mixed {m k : ℕ} {F : CascadeField} (h : F ∈ pairLowSub p m) :
    fpderiv k (pairDerivation p F)
      = pairDerivation p (fpderiv k F) + pairJetMix p m k F := by
  have h0 := pairMixCommutator_eq_zero (k := k) h
  rw [pairMixCommutator_apply] at h0
  linear_combination h0

/-! ## The gradient recursion -/

/-- The operator the two-coordinate law induces on gradient vectors. -/
noncomputable def pairGradShift (p : ℕ → MvPolynomial (Fin 2) ℂ) (m : ℕ)
    (u : ℕ → CascadeField) : ℕ → CascadeField :=
  fun k => pairDerivation p (u k) + ∑ l ∈ Finset.range (m + 1), pairResponse p k l * u l

/-- **The gradient of a derivative is the shifted gradient.** -/
theorem gradient_pairDerivation_eq {m : ℕ} {F : CascadeField} (h : F ∈ pairLowSub p m) :
    (fun l => fpderiv l (pairDerivation p F))
      = pairGradShift p m (fun l => fpderiv l F) := by
  funext k
  exact fpderiv_pairDerivation_mixed h

/-- **The gradient of an iterate is an iterate of the shifted operator.** -/
theorem gradient_iterate_pair_eq {m : ℕ} (r : ℕ) {F : CascadeField} (h : F ∈ pairLowSub p m) :
    (fun l => fpderiv l (((pairDerivation p : CascadeField → CascadeField)^[r]) F))
      = ((pairGradShift p m)^[r]) (fun l => fpderiv l F) := by
  induction r generalizing F with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply, ih (pairDerivation_mem_pairLowSub h),
        gradient_pairDerivation_eq h, Function.iterate_succ_apply]

end GaloisForLFunctions.HTGeometry
