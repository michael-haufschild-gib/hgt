import GaloisForLFunctions.HTGeometry.CascadeChainRule

/-!
# Mixed coordinate derivatives commute

The commutator of two derivations is again a derivation, and on a polynomial ring a derivation is
determined by its values on the variables.  A second partial derivative of a variable is a partial
derivative of a constant, so the commutator kills every variable and is therefore zero.

On the rational model the same commutator is a derivation of a fraction field vanishing on the
polynomial subring, hence zero: a derivation kills `u/v` as soon as it kills `u` and `v`.

The consequence used downstream is that a logarithmic gradient is a closed form: the expression
`∂_k (∂_l F / F)` is symmetric in `k` and `l`, with no hypothesis on `F`.
-/

namespace GaloisForLFunctions

open MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R]

/-! ## The commutator of two partial derivatives -/

/-- The commutator of two partial derivatives, as a linear map. -/
noncomputable def pderivCommutatorLin (i j : σ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun q := pderiv i (pderiv j q) - pderiv j (pderiv i q)
  map_add' x y := by
    simp only [map_add]
    ring
  map_smul' c x := by
    simp only [Derivation.map_smul, RingHom.id_apply, smul_sub]

theorem pderivCommutatorLin_apply (i j : σ) (q : MvPolynomial σ R) :
    pderivCommutatorLin i j q = pderiv i (pderiv j q) - pderiv j (pderiv i q) := rfl

/-- **The commutator of two partial derivatives is a derivation.** -/
noncomputable def pderivCommutator (i j : σ) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  Derivation.mk' (pderivCommutatorLin i j) (by
    intro a b
    simp only [pderivCommutatorLin_apply, Derivation.leibniz, smul_eq_mul, map_add]
    ring)

theorem pderivCommutator_apply (i j : σ) (q : MvPolynomial σ R) :
    pderivCommutator i j q = pderiv i (pderiv j q) - pderiv j (pderiv i q) := rfl

/-- A second partial derivative of a variable vanishes: the first one is already a constant. -/
theorem pderiv_pderiv_X (i j k : σ) :
    pderiv i (pderiv j (X k : MvPolynomial σ R)) = 0 := by
  by_cases hkj : k = j
  · subst hkj
    rw [pderiv_X_self, Derivation.map_one_eq_zero]
  · rw [pderiv_X_of_ne hkj, map_zero]

theorem pderivCommutator_eq_zero (i j : σ) :
    (pderivCommutator i j : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) = 0 := by
  refine MvPolynomial.derivation_ext fun k => ?_
  rw [pderivCommutator_apply, pderiv_pderiv_X, pderiv_pderiv_X]
  simp

/-- **Partial derivatives of a polynomial commute.** -/
theorem pderiv_comm (i j : σ) (q : MvPolynomial σ R) :
    pderiv i (pderiv j q) = pderiv j (pderiv i q) := by
  have h : (pderivCommutator i j : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) q = 0 := by
    rw [pderivCommutator_eq_zero]
    simp
  rw [pderivCommutator_apply] at h
  exact sub_eq_zero.mp h

namespace HTGeometry

/-! ## The commutator on the rational model -/

/-- The commutator of two coordinate derivations of the model, as a linear map. -/
noncomputable def fpderivCommutatorLin (k l : ℕ) : CascadeField →ₗ[ℂ] CascadeField where
  toFun x := fpderiv k (fpderiv l x) - fpderiv l (fpderiv k x)
  map_add' x y := by
    simp only [map_add]
    ring
  map_smul' c x := by
    simp only [Derivation.map_smul, RingHom.id_apply, smul_sub]

theorem fpderivCommutatorLin_apply (k l : ℕ) (x : CascadeField) :
    fpderivCommutatorLin k l x = fpderiv k (fpderiv l x) - fpderiv l (fpderiv k x) := rfl

/-- **The commutator of two coordinate derivations is a derivation.** -/
noncomputable def fpderivCommutator (k l : ℕ) : Derivation ℂ CascadeField CascadeField :=
  Derivation.mk' (fpderivCommutatorLin k l) (by
    intro a b
    simp only [fpderivCommutatorLin_apply, Derivation.leibniz, smul_eq_mul, map_add]
    ring)

theorem fpderivCommutator_apply (k l : ℕ) (x : CascadeField) :
    fpderivCommutator k l x = fpderiv k (fpderiv l x) - fpderiv l (fpderiv k x) := rfl

theorem fpderivCommutator_algebraMap (k l : ℕ) (N : MvPolynomial ℕ ℂ) :
    fpderivCommutator k l (algebraMap (MvPolynomial ℕ ℂ) CascadeField N) = 0 := by
  have hcomm := pderiv_comm (R := ℂ) k l N
  rw [fpderivCommutator_apply, fpderiv_algebraMap, fpderiv_algebraMap, fpderiv_algebraMap,
    fpderiv_algebraMap, hcomm, sub_self]

/-- **The coordinate derivations of the model commute.** -/
theorem fpderiv_comm (k l : ℕ) (x : CascadeField) :
    fpderiv k (fpderiv l x) = fpderiv l (fpderiv k x) := by
  have hzero : fpderivCommutator k l x = 0 := by
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial ℕ ℂ) x
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      fpderivCommutator_algebraMap, fpderivCommutator_algebraMap]
    simp
  rw [fpderivCommutator_apply] at hzero
  exact sub_eq_zero.mp hzero

/-- **A logarithmic gradient is a closed form.**  No hypothesis on `F` is needed: at `F = 0` both
sides vanish. -/
theorem fpderiv_logDeriv_symm (k l : ℕ) (F : CascadeField) :
    fpderiv k (fpderiv l F / F) = fpderiv l (fpderiv k F / F) := by
  rcases eq_or_ne F 0 with rfl | hF
  · simp
  · rw [div_eq_mul_inv, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz,
      Derivation.leibniz_inv, Derivation.leibniz_inv]
    simp only [smul_eq_mul, neg_mul, mul_neg]
    rw [fpderiv_comm k l F]
    ring

end HTGeometry

end GaloisForLFunctions
