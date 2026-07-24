import GaloisForLFunctions.HTGeometry.ScalarDifferentialRationalOrder

/-!
# Semilinear jet covariance and order preservation

A *semilinear clock dilation* `e` acts on the derivation by a constant factor,
`e(w′) = λ · (e w)′`, rather than commuting with it.  Iterating, the `n`-th jet transforms with a
weight `λ^n`:

`e(differentialJet n z) = λ^n · differentialJet n (e z)`.

Because the weights `λ^n` are nonzero base-field constants, they are absorbed into field generation:
the finite observable field is still carried onto the field at the same resolution,
`(jetObservableField C x N).map e = jetObservableField C (e x) N`, exactly as for a
derivation-preserving embedding.  Consequently a semilinear automorphism **preserves exact scalar
differential order**.

This is the order rigidity the *clock* needs (the clock is semilinear, not differential): it is the
semilinear analogue of `differentialJet_algHom` / `HasScalarDifferentialOrder.map`, and it feeds the
order-zero reduction that makes the clock act by a Möbius transform on the core generator (§3).
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C E : Type*} [Field C] [Field E] [Differential E] [Algebra C E]

/-- A power of a differential constant is a differential constant. -/
private theorem algebraMap_pow_deriv_zero
    {lam : C} (hconst : (algebraMap C E lam)′ = 0) (n : ℕ) :
    (algebraMap C E (lam ^ n))′ = 0 := by
  rw [map_pow]
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, Derivation.leibniz, ih, hconst, smul_zero, smul_zero, add_zero]

/-- **Semilinear jet covariance.**  A semilinear clock dilation `e` with `e(w′) = λ·(e w)′` (and `λ`
a differential constant) carries the `n`-th jet with weight `λ^n`:
`e(differentialJet n z) = λ^n · differentialJet n (e z)`. -/
theorem differentialJet_semilinear
    (e : E →ₐ[C] E) {lam : C} (hconst : (algebraMap C E lam)′ = 0)
    (hsemi : ∀ z : E, e z′ = algebraMap C E lam * (e z)′) (z : E) :
    ∀ n : ℕ, e (differentialJet n z) = algebraMap C E (lam ^ n) * differentialJet n (e z)
  | 0 => by simp
  | n + 1 => by
      rw [differentialJet_succ n z, hsemi,
        differentialJet_semilinear e hconst hsemi z n, Derivation.leibniz,
        algebraMap_pow_deriv_zero hconst, smul_zero, add_zero, smul_eq_mul,
        differentialJet_succ n (e z), ← mul_assoc, ← map_mul, ← pow_succ']

/-- **Semilinear embedding covariance.**  A semilinear clock dilation carries the finite observable
field onto the field at the same resolution: `(jetObservableField C x N).map e =
jetObservableField C (e x) N`.  The jet weights `λ^n` are nonzero constants, so they are absorbed
into field generation. -/
theorem jetObservableField_map_semilinear
    (e : E →ₐ[C] E) {lam : C} (hlam : lam ≠ 0) (hconst : (algebraMap C E lam)′ = 0)
    (hsemi : ∀ z : E, e z′ = algebraMap C E lam * (e z)′)
    (x : E) (N : ℕ) :
    (jetObservableField C x N).map e = jetObservableField C (e x) N := by
  rw [jetObservableField, jetObservableField, IntermediateField.adjoin_map]
  simp only [Set.image_image]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨n, hn, rfl⟩
    show e (differentialJet n x) ∈ IntermediateField.adjoin C
      ((fun m : ℕ => differentialJet m (e x)) '' Set.Iio N)
    rw [differentialJet_semilinear e hconst hsemi x n]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin C _ ⟨n, hn, rfl⟩)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨n, hn, rfl⟩
    show differentialJet n (e x) ∈ IntermediateField.adjoin C
      ((fun m : ℕ => e (differentialJet m x)) '' Set.Iio N)
    have hmem : algebraMap C E (lam ^ n) * differentialJet n (e x)
        ∈ IntermediateField.adjoin C
          ((fun m : ℕ => e (differentialJet m x)) '' Set.Iio N) := by
      rw [← differentialJet_semilinear e hconst hsemi x n]
      exact IntermediateField.subset_adjoin C _ ⟨n, hn, rfl⟩
    have hinv : differentialJet n (e x)
        = algebraMap C E ((lam ^ n)⁻¹)
          * (algebraMap C E (lam ^ n) * differentialJet n (e x)) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero n hlam), map_one, one_mul]
    rw [hinv]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) hmem

/-- **Semilinear order rigidity.**  A semilinear clock dilation preserves exact scalar differential
order: `HasScalarDifferentialOrder C y z n → HasScalarDifferentialOrder C (e y) (e z) n`. -/
theorem HasScalarDifferentialOrder.map_semilinear
    {y z : E} {n : ℕ} (e : E →ₐ[C] E) {lam : C} (hlam : lam ≠ 0)
    (hconst : (algebraMap C E lam)′ = 0)
    (hsemi : ∀ w : E, e w′ = algebraMap C E lam * (e w)′)
    (hz : HasScalarDifferentialOrder C y z n) :
    HasScalarDifferentialOrder C (e y) (e z) n := by
  constructor
  · rw [← jetObservableField_map_semilinear e hlam hconst hsemi y (n + 1)]
    exact (IntermediateField.map_mem_map
      (S := jetObservableField C y (n + 1)) e (x := z)).mpr hz.1
  · intro hlow
    apply hz.2
    rw [← jetObservableField_map_semilinear e hlam hconst hsemi y n] at hlow
    exact (IntermediateField.map_mem_map
      (S := jetObservableField C y n) e (x := z)).mp hlow

end

end GaloisForLFunctions.HTGeometry
