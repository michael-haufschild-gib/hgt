import Mathlib

/-!
# Strict inversion/Cartier base change, zero defect, and the odd conormal survivor

On `R = k[q, q⁻¹]` let `σ` be the strict inversion `q ↦ q⁻¹` and `ε` the Cartier specialization
`q ↦ 1`.

* `cartier_inversion` — `ε ∘ σ = ε`, so the two `R`-module structures on `S = k` used by the
  inversion/Cartier base change agree and the comparison has no defect;
* `inversion_sub_one` — the exact identity `σ(q − 1) = −q⁻¹(q − 1)`, hence `σ` preserves the ideal
  `I = (q − 1)` (`inversion_mem_span`);
* `inversion_conormal_odd` — `σ(q − 1) + (q − 1) ∈ I²`, i.e. `σ(e) = −e` on the conormal line;
* `positiveDisplacement_eq` and `inversion_positiveDisplacement` — the inversion-invariant positive
  displacement `q + q⁻¹ − 2` equals `(q − 1)² q⁻¹`, so the odd sign disappears after squaring;
* `radialGain_isSquare` — every multiplicative radial gain `p^{2a}` is already a positive square, so
  square-root fillability cannot select the critical radial origin.
-/

namespace GaloisForLFunctions.HTGeometry

open LaurentPolynomial

section StrictSquare

variable (k : Type*) [CommRing k]

/-- Strict inversion `q ↦ q⁻¹` on `k[q, q⁻¹]`. -/
noncomputable def inversion : LaurentPolynomial k →+* LaurentPolynomial k :=
  (LaurentPolynomial.invert (R := k)).toRingEquiv.toRingHom

/-- Cartier specialization `q ↦ 1`. -/
noncomputable def cartier : LaurentPolynomial k →+* k :=
  LaurentPolynomial.eval₂ (RingHom.id k) 1

variable {k}

@[simp] theorem inversion_T (n : ℤ) : inversion k (T n) = T (-n) := by
  simp [inversion]

@[simp] theorem inversion_C (a : k) : inversion k (C a) = C a := by
  simp [inversion]

@[simp] theorem cartier_T (n : ℤ) : cartier k (T n) = 1 := by
  rcases n with m | m
  · simp [cartier]
  · simp [cartier, Int.negSucc_eq]

@[simp] theorem cartier_C (a : k) : cartier k (C a) = a := by
  simp [cartier, LaurentPolynomial.eval₂_C]

/-- **Strict base change has no defect.**  Cartier specialization does not see the inversion. -/
theorem cartier_inversion (p : LaurentPolynomial k) : cartier k (inversion k p) = cartier k p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | C_mul_T n a => rw [map_mul, map_mul, map_mul, inversion_C, inversion_T, cartier_T, cartier_T]

/-- **The exact inversion identity on the ideal generator.** -/
theorem inversion_sub_one : inversion k (T 1 - 1) = -(T (-1)) * (T 1 - 1) := by
  have hT : (T (-1) : LaurentPolynomial k) * T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]
    simp
  rw [map_sub, inversion_T, map_one]
  linear_combination hT

/-- The ideal `I = (q − 1)`. -/
noncomputable def cartierIdeal : Ideal (LaurentPolynomial k) :=
  Ideal.span {(T 1 - 1 : LaurentPolynomial k)}

theorem generator_mem : (T 1 - 1 : LaurentPolynomial k) ∈ cartierIdeal (k := k) :=
  Ideal.subset_span rfl

/-- **The ideal is inversion stable.** -/
theorem inversion_mem_span : inversion k (T 1 - 1) ∈ cartierIdeal (k := k) := by
  rw [inversion_sub_one]
  exact Ideal.mul_mem_left _ _ generator_mem

/-- **The conormal class is odd.**  `σ(e) + e` lies in `I²`, so `σ(e) = −e` on `I/I²`. -/
theorem inversion_conormal_odd :
    inversion k (T 1 - 1) + (T 1 - 1) ∈ cartierIdeal (k := k) ^ 2 := by
  have hkey : inversion k (T 1 - 1) + (T 1 - 1)
      = (T (-1) : LaurentPolynomial k) * ((T 1 - 1) * (T 1 - 1)) := by
    have hT : (T (-1) : LaurentPolynomial k) * T 1 = 1 := by
      rw [← LaurentPolynomial.T_add]; simp
    rw [inversion_sub_one]
    linear_combination (1 - (T 1 : LaurentPolynomial k)) * hT
  rw [hkey, sq]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul generator_mem generator_mem)

/-- The inversion-invariant positive displacement `q + q⁻¹ − 2`. -/
noncomputable def positiveDisplacement : LaurentPolynomial k := T 1 + T (-1) - 2

/-- **The positive displacement is the squared conormal generator, up to a unit.** -/
theorem positiveDisplacement_eq :
    positiveDisplacement (k := k) = (T 1 - 1) * (T 1 - 1) * T (-1) := by
  have hT : (T 1 : LaurentPolynomial k) * T (-1) = 1 := by
    rw [← LaurentPolynomial.T_add]; simp
  rw [positiveDisplacement]
  linear_combination (2 - (T 1 : LaurentPolynomial k)) * hT

/-- **Inversion fixes the positive displacement.** -/
theorem inversion_positiveDisplacement :
    inversion k (positiveDisplacement (k := k)) = positiveDisplacement := by
  rw [positiveDisplacement, map_sub, map_add, inversion_T, inversion_T, map_ofNat]
  norm_num [positiveDisplacement]
  ring

end StrictSquare

section NoSelection

/-- **Every multiplicative radial gain is already a positive square.**  Square-root fillability of
the mate gain therefore declares every radius trivial, and cannot select the critical origin. -/
theorem radialGain_isSquare (p : ℕ) (hp : 0 < p) (a : ℝ) :
    ∃ r : ℝ, 0 < r ∧ r ^ 2 = (p : ℝ) ^ (2 * a) := by
  refine ⟨(p : ℝ) ^ a, Real.rpow_pos_of_pos (by exact_mod_cast hp) _, ?_⟩
  rw [← Real.rpow_natCast ((p : ℝ) ^ a) 2, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

theorem radialGain_isSquare_forall (p : ℕ) (hp : 0 < p) :
    ∀ a : ℝ, ∃ r : ℝ, 0 < r ∧ r ^ 2 = (p : ℝ) ^ (2 * a) :=
  fun a => radialGain_isSquare p hp a

end NoSelection

end GaloisForLFunctions.HTGeometry
