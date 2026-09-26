import GaloisForLFunctions.RHTower.QuadraticGaussSumSign
import GaloisForLFunctions.RHTower.HalfWeightTwistedCoefficients

/-!
# The root number of the Legendre symbol

For an odd prime `p`, the Legendre symbol `(·/p)` (`legendreC`) is a nontrivial, hence primitive,
real Dirichlet character. It is even exactly when `p ≡ 1 (mod 4)`, and by Gauss's evaluation
(`gaussQuad_of_mod_four_eq_one/three`, `gaussSum_legendre`) its Gauss sum is `√p` or `i√p`.

* **`rootNumber_legendre`**: the global root number `τ(χ)/(i^a √p)` equals `1`.
* **`completedLFunction_legendre_one_sub`**: `Λ(1 - s, (·/p)) = p^{s - 1/2} Λ(s, (·/p))`, the functional
  equation of the Legendre `L`-function with its sign determined.
-/

open Complex

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

section RootNumber

variable (p : ℕ) [hp : Fact p.Prime]

theorem legendreC_neg_one (hp2 : p ≠ 2) :
    legendreC p (-1) = ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℂ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  unfold legendreC
  rw [MulChar.ringHomComp_apply, quadraticChar_neg_one hchar, ZMod.card]
  rfl

omit hp in
theorem natCast_cpow_half : ((p : ℕ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt p : ℝ) : ℂ) := by
  rw [show ((p : ℕ) : ℂ) = (((p : ℝ)) : ℂ) by push_cast; rfl, sqrt_cpow_real (Nat.cast_nonneg p)]

/-- **The root number of the Legendre symbol is `1`**: for an odd prime `p`,
`τ((·/p)) = i^a √p` with `a = 0` if `(·/p)` is even and `a = 1` if it is odd. -/
theorem rootNumber_legendre (hp2 : p ≠ 2) :
    DirichletCharacter.rootNumber (legendreC p : DirichletCharacter ℂ p) = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  have hsp : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp.out.pos)
  have hsC : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsp.ne'
  unfold DirichletCharacter.rootNumber
  rw [gaussSum_legendre p hp2, natCast_cpow_half]
  rcases Nat.lt_or_ge (p % 4) 2 with h | h
  · have h1 : p % 4 = 1 := by omega
    have hev : DirichletCharacter.Even (legendreC p : DirichletCharacter ℂ p) := by
      unfold DirichletCharacter.Even
      rw [legendreC_neg_one p hp2, ZMod.χ₄_nat_one_mod_four h1]; simp
    rw [if_pos hev, gaussQuad_of_mod_four_eq_one p h1, pow_zero, div_one, div_self hsC]
  · have h3 : p % 4 = 3 := by omega
    have hodd' : ¬ DirichletCharacter.Even (legendreC p : DirichletCharacter ℂ p) := by
      unfold DirichletCharacter.Even
      rw [legendreC_neg_one p hp2, ZMod.χ₄_nat_three_mod_four h3]
      norm_num
    rw [if_neg hodd', gaussQuad_of_mod_four_eq_three p h3, pow_one]
    field_simp

theorem legendreC_ne_one (hp2 : p ≠ 2) : legendreC p ≠ 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  intro h
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have h1 : legendreC p a = 1 := by
    rw [h, MulChar.one_apply]
    exact Ne.isUnit (fun h0 => ha (by rw [h0]; exact ⟨0, by simp⟩))
  unfold legendreC at h1
  rw [MulChar.ringHomComp_apply, quadraticChar_neg_one_iff_not_isSquare.2 ha] at h1
  norm_num at h1

theorem legendreC_inv : (legendreC p)⁻¹ = legendreC p := by
  ext a
  rw [MulChar.inv_apply_eq_inv']
  unfold legendreC
  rw [MulChar.ringHomComp_apply]
  rcases quadraticChar_dichotomy (F := ZMod p) a.ne_zero with h | h <;> simp [h]

/-- **Functional equation of the Legendre `L`-function**:
`Λ(1 - s, (·/p)) = p^{s - 1/2} Λ(s, (·/p))`, the root number being `1`. -/
theorem completedLFunction_legendre_one_sub (hp2 : p ≠ 2) (s : ℂ) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    DirichletCharacter.completedLFunction (legendreC p : DirichletCharacter ℂ p) (1 - s) =
      (p : ℂ) ^ (s - 1 / 2) * DirichletCharacter.completedLFunction (legendreC p : DirichletCharacter ℂ p) s := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hprim : DirichletCharacter.IsPrimitive (legendreC p : DirichletCharacter ℂ p) :=
    isPrimitive_of_ne_one _ (legendreC_ne_one p hp2)
  have h := hprim.completedLFunction_one_sub s
  rw [rootNumber_legendre p hp2, mul_one] at h
  rw [h]
  congr 2
  exact legendreC_inv p

end RootNumber

end

end GaloisForLFunctions.RHTower.HalfWeight
