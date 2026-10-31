import GaloisForLFunctions.BiarithmeticGeometry.Affine.FactorialTranslations

/-!
# Finite rational grids outside a proper subgroup

Divide one rational outside a subgroup by a common factorial. Every prescribed
nonzero rational multiple remains outside, since an integer multiple recovers
the original rational. This separates finite grids after any finite set of slopes.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- A finite family of nonzero rational multiples simultaneously avoids a proper subgroup. -/
theorem exists_scale_finite_multiples_not_mem {ι : Type*} [Fintype ι]
    (H : AddSubgroup ℚ) (hH : H ≠ ⊤) (c : ι → ℚ) :
    ∃ q : ℚ, q ≠ 0 ∧ ∀ i, c i ≠ 0 → c i * q ∉ H := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : ℚ, r ∉ H := by
    by_contra! h
    apply hH
    ext r
    exact ⟨fun _ => trivial, fun _ => h r⟩
  have hr0 : r ≠ 0 := by
    intro he
    exact hr (he.symm ▸ H.zero_mem)
  let N := ∑ i, ((c i)⁻¹).den
  refine ⟨r * factorialTranslationStep N,
    mul_ne_zero hr0 (factorialTranslationStep_pos N).ne', ?_⟩
  intro i hi hmem
  have hd : ((c i)⁻¹).den ≤ N :=
    Finset.single_le_sum (f := fun j => ((c j)⁻¹).den)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  obtain ⟨m, hm⟩ := eq_int_mul_factorialTranslationStep (c i)⁻¹ hd
  have he : (m : ℚ) * (c i * (r * factorialTranslationStep N)) = r := by
    calc
      _ = r * (c i * ((m : ℚ) * factorialTranslationStep N)) := by ring
      _ = r * (c i * (c i)⁻¹) := by rw [← hm]
      _ = r := by rw [mul_inv_cancel₀ hi, mul_one]
  apply hr
  rw [← he]
  simpa only [zsmul_eq_mul] using H.zsmul_mem hmem m

/-- Every finite injective rational grid can be separated modulo a proper subgroup at all slopes. -/
theorem exists_scale_grid_differences_not_mem {ι J : Type*} [Fintype ι] [Fintype J]
    (H : AddSubgroup ℚ) (hH : H ≠ ⊤) (a : ι → ℚ) (ha : ∀ i, a i ≠ 0)
    (x : J → ℚ) (hx : Function.Injective x) :
    ∃ q : ℚ, q ≠ 0 ∧ ∀ i j l, j ≠ l → (q * x l - q * x j) / a i ∉ H := by
  obtain ⟨q, hq, hc⟩ := exists_scale_finite_multiples_not_mem H hH
    (fun z : ι × (J × J) => (x z.2.2 - x z.2.1) / a z.1)
  refine ⟨q, hq, ?_⟩
  intro i j l hjl
  have he : (x l - x j) / a i ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (fun h => hjl (hx h).symm)) (ha i)
  have heq : (q * x l - q * x j) / a i = ((x l - x j) / a i) * q := by ring
  rw [heq]
  exact hc (i, j, l) he

#print axioms exists_scale_finite_multiples_not_mem
#print axioms exists_scale_grid_differences_not_mem
end GaloisForLFunctions.BiarithmeticGeometry
