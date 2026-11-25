import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedCechComplex

/-! A map defined on homogeneous numerators descends when multiplying numerator
and denominator by the same coordinate product preserves its value. -/

noncomputable section

open MvPolynomial

namespace GlobalTheory

variable {ι R M T : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  {D : ℤ → Submodule R M} [PolyGradedSMul ι D] [AddCommGroup T] [Module R T]
  {s : Finset ι} {n : ℤ}
  (f : ∀ k : ℕ, D (n + k * s.card) →ₗ[R] T)
  (hf : ∀ (k : ℕ) (a : D (n + k * s.card)) (b : D (n + (k + 1 : ℕ) * s.card)),
    (b : M) = xProd R s • (a : M) → f (k + 1) b = f k a)

include hf

omit [IsScalarTower R (MvPolynomial ι R) M] in
theorem homLocLift_pow (k j : ℕ) (a : D (n + k * s.card)) :
    f (k + j) ⟨_, xProd_pow_smul_mem D a.2 j⟩ = f k a := by
  induction j with
  | zero => exact congrArg (f k) (Subtype.ext (by simp))
  | succ j ih => exact (hf (k + j) _ _ (by simp [pow_succ', mul_smul])).trans ih

private theorem homLocLift_congr {k j : ℕ} {a : D (n + k * s.card)} {b : D (n + j * s.card)}
    (h : homLocMk D s n k a = homLocMk D s n j b) : f k a = f j b := by
  obtain ⟨l, hl⟩ := ModuleFraction.frac_eq_iff.1 (congrArg Subtype.val h)
  have equal_numerators (p q : ℕ) (hpq : p = q) (x : D (n + p * s.card)) (y : D (n + q * s.card))
      (he : (x : M) = y) : f p x = f q y := by
    subst q
    rw [Subtype.ext he]
  rw [← homLocLift_pow f hf k (l + j), ← homLocLift_pow f hf j (l + k)]
  exact equal_numerators _ _ (by omega) _ _ hl

def homLocLift : homLoc D s n →ₗ[R] T :=
  have evaluate (k : ℕ) (a : D (n + k * s.card)) :
      f _ (exists_homLocMk D (homLocMk D s n k a)).choose_spec.choose = f k a :=
    homLocLift_congr f hf (exists_homLocMk D (homLocMk D s n k a)).choose_spec.choose_spec
  { toFun z := f _ (exists_homLocMk D z).choose_spec.choose
    map_add' z w := by
      obtain ⟨a, ha⟩ := exists_frac_of_mem_homLoc D z.2
      obtain ⟨b, hb⟩ := exists_frac_of_mem_homLoc D w.2
      obtain ⟨x, hx, ex⟩ := ha (max a b) (le_max_left _ _)
      obtain ⟨y, hy, ey⟩ := hb (max a b) (le_max_right _ _)
      obtain rfl : homLocMk D s n _ ⟨x, hx⟩ = z := Subtype.ext ex
      obtain rfl : homLocMk D s n _ ⟨y, hy⟩ = w := Subtype.ext ey
      rw [← map_add, evaluate, evaluate, evaluate, map_add]
    map_smul' r z := by
      obtain ⟨k, a, rfl⟩ := exists_homLocMk D z
      rw [← map_smul, evaluate, evaluate, map_smul, RingHom.id_apply] }

@[simp]
theorem homLocLift_mk (k : ℕ) (a : D (n + k * s.card)) :
    homLocLift f hf (homLocMk D s n k a) = f k a :=
  homLocLift_congr f hf (exists_homLocMk D (homLocMk D s n k a)).choose_spec.choose_spec

theorem homLocLift_injective_iff : Function.Injective (homLocLift f hf) ↔
    ∀ k a, f k a = 0 → ∃ l : ℕ, xProd R s ^ l • (a : M) = 0 := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h k a ha
    exact ModuleFraction.frac_eq_zero_iff.1
      (congrArg Subtype.val (h _ ((homLocLift_mk f hf k a).trans ha)))
  · intro h z hz
    obtain ⟨k, a, rfl⟩ := exists_homLocMk D z
    exact Subtype.ext (ModuleFraction.frac_eq_zero_iff.2 (h k a ((homLocLift_mk f hf k a).symm.trans hz)))

theorem homLocLift_surjective_iff : Function.Surjective (homLocLift f hf) ↔
    ∀ y, ∃ k a, f k a = y := by
  refine forall_congr' fun y => ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨k, a, rfl⟩ := exists_homLocMk D z
    exact ⟨k, a, (homLocLift_mk f hf k a).symm⟩
  · rintro ⟨k, a, rfl⟩
    exact ⟨_, homLocLift_mk f hf k a⟩

end GlobalTheory
