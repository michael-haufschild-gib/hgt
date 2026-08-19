import GaloisForLFunctions.HTGeometry.GammaMonomialPairIndependence

/-!
# Clearing the denominators of a shift factor

The shift factor of a Gamma monomial, `ρ_e(s) = ∏_k (s+λ_k)^{e_k}`, is rational rather than
polynomial when some exponent is negative.  Multiplying by `∏_k (s+λ_k)^m` for a single `m` large
enough for the whole finite family makes every factor a polynomial at once, which is what keeps the
shift-and-subtract induction inside the polynomial coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The cleared shift factor `∏_k (X + λ_k)^{m + e_k}`. -/
def clearedShiftFactor {r : ℕ} (lam : Fin r → ℂ) (e : Fin r → ℤ) (m : ℕ) : Polynomial ℂ :=
  ∏ k, (Polynomial.X + Polynomial.C (lam k)) ^ (((m : ℤ) + e k).toNat)

theorem eval_clearedShiftFactor {r : ℕ} (lam : Fin r → ℂ) (e : Fin r → ℤ) (m : ℕ) {s : ℂ}
    (hs : ∀ k, s + lam k ≠ 0) (hm : ∀ k, 0 ≤ (m : ℤ) + e k) :
    Polynomial.eval s (clearedShiftFactor lam e m)
      = (∏ k, (s + lam k) ^ ((m : ℤ))) * (∏ k, (s + lam k) ^ (e k)) := by
  rw [clearedShiftFactor, Polynomial.eval_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [← zpow_natCast, Int.toNat_of_nonneg (hm k), zpow_add₀ (hs k)]

theorem clearedShiftFactor_ne_zero {r : ℕ} (lam : Fin r → ℂ) (e : Fin r → ℤ) (m : ℕ) :
    clearedShiftFactor lam e m ≠ 0 := by
  rw [clearedShiftFactor]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_
  intro hcon
  have hdeg : (Polynomial.X + Polynomial.C (lam k)).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_add_C (lam k)
  rw [hcon] at hdeg
  simp at hdeg

/-- The common clearing power for a finite family of exponent vectors. -/
theorem exists_clearing_power {r : ℕ} {ι : Type*} (T : Finset ι) (e : ι → Fin r → ℤ) :
    ∃ m : ℕ, ∀ α ∈ T, ∀ k, 0 ≤ (m : ℤ) + e α k := by
  classical
  set M : ℕ := (T.biUnion fun α => (Finset.univ : Finset (Fin r)).image
    fun k => (e α k).natAbs).sup id with hM
  refine ⟨M, fun α hα k => ?_⟩
  have hmem : (e α k).natAbs ∈ T.biUnion fun α => (Finset.univ : Finset (Fin r)).image
      fun k => (e α k).natAbs :=
    Finset.mem_biUnion.mpr ⟨α, hα, Finset.mem_image_of_mem _ (Finset.mem_univ k)⟩
  have hle : (e α k).natAbs ≤ M := Finset.le_sup (f := id) hmem
  have hcast : ((e α k).natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast hle
  have habs : -(e α k) ≤ ((e α k).natAbs : ℤ) := by
    rcases Int.natAbs_eq (e α k) with h | h <;> omega
  omega

end

end GaloisForLFunctions.HTGeometry
