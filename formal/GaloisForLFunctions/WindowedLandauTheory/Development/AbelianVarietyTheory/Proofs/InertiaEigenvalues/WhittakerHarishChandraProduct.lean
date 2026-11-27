import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerParabolicCrossing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerOpenCellWeights

/-! Whittaker traces multiply under Harish–Chandra induction.
Only the open double coset contributes. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

private theorem class_of_character {G : Type} [Group G] {χ : G → ℂ} (hχ : IsChar χ) :
    IsClass χ := by
  obtain ⟨V, hV⟩ := hχ
  intro x y
  exact (hV (y * x * y⁻¹)).symm.trans ((V.char_conj x y).trans (hV x))

/-- Harish–Chandra induction of the two block characters multiplies their Whittaker traces. -/
theorem wh_hc_mul (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    {α : Gn g a → ℂ} {β : Gn g b → ℂ} (hα : IsChar α) (hβ : IsChar β) :
    wh ψ (hc a b α β (a + b)) = wh ψ α * wh ψ β := by
  let U := upperUnitriangular g (a + b)
  let P := twoBlockParabolic g a b
  let θ := whittakerCharacter ψ (a + b)
  let F (u : U) : ℂ := θ u
  let π : P →* Gn g a × Gn g b := twoBlockLevi
  let G (p : P) : ℂ := α (π p).1 * β (π p).2
  let Q := DoubleCoset.Quotient (U : Set (Gn g (a + b))) P
  letI : Fintype Q := mixedDoubleCosetFintype U P
  let w : Gn g (a + b) := permutationUnit (openCellPermutation a b)
  let q₀ := DoubleCoset.mk U P w
  have hF (u v : U) : F (v * u * v⁻¹) = F u := by
    apply congrArg Units.val
    rw [map_mul, map_mul, map_inv, mul_comm (θ v) (θ u), mul_assoc, mul_inv_cancel, mul_one]
  have hG (u v : P) : G (v * u * v⁻¹) = G u := by
    change α (π (v * u * v⁻¹)).1 * β (π (v * u * v⁻¹)).2 = α (π u).1 * β (π u).2
    rw [map_mul, map_mul, map_inv]
    exact congrArg₂ (· * ·) (class_of_character hα (π u).1 (π v).1)
      (class_of_character hβ (π u).2 (π v).2)
  have hz (q : Q) (hq : q ≠ q₀) : doubleCosetPairing U P F G q.out = 0 := by
    obtain ⟨σ, hσ⟩ := exists_parabolic_permutation_rep (g := g) (a := a) (b := b) q.out
    have hne : firstBlockImage σ ≠ firstBlockImage (openCellPermutation a b) := by
      intro h
      apply hq
      exact ((DoubleCoset.out_eq' U P q).symm.trans hσ.symm).trans
        (parabolic_coset_eq_of_firstBlockImage_eq (g := g) σ (openCellPermutation a b) h).symm
    exact (doubleCosetPairing_eq_of_mk_eq U P F G hF hG hσ.symm).trans
      (whittaker_overlap_eq_zero_of_crossing ψ hψ σ hne α β)
  calc
    _ = ∑ q : Q, doubleCosetPairing U P F G q.out := wh_hc_eq_doubleCosets ψ hα hβ
    _ = doubleCosetPairing U P F G q₀.out :=
      Finset.sum_eq_single_of_mem q₀ (Finset.mem_univ q₀) (fun q _ h => hz q h)
    _ = doubleCosetPairing U P F G w :=
      doubleCosetPairing_eq_of_mk_eq U P F G hF hG (DoubleCoset.out_eq' U P q₀)
    _ = _ := whittaker_overlap_openCell ψ hα hβ

end GlobalTheory.GLq
