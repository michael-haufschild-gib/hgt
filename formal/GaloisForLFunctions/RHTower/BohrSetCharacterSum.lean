import GaloisForLFunctions.RHTower.CharacterSumMeanValue

/-!
# Parseval for a subset of the unit group

`sum_normSq_setCharSum` evaluates the family second moment
`∑_{χ mod q} ‖∑_{b ∈ B} χ(b)‖²` of the character sums of a set `B ⊆ (ZMod q)ˣ` as `φ(q)·#B`.

This is the input needed to bound the multiplicative Bohr set factor in the dense model theorem of
Matomäki--Teräväinen, where `‖E_{b ∈ B} χ(b)‖²` is exactly the multiplier attached to each Fourier
coefficient by `bohr_convolution_identity`.
-/

open Finset

noncomputable section

namespace RHTower

/-- **Parseval for a subset of the unit group.**  The family second moment of the character sums
of an indicator equals `φ(q) · #B`. -/
theorem sum_normSq_setCharSum (n : ℕ) (B : Finset (ZMod (n + 1))ˣ) :
    ∑ χ : DirichletCharacter ℂ (n + 1), ‖∑ b ∈ B, χ (b : ZMod (n + 1))‖ ^ 2
      = ((n + 1).totient : ℝ) * (B.card : ℝ) := by
  classical
  set F : (ZMod (n + 1))ˣ → ℂ := fun u => if u ∈ B then 1 else 0 with hFdef
  have hbil := dirichletCharacterFamily_bilinear n F F
  have hleft : ∀ χ : DirichletCharacter ℂ (n + 1),
      (∑ u, F u * χ (u : ZMod (n + 1))) = ∑ b ∈ B, χ (b : ZMod (n + 1)) := by
    intro χ
    rw [hFdef]
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    congr 1
    simp
  have hright : ∀ χ : DirichletCharacter ℂ (n + 1),
      (∑ v, F v * χ ((v : ZMod (n + 1))⁻¹))
        = (starRingEnd ℂ) (∑ b ∈ B, χ (b : ZMod (n + 1))) := by
    intro χ
    rw [map_sum, hFdef]
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    rw [show (Finset.univ.filter (fun v : (ZMod (n + 1))ˣ => v ∈ B)) = B by
      simp]
    exact Finset.sum_congr rfl (fun b _ => (conj_char n χ b).symm)
  have hdiag : (∑ u, F u * F u) = (B.card : ℂ) := by
    rw [hFdef]
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    rw [show (Finset.univ.filter (fun v : (ZMod (n + 1))ˣ => v ∈ B)) = B by
      simp]
    simp
  simp only [hleft, hright, hdiag] at hbil
  have hcast : ((∑ χ : DirichletCharacter ℂ (n + 1),
      ‖∑ b ∈ B, χ (b : ZMod (n + 1))‖ ^ 2 : ℝ) : ℂ)
      = (((n + 1).totient : ℝ) * (B.card : ℝ) : ℝ) := by
    push_cast
    rw [← hbil]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [Complex.mul_conj']
  exact_mod_cast hcast

end RHTower
