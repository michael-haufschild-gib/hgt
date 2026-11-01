import GaloisForLFunctions.HeckeKreinToeplitz.Index.BoundedKreinLanger
import GaloisForLFunctions.HeckeKreinToeplitz.LogarithmicCharactersAndTheArithmeticIndexFormula
import GaloisForLFunctions.RHTower.ChiRamanujanPositiveRationalTrace
import GaloisForLFunctions.AdelicKreinGeometry.TheIndexOfAnInducedState

/-!
# Bounded converse Krein–Langer theorem on positive rationals

Prime valuations identify the full Hecke lattice with the countable free prime
lattice. Pullback preserves negative index, so the bounded spectral
classification descends with exactly the same number of distinct unitary atoms.
-/

namespace GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

open RHTower.BAGTrace

/-- Prime valuations identify the complete free prime lattice with the
multiplicative Hecke lattice. -/
def heckePrimeLatticeEquiv : Multiplicative (Nat.Primes →₀ ℤ) ≃* HeckeLattice where
  toFun v := positiveRationalEquiv v.toAdd
  invFun q := Multiplicative.ofAdd (positiveRationalEquiv.symm q)
  left_inv v := congrArg Multiplicative.ofAdd (positiveRationalEquiv.left_inv v.toAdd)
  right_inv q := positiveRationalEquiv.right_inv q
  map_mul' v w := Subtype.ext (rationalOfValuations_add v.toAdd w.toAdd)

/-- The bounded converse Krein–Langer theorem on the full positive rational
group: exactly the index many distinct positive unitary atoms suffice. -/
theorem bounded_hecke_krein_langer {k : HeckeLattice → ℂ}
    (hk : IsHermKernel k) {m : ℕ} (hm : negIndex k = m)
    (hbounded : ∃ M : ℝ, ∀ g, ‖k g‖ ≤ M) :
    ∃ (p : HeckeLattice → ℂ) (χ : Fin m → HeckeLattice →* ℂ) (a : Fin m → ℝ),
      IsPosDefKernel p ∧ Function.Injective χ ∧ (∀ j, IsUnitaryChar (χ j)) ∧
      (∀ j, 0 < a j) ∧ ∀ g, k g = p g - ∑ j, (a j : ℂ) * χ j g := by
  let e := heckePrimeLatticeEquiv
  have hherm : IsHermKernel (k ∘ e) := by
    intro g
    change k (e g⁻¹) = star (k (e g))
    rw [map_inv]
    exact hk (e g)
  have hindex : negIndex (k ∘ e) = m :=
    (AdelicKreinGeometry.negIndex_comp_of_surjective k e.toMonoidHom e.surjective).trans hm
  have hbound : ∃ M : ℝ, ∀ g, ‖(k ∘ e) g‖ ≤ M := by
    obtain ⟨M, hM⟩ := hbounded
    exact ⟨M, fun g => hM (e g)⟩
  obtain ⟨p, χ, a, hp, hinj, hunit, ha, hrep⟩ :=
    bounded_free_lattice_krein_langer hherm hindex hbound
  refine ⟨p ∘ e.symm, fun j => (χ j).comp e.symm.toMonoidHom, a, ?_, ?_, ?_, ha, ?_⟩
  · refine ⟨?_, fun n x c => ?_⟩
    · intro g
      change p (e.symm g⁻¹) = star (p (e.symm g))
      rw [map_inv]
      exact hp.1 (e.symm g)
    · have hg : gram (p ∘ e.symm) x = gram p (fun j => e.symm (x j)) := by
        ext i j
        simp only [gram, Function.comp_apply, map_mul, map_inv]
      rw [hg]
      exact hp.2 n _ c
  · intro i j hij
    apply hinj
    apply MonoidHom.ext
    intro g
    have h := congrArg (fun f : HeckeLattice →* ℂ => f (e g)) hij
    change χ i (e.symm (e g)) = χ j (e.symm (e g)) at h
    simpa only [MulEquiv.symm_apply_apply] using h
  · intro j g
    exact hunit j (e.symm g)
  · intro g
    change k g = p (e.symm g) - ∑ j, (a j : ℂ) * χ j (e.symm g)
    simpa only [Function.comp_apply, MulEquiv.apply_symm_apply] using hrep (e.symm g)

end

#print axioms heckePrimeLatticeEquiv
#print axioms bounded_hecke_krein_langer

end GaloisForLFunctions.HeckeKreinToeplitz
