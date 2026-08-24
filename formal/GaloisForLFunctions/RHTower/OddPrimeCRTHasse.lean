import GaloisForLFunctions.RHTower.DirichletCharacterQuadraticCRT

/-!
# Hasse gluing for certified odd-prime CRT families

For a finite certified family of distinct odd primes, reduction modulo the square-free product is
equivalent to simultaneous reduction at every prime factor.  This gives both halves of a finite
Hasse principle: local coordinates separate global residues, and every arbitrary local family
glues to one unique global residue.

Unlike ABHN reciprocity, no compatibility sum is needed here.  Coprimality makes the local target a
literal product, so every local packet is globally realizable.
-/

noncomputable section

namespace RHTower.OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- A residue modulo the square-free product is determined by all prime-local residues. -/
theorem oddPrimeCrt_congr_hasse_iff
    (P : OddPrimeFamily I) (x y : ZMod P.modulus) :
    x = y ↔ ∀ i : I, P.crtEquiv x i = P.crtEquiv y i := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    apply P.crtEquiv.injective
    funext i
    exact h i

/-- A global residue is zero exactly when every prime-local residue is zero. -/
theorem oddPrimeCrt_eq_zero_hasse_iff
    (P : OddPrimeFamily I) (x : ZMod P.modulus) :
    x = 0 ↔ ∀ i : I, P.crtEquiv x i = 0 := by
  constructor
  · rintro rfl
    intro i
    simp
  · intro h
    exact (oddPrimeCrt_congr_hasse_iff P x 0).2 (by simpa using h)

/-- Distinct global residues are separated at one certified prime place. -/
theorem exists_oddPrimeCrtCoordinate_ne_of_ne
    (P : OddPrimeFamily I) {x y : ZMod P.modulus} (hxy : x ≠ y) :
    ∃ i : I, P.crtEquiv x i ≠ P.crtEquiv y i := by
  by_contra h
  push Not at h
  exact hxy ((oddPrimeCrt_congr_hasse_iff P x y).2 h)

/-- Every family of prime-local residues glues to one unique global residue. -/
theorem oddPrimeCrt_hasse_existsUnique
    (P : OddPrimeFamily I) (locals : (i : I) → ZMod (P.prime i).1) :
    ∃! x : ZMod P.modulus, ∀ i : I, P.crtEquiv x i = locals i := by
  refine ⟨P.crtEquiv.symm locals, ?_, ?_⟩
  · intro i
    exact congrFun (P.crtEquiv.apply_symm_apply locals) i
  · intro y hy
    apply P.crtEquiv.injective
    funext i
    calc
      P.crtEquiv y i = locals i := hy i
      _ = P.crtEquiv (P.crtEquiv.symm locals) i :=
        (congrFun (P.crtEquiv.apply_symm_apply locals) i).symm

end RHTower.OddPrimeFamily
