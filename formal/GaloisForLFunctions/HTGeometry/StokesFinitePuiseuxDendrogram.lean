import GaloisForLFunctions.HTGeometry.StokesCanonicalThresholdCuts

/-!
# Finite Puiseux coefficients generate the canonical Stokes dendrogram

This module takes finite coefficient vectors on one common ramified cover as the sole source data.
The highest exponent at which two vectors differ is proved symmetric, bounded, strictly positive
off the diagonal, and acute-isosceles.  Therefore the coefficient family canonically generates the
positive rooted cuts whose normalized contacts are exactly those highest-difference exponents.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

noncomputable section

/-- Distinct finite Puiseux coefficient vectors with common denominator `N` and exponent
numerators in `0, ..., K`.  All constant terms vanish. -/
structure FinitePuiseuxFamily (m K N : ℕ) where
  coeff : Fin m → Fin (K + 1) → ℂ
  coverDegree_pos : 0 < N
  constant_zero : ∀ i, coeff i 0 = 0
  coeff_injective : Function.Injective coeff

namespace FinitePuiseuxFamily

variable {m K N : ℕ}

/-- Highest exponent numerator at which two finite Puiseux vectors differ. -/
def contactNumerator (p : FinitePuiseuxFamily m K N) (i j : Fin m) : ℕ :=
  Finset.univ.sup fun e => if p.coeff i e = p.coeff j e then 0 else e.val

@[simp] theorem contactNumerator_self (p : FinitePuiseuxFamily m K N) (i : Fin m) :
    p.contactNumerator i i = 0 := by
  simp [contactNumerator]

/-- Highest-difference numerator is symmetric. -/
theorem contactNumerator_symm (p : FinitePuiseuxFamily m K N) (i j : Fin m) :
    p.contactNumerator i j = p.contactNumerator j i := by
  apply Finset.sup_congr rfl
  intro e _
  by_cases h : p.coeff i e = p.coeff j e
  · rw [if_pos h, if_pos h.symm]
  · have hs : p.coeff j e ≠ p.coeff i e := Ne.symm h
    rw [if_neg h, if_neg hs]

/-- Highest-difference numerator lies in the declared finite exponent window. -/
theorem contactNumerator_le (p : FinitePuiseuxFamily m K N) (i j : Fin m) :
    p.contactNumerator i j ≤ K := by
  apply Finset.sup_le
  intro e _
  by_cases h : p.coeff i e = p.coeff j e
  · simp [h]
  · simp only [h, if_false]
    omega

/-- Coefficient equality is transitive at every exponent, forcing the acute-isosceles law for
highest differences. -/
theorem contactNumerator_acute (p : FinitePuiseuxFamily m K N) :
    FiniteContactDendrogram.IsAcute p.contactNumerator := by
  intro i j k
  apply Finset.sup_le
  intro e he
  by_cases hij : p.coeff i e = p.coeff j e
  · simp [hij]
  · simp only [hij, if_false]
    have hor : p.coeff i e ≠ p.coeff k e ∨ p.coeff j e ≠ p.coeff k e := by
      by_contra h
      push Not at h
      exact hij (h.1.trans h.2.symm)
    rcases hor with hik | hjk
    · have hle := (Finset.le_sup (s := Finset.univ)
        (f := fun a => if p.coeff i a = p.coeff k a then 0 else a.val)
        (Finset.mem_univ e))
      simp only [hik, if_false] at hle
      exact (show e.val ≤ p.contactNumerator i k by
        simpa [contactNumerator] using hle).trans (le_max_left _ _)
    · have hle := (Finset.le_sup (s := Finset.univ)
        (f := fun a => if p.coeff j a = p.coeff k a then 0 else a.val)
        (Finset.mem_univ e))
      simp only [hjk, if_false] at hle
      exact (show e.val ≤ p.contactNumerator j k by
        simpa [contactNumerator] using hle).trans (le_max_right _ _)

/-- Distinct zero-constant coefficient vectors differ at a positive exponent. -/
theorem contactNumerator_pos_of_ne (p : FinitePuiseuxFamily m K N)
    {i j : Fin m} (hij : i ≠ j) : 0 < p.contactNumerator i j := by
  have hcoeff : p.coeff i ≠ p.coeff j := fun h => hij (p.coeff_injective h)
  obtain ⟨e, he⟩ : ∃ e, p.coeff i e ≠ p.coeff j e := by
    by_contra h
    push Not at h
    exact hcoeff (funext h)
  have he0 : e ≠ 0 := by
    intro hzero
    subst e
    exact he ((p.constant_zero i).trans (p.constant_zero j).symm)
  have hval : 0 < e.val := Fin.pos_iff_ne_zero.mpr he0
  have hle : e.val ≤ p.contactNumerator i j := by
    have hsup := Finset.le_sup (s := Finset.univ)
      (f := fun a => if p.coeff i a = p.coeff j a then 0 else a.val)
      (Finset.mem_univ e)
    simp only [he, if_false] at hsup
    simpa [contactNumerator] using hsup
  exact hval.trans_le hle

/-- Coefficient-derived integral contact dendrogram. -/
def toNatContactDendrogram (p : FinitePuiseuxFamily m K N) :
    NatContactDendrogram m K N where
  contactNumerator := p.contactNumerator
  coverDegree_pos := p.coverDegree_pos
  contact_self := p.contactNumerator_self
  contact_symm := p.contactNumerator_symm
  contact_acute := p.contactNumerator_acute
  contact_pos_of_ne := p.contactNumerator_pos_of_ne
  contact_le := p.contactNumerator_le

/-- Canonical positive rooted cuts generated from the finite coefficients. -/
noncomputable def canonicalCuts (p : FinitePuiseuxFamily m K N) :=
  p.toNatContactDendrogram.canonicalCuts

/-- **Coefficient-level rooted Stokes realization.** Explicit finite Puiseux coefficients alone
generate cuts whose contact is their normalized highest-difference order. -/
theorem canonicalCuts_contact_eq (p : FinitePuiseuxFamily m K N) (i j : Fin m) :
    p.canonicalCuts.contact i j = p.contactNumerator i j / (N : ℝ) :=
  p.toNatContactDendrogram.canonicalCuts_contact_eq i j

end FinitePuiseuxFamily
end
end IrregularStokes
end GaloisForLFunctions
