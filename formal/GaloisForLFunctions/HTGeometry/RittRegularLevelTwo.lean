import GaloisForLFunctions.HTGeometry.RittRegularPredicate
import GaloisForLFunctions.HTGeometry.RittGeneralInhomogeneity

/-!
# The level-two classification with a regularity predicate

The affine alternative of the level-two classification carries the provenance of its inhomogeneity:
`h` is a coefficient of the input inhomogeneity divided by the monomial `(q/ρ)^j·q^k`.  So any
predicate on the base closed under sums, products and integer powers of the two multipliers passes
from the input coefficients to `h`, and the alternative becomes refutable — a regular inhomogeneity
is exactly what the pole count of an affine transport equation consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

omit [CharZero K] [CharZero L] in
/-- **Jet order two with a nonzero inhomogeneity, with the regularity of the inhomogeneity
carried through.** -/
theorem level_two_regular_inhom (Fr : RittFrame K L) {τ : L} {q : K}
    {P : K → Prop} (hP : RittRegular Fr q P)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 2)
    {c : K} (hc : c ≠ 0) {i₀ k₀ : ℤ} (hcik : c = q ^ i₀ * Fr.ρ ^ k₀)
    {G : ℕ → K[X]} {n : ℕ} (hG : ∃ j, j < n ∧ G j ≠ 0)
    (hGP : ∀ j k : ℕ, P ((G j).coeff k))
    (hrel : Fr.σ V = algebraMap K L c * V
      + ∑ j ∈ Finset.range n, aeval τ (G j) * (Fr.d τ) ^ j) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ P h ∧
      Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) := by
  rcases level_two_nonzero_inhom Fr hqconst hshift hq htr0 htr1 hV0 hV hc hcik hG hrel with
      hritt | ⟨u, h, I, J, j, k, hu0, hh0, hprov, hbase⟩
  · exact Or.inl hritt
  · exact Or.inr ⟨u, h, I, J, hu0, hh0, hprov ▸ hP.div_pass hq (hGP j k) j k, hbase⟩

end GaloisForLFunctions.HTGeometry
