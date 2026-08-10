import GaloisForLFunctions.RHTower.BeurlingSystemDecomposition

/-!
# The local-prefix nonrobustness law

A certificate class for the Möbius decay of a Beurling system is *sound* when membership forces
`Φ_P(x) = O(x^{-1/2-ε})` for every positive `ε`, and it is a *finite-prefix neighbourhood* of a
system when agreeing with that system below one finite cutoff already implies membership.  If some
system agreeing below every prescribed cutoff violates every `O(x^{-a})` with `a > 1/2`, then no
sound class can be a finite-prefix neighbourhood: soundness and openness in the prefix topology are
incompatible.  This is `(BF22)`, and the quantifier structure is the whole content.
-/

open scoped BigOperators

namespace RHTower

namespace BeurlingSystem

/-- Agreement of two systems below a cutoff: their prime labels of norm at most `R` correspond
bijectively with equal norms. -/
def AgreesBelow (B₀ B : BeurlingSystem) (R : ℝ) : Prop :=
  ∃ e : {p : B₀.Label // B₀.labelNorm p ≤ R} ≃ {p : B.Label // B.labelNorm p ≤ R},
    ∀ p, B.labelNorm ((e p : {p : B.Label // B.labelNorm p ≤ R}) : B.Label)
      = B₀.labelNorm (p : B₀.Label)

/-- The decay statement `(BF13)` at exponent `a`. -/
def HasMoebiusDecay (B : BeurlingSystem) (a : ℝ) : Prop :=
  ∃ K x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, 0 < x → x ≤ x₀ → |B.phi x| ≤ K * x ^ (-a)

/-- Soundness of a certificate class `(BF22)`: membership forces the strict-half decay at every
exponent above one half. -/
def IsSoundCertificate (𝒞 : Set BeurlingSystem) : Prop :=
  ∀ B ∈ 𝒞, ∀ ε : ℝ, 0 < ε → B.HasMoebiusDecay (1 / 2 + ε)

/-- A certificate class is a finite-prefix neighbourhood of a system when agreement below one
finite cutoff already forces membership. -/
def IsPrefixNeighborhood (𝒞 : Set BeurlingSystem) (B₀ : BeurlingSystem) : Prop :=
  ∃ R : ℝ, ∀ B : BeurlingSystem, AgreesBelow B₀ B R → B ∈ 𝒞

/-- **The local-prefix nonrobustness law `(BF22)`.**  If below every prescribed cutoff there is an
agreeing system whose Möbius sum violates some strict-half decay exponent, then no sound
certificate class is a finite-prefix neighbourhood of the reference system. -/
theorem not_isPrefixNeighborhood_of_isSoundCertificate {B₀ : BeurlingSystem}
    {𝒞 : Set BeurlingSystem} (hsound : IsSoundCertificate 𝒞)
    (hcounter : ∀ R : ℝ, ∃ B : BeurlingSystem, AgreesBelow B₀ B R ∧
      ∃ a : ℝ, 1 / 2 < a ∧ ¬ B.HasMoebiusDecay a) :
    ¬ IsPrefixNeighborhood 𝒞 B₀ := by
  rintro ⟨R, hR⟩
  obtain ⟨B, hagree, a, ha, hfail⟩ := hcounter R
  exact hfail (by
    have hmem : B ∈ 𝒞 := hR B hagree
    have hε : 0 < a - 1 / 2 := by linarith
    have := hsound B hmem (a - 1 / 2) hε
    have harg : (1 : ℝ) / 2 + (a - 1 / 2) = a := by ring
    rwa [harg] at this)

/-- **Contrapositive form.**  A sound certificate class that does contain a finite-prefix
neighbourhood of the reference system forces every agreeing system to satisfy every strict-half
decay exponent. -/
theorem hasMoebiusDecay_of_isPrefixNeighborhood {B₀ : BeurlingSystem} {𝒞 : Set BeurlingSystem}
    (hsound : IsSoundCertificate 𝒞) {R : ℝ}
    (hR : ∀ B : BeurlingSystem, AgreesBelow B₀ B R → B ∈ 𝒞) {B : BeurlingSystem}
    (hagree : AgreesBelow B₀ B R) {a : ℝ} (ha : 1 / 2 < a) : B.HasMoebiusDecay a := by
  have hε : 0 < a - 1 / 2 := by linarith
  have hdecay := hsound B (hR B hagree) (a - 1 / 2) hε
  have harg : (1 : ℝ) / 2 + (a - 1 / 2) = a := by ring
  rwa [harg] at hdecay


end BeurlingSystem

end RHTower
