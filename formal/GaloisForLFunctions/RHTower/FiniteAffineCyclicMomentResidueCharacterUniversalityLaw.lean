import GaloisForLFunctions.HTGeometry.MeromorphicEquivariantResidueCharacterUniversalityLaw
import GaloisForLFunctions.RHTower.EquivariantAnalyticOrderCyclicSpectrumUniversalityLaw

/-!
# Finite affine cyclic moment-residue-character universality

The sharp centered-moment criterion for a finite cyclic spectrum determines more than its symmetry
and central multiplicity congruence.  The same central multiplicity is the signed meromorphic order
of the centered characteristic product, its logarithmic-derivative residue, and the exponent that
realizes the product's cyclic character.
-/

open scoped BigOperators
open Complex Filter Topology Finset

namespace GaloisForLFunctions

noncomputable section

/-- **Finite affine cyclic moment-residue-character universality law.** Vanishing of the first
sharp block of nontrivial-character centered moments is equivalent to cyclic multiset symmetry,
characteristic-product covariance, the center-multiplicity congruence, the signed-order character
identity, and logarithmic-residue recovery of that same central multiplicity. -/
theorem finiteAffineCyclicMomentResidueCharacterUniversality
    {n d : ℕ} (f : Fin n → ℂ) (c : ℂ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (hd : d ≠ 0) :
    (∀ k, k ≤ n → ¬ d ∣ k → ∑ i, (f i - c) ^ k = 0) ↔
      (Finset.univ.val.map f).map (fun z => c + ζ * (z - c)) =
          Finset.univ.val.map f ∧
        (∀ z, finiteCenteredSpectralProduct f c (ζ * z) =
          ζ ^ n * finiteCenteredSpectralProduct f c z) ∧
        Nat.ModEq d (Finset.univ.filter fun i => f i = c).card n ∧
        ζ ^ ((Finset.univ.filter fun i => f i = c).card : ℤ) = ζ ^ n ∧
        Tendsto
          (fun z => z * logDeriv (finiteCenteredSpectralProduct f c) z)
          (𝓝[≠] 0)
          (𝓝 (((Finset.univ.filter fun i => f i = c).card : ℕ) : ℂ)) := by
  rw [finiteAffineCyclicMomentCharacterOrderUniversalityLaw f c hζ hd]
  constructor
  · rintro ⟨hfixed, hcov, hmod⟩
    have han : AnalyticAt ℂ (finiteCenteredSpectralProduct f c) 0 := by
      unfold finiteCenteredSpectralProduct
      fun_prop
    have horder :
        meromorphicOrderAt (finiteCenteredSpectralProduct f c) 0 =
          ((Finset.univ.filter fun i => f i = c).card : ℤ) := by
      rw [han.meromorphicOrderAt_eq,
        finiteCenteredSpectralProduct_analyticOrderAt_zero]
      simp
    have hres :=
      HTGeometry.meromorphicEquivariant_residueCharacterLaw
        (f := finiteCenteredSpectralProduct f c)
        (τ := fun z : ℂ => ζ * z) (c := 0) (χ := ζ ^ n)
        han.meromorphicAt
        (analyticAt_const.mul analyticAt_id)
        (by simp)
        (by rw [deriv_const_mul_id]; exact hζ.ne_zero hd)
        (by filter_upwards with z using hcov z)
        horder
    rw [deriv_const_mul_id] at hres
    exact ⟨hfixed, hcov, hmod, hres.1, by simpa using hres.2⟩
  · rintro ⟨hfixed, hcov, hmod, _, _⟩
    exact ⟨hfixed, hcov, hmod⟩

end

end GaloisForLFunctions
