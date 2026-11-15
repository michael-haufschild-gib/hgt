import GaloisForLFunctions.MetaplecticMobiusDescent.ThePrimaryCubicGaussSumFixesTheSign
import GaloisForLFunctions.FamilyContinuationTheory.HarmonicGaussianPoissonGivesGrossencharacterContinuation

/-!
# The rungs are tensor powers of the cubic Gauss sums

The rung `L(w, ψ₆^k ψ)` of the cubic tower has at a prime `𝔭 ∤ 3` the coefficient `ψ₆(𝔭)^k ψ(𝔭)`
(`grossenPrimeTerm`). The normalized cubic Gauss sum `g̃_𝔭` of MMD has cube `−π_𝔭/|π_𝔭|`, `π_𝔭` the
primary generator (`normalizedCubicGauss_cube`), while `ψ₆(𝔭) = (π̄_𝔭/|π_𝔭|)^6`. Hence

  `ψ₆(𝔭) = \overline{g̃_𝔭}^{18}`  (`idealPsiSix_eq_conj_normalizedCubicGauss_pow`),

and the Euler factor of the rung of level `k` at `𝔭` is that of the tensor power `\overline{g̃_𝔭}^{18k}`
twisted by `ψ` (`grossenPrimeTerm_eq_conj_normalizedCubicGauss`). The Grössencharacter rung of E6 is
the tensor-power lever of E5 applied to the cubic Gauss sums: a seed for the rungs is a seed for the
powers of a rank-one Gauss sum of order three.
-/

noncomputable section

open NumberField Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein HeckeLFunctions
  FamilyContinuationTheory IsDedekindDomain

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- **The sextic Grössencharacter is the eighteenth power of the conjugate normalized cubic Gauss
sum**: `ψ₆(𝔭) = (π̄/|π|)^6 = \overline{(−π/|π|)}^6 = \overline{g̃_𝔭^3}^6`. -/
theorem idealPsiSix_eq_conj_normalizedCubicGauss_pow (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : idealPsiSix P = conj (normalizedCubicGauss P hgood) ^ 18 := by
  have h1 : idealPsiSix P = elemPsiSix (primaryGenerator P hgood) := by
    rw [← idealPsiSix_span_singleton, ← (primaryGenerator_spec P hgood).1]
  rw [h1, elemPsiSix_apply, complexUnitConj_apply, show (18 : ℕ) = 3 * 6 by norm_num, pow_mul,
    ← map_pow, normalizedCubicGauss_cube, map_div₀, map_neg, Complex.conj_ofReal, neg_div,
    neg_pow, show ((-1 : ℂ)) ^ 6 = 1 by norm_num, one_mul]

theorem idealPsiSix_pow_eq (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (k : ℕ) :
    idealPsiSix P ^ k = conj (normalizedCubicGauss P hgood) ^ (18 * k) := by
  rw [idealPsiSix_eq_conj_normalizedCubicGauss_pow P hgood, pow_mul]

/-- **The Euler factor of a rung away from `3`** is that of the tensor power
`\overline{g̃_𝔭}^{18k}` twisted by the primitive finite-order character `ψ`. -/
theorem grossenPrimeTerm_eq_conj_normalizedCubicGauss (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    (k : ℕ) (w : ℂ) (v : HeightOneSpectrum O) (hv : lambda ∉ v.asIdeal) :
    haveI := v.isMaximal
    grossenPrimeTerm 𝔪 ψ k w v = conj (normalizedCubicGauss v.asIdeal hv) ^ (18 * k) *
      primitiveIdealValue 𝔪 ψ v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-w) := by
  haveI := v.isMaximal
  rw [grossenPrimeTerm, idealPsiSix_pow_eq v.asIdeal hv]

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
