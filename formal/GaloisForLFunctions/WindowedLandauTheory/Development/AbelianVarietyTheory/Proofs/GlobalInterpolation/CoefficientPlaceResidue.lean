import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefficientComplexPlaces
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResidualInertiaPolynomial

/-! The common coefficient place reduces lifted inertia polynomials for any
p-adic integral model, including at places with no chosen local row. -/

noncomputable section

open IsLocalRing Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.N
open WindowedLandauTheory.CyclotomicNorms
open GlobalTheory.TeichPlace

namespace WindowedLandauTheory.NormalizedTypes.CoefficientComplexPlace

variable {D : D7} {w : D.what₂.places.Pl} (P : CoefficientComplexPlace D w)

local notation "ℓ" => D.what₂.places.resChar w
local notation "Zbar" => (@padicAlgClIntegers ℓ (Fact.mk (D.what₂.places.resChar_prime w)))
local notation "FbarAt" => Fb ℓ (D.what₂.places.resChar_prime w)

def integersEquiv : Zbar ≃+* P.ring := (valuationComapEquiv Zbar P.ι.symm).symm

/-- The residue map induced by the common complex place, read on p-adic
integral coefficients. -/
def residueHom : Zbar →+* FbarAt :=
  (P.κ.toRingHom.comp (residue P.ring)).comp P.integersEquiv.toRingHom

def reduce {g : ℕ} [Fact g.Prime] (t : Fbar g →* ℂ) : Fbar g →* FbarAt :=
  @reduceLift ℓ ⟨D.what₂.places.resChar_prime w⟩ ℂ _ P.ring P.κ g _ t

theorem reduce_inj_of_coprime {g : ℕ} [Fact g.Prime] (t : Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    {x y : Fbar g} (hx : x ≠ 0) (hy : y ≠ 0)
    (hpx : (orderOf x).Coprime ℓ) (hpy : (orderOf y).Coprime ℓ)
    (h : P.reduce t x = P.reduce t y) : x = y := by
  letI : Fact (ℓ).Prime := ⟨D.what₂.places.resChar_prime w⟩
  exact reduceLift_inj_of_coprime P.ring P.κ t ht hx hy hpx hpy h

/-- Calculate the reduction at the common coefficient place from a split
complex polynomial, keeping the full multiset of roots. -/
theorem map_residue_eq_of_lifted_split {g : ℕ} [Fact g.Prime] (t : Fbar g →* ℂ)
    (Q : Zbar[X]) (S : Multiset (Fbar g)) (hS : ∀ x ∈ S, x ≠ 0)
    (hQ : Q.map (P.ι.toRingHom.comp (Zbar).subtype) = (S.map fun x => X - C (t x)).prod) :
    Q.map P.residueHom = (S.map fun x => X - C (P.reduce t (primeToPart ℓ x))).prod := by
  letI : Fact (ℓ).Prime := ⟨D.what₂.places.resChar_prime w⟩
  exact map_eq_prod_reduceLift P.ring P.κ t P.integersEquiv.toRingHom Q S hS hQ

/-- A complex unipotent characteristic polynomial remains unipotent after
reducing an integral polynomial that realizes it. -/
theorem map_residue_eq_unipotent (Q : Zbar[X]) (n : ℕ)
    (hQ : Q.map (P.ι.toRingHom.comp (Zbar).subtype) = (X - 1) ^ n) :
    Q.map P.residueHom = (X - 1) ^ n := by
  have hj : Function.Injective (P.ι.toRingHom.comp (Zbar).subtype) :=
    P.ι.injective.comp Subtype.val_injective
  have hQ' : Q = (X - 1) ^ n := by
    apply Polynomial.map_injective _ hj
    rw [hQ, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  rw [hQ', Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]

end WindowedLandauTheory.NormalizedTypes.CoefficientComplexPlace
