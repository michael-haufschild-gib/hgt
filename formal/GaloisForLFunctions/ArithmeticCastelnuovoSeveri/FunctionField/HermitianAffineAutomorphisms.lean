import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTraceFieldEmbedding
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldGenerators
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerNormFibers
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.SquareFieldTraceFibers

/-!
# Affine automorphisms of Hermitian radical fields

For `v^(Q+1)=c(x-x^Q)`, every nonzero constant `ξ` and every
Frobenius-fixed constant `a` give the automorphism
`(x,v) ↦ (ξ^(Q+1)x+a, ξv)`. Recovering both generators proves
surjectivity over the original square constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ)
local notation "K" => SquareConstantField p s
local notation "H" => SquareKummerField p s c (p ^ (s + 1) - 2) 1

private instance hermitianAffine_charP : CharP H p :=
  charP_of_injective_algebraMap (algebraMap K H).injective p

private theorem hermitianAffine_map_ne_zero {a : K} (ha : a ≠ 0) :
    algebraMap K H a ≠ 0 := by
  intro h
  apply ha
  apply (algebraMap K H).injective
  simpa only [map_zero] using h

/-- The affine image of the rational coordinate in a Hermitian radical field. -/
def hermitianAffineCoordinate (ξ : Kˣ) (a : squareFrobeniusFixedField p s) : H :=
  algebraMap K H ((ξ : K) ^ (p ^ (s + 1) + 1)) * algebraMap K[X] H X +
    algebraMap K H a.val

/-- A nonzero affine change of the Hermitian coordinate remains transcendental. -/
theorem hermitianAffineCoordinate_transcendental
    (ξ : Kˣ) (a : squareFrobeniusFixedField p s) :
    Transcendental K (hermitianAffineCoordinate p s c ξ a) := by
  intro h
  have hc : algebraMap K H ((ξ : K) ^ (p ^ (s + 1) + 1)) ≠ 0 :=
    hermitianAffine_map_ne_zero p s c (pow_ne_zero _ ξ.ne_zero)
  have hi : IsIntegral K ((algebraMap K H ((ξ : K) ^ (p ^ (s + 1) + 1)))⁻¹) := by
    rw [← map_inv₀]
    exact isIntegral_algebraMap
  have hr := hi.mul (h.isIntegral.sub
    (show IsIntegral K (algebraMap K H a.val) from isIntegral_algebraMap))
  have heq : (algebraMap K H ((ξ : K) ^ (p ^ (s + 1) + 1)))⁻¹ *
      (hermitianAffineCoordinate p s c ξ a - algebraMap K H a.val) =
        algebraMap K[X] H X := by
    rw [hermitianAffineCoordinate, add_sub_cancel_right, ← mul_assoc,
      inv_mul_cancel₀ hc, one_mul]
  rw [heq] at hr
  exact kummerBranchField_coordinate_transcendental c (p ^ (s + 1) - 2) 1
    (p ^ (s + 1)) hr.isAlgebraic

private theorem hermitianAffine_equation (ξ : Kˣ) (a : squareFrobeniusFixedField p s) :
    (algebraMap K H ξ * AdjoinRoot.root
      (kummerBranchFieldPolynomial c (p ^ (s + 1) - 2) 1 (p ^ (s + 1)))) ^
        (p ^ (s + 1) + 1) =
    algebraMap K H c * hermitianAffineCoordinate p s c ξ a *
      (1 - hermitianAffineCoordinate p s c ξ a ^ (p ^ (s + 1) - 2 + 1)) ^ 1 := by
  let Q := p ^ (s + 1)
  let y := algebraMap K[X] H X
  let z := AdjoinRoot.root (kummerBranchFieldPolynomial c (Q - 2) 1 Q)
  let w := hermitianAffineCoordinate p s c ξ a
  have hQ : 2 ≤ Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hz : z ^ (Q + 1) = algebraMap K H c * (y - y ^ Q) := by
    have hbranch : y * (1 - y ^ (Q - 2 + 1)) = y - y ^ Q := by
      rw [show Q - 2 + 1 = Q - 1 by omega, mul_sub, mul_one, ← pow_succ',
        Nat.sub_add_cancel (by omega : 1 ≤ Q)]
    rw [kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply, kummerBranch]
    simp only [map_mul, map_pow, map_sub, map_one, pow_one]
    change algebraMap K H c * y * (1 - y ^ (Q - 2 + 1)) = _
    rw [mul_assoc, hbranch]
  have ha : (a.val : K) ^ Q = a.val := a.property
  have hn : ((ξ : K) ^ (Q + 1)) ^ Q = (ξ : K) ^ (Q + 1) :=
    squareConstantField_norm_fixed p s ξ
  have hnmap : (algebraMap K H ((ξ : K) ^ (Q + 1))) ^ Q =
      algebraMap K H ((ξ : K) ^ (Q + 1)) :=
    (map_pow (algebraMap K H) ((ξ : K) ^ (Q + 1)) Q).symm.trans
      (congrArg (algebraMap K H) hn)
  have hamap : (algebraMap K H a.val) ^ Q = algebraMap K H a.val :=
    (map_pow (algebraMap K H) a.val Q).symm.trans (congrArg (algebraMap K H) ha)
  have hw : w - w ^ Q = algebraMap K H ((ξ : K) ^ (Q + 1)) * (y - y ^ Q) := by
    change (algebraMap K H ((ξ : K) ^ (Q + 1)) * y + algebraMap K H a.val) -
      (algebraMap K H ((ξ : K) ^ (Q + 1)) * y + algebraMap K H a.val) ^ p ^ (s + 1) = _
    rw [add_pow_char_pow, mul_pow, hnmap, hamap]
    ring
  have hwprod : w * (1 - w ^ (Q - 1)) = w - w ^ Q := by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  change (algebraMap K H ξ * z) ^ (Q + 1) =
    algebraMap K H c * w * (1 - w ^ (Q - 2 + 1)) ^ 1
  rw [pow_one, show Q - 2 + 1 = Q - 1 by omega,
    mul_assoc (algebraMap K H c), hwprod, hw, mul_pow, hz,
    ← map_pow (algebraMap K H) (ξ : K) (Q + 1)]
  ring

/-- The affine Hermitian substitutions extend to constant-field homomorphisms. -/
def hermitianAffineHom (ξ : Kˣ) (a : squareFrobeniusFixedField p s) : H →ₐ[K] H :=
  kummerBranchFieldHomOfCoordinates c (p ^ (s + 1) - 2) 1 (p ^ (s + 1))
    (hermitianAffineCoordinate p s c ξ a)
    (algebraMap K H ξ * AdjoinRoot.root
      (kummerBranchFieldPolynomial c (p ^ (s + 1) - 2) 1 (p ^ (s + 1))))
    (hermitianAffineCoordinate_transcendental p s c ξ a)
    (hermitianAffine_equation p s c ξ a)

/-- The rational coordinate transforms by norm scaling and fixed-field translation. -/
theorem hermitianAffineHom_coordinate (ξ : Kˣ) (a : squareFrobeniusFixedField p s) :
    hermitianAffineHom p s c ξ a (algebraMap K[X] H X) = hermitianAffineCoordinate p s c ξ a :=
  kummerBranchFieldHomOfCoordinates_coordinate _ _ _ _ _ _ _ _

/-- The Hermitian radical is multiplied by the chosen unit. -/
theorem hermitianAffineHom_root (ξ : Kˣ) (a : squareFrobeniusFixedField p s) :
    hermitianAffineHom p s c ξ a
      (AdjoinRoot.root (kummerBranchFieldPolynomial c (p ^ (s + 1) - 2) 1 (p ^ (s + 1)))) =
    algebraMap K H ξ * AdjoinRoot.root
      (kummerBranchFieldPolynomial c (p ^ (s + 1) - 2) 1 (p ^ (s + 1))) :=
  kummerBranchFieldHomOfCoordinates_root _ _ _ _ _ _ _ _

/-- Both original generators can be recovered from their affine images. -/
theorem hermitianAffineHom_surjective (ξ : Kˣ) (a : squareFrobeniusFixedField p s) :
    Function.Surjective (hermitianAffineHom p s c ξ a) := by
  let f := hermitianAffineHom p s c ξ a
  have hy : algebraMap K[X] H X ∈ f.fieldRange := by
    have hw : hermitianAffineCoordinate p s c ξ a ∈ f.fieldRange :=
      ⟨_, hermitianAffineHom_coordinate p s c ξ a⟩
    have h := f.fieldRange.mul_mem (f.fieldRange.inv_mem
      (f.fieldRange.algebraMap_mem ((ξ : K) ^ (p ^ (s + 1) + 1))))
      (f.fieldRange.sub_mem hw (f.fieldRange.algebraMap_mem a.val))
    rw [hermitianAffineCoordinate, add_sub_cancel_right, ← mul_assoc,
      inv_mul_cancel₀ (hermitianAffine_map_ne_zero p s c (pow_ne_zero _ ξ.ne_zero)), one_mul] at h
    exact h
  have hz : AdjoinRoot.root (kummerBranchFieldPolynomial c (p ^ (s + 1) - 2) 1
      (p ^ (s + 1))) ∈ f.fieldRange := by
    have h := f.fieldRange.mul_mem (f.fieldRange.inv_mem (f.fieldRange.algebraMap_mem (ξ : K)))
      (show f (AdjoinRoot.root (kummerBranchFieldPolynomial c (p ^ (s + 1) - 2) 1
        (p ^ (s + 1)))) ∈ f.fieldRange from ⟨_, rfl⟩)
    change (algebraMap K H (ξ : K))⁻¹ * hermitianAffineHom p s c ξ a
      (AdjoinRoot.root (kummerBranchFieldPolynomial c (p ^ (s + 1) - 2) 1
        (p ^ (s + 1)))) ∈ f.fieldRange at h
    rw [hermitianAffineHom_root, ← mul_assoc,
      inv_mul_cancel₀ (hermitianAffine_map_ne_zero p s c ξ.ne_zero), one_mul] at h
    exact h
  have ht := kummerBranchField_eq_top_of_coordinate_root_mem c (p ^ (s + 1) - 2) 1
    (p ^ (s + 1)) f.fieldRange hy hz
  intro x
  have hx : x ∈ f.fieldRange := by rw [ht]; trivial
  exact hx

/-- Norm scaling and fixed-field translation give actual Hermitian field automorphisms. -/
def hermitianAffineAut (ξ : Kˣ) (a : squareFrobeniusFixedField p s) : H ≃ₐ[K] H :=
  AlgEquiv.ofBijective (hermitianAffineHom p s c ξ a)
    ⟨(hermitianAffineHom p s c ξ a).injective, hermitianAffineHom_surjective p s c ξ a⟩

/-- The scaling and translation parameters are recovered from the two generator images. -/
theorem hermitianAffineAut_injective :
    Function.Injective (fun u : Kˣ × squareFrobeniusFixedField p s =>
      hermitianAffineAut p s c u.1 u.2) := by
  rintro ⟨ξ, a⟩ ⟨μ, b⟩ h
  have hz := congrArg (fun σ : H ≃ₐ[K] H => σ
    (AdjoinRoot.root (kummerBranchFieldPolynomial c (p ^ (s + 1) - 2) 1
      (p ^ (s + 1))))) h
  change hermitianAffineHom p s c ξ a
      (AdjoinRoot.root (kummerBranchFieldPolynomial c (p ^ (s + 1) - 2) 1 (p ^ (s + 1)))) =
    hermitianAffineHom p s c μ b
      (AdjoinRoot.root (kummerBranchFieldPolynomial c (p ^ (s + 1) - 2) 1 (p ^ (s + 1)))) at hz
  rw [hermitianAffineHom_root, hermitianAffineHom_root] at hz
  have hξ : ξ = μ := Units.ext ((algebraMap K H).injective
    (mul_right_cancel₀ (kummerBranchField_root_ne_zero c (p ^ (s + 1) - 2) 1
      (p ^ (s + 1))) hz))
  subst μ
  have hy := congrArg (fun σ : H ≃ₐ[K] H => σ (algebraMap K[X] H X)) h
  change hermitianAffineHom p s c ξ a (algebraMap K[X] H X) =
    hermitianAffineHom p s c ξ b (algebraMap K[X] H X) at hy
  rw [hermitianAffineHom_coordinate, hermitianAffineHom_coordinate] at hy
  have ha : a = b := Subtype.ext ((algebraMap K H).injective
    (add_left_cancel (show algebraMap K H ((ξ : K) ^ (p ^ (s + 1) + 1)) *
      algebraMap K[X] H X + algebraMap K H a.val =
      algebraMap K H ((ξ : K) ^ (p ^ (s + 1) + 1)) * algebraMap K[X] H X +
        algebraMap K H b.val from hy)))
  exact Prod.ext rfl ha

/-- There are exactly `Q(Q²-1)` distinct affine automorphisms in this explicit family. -/
theorem hermitianAffineAut_range_card :
    Nat.card (Set.range (fun u : Kˣ × squareFrobeniusFixedField p s =>
      hermitianAffineAut p s c u.1 u.2)) =
        (p ^ (2 * (s + 1)) - 1) * p ^ (s + 1) := by
  rw [← Nat.card_congr (Equiv.ofInjective _ (hermitianAffineAut_injective p s c)),
    Nat.card_prod, Nat.card_units, squareConstantField_card, squareFrobeniusFixedField_card]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
