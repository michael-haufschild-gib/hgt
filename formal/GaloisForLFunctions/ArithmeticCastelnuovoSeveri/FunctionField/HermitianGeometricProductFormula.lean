import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianDegreeZeroSections

/-!
# The geometric Hermitian product formula

Orbit tangents make the degree-normalized part of every place divisor torsion.
Since a principal divisor supported only at infinity is zero, this proves
the product formula on the actual normalization primes. Degree splits off
a copy of the integers in the divisor class group. Its kernel is exactly
the torsion and has no characteristic-primary component.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "H" => HermitianGeometricField p s
local notation "W" => HeightOneSpectrum (HermitianGeometricNormalization p s)
local notation "Pts" => HermitianGeometricPoint p s
local notation "Div" => HermitianGeometricPlaceDivisor p s
local notation "D₀" => hermitianGeometricDegreeZeroPart p s
local notation "divH" => hermitianGeometricPrincipalDivisorHom p s
local notation "∞ₕ" => ((0, 1) : Div)

private def finiteDegree : (W →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

/-- Signed coefficient sum over all normalization primes and the unique infinity place. -/
def hermitianPlaceDegree : Div →+ ℤ :=
  (finiteDegree p s).comp (AddMonoidHom.fst _ _) + AddMonoidHom.snd _ _

local notation "degH" => hermitianPlaceDegree p s

private theorem finite_normalization (A : W →₀ ℤ) :
    ∃ D : Pts →₀ ℤ, D₀ D = (A, -finiteDegree p s A) := by
  let ψ := Finsupp.liftAddHom (α := Pts) (fun P => zmultiplesHom Div
    (hermitianGeometricPointDifference p s P))
  change ∃ D, ψ D = _
  induction A using Finsupp.induction_linear with
  | zero => exact ⟨0, by rw [map_zero, map_zero, neg_zero]; rfl⟩
  | add x y hx hy =>
    obtain ⟨D, hD⟩ := hx
    obtain ⟨C, hC⟩ := hy
    exact ⟨D+C, by rw [map_add, hD, hC, map_add, neg_add]; rfl⟩
  | single w n =>
    refine ⟨Finsupp.single (some (hermitianGeometricClosedPoint p s w)) n, ?_⟩
    rw [Finsupp.liftAddHom_apply_single, finiteDegree, Finsupp.liftAddHom_apply_single]
    change n • (Finsupp.single (hermitianGeometricPointPrime p s
      (hermitianGeometricClosedPoint p s w)) (1 : ℤ), (-1 : ℤ)) = _
    rw [hermitianGeometricPointPrime_closedPoint]
    apply Prod.ext
    · change n • Finsupp.single w (1 : ℤ) = _
      rw [Finsupp.smul_single, zsmul_eq_mul, mul_one]
    · change n • (-1 : ℤ) = -n
      rw [zsmul_eq_mul, mul_neg_one]

/-- Every actual divisor is equivalent up to prime-to-characteristic torsion to its degree at infinity. -/
theorem hermitianPlaceDegree_primeToChar_principal (A : Div) :
    ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • (A - degH A • ∞ₕ) ∈ (divH).range := by
  obtain ⟨D, hD⟩ := finite_normalization p s A.1
  obtain ⟨n, hn, hp, u, hu⟩ := hermitianDegreeZeroPart_primeToChar_principal p s D
  refine ⟨n, hn, hp, u, ?_⟩
  rw [hu, hD]
  congr 1
  apply Prod.ext
  · change A.1 = A.1 - _ • 0
    rw [smul_zero, sub_zero]
  · change -(finiteDegree p s A.1) = A.2 - (finiteDegree p s A.1 + A.2) • (1 : ℤ)
    rw [zsmul_eq_mul, mul_one]
    abel

/-- A function with divisor supported at the unique infinity place has zero divisor. -/
theorem hermitianInfinity_principal_iff (z : ℤ) :
    z • ∞ₕ ∈ (divH).range ↔ z = 0 := by
  have nonneg_case (v : Additive Hˣ) (t : ℤ) (ht : 0 ≤ t) (hv : divH v = t • ∞ₕ) : t = 0 := by
    have he : 0 ≤ divH v := hv ▸ smul_nonneg ht
      (hermitianGeometricPointDivisor_nonneg p s none)
    have hz := (hermitianGeometric_principal_eq_zero_iff_constant p s _ v.toMul.ne_zero).2
      ((hermitianGeometric_effective_principal_iff_constant p s _ v.toMul.ne_zero).1 he)
    change divH v = 0 at hz
    rw [hv] at hz
    simpa only [Prod.snd_smul, zsmul_eq_mul, mul_one, Prod.snd_zero] using congrArg Prod.snd hz
  refine ⟨?_, fun h => by rw [h, zero_smul]; exact (divH).range.zero_mem⟩
  rintro ⟨u, hu⟩
  rcases le_total 0 z with h | h
  · exact nonneg_case u z h hu
  · have ht := nonneg_case (-u) (-z) (neg_nonneg.mpr h) (by rw [map_neg, hu, neg_smul])
    exact neg_eq_zero.mp ht

/-- Product formula for every unit of the geometric Hermitian function field. -/
theorem hermitianPlaceDegree_principal (u : Additive Hˣ) : degH (divH u) = 0 := by
  let z := degH (divH u)
  obtain ⟨n, hn, _, v, hv⟩ := hermitianPlaceDegree_primeToChar_principal p s (divH u)
  have he : ((n : ℤ) * z) • ∞ₕ ∈ (divH).range := by
    refine ⟨n • u - v, ?_⟩
    rw [map_sub, map_nsmul, hv, nsmul_sub, sub_sub_cancel, mul_smul, natCast_zsmul]
  exact (mul_eq_zero.mp ((hermitianInfinity_principal_iff p s _).1 he)).resolve_left
    (Int.natCast_ne_zero.mpr hn.ne')

/-- Geometric divisor classes formed from the actual function field and place divisors. -/
abbrev HermitianGeometricPicard := Div ⧸ (divH).range

local notation "Pic" => HermitianGeometricPicard p s
local notation "cl" => QuotientAddGroup.mk' (divH).range

/-- Degree on the Picard group. -/
def hermitianPicardDegree : Pic →+ ℤ :=
  QuotientAddGroup.lift _ degH (by rintro _ ⟨u, rfl⟩; exact hermitianPlaceDegree_principal p s u)

local notation "δ" => hermitianPicardDegree p s

/-- The infinity class splits degree onto the integers. -/
theorem hermitianPicardDegree_infinity (z : ℤ) : δ (z • cl ∞ₕ) = z := by
  rw [map_zsmul]
  change z • (finiteDegree p s 0 + 1) = z
  rw [map_zero, zero_add, zsmul_eq_mul, mul_one]

/-- Torsion in the geometric class group is exactly degree zero, with prime-to-p annihilators. -/
theorem hermitianPicardDegree_zero_iff (c : Pic) :
    δ c = 0 ↔ ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • c = 0 := by
  constructor
  · obtain ⟨A, rfl⟩ := QuotientAddGroup.mk'_surjective (divH).range c
    change degH A = 0 → _
    intro h
    obtain ⟨n, hn, hp, hmem⟩ := hermitianPlaceDegree_primeToChar_principal p s A
    rw [h, zero_smul, sub_zero] at hmem
    refine ⟨n, hn, hp, ?_⟩
    rw [← map_nsmul]
    exact QuotientAddGroup.eq_zero_iff.mpr hmem
  · rintro ⟨n, hn, _, h⟩
    have he := congrArg δ h
    rw [map_nsmul, map_zero, nsmul_eq_mul] at he
    exact (mul_eq_zero.mp he).resolve_left (Int.natCast_ne_zero.mpr hn.ne')

/-- Explicit splitting by degree into the free infinity class and the degree-zero subgroup. -/
def hermitianPicardSplit : Pic ≃+ ℤ × (δ).ker where
  toFun c := (δ c, ⟨c - δ c • cl ∞ₕ, by
    change δ (c - δ c • cl ∞ₕ) = 0
    rw [map_sub, hermitianPicardDegree_infinity, sub_self]⟩)
  invFun t := t.1 • cl ∞ₕ + t.2.val
  left_inv c := by dsimp; abel
  right_inv := by
    rintro ⟨z,k⟩
    have hk : δ k.val = 0 := k.property
    have hd : δ (z • cl ∞ₕ + k.val) = z := by
      rw [map_add, hermitianPicardDegree_infinity, hk, add_zero]
    apply Prod.ext hd
    apply Subtype.ext
    change z • cl ∞ₕ + k.val - δ (z • cl ∞ₕ + k.val) • cl ∞ₕ = k.val
    rw [hd]; abel
  map_add' x y := by
    apply Prod.ext (map_add δ x y)
    apply Subtype.ext
    change x + y - δ (x+y) • cl ∞ₕ = (x - δ x • cl ∞ₕ) + (y - δ y • cl ∞ₕ)
    rw [map_add, add_smul]; abel

#print axioms hermitianPlaceDegree_primeToChar_principal
#print axioms hermitianInfinity_principal_iff
#print axioms hermitianPlaceDegree_principal
#print axioms hermitianPicardDegree_infinity
#print axioms hermitianPicardDegree_zero_iff
#print axioms hermitianPicardSplit

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
