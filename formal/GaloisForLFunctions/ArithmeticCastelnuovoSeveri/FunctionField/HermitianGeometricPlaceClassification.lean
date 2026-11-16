import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricFinitePlaces
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricInfinity

/-!
# All geometric Hermitian places, including infinity

Every proper constant-field valuation ring containing the additive
coordinate has a finite normalization center. Otherwise inversion gives
a finite center whose additive residue is zero. The Hermitian equation
forces its radical residue to vanish too, so this center is the origin.
Inverting again proves uniqueness of the place at infinity.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "η" => hermitianExtensionTraceConstant p s E
local notation "u" => hermitianExtensionAdditiveCoordinate p s E
local notation "O" => hermitianAffineOrigin p s E
local notation "V₀" => hermitianGeometricPointValuation p s O
local notation "V∞" => hermitianGeometricInfinityValuation p s

/-- The additive coordinate is not integral at geometric infinity. -/
theorem hermitianGeometricInfinity_additive_notMem : u ∉ V∞.valuationSubring := by
  have hlt : (1 : WithZero (Multiplicative ℤ)) < V∞ u := by
    rw [hermitianGeometricInfinityValuation_additive, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  intro h
  exact (not_lt_of_ge ((Valuation.mem_valuationSubring_iff V∞ u).mp h)) hlt

/-- The geometric infinity valuation defines a proper constant-field place. -/
def hermitianGeometricInfinityConstantPlace : ConstantFieldPlaces E H := by
  refine ⟨V∞.valuationSubring, ?_, ?_⟩
  · intro h
    apply hermitianGeometricInfinity_additive_notMem p s
    rw [h]
    trivial
  · intro a
    change V∞ (algebraMap E H a) ≤ 1
    by_cases ha : a = 0
    · rw [ha, map_zero, map_zero]
      exact zero_le_one
    · rw [hermitianGeometricInfinityValuation_constant p s a ha]

/-- A constant-field place where the additive coordinate has a pole is the constructed infinity place. -/
theorem hermitianGeometric_infinity_of_additive_notMem
    (W : ConstantFieldPlaces E H) (hu : u ∉ W.val) : W.val = V∞.valuationSubring := by
  let f := hermitianGeometricInversionHom p s
  let W' := W.val.comap f.toRingHom
  have hproper : W' ≠ ⊤ := by
    intro htop
    apply W.property.1
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := hermitianGeometricInversionHom_surjective p s x
    have hm : y ∈ W' := by rw [htop]; trivial
    change f y ∈ W.val at hm
    rwa [hy] at hm
  have hconstants (a : E) : algebraMap E H a ∈ W' := by
    change f (algebraMap E H a) ∈ W.val
    rw [AlgHom.commutes]
    exact W.property.2 a
  have hy : algebraMap E[X] H X ∈ W' := by
    change f (algebraMap E[X] H X) ∈ W.val
    rw [← hermitianExtensionAdditiveCoordinate_recover p s E, map_mul, AlgHom.commutes,
      hermitianGeometricInversionHom_additive]
    exact W.val.mul_mem _ _ (W.property.2 (η : E)) ((W.val.mem_or_inv_mem u).resolve_left hu)
  obtain ⟨w, hw⟩ := polynomialNormalization_finitePlace_of_coordinate_mem
    W' hproper hconstants hy
  have hinv : u⁻¹ ∉ (w.valuation H).valuationSubring := by
    intro h
    rw [hw] at h
    change f (u⁻¹) ∈ W.val at h
    rw [map_inv₀, hermitianGeometricInversionHom_additive, inv_inv] at h
    exact hu h
  let P := hermitianGeometricClosedPoint p s w
  have hb : P.val.2 = 0 := by
    change polynomialGeometricResidue E B w (hermitianGeometricIntegralAdditive p s) = 0
    by_contra hb
    have hn : hermitianGeometricIntegralAdditive p s ∉ w.asIdeal := by
      intro hm
      apply hb
      apply (polynomialGeometricResidue_eq_iff E B w _ 0).mpr
      simpa only [map_zero, sub_zero] using hm
    have hv : w.valuation H u = 1 := by
      rw [← hermitianGeometricIntegralAdditive_coe p s]
      exact (w.valuation_eq_one_iff_notMem (K := H)).mpr hn
    apply hinv
    change w.valuation H (u⁻¹) ≤ 1
    rw [map_inv₀, hv, inv_one]
  have ha : P.val.1 = 0 := by
    have h := P.property
    rw [hb, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), zero_add] at h
    exact eq_zero_of_pow_eq_zero h.symm
  have hP : P = O := Subtype.ext (Prod.ext ha hb)
  have hwo : w = hermitianGeometricPointPrime p s O := by
    rw [← hP]
    exact (hermitianGeometricPointPrime_closedPoint p s w).symm
  have he : W' = V₀.valuationSubring := by
    rw [← hw, hwo, hermitianGeometricPointPrime_valuation]
  ext x
  change x ∈ W.val ↔ f x ∈ V₀.valuationSubring
  have hm : f x ∈ W' ↔ f x ∈ V₀.valuationSubring := by rw [he]
  change f (f x) ∈ W.val ↔ f x ∈ V₀.valuationSubring at hm
  have hff : f (f x) = x := hermitianGeometricInversion_involutive p s x
  rwa [hff] at hm

/-- Finite normalization primes and the unique infinity place exhaust all constant-field places. -/
theorem hermitianGeometric_constantPlace_cases (W : ConstantFieldPlaces E H) :
    (∃ w : HeightOneSpectrum B, polynomialNormalizationFiniteConstantPlace (K := E) w = W) ∨
      hermitianGeometricInfinityConstantPlace p s = W := by
  by_cases hu : u ∈ W.val
  · have hy : algebraMap E[X] H X ∈ W.val := by
      rw [← hermitianExtensionAdditiveCoordinate_recover p s E]
      exact W.val.mul_mem _ _ (W.property.2 (η : E)) hu
    obtain ⟨w, hw⟩ := polynomialNormalization_finitePlace_of_coordinate_mem
      W.val W.property.1 W.property.2 hy
    exact Or.inl ⟨w, Subtype.ext hw⟩
  · exact Or.inr (Subtype.ext (hermitianGeometric_infinity_of_additive_notMem p s W hu).symm)

/-- Infinity is distinct from every finite normalization place. -/
theorem hermitianGeometric_finitePlace_ne_infinity (w : HeightOneSpectrum B) :
    polynomialNormalizationFiniteConstantPlace (K := E) w ≠
      hermitianGeometricInfinityConstantPlace p s := by
  intro h
  have hu : u ∈ (polynomialNormalizationFiniteConstantPlace (K := E) w).val := by
    change w.valuation H u ≤ 1
    rw [← hermitianGeometricIntegralAdditive_coe p s]
    exact w.valuation_le_one (hermitianGeometricIntegralAdditive p s)
  rw [congrArg Subtype.val h] at hu
  exact hermitianGeometricInfinity_additive_notMem p s hu

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
