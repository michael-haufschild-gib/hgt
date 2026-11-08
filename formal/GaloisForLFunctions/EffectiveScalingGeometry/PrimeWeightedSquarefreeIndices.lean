import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedParityCoordinates
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeSquarefreeIndices

/-!
# Squarefree labels for integral prime-weighted torsion

A prime divides a face product exactly when it belongs to the face. Thus odd
faces omitting three correspond precisely to squarefree integers coprime to
six. Multiplication reindexes the parity window `2m ≤ N < 3m`, preserving the
number of prime factors and every coefficient. The parity equivalence is
linear over the integers, matching the integral homology comparison.
-/

noncomputable section
open scoped Classical
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder

/-- A prime divides a face product precisely when it belongs to the face. -/
theorem primeFaceProduct_dvd_iff {k : ℕ} (s : Set.powersetCard Nat.Primes k)
    (p : Nat.Primes) : p.val ∣ primeFaceProduct s ↔ p ∈ s.val := by
  rw [← primeFaceNumbers_mem s p,← primeFaceProduct_primeFactors]
  constructor
  · intro h
    exact p.property.mem_primeFactors h (primeFaceProduct_squarefree s).ne_zero
  · intro h
    exact (Nat.mem_primeFactors.mp h).2.1

/-- Omitting the two smallest primes is exactly coprimality with six. -/
theorem primeFaceProduct_coprime_six_iff {k : ℕ} (s : Set.powersetCard Nat.Primes k) :
    Nat.Coprime (primeFaceProduct s) 6 ↔ primeTwoLabel ∉ s.val ∧ primeThreeLabel ∉ s.val := by
  rw [Nat.coprime_comm]
  change Nat.Coprime (2*3) (primeFaceProduct s) ↔ _
  rw [Nat.coprime_mul_iff_left,Nat.prime_two.coprime_iff_not_dvd,Nat.prime_three.coprime_iff_not_dvd]
  change (¬ primeTwoLabel.val ∣ primeFaceProduct s) ∧
    (¬ primeThreeLabel.val ∣ primeFaceProduct s) ↔ _
  rw [primeFaceProduct_dvd_iff,primeFaceProduct_dvd_iff]

/-- Squarefree arithmetic labels in the parity-torsion window. -/
def squarefreeTorsionLabels (k N : ℕ) : Set (SquarefreeDegree k) :=
  {m | Nat.Coprime m.val 6 ∧ 2*m.val ≤ N ∧ N < 3*m.val}

theorem primeFaceSquarefreeEquiv_torsion (k N : ℕ) (s : Set.powersetCard Nat.Primes k) :
    primeFaceSquarefreeEquiv k s ∈ squarefreeTorsionLabels k N ↔ s ∈ primeTorsionFaces k N := by
  change Nat.Coprime (primeFaceProduct s) 6 ∧ 2*primeFaceProduct s ≤ N ∧
    N < 3*primeFaceProduct s ↔ _
  rw [primeFaceProduct_coprime_six_iff]
  change ((_ ∧ _) ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  tauto

/-- Reindex parity coefficients by squarefree products, preserving integer scalars. -/
def primeParityCoordinateReindex (k : ℕ) :
    (Set.powersetCard Nat.Primes k →₀ ZMod 2) ≃ₗ[ℤ] (SquarefreeDegree k →₀ ZMod 2) :=
  Finsupp.domLCongr (primeFaceSquarefreeEquiv k)

abbrev squarefreeTorsionCoordinates (k N : ℕ) :=
  Finsupp.supported (ZMod 2) ℤ (squarefreeTorsionLabels k N)

theorem primeParityCoordinateReindex_mem_iff (k N : ℕ)
    (x : Set.powersetCard Nat.Primes k →₀ ZMod 2) :
    primeParityCoordinateReindex k x ∈ squarefreeTorsionCoordinates k N ↔
      x ∈ primeTorsionCoordinates k N := by
  rw [Finsupp.mem_supported',Finsupp.mem_supported']
  constructor
  · intro h s hs
    have hm : primeFaceSquarefreeEquiv k s ∉ squarefreeTorsionLabels k N :=
      fun hm => hs ((primeFaceSquarefreeEquiv_torsion k N s).mp hm)
    have hz := h (primeFaceSquarefreeEquiv k s) hm
    change x ((primeFaceSquarefreeEquiv k).symm (primeFaceSquarefreeEquiv k s)) = 0 at hz
    simpa only [Equiv.symm_apply_apply] using hz
  · intro h m hm
    change x ((primeFaceSquarefreeEquiv k).symm m) = 0
    apply h
    intro hs
    have hh := (primeFaceSquarefreeEquiv_torsion k N ((primeFaceSquarefreeEquiv k).symm m)).mpr hs
    exact hm (by simpa only [Equiv.apply_symm_apply] using hh)

/-- Arithmetic reindexing of the surviving parity coefficients. -/
def primeTorsionArithmeticEquiv (k N : ℕ) :
    primeTorsionCoordinates k N ≃ₗ[ℤ] squarefreeTorsionCoordinates k N where
  toFun x := ⟨primeParityCoordinateReindex k x.val,
    (primeParityCoordinateReindex_mem_iff k N x.val).mpr x.property⟩
  invFun y := ⟨(primeParityCoordinateReindex k).symm y.val,
    (primeParityCoordinateReindex_mem_iff k N _).mp (by
      rw [LinearEquiv.apply_symm_apply]
      exact y.property)⟩
  left_inv x := Subtype.ext ((primeParityCoordinateReindex k).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((primeParityCoordinateReindex k).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((primeParityCoordinateReindex k).map_add x.val y.val)
  map_smul' a x := Subtype.ext ((primeParityCoordinateReindex k).map_smul a x.val)

theorem primeTorsionArithmeticEquiv_apply (k N : ℕ) (x : primeTorsionCoordinates k N)
    (m : SquarefreeDegree k) :
    (primeTorsionArithmeticEquiv k N x).val m = x.val ((primeFaceSquarefreeEquiv k).symm m) := rfl

#print axioms primeFaceProduct_coprime_six_iff
#print axioms primeTorsionArithmeticEquiv
end GaloisForLFunctions.EffectiveScalingGeometry
