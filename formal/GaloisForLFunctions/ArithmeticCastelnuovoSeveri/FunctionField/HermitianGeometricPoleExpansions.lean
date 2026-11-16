import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricFinitePlaces
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricInfinity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.CoprimePoleMonomials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityPolynomialOrders

/-!
# Polynomial pole bounds over the geometric Hermitian constants

The normalization gives polynomial expansions in reduced radical powers.
Their pole orders are `(Q+1) deg(aᵢ) + Q i`, distinct modulo `Q+1` for
different reduced indices. Thus cancellation cannot conceal a larger pole.
For `d<Q`, a sole infinity pole bounded by `d(Q+1)` forces total degree at
most `d` in the two affine coordinates.
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
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "V" => hermitianGeometricInfinityValuation p s

/-- The actual affine normalization is the intersection of all finite valuation rings. -/
theorem hermitianGeometric_integral_iff_finite_valuations (f : H) :
    IsIntegral E[X] f ↔ ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1 := by
  constructor
  · intro hf w
    exact w.valuation_le_one (⟨f, hf⟩ : B)
  · intro hf
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one H f hf
    rw [← hb]
    exact b.property

/-- A polynomial in the original parameter has infinity pole order `(Q+1) deg(f)`. -/
theorem hermitianGeometricInfinityValuation_polynomial (f : E[X]) (hf : f ≠ 0) :
    V (algebraMap E[X] H f) = WithZero.exp (((Q + 1) * f.natDegree : ℕ) : ℤ) := by
  let y : H := algebraMap E[X] H X
  let e := hermitianGeometricInversionHom p s
  let w := hermitianGeometricPointPrime p s (hermitianAffineOrigin p s E)
  have hV (x : H) : V x = w.valuation H (e x) := by
    rw [hermitianGeometricPointPrime_valuation]
    rfl
  have hy : V y = WithZero.exp ((Q + 1 : ℕ) : ℤ) := by
    change V (algebraMap E[X] H X) = _
    rw [← hermitianExtensionAdditiveCoordinate_recover p s E, map_mul,
      hermitianGeometricInfinityValuation_constant p s _ (η).ne_zero,
      one_mul, hermitianGeometricInfinityValuation_additive]
  have hey : w.valuation H (e y) = WithZero.exp ((Q + 1 : ℕ) : ℤ) := (hV y).symm.trans hy
  have hgt : 1 < w.valuation H (e y) := by
    rw [hey, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact_mod_cast Nat.succ_pos Q
  have hhom : e.comp (IsScalarTower.toAlgHom E E[X] H) = aeval (e y) := by
    apply Polynomial.algHom_ext
    rw [aeval_X]
    rfl
  have hpoly : e (algebraMap E[X] H f) = aeval (e y) f :=
    congrArg (fun h : E[X] →ₐ[E] H => h f) hhom
  rw [hV (algebraMap E[X] H f), hpoly,
    heightOne_aeval_valuation w (e y) hgt f hf, hey, ← WithZero.exp_nsmul]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_mul]
  ring

/-- The reduced polynomial expansion in the actual geometric function field. -/
def hermitianGeometricPolynomialExpansion (a : Fin (Q + 1) → E[X]) : H :=
  ∑ i, algebraMap E[X] H (a i) * z ^ i.val

/-- A nonzero polynomial radical term has its exact weighted pole order. -/
theorem hermitianGeometricInfinityValuation_polynomialMonomial
    (a : E[X]) (ha : a ≠ 0) (i : Fin (Q + 1)) :
    V (algebraMap E[X] H a * z ^ i.val) =
      WithZero.exp (((Q + 1) * a.natDegree + Q * i.val : ℕ) : ℤ) := by
  rw [map_mul, hermitianGeometricInfinityValuation_polynomial p s a ha,
    map_pow, hermitianGeometricInfinityValuation_radical,
    ← WithZero.exp_nsmul, ← WithZero.exp_add]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul]
  ring

/-- A pole bound on a reduced expansion is exactly a separate bound on every nonzero coefficient. -/
theorem hermitianGeometricPolynomialExpansion_pole_bound_iff
    (a : Fin (Q + 1) → E[X]) (m : ℕ) :
    V (hermitianGeometricPolynomialExpansion p s a) ≤ WithZero.exp (m : ℤ) ↔
      ∀ i, a i ≠ 0 → (Q + 1) * (a i).natDegree + Q * i.val ≤ m := by
  classical
  let f := fun i : Fin (Q + 1) => algebraMap E[X] H (a i) * z ^ i.val
  have hcoprime : (Q + 1).Coprime Q := by
    have h := kummerInfinity_primePower_poleDegree_coprime p s s 1
    rw [kummerInfinity_primePower_poleDegree, pow_one] at h
    exact h
  have hsep : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      i ≠ j → V (f i) = V (f j) → V (f i) = 0 := by
    intro i _ j _ hij heq
    by_cases hi : a i = 0
    · simp only [f, hi, map_zero, zero_mul]
    have hj : a j ≠ 0 := by
      intro hj
      have hz : V (f j) = 0 := by simp only [f, hj, map_zero, zero_mul]
      rw [hz, hermitianGeometricInfinityValuation_polynomialMonomial p s (a i) hi i] at heq
      exact WithZero.exp_ne_zero heq
    rw [hermitianGeometricInfinityValuation_polynomialMonomial p s (a i) hi i,
      hermitianGeometricInfinityValuation_polynomialMonomial p s (a j) hj j] at heq
    have hw : ((a i).natDegree, i) = ((a j).natDegree, j) :=
      coprime_monomialWeight_injective (Nat.succ_pos Q) hcoprime
        (Nat.cast_injective (WithZero.exp_injective heq))
    exact (hij (congrArg Prod.snd hw)).elim
  constructor
  · intro h i hi
    have hb := valuation_terms_le_of_separated V Finset.univ f hsep (WithZero.exp (m : ℤ)) h i
      (Finset.mem_univ i)
    rw [hermitianGeometricInfinityValuation_polynomialMonomial p s (a i) hi i,
      WithZero.exp_le_exp] at hb
    exact_mod_cast hb
  · intro h
    apply (V).map_sum_le
    intro i _
    by_cases hi : a i = 0
    · simp only [hi, map_zero, zero_mul]
      exact zero_le
    · rw [hermitianGeometricInfinityValuation_polynomialMonomial p s (a i) hi i,
        WithZero.exp_le_exp]
      exact_mod_cast h i hi

/-- Every function with only a bounded infinity pole has reduced coefficients of bounded weighted degree. -/
theorem hermitianGeometric_exists_bounded_polynomial_expansion (f : H) (m : ℕ)
    (hf : ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1)
    (hInfinity : V f ≤ WithZero.exp (m : ℤ)) :
    ∃ a : Fin (Q + 1) → E[X], f = hermitianGeometricPolynomialExpansion p s a ∧
      ∀ i, a i ≠ 0 → (Q + 1) * (a i).natDegree + Q * i.val ≤ m := by
  obtain ⟨a, ha⟩ := hermitianGeometric_integral_power_expansion p s f
    ((hermitianGeometric_integral_iff_finite_valuations p s f).mpr hf)
  refine ⟨a, ha, (hermitianGeometricPolynomialExpansion_pole_bound_iff p s a m).mp ?_⟩
  change V (∑ i, algebraMap E[X] H (a i) * z ^ i.val) ≤ _
  rw [← ha]
  exact hInfinity

private theorem total_degree_le_of_weight_bound {q u v d : ℕ} (hd : d < q)
    (h : (q + 1) * v + q * u ≤ d * (q + 1)) : u + v ≤ d := by
  by_contra hu
  have hsum : d + 1 ≤ u + v := by omega
  have hmul := Nat.mul_le_mul_left q hsum
  nlinarith only [h, hmul, hd]

/-- Below `Q`, an infinity pole bound `d(Q+1)` gives a polynomial of total degree at most `d`. -/
theorem hermitianGeometric_exists_lowDegree_polynomial_expansion (f : H) (d : ℕ) (hd : d < Q)
    (hf : ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1)
    (hInfinity : V f ≤ WithZero.exp ((d * (Q + 1) : ℕ) : ℤ)) :
    ∃ a : Fin (Q + 1) → E[X], f = hermitianGeometricPolynomialExpansion p s a ∧
      ∀ i, a i ≠ 0 → i.val + (a i).natDegree ≤ d := by
  obtain ⟨a, ha, hb⟩ := hermitianGeometric_exists_bounded_polynomial_expansion p s f _ hf hInfinity
  exact ⟨a, ha, fun i hi => total_degree_le_of_weight_bound hd (hb i hi)⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
