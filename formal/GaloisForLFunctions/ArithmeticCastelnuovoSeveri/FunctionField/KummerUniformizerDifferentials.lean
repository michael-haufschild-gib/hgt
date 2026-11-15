import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerUniformizerPowerExpansions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerKaehlerDimension

/-!
# Differentiation in a uniformizer

Frobenius power expansions express every differential as a multiple of
the differential of a local parameter. An integral function has integral
coefficients in that expansion, so its differential has integral
coefficient as well. The parameter differential is nonzero.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A derivation in characteristic `p` kills every `p`th power. -/
theorem derivation_frobenius_power_eq_zero
    {K L M : Type*} [CommRing K] [CommRing L] [Algebra K L]
    [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M]
    (p : ℕ) [CharP L p] (D : Derivation K L M) (a : L) : D (a ^ p) = 0 := by
  rw [D.leibniz_pow, ← Nat.cast_smul_eq_nsmul L, CharP.cast_eq_zero, zero_smul]

/-- Differentiating a Frobenius power expansion leaves only derivatives of parameter powers. -/
theorem derivation_uniformizer_power_expansion
    {K L M : Type*} [CommRing K] [CommRing L] [Algebra K L]
    [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M]
    (p : ℕ) [CharP L p] (D : Derivation K L M) (π : L) (a : Fin p → L) :
    D (∑ i : Fin p, a i ^ p * π ^ i.val) =
      (∑ i : Fin p, a i ^ p * (i.val : L) * π ^ (i.val - 1)) • D π := by
  classical
  rw [map_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.leibniz, derivation_frobenius_power_eq_zero, smul_zero, add_zero,
    D.leibniz_pow, ← Nat.cast_smul_eq_nsmul L]
  simp only [mul_smul]

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (v : Valuation (SquareKummerField p s c b R) (WithZero (Multiplicative ℤ)))
    (π : SquareKummerField p s c b R) (hπ : v π = WithZero.exp (-1 : ℤ))

include v hπ

/-- Every function differential is a scalar multiple of the uniformizer differential. -/
theorem squareKummer_differential_uniformizer_multiple
    (x : SquareKummerField p s c b R) :
    ∃ a : SquareKummerField p s c b R,
      KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) x =
        a • KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) π := by
  obtain ⟨a, ha⟩ := squareKummer_uniformizer_power_expansion p s c b R v π hπ x
  refine ⟨∑ i : Fin p, a i ^ p * (i.val : SquareKummerField p s c b R) * π ^ (i.val - 1), ?_⟩
  rw [ha, derivation_uniformizer_power_expansion]

/-- Differentiating a valuation integer gives an integral multiple of the parameter differential. -/
theorem squareKummer_integral_differential_uniformizer_multiple
    (x : SquareKummerField p s c b R) (hx : v x ≤ 1) :
    ∃ a : SquareKummerField p s c b R, v a ≤ 1 ∧
      KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) x =
        a • KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) π := by
  classical
  obtain ⟨a, ha, hax⟩ := squareKummer_uniformizer_integral_power_expansion p s c b R v π hπ x hx
  refine ⟨∑ i : Fin p, a i ^ p * (i.val : SquareKummerField p s c b R) * π ^ (i.val - 1), ?_, ?_⟩
  · have hπmem : π ∈ v.valuationSubring := by
      change v π ≤ 1
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    change (∑ i : Fin p, a i ^ p * (i.val : SquareKummerField p s c b R) * π ^ (i.val - 1)) ∈
      v.valuationSubring
    exact sum_mem fun i _ => mul_mem (mul_mem (pow_mem (ha i) p)
      (natCast_mem _ _)) (pow_mem hπmem _)
  · rw [hax, derivation_uniformizer_power_expansion]

/-- Every uniformizer has nonzero differential over the finite constant field. -/
theorem squareKummer_uniformizer_differential_ne_zero :
    KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) π ≠ 0 := by
  intro hπD
  obtain ⟨a, ha⟩ := squareKummer_differential_uniformizer_multiple p s c b R v π hπ
    (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) Polynomial.X)
  rw [hπD, smul_zero] at ha
  exact squareKummer_coordinate_differential_ne_zero p s c b R ha

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
