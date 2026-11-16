import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricPrescribedPoleSections

/-!
# Principal-divisor rigidity on the geometric Hermitian field

The degree-zero pole expansion proves that a function regular at every
finite normalization prime and at infinity is a geometric constant.
Consequently an effective principal divisor of a nonzero function is zero,
and two nonzero functions have equal principal divisors exactly when they
differ by a nonzero geometric constant.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s

/-- A rational function regular at every geometric place is a constant. -/
theorem hermitianGeometric_constant_of_regular (f : H)
    (hf : ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1)
    (hi : hermitianGeometricInfinityValuation p s f ≤ 1) :
    ∃ c : E, f = algebraMap E H c := by
  classical
  have hQ : 0 < Q := pow_pos (Fact.out : p.Prime).pos _
  obtain ⟨a, ha, hb⟩ := hermitianGeometric_exists_lowDegree_polynomial_expansion p s f 0 hQ hf
    (by simpa only [Nat.zero_mul, Nat.cast_zero, WithZero.exp_zero] using hi)
  let i₀ : Fin (Q + 1) := ⟨0, Nat.succ_pos Q⟩
  have hz (i : Fin (Q + 1)) (hne : i ≠ i₀) : a i = 0 := by
    by_contra h
    have hval : i.val = 0 := by have := hb i h; omega
    exact hne (Fin.ext hval)
  have hdeg : (a i₀).natDegree ≤ 0 := by
    by_cases h : a i₀ = 0
    · simp only [h, Polynomial.natDegree_zero, le_refl]
    · simpa only [i₀, Nat.zero_add] using hb i₀ h
  have hc := Polynomial.eq_C_of_natDegree_le_zero hdeg
  refine ⟨(a i₀).coeff 0, ?_⟩
  rw [ha, hermitianGeometricPolynomialExpansion, Finset.sum_eq_single i₀]
  · simp only [i₀, pow_zero, mul_one]
    calc
      algebraMap E[X] H (a i₀) = algebraMap E[X] H (C ((a i₀).coeff 0)) :=
        congrArg (algebraMap E[X] H) hc
      _ = algebraMap E H ((a i₀).coeff 0) :=
        (IsScalarTower.algebraMap_apply E E[X] H _).symm
  · intro i _ hne
    rw [hz i hne, map_zero, zero_mul]
  · intro h
    exact (h (Finset.mem_univ i₀)).elim

/-- Every nonzero geometric constant has zero principal divisor. -/
theorem hermitianGeometricZeroPoleDivisor_constant (c : E) (hc : c ≠ 0) :
    hermitianGeometricZeroPoleDivisor p s (algebraMap E H c) = 0 := by
  apply Prod.ext
  · ext w
    change -WithZero.log (w.valuation H (algebraMap E H c)) = 0
    rw [heightOne_valuation_constant w c hc, WithZero.log_one, neg_zero]
  · change -WithZero.log (hermitianGeometricInfinityValuation p s (algebraMap E H c)) = 0
    rw [hermitianGeometricInfinityValuation_constant p s c hc, WithZero.log_one, neg_zero]

/-- A nonzero function has an effective principal divisor exactly when it is a nonzero constant. -/
theorem hermitianGeometric_effective_principal_iff_constant (f : H) (hf : f ≠ 0) :
    0 ≤ hermitianGeometricZeroPoleDivisor p s f ↔
      ∃ c : E, c ≠ 0 ∧ f = algebraMap E H c := by
  constructor
  · intro h
    have hb : 0 ≤ hermitianGeometricZeroPoleDivisor p s f + (0 : ℤ) • (0, 1) := by
      simpa only [zero_smul, add_zero] using h
    obtain ⟨hfinite, hinfinity⟩ :=
      (hermitianGeometricZeroPoleDivisor_add_infinity_nonneg_iff p s f hf 0).mp hb
    rw [WithZero.exp_zero] at hinfinity
    obtain ⟨c, hc⟩ := hermitianGeometric_constant_of_regular p s f hfinite hinfinity
    refine ⟨c, ?_, hc⟩
    intro hz
    apply hf
    rw [hc, hz, map_zero]
  · rintro ⟨c, hc, heq⟩
    simpa only [heq, hermitianGeometricZeroPoleDivisor_constant p s c hc] using
      (le_refl (0 : HermitianGeometricPlaceDivisor p s))

/-- The kernel of the actual principal-divisor map consists precisely of nonzero constants. -/
theorem hermitianGeometric_principal_eq_zero_iff_constant (f : H) (hf : f ≠ 0) :
    hermitianGeometricZeroPoleDivisor p s f = 0 ↔
      ∃ c : E, c ≠ 0 ∧ f = algebraMap E H c := by
  constructor
  · intro h
    apply (hermitianGeometric_effective_principal_iff_constant p s f hf).mp
    simpa only [h] using (le_refl (0 : HermitianGeometricPlaceDivisor p s))
  · rintro ⟨c, hc, heq⟩
    rw [heq, hermitianGeometricZeroPoleDivisor_constant p s c hc]

/-- Inverting a function negates its principal divisor. -/
theorem hermitianGeometricZeroPoleDivisor_inv (f : H) :
    hermitianGeometricZeroPoleDivisor p s f⁻¹ = -hermitianGeometricZeroPoleDivisor p s f := by
  apply Prod.ext
  · change -finiteValuationDivisor B H f⁻¹ = -(-finiteValuationDivisor B H f)
    rw [finiteValuationDivisor_inv]
  · change -WithZero.log (hermitianGeometricInfinityValuation p s f⁻¹) =
      -(-WithZero.log (hermitianGeometricInfinityValuation p s f))
    rw [map_inv₀, WithZero.log_inv]

/-- Dividing nonzero functions subtracts their principal divisors. -/
theorem hermitianGeometricZeroPoleDivisor_div (f g : H) (hf : f ≠ 0) (hg : g ≠ 0) :
    hermitianGeometricZeroPoleDivisor p s (f / g) =
      hermitianGeometricZeroPoleDivisor p s f - hermitianGeometricZeroPoleDivisor p s g := by
  rw [div_eq_mul_inv, hermitianGeometricZeroPoleDivisor_mul p s f g⁻¹ hf (inv_ne_zero hg),
    hermitianGeometricZeroPoleDivisor_inv, sub_eq_add_neg]

/-- Equal principal divisors determine a nonzero rational function up to a geometric constant. -/
theorem hermitianGeometric_principal_eq_iff_constant_multiple
    (f g : H) (hf : f ≠ 0) (hg : g ≠ 0) :
    hermitianGeometricZeroPoleDivisor p s f = hermitianGeometricZeroPoleDivisor p s g ↔
      ∃ c : E, c ≠ 0 ∧ f = algebraMap E H c * g := by
  constructor
  · intro h
    have hdiv : hermitianGeometricZeroPoleDivisor p s (f / g) = 0 := by
      rw [hermitianGeometricZeroPoleDivisor_div p s f g hf hg, h, sub_self]
    obtain ⟨c, hc, heq⟩ :=
      (hermitianGeometric_principal_eq_zero_iff_constant p s (f / g) (div_ne_zero hf hg)).mp hdiv
    exact ⟨c, hc, ((eq_div_iff hg).mp heq.symm).symm⟩
  · rintro ⟨c, hc, heq⟩
    have hmap : algebraMap E H c ≠ 0 := (map_ne_zero _).mpr hc
    rw [heq, hermitianGeometricZeroPoleDivisor_mul p s _ g hmap hg,
      hermitianGeometricZeroPoleDivisor_constant p s c hc, zero_add]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
