import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricPrincipalDivisorRigidity

/-!
# Lifting principal-divisor power relations to functions

If `div(f)=n div(g)` for nonzero functions and `n>0`, then `f/g^n` is
a nonzero geometric constant. Taking an `n`-th root of that constant
gives an actual root of `f` whose divisor is exactly `div(g)`.

For a Frobenius-invariant signed geometric divisor, the tangent product
supplies the required principal witness. Thus the Frobenius divisor
relation gives power roots with their precise divisors, in every positive
exponent and without a coprimality condition on the exponent.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s

/-- A natural power multiplies the actual principal divisor by its exponent. -/
theorem hermitianGeometricZeroPoleDivisor_pow (f : H) (hf : f ≠ 0) (n : ℕ) :
    hermitianGeometricZeroPoleDivisor p s (f ^ n) = n • hermitianGeometricZeroPoleDivisor p s f := by
  induction n with
  | zero => rw [pow_zero, hermitianGeometricZeroPoleDivisor_one, zero_smul]
  | succ n ih =>
    rw [pow_succ, hermitianGeometricZeroPoleDivisor_mul p s (f ^ n) f (pow_ne_zero n hf) hf,
      ih, succ_nsmul]

/-- A principal-divisor power relation is equivalent to an actual power root with the prescribed divisor. -/
theorem hermitianGeometric_principal_power_iff
    (f g : H) (hf : f ≠ 0) (hg : g ≠ 0) (n : ℕ) (hn : 0 < n) :
    hermitianGeometricZeroPoleDivisor p s f = n • hermitianGeometricZeroPoleDivisor p s g ↔
      ∃ h : H, h ≠ 0 ∧ h ^ n = f ∧
        hermitianGeometricZeroPoleDivisor p s h = hermitianGeometricZeroPoleDivisor p s g := by
  constructor
  · intro hdiv
    have hequal : hermitianGeometricZeroPoleDivisor p s f =
        hermitianGeometricZeroPoleDivisor p s (g ^ n) :=
      hdiv.trans (hermitianGeometricZeroPoleDivisor_pow p s g hg n).symm
    obtain ⟨c, hc, hconstant⟩ :=
      (hermitianGeometric_principal_eq_iff_constant_multiple p s f (g ^ n) hf
        (pow_ne_zero n hg)).mp hequal
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c hn
    have hb0 : b ≠ 0 := by
      intro hz
      rw [hz, zero_pow (Nat.ne_of_gt hn)] at hb
      exact hc hb.symm
    have hmap : algebraMap E H b ≠ 0 := (_root_.map_ne_zero _).mpr hb0
    refine ⟨algebraMap E H b * g, mul_ne_zero hmap hg, ?_, ?_⟩
    · rw [mul_pow, ← map_pow, hb, ← hconstant]
    · rw [hermitianGeometricZeroPoleDivisor_mul p s _ g hmap hg,
        hermitianGeometricZeroPoleDivisor_constant p s b hb0, zero_add]
  · rintro ⟨h, hh, hpower, hdiv⟩
    rw [← hpower, hermitianGeometricZeroPoleDivisor_pow p s h hh n, hdiv]

/-- The explicit Frobenius tangent relation lifts every matching divisor power to a function power. -/
theorem hermitianGeometric_exists_pow_of_frobenius_principal
    (D : HermitianGeometricPoint p s →₀ ℤ)
    (hFr : hermitianGeometricFrobeniusDivisor p s D = D)
    (f : H) (hf : f ≠ 0) (n : ℕ) (hn : 0 < n)
    (hdiv : hermitianGeometricZeroPoleDivisor p s f =
      n • (((Q + 1 : ℕ) : ℤ) • hermitianGeometricDegreeZeroPart p s D)) :
    ∃ h : H, h ≠ 0 ∧ h ^ n = f ∧ hermitianGeometricZeroPoleDivisor p s h =
      ((Q + 1 : ℕ) : ℤ) • hermitianGeometricDegreeZeroPart p s D := by
  let g : H := (hermitianGeometricTangentProduct p s D : H)
  have hg : g ≠ 0 := Units.ne_zero (hermitianGeometricTangentProduct p s D)
  have hgdiv : hermitianGeometricZeroPoleDivisor p s g =
      ((Q + 1 : ℕ) : ℤ) • hermitianGeometricDegreeZeroPart p s D :=
    hermitianGeometricTangentProduct_divisor_of_frobenius_fixed p s D hFr
  have hrelation : hermitianGeometricZeroPoleDivisor p s f =
      n • hermitianGeometricZeroPoleDivisor p s g := by
    rw [hgdiv]
    exact hdiv
  obtain ⟨h, hh, hpower, hhdiv⟩ :=
    (hermitianGeometric_principal_power_iff p s f g hf hg n hn).mp hrelation
  exact ⟨h, hh, hpower, hhdiv.trans hgdiv⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
