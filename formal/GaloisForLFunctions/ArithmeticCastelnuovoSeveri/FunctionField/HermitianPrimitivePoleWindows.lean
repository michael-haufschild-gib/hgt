import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianPointClassOrders

/-!
# Exact first pole of a power on the affine Hermitian curve

A nonconstant d-th power regular on the affine curve has pole order at least
dQ at infinity. Powers of the radical coordinate attain equality. In
particular every tangent is primitive, including the tangents whose whole
divisor is divisible by Q+1.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "V" => hermitianGeometricInfinityValuation p s
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "T" => hermitianGeometricTangentFunction p s

/-- A positive pole at infinity of an affine regular d-th power has order at least dQ. -/
theorem hermitianPower_pole_lower (g : H) (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hf : ∀ w : HeightOneSpectrum B, w.valuation H (g^d) ≤ 1)
    (hi : V (g^d) = WithZero.exp (m:ℤ)) : d*Q ≤ m := by
  have hg : g ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne', map_zero] at hi
    exact WithZero.exp_ne_zero hi.symm
  have hV : V g ≠ 0 := (map_ne_zero _).2 hg
  let k := WithZero.log (V g)
  have hk : V g = WithZero.exp k := (WithZero.exp_log hV).symm
  have hkm : (d:ℤ)*k = m := by
    rw [map_pow, hk, ← WithZero.exp_nsmul, nsmul_eq_mul] at hi
    exact WithZero.exp_injective hi
  have hreg (w : HeightOneSpectrum B) : w.valuation H g ≤ 1 := by
    by_contra! h
    have he := hf w
    rw [map_pow] at he
    exact (one_lt_pow₀ h hd.ne').not_ge he
  have hQ : 0 < Q := pow_pos (Fact.out : p.Prime).pos _
  have hgap : (Q:ℤ) ≤ k := by
    by_contra! ht
    have hl : V g ≤ WithZero.exp ((Q-1:ℕ):ℤ) := by
      rw [hk,WithZero.exp_le_exp,Nat.cast_sub hQ,Nat.cast_one,Nat.cast_pow]
      omega
    obtain ⟨c,hc⟩ := hermitianGeometric_constant_of_pole_lt p s g (Q-1) (by omega) hreg hl
    have hc₀ : c ≠ 0 := fun he => hg (hc.trans (he ▸ map_zero _))
    rw [hc, hermitianGeometricInfinityValuation_constant p s c hc₀, ← WithZero.exp_zero] at hk
    have he := WithZero.exp_injective hk
    rw [← he, mul_zero] at hkm
    omega
  exact_mod_cast (mul_le_mul_of_nonneg_left hgap (Int.natCast_nonneg d)).trans_eq hkm

/-- Among positive pole orders of affine regular d-th powers, the least is exactly dQ. -/
theorem hermitianPower_first_pole (d : ℕ) (hd : 0 < d) :
    IsLeast {m : ℕ | 0 < m ∧ ∃ g : H,
      (∀ w : HeightOneSpectrum B, w.valuation H (g^d) ≤ 1) ∧
        V (g^d) = WithZero.exp (m:ℤ)} (d*Q) := by
  refine ⟨⟨Nat.mul_pos hd (pow_pos (Fact.out : p.Prime).pos _),z,?_,?_⟩,?_⟩
  · intro w
    rw [map_pow, ← hermitianGeometricIntegralRadical_coe]
    exact pow_le_one₀ zero_le (w.valuation_le_one _)
  · rw [map_pow, hermitianGeometricInfinityValuation_radical, ← WithZero.exp_nsmul,
      nsmul_eq_mul, Nat.cast_mul]
  · rintro m ⟨hm,g,hf,hi⟩
    exact hermitianPower_pole_lower p s g d m hd hm hf hi

/-- No geometric tangent function is a proper power in the actual function field. -/
theorem hermitianGeometricTangent_powerFree (P : HermitianAffinePoint p s E) (d : ℕ)
    (hd : 2 ≤ d) (g : H) : g^d ≠ T P := by
  intro he
  have hreg (w : HeightOneSpectrum B) : w.valuation H (g^d) ≤ 1 := by
    rw [he, hermitianGeometricClosedPoint_valuation, hermitianGeometricPointValuation_tangent_all,
      ← WithZero.exp_zero, WithZero.exp_le_exp]
    exact neg_nonpos.mpr (Int.natCast_nonneg _)
  have hle := hermitianPower_pole_lower p s g d (Q+1) (by omega) (Nat.succ_pos _) hreg
    (he ▸ hermitianGeometricInfinityValuation_tangent p s P)
  have hQ : 1 < Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hlo := Nat.mul_le_mul_right Q hd
  omega

#print axioms hermitianPower_pole_lower
#print axioms hermitianPower_first_pole
#print axioms hermitianGeometricTangent_powerFree

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
