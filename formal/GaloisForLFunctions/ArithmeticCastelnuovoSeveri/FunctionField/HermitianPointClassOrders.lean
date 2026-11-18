import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricProductFormula

/-!
# Orders of geometric Hermitian Abel–Jacobi points

The first possible positive pole order at infinity is Q. Together with
prime-to-characteristic torsion this puts every affine point class at
order at least Q+1. At every square-field point the tangent attains this
bound. Square Frobenius acts by minus Q on all the point classes.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain Function
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "Pts" => HermitianAffinePoint p s E
local notation "Div" => HermitianGeometricPlaceDivisor p s
local notation "F" => hermitianFrobeniusPoint p s E
local notation "V" => hermitianGeometricInfinityValuation p s
local notation "prin" => AddMonoidHom.range (hermitianGeometricPrincipalDivisorHom p s)
local notation "cl" => hermitianGeometricClass p s
local notation "Δ" => hermitianGeometricPointDifference p s
local notation "∞ₕ" => ((0,1) : Div)

/-- The first Q-1 possible pole orders at geometric infinity give only constant sections. -/
theorem hermitianGeometric_constant_of_pole_lt (f : H) (m : ℕ) (hm : m < Q)
    (hf : ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1) (hi : V f ≤ WithZero.exp (m : ℤ)) :
    ∃ c : E, f = algebraMap E H c := by
  apply hermitianGeometric_constant_of_regular p s f hf
  obtain ⟨a, ha, hb⟩ := hermitianGeometric_exists_bounded_polynomial_expansion p s f m hf hi
  rw [ha, ← WithZero.exp_zero]
  apply (hermitianGeometricPolynomialExpansion_pole_bound_iff p s a 0).2
  intro i h
  have hw := hb i h
  have hi₀ : i.val = 0 := by
    by_contra hn
    have hle := Nat.mul_le_mul_left Q (Nat.one_le_iff_ne_zero.mpr hn)
    omega
  have ha₀ : (a i).natDegree = 0 := by
    by_contra hn
    have hle := Nat.mul_le_mul_left (Q+1) (Nat.one_le_iff_ne_zero.mpr hn)
    omega
  simp only [hi₀, ha₀, mul_zero, zero_add, le_refl]

/-- The Abel–Jacobi class of an actual geometric affine point with infinity as origin. -/
def hermitianAffineClass (P : Pts) : HermitianGeometricPicard p s := cl (Δ (some P))
local notation "J" => hermitianAffineClass p s

/-- The Frobenius endomorphism acts on point classes by the integer -Q. -/
theorem hermitianAffineClass_frobenius (P : Pts) : J (F P) = -(Q • J P) := by
  have h := hermitianGeometricTangentUnit_divisor p s (some P)
  have he : ((Q:ℕ):ℤ) • Δ (some P) + Δ (some (F P)) ∈ prin := ⟨_, h⟩
  have hz := (QuotientAddGroup.eq_zero_iff _).2 he
  change cl (_ + _) = 0 at hz
  rw [map_add, map_zsmul, natCast_zsmul] at hz
  change Q • J P + J (F P) = 0 at hz
  calc
    J (F P) = -(Q • J P) + (Q • J P + J (F P)) := by abel
    _ = -(Q • J P) := by rw [hz, add_zero]

/-- The full square-Frobenius orbit maps to an integer-power orbit in the Picard group. -/
theorem hermitianAffineClass_iterate (P : Pts) (n : ℕ) :
    J (F^[n] P) = (-((Q:ℕ):ℤ))^n • J P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', hermitianAffineClass_frobenius, ih]
    simp only [pow_succ' (-((Q:ℕ):ℤ)) n, mul_smul, neg_smul, natCast_zsmul]

/-- The order of every geometric affine point class is positive and prime to the characteristic. -/
theorem hermitianAffineClass_order_coprime (P : Pts) :
    0 < addOrderOf (J P) ∧ (addOrderOf (J P)).Coprime p := by
  let D := Finsupp.single (some P) (1 : ℤ)
  have he : hermitianGeometricDegreeZeroPart p s D = Δ (some P) := by
    simp [hermitianGeometricDegreeZeroPart, D]
  obtain ⟨n,hn,hp,u,hu⟩ := hermitianDegreeZeroPart_primeToChar_principal p s D
  rw [he] at hu
  have hz : n • J P = 0 := by
    change n • cl _ = 0
    rw [← map_nsmul]
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨u,hu⟩
  exact ⟨addOrderOf_pos_iff.mpr (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n,hn,hz⟩),
    hp.of_dvd_left (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz)⟩

/-- No positive multiple strictly smaller than the first nongap can be principal. -/
theorem hermitianAffineClass_nsmul_ne_zero_of_lt (P : Pts) (n : ℕ) (hn : 0 < n) (hlt : n < Q) :
    n • J P ≠ 0 := by
  intro hz
  change n • cl _ = 0 at hz
  rw [← map_nsmul] at hz
  obtain ⟨u, hu⟩ := (QuotientAddGroup.eq_zero_iff _).1 hz
  let f : H := (u.toMul : Hˣ)
  have hpoint := hermitianGeometricPointDifference_eq p s (some P)
  have he : 0 ≤ hermitianGeometricZeroPoleDivisor p s f + (n : ℤ) • ∞ₕ := by
    change 0 ≤ hermitianGeometricPrincipalDivisorHom p s u + _
    rw [hu, hpoint, nsmul_sub, natCast_zsmul, sub_add_cancel]
    exact nsmul_nonneg (hermitianGeometricPointDivisor_nonneg p s (some P)) n
  obtain ⟨hf, hi⟩ := (hermitianGeometricZeroPoleDivisor_add_infinity_nonneg_iff
    p s f u.toMul.ne_zero n).1 he
  obtain ⟨c, hc⟩ := hermitianGeometric_constant_of_pole_lt p s f n hlt hf hi
  have hcn : c ≠ 0 := fun he => u.toMul.ne_zero (hc.trans (he ▸ map_zero _))
  have hdiv := hermitianGeometricZeroPoleDivisor_constant p s c hcn
  rw [← hc] at hdiv
  change hermitianGeometricPrincipalDivisorHom p s u = 0 at hdiv
  rw [hu] at hdiv
  have hval : n • (-1 : ℤ) = 0 := congrArg Prod.snd hdiv
  rw [nsmul_eq_mul, mul_neg_one] at hval
  omega

/-- Every geometric affine point class has order at least Q+1. -/
theorem hermitianAffineClass_order_lower (P : Pts) : Q+1 ≤ addOrderOf (J P) := by
  obtain ⟨hpos,hcop⟩ := hermitianAffineClass_order_coprime p s P
  have hle : Q ≤ addOrderOf (J P) := le_of_not_gt fun h =>
    hermitianAffineClass_nsmul_ne_zero_of_lt p s P _ hpos h (addOrderOf_nsmul_eq_zero _)
  have hne : addOrderOf (J P) ≠ Q := by
    intro h
    rw [h] at hcop
    apply (Fact.out : p.Prime).not_dvd_one
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (dvd_pow dvd_rfl (Nat.succ_ne_zero s)) dvd_rfl
  omega

/-- Every square-field affine point attains the universal lower bound exactly. -/
theorem hermitianAffineClass_order_of_fixed (P : Pts) (h : F P = P) :
    addOrderOf (J P) = Q+1 := by
  have hf := hermitianAffineClass_frobenius p s P
  rw [h] at hf
  have hz : (Q+1) • J P = 0 := by
    rw [succ_nsmul]
    exact (congrArg (fun v => Q • J P + v) hf).trans (add_neg_cancel _)
  exact Nat.le_antisymm (Nat.le_of_dvd (Nat.succ_pos _) (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz))
    (hermitianAffineClass_order_lower p s P)

#print axioms hermitianGeometric_constant_of_pole_lt
#print axioms hermitianAffineClass_frobenius
#print axioms hermitianAffineClass_iterate
#print axioms hermitianAffineClass_order_coprime
#print axioms hermitianAffineClass_nsmul_ne_zero_of_lt
#print axioms hermitianAffineClass_order_lower
#print axioms hermitianAffineClass_order_of_fixed

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
