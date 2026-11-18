import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianPlaneContactOrders

/-!
# First nongap at every geometric affine Hermitian point

Multiplication by the tangent moves a single pole of order less than Q
into the plane linear system. The remaining contacts either specify a
double point or the secant through the point and its distinct Frobenius
image. Both characterize the tangent. The ratio of a vertical line to the
tangent realizes the sharp boundary at every point.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "φ" => algebraMap E H
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "T" => hermitianGeometricTangentFunction p s
local notation "Pts" => HermitianAffinePoint p s E
local notation "V" => hermitianGeometricPointValuation p s
local notation "W" => hermitianGeometricInfinityValuation p s
local notation "F" => hermitianFrobeniusPoint p s E

private theorem exp_neg_one_small : WithZero.exp (-1:ℤ) < 1 := by
  rw [← WithZero.exp_zero,WithZero.exp_lt_exp]; omega

private theorem tangent_finite_le (P U : Pts) : V U (T P) ≤ 1 := by
  rw [hermitianGeometricPointValuation_tangent_all,← WithZero.exp_zero,WithZero.exp_le_exp]
  exact neg_nonpos.mpr (Int.natCast_nonneg _)

/-- Two distinct Frobenius contacts cut out the tangent inside the complete plane linear system. -/
theorem hermitianPlaneSection_twoContacts (P : Pts) (hP : F P ≠ P) (f : H)
    (hf : ∀ w : HeightOneSpectrum B, w.valuation H f ≤ 1) (hi : W f ≤ WithZero.exp ((Q+1:ℕ):ℤ))
    (h₁ : V P f < 1) (h₂ : V (F P) f < 1) : ∃ c : E, f = φ c*T P := by
  obtain ⟨a,b,c,he⟩ := hermitianPlaneSections_adapted p s P f hf hi
  have ha : a=0 := by
    by_contra h
    rw [he,hermitianPlaneSection_value,if_pos h] at h₁
    exact lt_irrefl _ h₁
  rw [ha,map_zero,zero_add] at he
  have hb : b=0 := by
    by_contra h
    have hx : (F P).val.1 ≠ P.val.1 := fun h => hP ((hermitianFrobeniusPoint_eq_self_iff p s E P).2 h)
    have hz : V (F P) (φ b*(z-φ P.val.1)) = 1 := by
      rw [map_mul,hermitianGeometricPointValuation_constant p s _ b h,
        hermitianGeometricPointValuation_radical_sub_of_ne p s _ _ hx,one_mul]
    have ht : V (F P) (φ c*T P) < 1 := by
      by_cases hc : c=0
      · rw [hc,map_zero,zero_mul,map_zero]; exact zero_lt_one
      · rw [map_mul,hermitianGeometricPointValuation_constant p s _ c hc,one_mul,
          hermitianGeometricPointValuation_tangent_frobenius p s P hP]
        exact exp_neg_one_small
    rw [he,(V (F P)).map_add_eq_of_lt_left (ht.trans_eq hz.symm),hz] at h₂
    exact lt_irrefl _ h₂
  exact ⟨c, by simpa only [hb,map_zero,zero_mul,zero_add] using he⟩

/-- Functions regular away from the indicated affine point, with its pole bounded by m. -/
def hermitianSinglePoleBound (P : Pts) (m : ℕ) (f : H) : Prop :=
  W f ≤ 1 ∧ V P f ≤ WithZero.exp (m:ℤ) ∧ ∀ U : Pts, U ≠ P → V U f ≤ 1

/-- Every one-point pole space below Q consists of constants, including at non-rational points. -/
theorem hermitianSinglePole_constant_of_lt (P : Pts) (m : ℕ) (hm : m<Q) (f : H)
    (hf : hermitianSinglePoleBound p s P m f) : ∃ c : E, f = φ c := by
  let g := f*T P
  have hp (n : ℕ) (h : V P (T P) = WithZero.exp (-(n:ℤ))) :
      V P g ≤ WithZero.exp ((m:ℤ)-n) := by
    change V P (f*T P) ≤ _
    rw [map_mul,h,sub_eq_add_neg,WithZero.exp_add]
    exact mul_le_mul_left hf.2.1 _
  have ht := hermitianGeometricPointValuation_tangent p s P
  have h₁ : V P g < 1 := by
    by_cases h : P.val.1^(Q*Q) = P.val.1
    · rw [if_pos h] at ht
      exact (hp _ ht).trans_lt (by rw [← WithZero.exp_zero,WithZero.exp_lt_exp]; omega)
    · rw [if_neg h] at ht
      exact (hp _ ht).trans_lt (by rw [← WithZero.exp_zero,WithZero.exp_lt_exp]; omega)
  have hreg (w : HeightOneSpectrum B) : w.valuation H g ≤ 1 := by
    rw [hermitianGeometricClosedPoint_valuation]
    let U := hermitianGeometricClosedPoint p s w
    by_cases h : U=P
    · change V U g ≤ 1; rw [h]; exact h₁.le
    · change V U (f*T P) ≤ 1
      rw [map_mul]
      exact mul_le_one' (hf.2.2 U h) (tangent_finite_le p s P U)
  have hi : W g ≤ WithZero.exp ((Q+1:ℕ):ℤ) := by
    change W (f*T P) ≤ _
    rw [map_mul,hermitianGeometricInfinityValuation_tangent]
    exact mul_le_of_le_one_left' hf.1
  have hline : ∃ c : E, g=φ c*T P := by
    by_cases h : F P=P
    · rw [if_pos ((hermitianFrobeniusPoint_eq_self_iff p s E P).1 h)] at ht
      apply (hermitianPlaneSection_highContact_iff p s P g hreg hi).1
      exact (hp _ ht).trans_lt (by rw [WithZero.exp_lt_exp]; omega)
    · apply hermitianPlaneSection_twoContacts p s P h g hreg hi h₁
      change V (F P) (f*T P) < 1
      rw [map_mul,hermitianGeometricPointValuation_tangent_frobenius p s P h]
      exact (mul_le_of_le_one_left' (hf.2.2 _ h)).trans_lt exp_neg_one_small
  obtain ⟨c,hc⟩ := hline
  exact ⟨c,mul_right_cancel₀ (hermitianGeometricTangentFunction_ne_zero p s P) hc⟩

/-- Projection from the Frobenius point gives an explicit function with unique pole of order Q. -/
def hermitianVerticalOverTangent (P : Pts) : H := (z - φ (F P).val.1) / T P

/-- The vertical-over-tangent ratio has pole order exactly Q at its indicated point. -/
theorem hermitianVerticalOverTangent_at_point (P : Pts) :
    V P (hermitianVerticalOverTangent p s P) = WithZero.exp ((Q:ℕ):ℤ) := by
  rw [hermitianVerticalOverTangent,map_div₀,hermitianGeometricPointValuation_tangent]
  by_cases h : F P=P
  · rw [if_pos ((hermitianFrobeniusPoint_eq_self_iff p s E P).1 h),h,
      hermitianGeometricPointValuation_radical_sub,← WithZero.exp_sub]
    congr 1; omega
  · have hx : P.val.1 ≠ (F P).val.1 := fun he => h ((hermitianFrobeniusPoint_eq_self_iff p s E P).2 he.symm)
    rw [if_neg (fun he => h ((hermitianFrobeniusPoint_eq_self_iff p s E P).2 he)),
      hermitianGeometricPointValuation_radical_sub_of_ne p s P _ hx,one_div,
      ← WithZero.exp_neg,neg_neg]

/-- The same ratio has a simple zero at infinity, independently of the point's field of definition. -/
theorem hermitianVerticalOverTangent_at_infinity (P : Pts) :
    W (hermitianVerticalOverTangent p s P) = WithZero.exp (-1:ℤ) := by
  have hQ := pow_pos (Fact.out : p.Prime).pos (s+1)
  have hc : W (φ (F P).val.1) ≤ 1 := by
    by_cases he : (F P).val.1 = 0
    · rw [he,map_zero,map_zero]; exact zero_le_one
    · exact (hermitianGeometricInfinityValuation_constant p s _ he).le
  have hlt : W (φ (F P).val.1) < W z := hc.trans_lt (by
    rw [hermitianGeometricInfinityValuation_radical,← WithZero.exp_zero,WithZero.exp_lt_exp]
    exact_mod_cast hQ)
  rw [hermitianVerticalOverTangent,map_div₀,(W).map_sub_eq_of_lt_left hlt,
    hermitianGeometricInfinityValuation_radical,hermitianGeometricInfinityValuation_tangent,← WithZero.exp_sub]
  congr 1; omega

/-- Every other finite place is regular for this explicit degree-Q pencil. -/
theorem hermitianVerticalOverTangent_poleBound (P : Pts) :
    hermitianSinglePoleBound p s P Q (hermitianVerticalOverTangent p s P) := by
  refine ⟨(hermitianVerticalOverTangent_at_infinity p s P).le.trans exp_neg_one_small.le,
    (hermitianVerticalOverTangent_at_point p s P).le,?_⟩
  intro U hU
  rw [hermitianVerticalOverTangent,map_div₀]
  by_cases hF : U=F P
  · subst U
    rw [hermitianGeometricPointValuation_radical_sub, hermitianGeometricPointValuation_tangent_frobenius p s P hU,
      div_self WithZero.exp_ne_zero]
  · rw [hermitianGeometricPointValuation_tangent_unit p s P U hU hF,div_one]
    by_cases hx : U.val.1 = (F P).val.1
    · rw [← hx,hermitianGeometricPointValuation_radical_sub]
      exact exp_neg_one_small.le
    · exact (hermitianGeometricPointValuation_radical_sub_of_ne p s U _ hx).le

/-- The first positive nongap of each geometric affine point is Q. -/
theorem hermitianAffinePoint_first_nongap (P : Pts) :
    IsLeast {m : ℕ | 0 < m ∧ ∃ f : H, hermitianSinglePoleBound p s P m f ∧
      V P f = WithZero.exp (m:ℤ)} Q := by
  refine ⟨⟨pow_pos (Fact.out : p.Prime).pos _,hermitianVerticalOverTangent p s P,
    hermitianVerticalOverTangent_poleBound p s P,
    hermitianVerticalOverTangent_at_point p s P⟩,?_⟩
  rintro m ⟨hm,f,hf,he⟩
  by_contra! h
  obtain ⟨c,rfl⟩ := hermitianSinglePole_constant_of_lt p s P m h f hf
  by_cases hc : c=0
  · rw [hc,map_zero,map_zero] at he; exact WithZero.exp_ne_zero he.symm
  · rw [hermitianGeometricPointValuation_constant p s P c hc,← WithZero.exp_zero] at he
    have hz := WithZero.exp_injective he
    omega

#print axioms hermitianPlaneSection_twoContacts
#print axioms hermitianSinglePole_constant_of_lt
#print axioms hermitianVerticalOverTangent_at_point
#print axioms hermitianVerticalOverTangent_at_infinity
#print axioms hermitianVerticalOverTangent_poleBound
#print axioms hermitianAffinePoint_first_nongap

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
