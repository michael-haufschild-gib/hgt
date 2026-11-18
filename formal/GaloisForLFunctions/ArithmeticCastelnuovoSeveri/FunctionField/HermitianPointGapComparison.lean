import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianInfinityPoleWindowRanks
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianPointPoleSemigroups
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianPointClassOrders

/-!
# Moving pole windows between a geometric point and infinity

A principal multiple of P-infinity transfers a one-point pole window into
the infinity window by multiplication. Comparing independent exact pole
orders bounds the number of nongaps at P in every class-period window.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "Pts" => HermitianAffinePoint p s E
local notation "Div" => HermitianGeometricPlaceDivisor p s
local notation "J" => hermitianAffineClass p s
local notation "V" => hermitianGeometricPointValuation p s
local notation "W" => hermitianGeometricInfinityValuation p s
local notation "w" => hermitianGeometricPointPrime p s
local notation "S" => hermitianPointPoleSemigroup p s

/-- Every multiple of a point-class order has a function whose entire zero divisor is nP
and whose entire pole divisor is n times infinity. -/
theorem hermitianPointClass_transfer_function (P : Pts) (n : ℕ) (hn : addOrderOf (J P) ∣ n) :
    ∃ g : Hˣ, W (g:H) = WithZero.exp (n:ℤ) ∧ ∀ U : Pts,
      V U (g:H) = WithZero.exp (if U=P then -(n:ℤ) else 0) := by
  have hz := addOrderOf_dvd_iff_nsmul_eq_zero.mp hn
  change n • hermitianGeometricClass p s (hermitianGeometricPointDifference p s (some P)) = 0 at hz
  rw [← map_nsmul] at hz
  obtain ⟨u,hu⟩ := (QuotientAddGroup.eq_zero_iff _).1 hz
  let g := u.toMul
  refine ⟨g,?_,?_⟩
  · have he := congrArg Prod.snd hu
    change -WithZero.log (W (g:H)) = n • (-1:ℤ) at he
    rw [nsmul_eq_mul,mul_neg_one,neg_inj] at he
    rw [← he,WithZero.exp_log ((map_ne_zero _).2 g.ne_zero)]
  · intro U
    have he := congrArg (fun D : Div => D.1 (w U)) hu
    change -WithZero.log ((w U).valuation H (g:H)) = n • (Finsupp.single (w P) (1:ℤ) (w U)) at he
    rw [hermitianGeometricPointPrime_valuation,nsmul_eq_mul] at he
    rw [← WithZero.exp_log ((map_ne_zero (V U)).2 g.ne_zero)]
    apply congrArg WithZero.exp
    by_cases h : U=P
    · rw [h,Finsupp.single_eq_same,mul_one] at he
      rw [if_pos h,h]; omega
    · have hw : w U ≠ w P := (hermitianGeometricFinitePointEquiv p s).symm.injective.ne h
      rw [Finsupp.single_eq_of_ne hw,mul_zero] at he
      rw [if_neg h]; omega

private theorem transfer_mem {P : Pts} {N d : ℕ} {g f : H}
    (hg : W g = WithZero.exp (N:ℤ)) (hV : ∀ U : Pts, V U g = WithZero.exp (if U=P then -(N:ℤ) else 0))
    (hN : d ≤ N) (hf : hermitianSinglePoleBound p s P d f) :
    g*f ∈ hermitianInfinityPoleWindow p s N := by
  refine ⟨(hermitianGeometric_integral_iff_finite_valuations p s _).2 ?_,?_⟩
  · intro v
    rw [hermitianGeometricClosedPoint_valuation,map_mul,hV]
    let U := hermitianGeometricClosedPoint p s v
    by_cases he : U=P
    · change WithZero.exp (if U=P then -(N:ℤ) else 0) * V U f ≤ 1
      rw [if_pos he,he]
      calc
        _ ≤ WithZero.exp (-(N:ℤ)) * WithZero.exp (d:ℤ) := mul_le_mul_right hf.2.1 _
        _ ≤ 1 := by rw [← WithZero.exp_add,← WithZero.exp_zero,WithZero.exp_le_exp]; omega
    · change WithZero.exp (if U=P then -(N:ℤ) else 0) * V U f ≤ 1
      rw [if_neg he,WithZero.exp_zero,one_mul]; exact hf.2.2 U he
  · rw [map_mul,hg]
    exact mul_le_of_le_one_right' hf.1

/-- A class-period window at P has at most as many distinct pole orders as the same infinity window. -/
theorem hermitianPoint_nongap_count_le (P : Pts) (N : ℕ) (hN : addOrderOf (J P) ∣ N) :
    Nat.card {d : Fin (N+1) // d.val ∈ S P} ≤
      Nat.card {d : Fin (N+1) // d.val ∈ hermitianInfinityOrders p s} := by
  classical
  let I := {d : Fin (N+1) // d.val ∈ S P}
  letI : Fintype I := Fintype.ofFinite _
  obtain ⟨g,hg,hV⟩ := hermitianPointClass_transfer_function p s P N hN
  have hf (d : I) : ∃ f : H, hermitianSinglePoleBound p s P d.val.val f ∧
      V P f = WithZero.exp (d.val.val:ℤ) := d.property
  choose f hbound hval using hf
  let T (d : I) : hermitianInfinityPoleWindow p s N :=
    ⟨(g:H)*f d,transfer_mem p s hg hV (Nat.le_of_lt_succ d.val.isLt) (hbound d)⟩
  have hVf (d : I) : V P ((T d):H) = V P (g:H) * WithZero.exp (d.val.val:ℤ) := by
    change V P ((g:H)*f d) = _
    rw [map_mul,hval]
  have hind : LinearIndependent E (fun d => ((T d):H)) := by
    apply linearIndependent_of_distinct_valuation (V P) (hermitianGeometricPointValuation_constant p s P)
    · intro a b he
      change V P ((T a):H) = V P ((T b):H) at he
      rw [hVf,hVf] at he
      apply Subtype.ext; apply Fin.ext; apply Nat.cast_injective (R := ℤ); apply WithZero.exp_injective
      exact mul_left_cancel₀ ((map_ne_zero _).2 g.ne_zero) he
    · intro d hd
      have hv := hVf d
      rw [hd,map_zero] at hv
      exact (mul_ne_zero ((map_ne_zero _).2 g.ne_zero) WithZero.exp_ne_zero) hv.symm
  have hi : LinearIndependent E T := LinearIndependent.of_comp (hermitianInfinityPoleWindow p s N).subtype hind
  rw [← hermitianInfinityPoleWindow_dimension, Nat.card_eq_fintype_card]
  exact hi.fintype_card_le_finrank

#print axioms hermitianPointClass_transfer_function
#print axioms hermitianPoint_nongap_count_le
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
