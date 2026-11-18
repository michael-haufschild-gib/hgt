import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerExtensionCountSequence

/-!
# The two residue classes in the square contacts of a Kummer curve

In extension degree 2e the square contact is the point count in degree e.
Remove the two known poles and divide by the square-root field size to the
power e. The resulting endpoint kernel has two real residue classes with
opposite signs. This holds for literal rational-place counts over every
extension and identifies the involution needed for a positive pairing.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open Finset ArithmeticCastelnuovoSeveri ArithmeticHarmonicAnalysis

variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)

local notation "s" => kummerSquareIndex d n
local notation "Q" => p ^ (s+1)
local notation "K" => SquareConstantField p s
local notation "q" => p ^ (d+1)
local notation "R" => kummerExponent q r
local notation "c₀" => (kummerTraceConstant p s)⁻¹ ^ R
local notation "g" => Module.finrank K (globalRegularDifferentials K (SquareKummerField p s c₀ (q-2) R))

/-- Primitive square-contact trace in extension degree m. A square ratio
contributes only in even degree, where its root has degree m/2. -/
def kummerSquareTrace (m : ℕ) : ℝ :=
  if m%2=0 then
    ((((Q : ℕ) : ℝ)^2)^(m/2) + 1 - primePowerKummerExtensionPointCount p d n r (m/2)) /
      ((Q : ℕ) : ℝ)^(m/2)
  else 0

private theorem square_trace_even (e : ℕ) (he : 0 < e) :
    kummerSquareTrace p d n r (2*e) = (2*g : ℕ)*(-1 : ℝ)^e := by
  letI : NeZero e := ⟨he.ne'⟩
  have hreal : (primePowerKummerExtensionPointCount p d n r e : ℝ) =
      (((Q : ℕ) : ℝ)^2)^e + 1 - (2*g : ℕ)*(-((Q : ℕ) : ℝ))^e := by
    apply Complex.ofReal_injective
    push_cast
    exact primePowerKummerExtensionPointCount_eq p d n r e
  have hQ : (0 : ℝ) < (Q : ℕ) := Nat.cast_pos.mpr (pow_pos (Fact.out : p.Prime).pos _)
  simp only [kummerSquareTrace,Nat.mul_mod_right,Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),if_true]
  rw [hreal, neg_eq_neg_one_mul, mul_pow]
  field_simp
  <;> ring

/-- The alternating moment on one of the two residue classes. -/
def parityMoment (b : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ S, if i%2=b then w i*(-1 : ℝ)^(i/2) else 0

private theorem square_trace_lag (L i j : ℕ) :
    kummerSquareTrace p d n r (4*(L+1)+i+j) =
      (2*g : ℕ) * (((if i%2=0 then (-1 : ℝ)^(i/2) else 0) *
                     (if j%2=0 then (-1 : ℝ)^(j/2) else 0)) -
                    ((if i%2=1 then (-1 : ℝ)^(i/2) else 0) *
                     (if j%2=1 then (-1 : ℝ)^(j/2) else 0))) := by
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have he : 4*(L+1)+i+j = 2*(2*(L+1)+i/2+j/2) := by omega
    rw [he,square_trace_even p d n r _ (by omega)]
    simp [hi,hj,pow_add,pow_mul]
  · have ho : (4*(L+1)+i+j)%2 ≠ 0 := by omega
    simp [kummerSquareTrace,hi,hj,ho]
  · have ho : (4*(L+1)+i+j)%2 ≠ 0 := by omega
    simp [kummerSquareTrace,hi,hj,ho]
  · have he : 4*(L+1)+i+j = 2*(2*(L+1)+i/2+j/2+1) := by omega
    rw [he,square_trace_even p d n r _ (by omega)]
    simp [hi,hj,pow_add,pow_mul]

/-- Gluing any two signed families of upper endpoints yields the difference
of their two parity moments. The result is uniform in separation and support.
Changing the sign of the odd part in the second divisor produces a sum of
squares on the diagonal. -/
theorem kummer_mixed_square_trace (L : ℕ) (S T : Finset ℕ) (u v : ℕ → ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, u i*v j*kummerSquareTrace p d n r (4*(L+1)+i+j)) =
      (2*g : ℕ)*(parityMoment 0 S u*parityMoment 0 T v -
                 parityMoment 1 S u*parityMoment 1 T v) := by
  simp only [parityMoment, mul_sub, sum_mul, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [square_trace_lag]
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
    simp [hi,hj] <;> ring

#print axioms kummer_mixed_square_trace

end GaloisForLFunctions.SignedArithmeticCorrespondences
