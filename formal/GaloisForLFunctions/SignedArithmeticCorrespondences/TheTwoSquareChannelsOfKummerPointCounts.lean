import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerClosedPointDegrees

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
open ArithmeticCastelnuovoSeveri.PolynomialOrderClosedPoints

variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)

local notation "s" => kummerSquareIndex d n
local notation "Q" => p ^ (s+1)
local notation "K" => SquareConstantField p s
local notation "A" => PrimePowerKummerThreePointAffineNormalization p d n r
local notation "q" => p ^ (d+1)
local notation "R" => kummerExponent q r
local notation "c₀" => (kummerTraceConstant p s)⁻¹ ^ R
local notation "g" => Module.finrank K (globalRegularDifferentials K (SquareKummerField p s c₀ (q-2) R))

/-- Raw square contact of the closed places in positive degree m. The
rational place at infinity has degree one. A finite closed place v enters
with its full degree precisely when its local multiplicity is even. -/
def kummerClosedSquareContact (m : ℕ) : ℕ :=
  if m = 0 then 0 else (if 2 ∣ m then 1 else 0) +
    ∑ v ∈ placesDegreeLe K A p (m/2),
      if 2*placeDegree K A v ∣ m then placeDegree K A v else 0

/-- Extracting all even local powers of the closed places recovers the
literal extension point count at half the original degree. -/
theorem kummerClosedSquareContact_even (e : ℕ) [NeZero e] :
    kummerClosedSquareContact p d n r (2*e) = primePowerKummerExtensionPointCount p d n r e := by
  rw [primePowerKummerExtensionPointCount_eq_closed_degree_sum]
  simp only [kummerClosedSquareContact,if_neg (Nat.mul_ne_zero (Nat.succ_ne_zero 1) (NeZero.ne e)),dvd_mul_right,if_true,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)]

/-- Primitive square-contact trace in extension degree m. A square ratio
contributes only in even degree, where its root has degree m/2. -/
def kummerSquareTrace (m : ℕ) : ℝ :=
  if 0 < m ∧ m % 2 = 0 then
    ((((Q : ℕ) : ℝ)^2)^(m/2) + 1 - kummerClosedSquareContact p d n r m) /
      ((Q : ℕ) : ℝ)^(m/2)
  else 0

private theorem square_trace_even (e : ℕ) (he : 0 < e) :
    kummerSquareTrace p d n r (2*e) = (2*g : ℕ)*(-1 : ℝ)^e := by
  letI : NeZero e := ⟨he.ne'⟩
  have hreal : (primePowerKummerExtensionPointCount p d n r e : ℝ) =
      (((Q : ℕ) : ℝ)^2)^e + 1 - (2*g : ℕ)*(-((Q : ℕ) : ℝ))^e := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_natCast, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Nat.cast_pow] using
      primePowerKummerExtensionPointCount_eq p d n r e
  have hQ : (0 : ℝ) < (Q : ℕ) := Nat.cast_pos.mpr (pow_pos (Fact.out : p.Prime).pos _)
  have hm : 0<2*e ∧ (2*e)%2=0 := ⟨Nat.mul_pos (by norm_num) he,Nat.mul_mod_right 2 e⟩
  rw [kummerSquareTrace,if_pos hm,Nat.mul_div_cancel_left e (by norm_num : 0<2),
    kummerClosedSquareContact_even,hreal,show -((Q:ℕ):ℝ) = (-1)*((Q:ℕ):ℝ) by ring,mul_pow]
  field_simp [pow_ne_zero e hQ.ne']
  ring

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
  simp only [parityMoment, sum_mul_sum]
  simp only [mul_sub, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [square_trace_lag]
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
    simp [hi,hj] <;> ring

/-- Dualizing the odd residue class gives an effective square on the actual
extension counts. Both parity moments survive at arbitrary support size. -/
theorem kummer_dual_square_trace (L : ℕ) (S : Finset ℕ) (u : ℕ → ℝ) :
    let v := fun j => if j%2=0 then u j else -u j
    (∑ i ∈ S, ∑ j ∈ S, u i*v j*kummerSquareTrace p d n r (4*(L+1)+i+j)) =
      (2*g : ℕ)*(parityMoment 0 S u ^ 2 + parityMoment 1 S u ^ 2) := by
  intro v
  have hev : parityMoment 0 S v = parityMoment 0 S u := by
    apply sum_congr rfl
    intro j _
    by_cases h : j%2=0 <;> simp [v,h]
  have hod : parityMoment 1 S v = -parityMoment 1 S u := by
    unfold parityMoment
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [v,h]
  rw [kummer_mixed_square_trace,hev,hod]
  ring

#print axioms kummerClosedSquareContact_even
#print axioms kummer_mixed_square_trace
#print axioms kummer_dual_square_trace

/-- Without the odd duality sign, effectivity on every divisor at any fixed
extension block is equivalent to the explicit genus-zero divisibility law. -/
theorem kummer_unmodified_effective_iff (L : ℕ) :
    (∀ (S : Finset ℕ) (u : ℕ → ℝ), 0 ≤ ∑ i ∈ S, ∑ j ∈ S,
      u i*u j*kummerSquareTrace p d n r (4*(L+1)+i+j)) ↔ Q+1 ∣ R := by
  rw [← squareKummer_regularDifferential_finrank_eq_zero_iff p s c₀ d r]
  constructor
  · intro h
    have hh := h {1} (fun _ => 1)
    rw [kummer_mixed_square_trace] at hh
    have hneg : (2*g:ℕ) ≤ (0:ℝ) := by
      norm_num [parityMoment] at hh ⊢
      linarith only [hh]
    have hn : 2*g ≤ 0 := by exact_mod_cast hneg
    omega
  · intro hg S u
    rw [kummer_mixed_square_trace,hg]
    simp

#print axioms kummer_unmodified_effective_iff

/-- Taking branch exponent one gives genuine negative self-intersections in
every extension block, over each of the square constant fields in the family. -/
theorem kummer_has_negative_ordinary_square (L : ℕ) :
    ∃ (S : Finset ℕ) (u : ℕ → ℝ), (∑ i ∈ S, ∑ j ∈ S,
      u i*u j*kummerSquareTrace p d n 1 (4*(L+1)+i+j)) < 0 := by
  have hQ : 0 < Q := pow_pos (Fact.out : p.Prime).pos _
  have hdiv : ¬ Q+1 ∣ kummerExponent q 1 := by
    simp only [kummerExponent,sum_range_one,pow_zero,Nat.dvd_one]
    omega
  have h := mt (kummer_unmodified_effective_iff p d n 1 L).mp hdiv
  push Not at h
  exact h

#print axioms kummer_has_negative_ordinary_square

end GaloisForLFunctions.SignedArithmeticCorrespondences
