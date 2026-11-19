import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositePrimeExcursionsOnOneFixedBand

/-!
# Reciprocal-square weights on joint prime excursions

The duality of a weight and its reciprocal in the quadratic Muckenhoupt
condition (Fang–Phan, Proposition 2.2) gives an exact price for replacing
the numerator weight by a constant. The price is a variance of the
numerators themselves and has a uniform bound on every multiplicative band.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Quadratic mass of a finite set of numerators. -/
def numeratorSquareMass (S : Finset ℕ) : ℝ := ∑ H ∈ S, (H:ℝ)^2

/-- The reciprocal-square mass occurring in the joint excursion moment. -/
def numeratorInverseMass (S : Finset ℕ) : ℝ := ∑ H ∈ S, 1/(H:ℝ)^2

private theorem reciprocal_cross {H J : ℕ} (hH : 0 < H) (hJ : 0 < J) :
    (((H:ℝ)^2-(J:ℝ)^2)/((H:ℝ)*J))^2 =
      (H:ℝ)^2*(1/(J:ℝ)^2) + (J:ℝ)^2*(1/(H:ℝ)^2) - 2 := by
  field_simp [Nat.cast_ne_zero.mpr hH.ne' (R:=ℝ), Nat.cast_ne_zero.mpr hJ.ne' (R:=ℝ)]
  ring

/-- Twice the unnormalized quadratic weight defect is the sum of squared
pairwise distortions. This identity includes the empty set. -/
theorem numerator_weight_defect (S : Finset ℕ) (hS : ∀ H ∈ S, 0 < H) :
    ∑ H ∈ S, ∑ J ∈ S, (((H:ℝ)^2-(J:ℝ)^2)/((H:ℝ)*J))^2 =
      2*(numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2) := by
  have inner (H : ℕ) (hH : H ∈ S) :
      ∑ J ∈ S, (((H:ℝ)^2-(J:ℝ)^2)/((H:ℝ)*J))^2 =
        (H:ℝ)^2*numeratorInverseMass S + numeratorSquareMass S*(1/(H:ℝ)^2) - S.card*2 := by
    rw [sum_congr rfl (fun J hJ => reciprocal_cross (hS H hH) (hS J hJ)),
      sum_sub_distrib,sum_add_distrib,← mul_sum,← sum_mul,sum_const,nsmul_eq_mul]
    rfl
  rw [sum_congr rfl inner,sum_sub_distrib,sum_add_distrib,← sum_mul,← mul_sum,sum_const,nsmul_eq_mul]
  change numeratorSquareMass S * numeratorInverseMass S + numeratorSquareMass S * numeratorInverseMass S -
    (S.card:ℝ)*(S.card*2) = _
  ring

/-- Uniform bound for the distortion in a multiplicative numerator band.
The constant depends only on its two endpoints; squaring their difference
makes the deviation quadratic on short relative bands. -/
theorem numerator_band_distortion (S : Finset ℕ) {a b : ℝ} (ha : 0 < a)
    (hS : ∀ H ∈ S, a ≤ (H:ℝ) ∧ (H:ℝ) ≤ b) :
    4*(a*b)^2*(numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2) ≤
      (S.card:ℝ)^2*(b^2-a^2)^2 := by
  let P := numeratorSquareMass S
  let Q := numeratorInverseMass S
  have hp : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hq : 0 ≤ Q := sum_nonneg fun _ _ => by positivity
  have site (H : ℕ) (hH : H ∈ S) :
      (H:ℝ)^2+(a*b)^2*(1/(H:ℝ)^2) ≤ a^2+b^2 := by
    obtain ⟨hl,hu⟩ := hS H hH
    have hh := ha.trans_le hl
    have hx := mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha.le hl 2))
      (sub_nonneg.mpr (pow_le_pow_left₀ hh.le hu 2))
    field_simp [hh.ne']
    nlinarith only [hx]
  have h := sum_le_sum site
  rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul] at h
  change P+(a*b)^2*Q ≤ S.card*(a^2+b^2) at h
  have hs := mul_self_le_mul_self (add_nonneg hp (mul_nonneg (sq_nonneg _) hq)) h
  change 4*(a*b)^2*(P*Q-(S.card:ℝ)^2) ≤ _
  nlinarith only [hs,sq_nonneg (P-(a*b)^2*Q)]

/-- Exact covariance price of replacing reciprocal-square mass by counting
mass. Only the centered part of the observable contributes to the error. -/
theorem numerator_counting_covariance (S : Finset ℕ) (hS : ∀ H ∈ S, 0 < H) (g : ℕ → ℝ) (c : ℝ) :
    (numeratorInverseMass S*(∑ H ∈ S, g H) - S.card*(∑ H ∈ S, g H/(H:ℝ)^2))^2 ≤
      (∑ H ∈ S, ((g H-c)/(H:ℝ))^2) * (numeratorInverseMass S *
        (numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2)) := by
  let Q := numeratorInverseMass S
  let n : ℝ := S.card
  let x (H : ℕ) := (g H-c)/(H:ℝ)
  let y (H : ℕ) := Q*(H:ℝ)-n/(H:ℝ)
  have cross (H : ℕ) (hH : H ∈ S) :
      x H*y H = Q*g H - n*(g H/(H:ℝ)^2) - Q*c + n*c*(1/(H:ℝ)^2) := by
    dsimp only [x,y]
    field_simp [Nat.cast_ne_zero.mpr (hS H hH).ne' (R:=ℝ)]
    ring
  have yy (H : ℕ) (hH : H ∈ S) :
      y H^2 = Q^2*(H:ℝ)^2 - 2*Q*n + n^2*(1/(H:ℝ)^2) := by
    dsimp only [y]
    field_simp [Nat.cast_ne_zero.mpr (hS H hH).ne' (R:=ℝ)]
    ring
  have dot : (∑ H ∈ S, x H*y H) = Q*(∑ H ∈ S, g H)-n*(∑ H ∈ S, g H/(H:ℝ)^2) := by
    rw [sum_congr rfl cross,sum_add_distrib,sum_sub_distrib,sum_sub_distrib,
      ← mul_sum,← mul_sum,← mul_sum,sum_const,nsmul_eq_mul]
    change _ - n*(Q*c) + n*c*Q = _
    ring
  have cost : (∑ H ∈ S, y H^2) = Q*(numeratorSquareMass S*Q-n^2) := by
    rw [sum_congr rfl yy,sum_add_distrib,sum_sub_distrib,← mul_sum,← mul_sum,sum_const,nsmul_eq_mul]
    change Q^2*numeratorSquareMass S - n*(2*Q*n) + n^2*Q = _
    ring
  have cs := sum_mul_sq_le_sq_mul_sq S x y
  rw [dot,cost] at cs
  exact cs

/-- On the actual set of joint excursions, a constant raw product has zero
counting-replacement error. In general its centered weighted second moment
and the geometric spread of the eligible numerators pay for the error. -/
theorem opposite_prime_counting_covariance (left : Bool) (s a g d T : ℝ) (k L : ℕ) (c : ℝ) :
    let S := largeOppositePrimeNumerators left s a g d T k L
    let value (H : ℕ) := (H:ℝ)^2*oppositePrimeProduct left s k L H
    (numeratorInverseMass S*(∑ H ∈ S, value H) -
      S.card*(∑ H ∈ S, oppositePrimeProduct left s k L H))^2 ≤
      (∑ H ∈ S, ((value H-c)/(H:ℝ))^2)*(numeratorInverseMass S*
        (numeratorSquareMass S*numeratorInverseMass S-(S.card:ℝ)^2)) := by
  intro S value
  have hS (H : ℕ) (hH : H ∈ S) : 0 < H := by
    have h := (mem_filter.mp (mem_filter.mp hH).1).2.1
    exact Nat.cast_pos.mp ((Real.exp_pos T).trans_le h)
  have he (H : ℕ) (hH : H ∈ S) : value H/(H:ℝ)^2=oppositePrimeProduct left s k L H :=
    mul_div_cancel_left₀ _ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (hS H hH).ne'))
  have hh := numerator_counting_covariance S hS value c
  rw [sum_congr rfl he] at hh
  exact hh

#print axioms numerator_weight_defect
#print axioms numerator_band_distortion
#print axioms numerator_counting_covariance
#print axioms opposite_prime_counting_covariance
end GaloisForLFunctions.ExclusionOfTheCriticalState
