import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheRemoteVariationOfTheStateWeights
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw

/-!
# Reciprocal prime intervals at the zero abscissa

Abel summation transfers the upper Chebyshev exponent to ordered intervals
of reciprocal Mangoldt excess, uniformly in the right endpoint.
-/

noncomputable section
open ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

private theorem centeredAbelPrefix_zero_base (j : ℕ) :
    centeredAbelPrefix 0 j = Chebyshev.psi j-j := by
  have h := _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc (Nat.cast_nonneg (α := ℝ) j)
  simp only [Chebyshev.psi_zero,sub_zero,Nat.floor_zero,Nat.floor_natCast] at h
  rw [centeredAbelPrefix,Finset.sum_sub_distrib,← h,Finset.sum_const,Nat.card_Ioc,
    Nat.sub_zero,nsmul_eq_mul,mul_one]

/-- Concavity of the power d majorizes the reciprocal Abel cost by a
telescoping difference at consecutive positive real abscissae. -/
private theorem reciprocal_power_step {d x : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hx : 1 ≤ x) :
    x^(1-d)*(x⁻¹-(x+1)⁻¹) ≤ (x^(-d)-(x+1)^(-d))/d := by
  have hx0 := zero_lt_one.trans_le hx
  have hx1 : 0 < x+1 := by linarith only [hx]
  have hBern := rpow_one_add_le_one_add_mul_self (s := -(x+1)⁻¹)
    (by have h := inv_le_one_of_one_le₀ (by linarith only [hx] : 1 ≤ x+1); linarith only [h]) hd.le hd1
  rw [show 1 + -(x+1)⁻¹ = x/(x+1) by field_simp; ring,Real.div_rpow hx0.le hx1.le] at hBern
  have hmult := mul_le_mul_of_nonneg_left hBern (Real.rpow_nonneg hx0.le (-d))
  have hcancel : x^(-d)*(x^d/(x+1)^d)=(x+1)^(-d) := by
    rw [← mul_div_assoc,← Real.rpow_add hx0,neg_add_cancel,Real.rpow_zero,Real.rpow_neg hx1.le,one_div]
  rw [hcancel] at hmult
  have hleft : x^(1-d)*(x⁻¹-(x+1)⁻¹) = x^(-d)*(x+1)⁻¹ := by
    rw [sub_eq_add_neg (1:ℝ),Real.rpow_add hx0,Real.rpow_one]
    field_simp [hx0.ne',hx1.ne']; ring
  rw [hleft,le_div_iff₀ hd]
  linarith only [hmult]

/-- Ordered reciprocal excess over every finite interval decays at each
power strictly below one minus the supremum of the zero real parts. -/
theorem centered_reciprocal_prime_intervals_of_zeroReSup {d : ℝ} (hd : 0 < d)
    (hθ : zeroReSup < 1-d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k L : ℕ, 1 ≤ k → k ≤ L →
      |∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)/(n:ℝ)| ≤ B*(k:ℝ)^(-d) := by
  obtain ⟨C,hC,hE⟩ := exists_abs_chebyshevPsi_sub_le_rpow hθ
  have hd1 : d ≤ 1 := by linarith only [half_le_zeroReSup,hθ]
  let D := fun n : ℕ => (n:ℝ)^(-d)
  let P := centeredAbelPrefix 0
  have herr (j : ℕ) (hj : 1 ≤ j) : |P j| ≤ C*(j:ℝ)^(1-d) := by
    rw [show P j=Chebyshev.psi j-j from centeredAbelPrefix_zero_base j]
    exact hE j (by exact_mod_cast hj)
  have hend (j : ℕ) (hj : 1 ≤ j) : |(j:ℝ)⁻¹*P j| ≤ C*D j := by
    have hj0 : (0:ℝ) < j := by exact_mod_cast hj
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hj0.le)]
    apply (mul_le_mul_of_nonneg_left (herr j hj) (inv_nonneg.mpr hj0.le)).trans_eq
    have heq : (j:ℝ)^(1-d) = j*D j := by
      rw [sub_eq_add_neg,Real.rpow_add hj0,Real.rpow_one]
    rw [heq]; field_simp
  have hcost (j : ℕ) (hj : 1 ≤ j) :
      |P j*((j:ℝ)⁻¹-((j+1:ℕ):ℝ)⁻¹)| ≤ (C/d)*(D j-D (j+1)) := by
    have hj0 : (0:ℝ) < j := by exact_mod_cast hj
    have hdec : 0 ≤ (j:ℝ)⁻¹-((j:ℝ)+1)⁻¹ := sub_nonneg.mpr
      ((inv_le_inv₀ (by positivity) hj0).2 (le_add_of_nonneg_right zero_le_one))
    rw [Nat.cast_add_one,abs_mul,abs_of_nonneg hdec]
    apply (mul_le_mul_of_nonneg_right (herr j hj) hdec).trans
    have h := mul_le_mul_of_nonneg_left (reciprocal_power_step hd hd1
      (show (1:ℝ) ≤ j by exact_mod_cast hj)) hC
    simpa only [D,Nat.cast_add_one,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h
  refine ⟨2*C+C/d,by positivity,fun k L hk hkL => ?_⟩
  have hsum : ∑ j ∈ Finset.Ico k L, |P j*((j:ℝ)⁻¹-((j+1:ℕ):ℝ)⁻¹)| ≤ (C/d)*(D k-D L) := by
    induction L, hkL using Nat.le_induction with
    | base => simp
    | succ L hL ih =>
      rw [Finset.sum_Ico_succ_top hL]
      linarith only [add_le_add ih (hcost L (hk.trans hL))]
  have hparts := centeredAbelPrefix_by_parts (fun j : ℕ => (j:ℝ)⁻¹) (Nat.zero_le k) hkL
  simp only [div_eq_mul_inv]
  rw [hparts]
  rw [div_eq_mul_inv C d] at hsum
  have hD := Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < k by omega) : (0:ℝ) < k)
    (show (k:ℝ) ≤ L by exact_mod_cast hkL) (neg_nonpos.mpr hd.le)
  have hA := abs_add_le ((L:ℝ)⁻¹*P L-(k:ℝ)⁻¹*P k)
    (∑ j ∈ Finset.Ico k L, P j*((j:ℝ)⁻¹-((j+1:ℕ):ℝ)⁻¹))
  have hB := abs_sub ((L:ℝ)⁻¹*P L) ((k:ℝ)⁻¹*P k)
  have hS := Finset.abs_sum_le_sum_abs (fun j : ℕ => P j*((j:ℝ)⁻¹-((j+1:ℕ):ℝ)⁻¹)) (Finset.Ico k L)
  have hDL : 0 ≤ D L := Real.rpow_nonneg (Nat.cast_nonneg _) _
  change D L ≤ D k at hD
  linarith only [hA,hB,hS,hsum,hend k hk,hend L (hk.trans hkL),
    mul_le_mul_of_nonneg_left hD hC,mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hd.le)) hDL]

#print axioms centered_reciprocal_prime_intervals_of_zeroReSup
end GaloisForLFunctions.ExclusionOfTheCriticalState
