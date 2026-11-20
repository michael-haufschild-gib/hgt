import GaloisForLFunctions.RHTower.MobiusWeightedLineEnergyExponentLaw
import GaloisForLFunctions.RHTower.DirichletAbel

/-!
# Left and right bounds for a finite Möbius section

Abel summation measures every positive vertical line by one absolute
Mertens prefix and its reciprocal average. On a far right line the
mollified error has no coefficients through the cutoff, which gives an
arbitrarily large power of decay as the line moves to the right.
-/

noncomputable section
open Finset Filter Complex
open _root_.RHTower
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Reciprocal mass of the absolute Mertens prefixes. -/
def mertensAbelMass (N : ℕ) := ∑ j ∈ range N, ‖mobiusMertensPartialSum (j+1)‖/((j:ℝ)+1)

/-- Cost of the finite Dirichlet section, including its terminal value. -/
def mertensAbelCost (N : ℕ) := ‖mobiusMertensPartialSum N‖+mertensAbelMass N

theorem mertens_abel_mass_nonneg (N : ℕ) : 0 ≤ mertensAbelMass N :=
  sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (by positivity)

/-- A single finite arithmetic cost bounds the whole right half-plane
after dividing the reading by one plus the frequency norm. -/
theorem norm_mertens_section_from_abel_cost {N : ℕ} (hN : 1≤N) {s : ℂ} (hs : 0<s.re) :
    ‖edPoly mobCoeff (Icc 1 N) s‖ ≤ (1+‖s‖)*mertensAbelCost N := by
  let g := fun n => mobCoeff (n+1)
  have head (i : ℕ) : coeffPartial g i = mobiusMertensPartialSum i :=
    sum_range_mobCoeff_succ_eq_mobiusMertensPartialSum i
  rw [edPoly_mobCoeff_Icc_eq_sum_range]
  simp only [smul_eq_mul]
  rw [sum_eq_abelPartial g s N,head]
  apply (norm_add_le _ _).trans
  have hsN := Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr hN : 1≤(N:ℝ)) (neg_nonpos.mpr hs.le)
  have left : ‖(((N:ℝ):ℂ)^(-s))*mobiusMertensPartialSum N‖ ≤ ‖mobiusMertensPartialSum N‖ := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hN : 0<(N:ℝ)),Complex.neg_re]
    exact mul_le_of_le_one_left (norm_nonneg _) hsN
  have row (i : ℕ) : ‖coeffPartial g (i+1) * (((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((i : ℝ) + 2 : ℝ)) : ℂ) ^ (-s))‖ ≤
      ‖s‖*(‖mobiusMertensPartialSum (i+1)‖/((i:ℝ)+1)) := by
    have xp : 0 < (i:ℝ)+1 := by positivity
    have diff := _root_.RHTower.norm_cpow_shift_sub_le_of_nonneg (x:=(i:ℝ)+1) (b:=1) xp zero_le_one hs
    rw [show (i:ℝ)+1+1=(i:ℝ)+2 by ring,mul_one] at diff
    rw [norm_sub_rev] at diff
    have hweight := Real.rpow_le_rpow_of_exponent_le (show 1≤(i:ℝ)+1 from le_add_of_nonneg_left (Nat.cast_nonneg i))
      (by linarith only [hs] : -s.re-1 ≤ -1)
    rw [Real.rpow_neg_one] at hweight
    rw [norm_mul,head]
    exact (mul_le_mul_of_nonneg_left (diff.trans (mul_le_mul_of_nonneg_left hweight (norm_nonneg s))) (norm_nonneg _)).trans_eq (by rw [div_eq_mul_inv]; ring)
  have right := (norm_sum_le _ _).trans (sum_le_sum (s:=range (N-1)) (fun i _ => row i))
  rw [←mul_sum] at right
  have mass : (∑ i ∈ range (N-1), ‖mobiusMertensPartialSum (i+1)‖/((i:ℝ)+1)) ≤ mertensAbelMass N :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.sub_le ..))
      fun _ _ _ => div_nonneg (norm_nonneg _) (by positivity)
  dsimp only [mertensAbelCost]
  linarith only [left,right,mul_le_mul_of_nonneg_left mass (norm_nonneg s),mertens_abel_mass_nonneg N,
    mul_nonneg (norm_nonneg s) (norm_nonneg (mobiusMertensPartialSum N))]

/-- Uniform far-edge bound for the actual mollified error at every real
abscissa at least three. The constant is independent of the abscissa. -/
theorem far_right_mertens_error :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N : ℕ}, 1≤N → ∀ {s : ℂ}, 3 ≤ s.re →
      ‖mobMollifiedError N s‖ ≤ D*(N:ℝ)^(3-s.re) := by
  let w := fun n : ℕ => (n:ℝ)^(-(2:ℝ))
  have sw : Summable w := Real.summable_nat_rpow.mpr (by norm_num)
  refine ⟨∑' n,w n,tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _),fun {N} hN {s} hs => ?_⟩
  rw [mobMollifiedError_eq_LSeries N (by linarith)]
  let X := (N:ℝ)^(3-s.re)
  have major := sw.mul_left X
  have bound (n : ℕ) : ‖LSeries.term (mobTailCoeff N) s n‖ ≤ X*w n := by
    rw [LSeries.norm_term_eq]
    by_cases hn : n ≤ N
    · rw [mobTailCoeff_eq_zero_of_le hn,norm_zero,zero_div,ite_self]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hNn := lt_of_not_ge hn
    have np : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
    rw [if_neg (Nat.ne_of_gt (by omega : 0<n))]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos np _)).mpr
    have cmp := Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hN : 0<(N:ℝ))
      (Nat.cast_le.mpr hNn.le) (sub_nonpos.mpr hs)
    have hcoeff := norm_mobTailCoeff_le hN hNn
    calc ‖mobTailCoeff N n‖ ≤ n := hcoeff
         _ = ((n:ℝ)^(3-s.re)*w n)*(n:ℝ)^s.re := by
           dsimp only [w]; rw [←Real.rpow_add np,←Real.rpow_add np,show 3-s.re + -(2:ℝ) + s.re = 1 by ring,Real.rpow_one]
         _ ≤ _ := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_right cmp (Real.rpow_nonneg np.le _)) (Real.rpow_nonneg np.le _)
  have hsumm := Summable.of_nonneg_of_le (fun n => norm_nonneg _) bound major
  exact (norm_tsum_le_tsum_norm hsumm).trans ((hsumm.tsum_le_tsum bound major).trans_eq (by
    rw [tsum_mul_left]; exact mul_comm _ _))

#print axioms norm_mertens_section_from_abel_cost
#print axioms far_right_mertens_error
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
