import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLogScheduleBoundaryNoGo

/-!
# A fixed lower bound for the literal pole-factor approximants

At `s = 2/3`, the Cayley coordinate is `-2`. After degree four the positive-half partial
sum is at most `-1/2`; the negative-half partial sum has absolute value at least one.
The latter follows by separate monotonicity of the even and odd partial sums.
Thus the actual product has norm at least `1/2`, independently of the pole-degree clock.
-/

open Complex Filter Metric Set Topology
open GaloisForLFunctions
open scoped BigOperators
noncomputable section
namespace RHTower

private def halfTwoThirdsTerm (k : ℕ) : ℝ := Ring.choose (1 / 2 : ℝ) k * (-2 : ℝ)^k
private def halfTwoThirdsSum (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, halfTwoThirdsTerm k
private def negHalfTwoThirdsWeight (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) * (1 / 2 : ℝ)^k
private def negHalfTwoThirdsSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ)^k * negHalfTwoThirdsWeight k

private theorem halfTwoThirdsTerm_nonpos {k : ℕ} (hk : 1 ≤ k) :
    halfTwoThirdsTerm k ≤ 0 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num [halfTwoThirdsTerm]
  | succ k hk ih =>
    have hrec := choose_succ_field (1 / 2 : ℝ) k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
        Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
      rw [eq_div_iff hk1.ne']
      simpa only [mul_comm] using hrec
    have heq : halfTwoThirdsTerm (k + 1) = halfTwoThirdsTerm k *
        (2 * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) := by
      unfold halfTwoThirdsTerm
      rw [hchoose, pow_succ]
      ring
    rw [heq]
    exact mul_nonpos_of_nonpos_of_nonneg ih
      (div_nonneg (mul_nonneg (by norm_num) (by linarith)) hk1.le)

private theorem halfTwoThirdsSum_le {N : ℕ} (hN : 3 ≤ N) :
    halfTwoThirdsSum N ≤ -1 / 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h := choose_succ_field (1 / 2 : ℝ) 1
    norm_num at h
    have htwo : Ring.choose (1 / 2 : ℝ) 2 = -1 / 8 := by linarith
    norm_num [halfTwoThirdsSum, halfTwoThirdsTerm, Finset.sum_range_succ, htwo]
  | succ N hN ih =>
    rw [halfTwoThirdsSum, Finset.sum_range_succ, ← halfTwoThirdsSum]
    exact (add_le_of_nonpos_right (halfTwoThirdsTerm_nonpos (by omega))).trans ih

private theorem negHalfTwoThirdsWeight_mono : Monotone negHalfTwoThirdsWeight := by
  apply monotone_nat_of_le_succ
  intro k
  have hcb : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
      2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc : (0 : ℝ) ≤ (Nat.centralBinom k : ℝ) := Nat.cast_nonneg _
  have hC : (Nat.centralBinom k : ℝ) ≤ (Nat.centralBinom (k+1) : ℝ) * (1 / 2) := by
    nlinarith
  dsimp [negHalfTwoThirdsWeight]
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right hC (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k)]

private theorem negHalfTwoThirdsSum_step (N : ℕ) :
    negHalfTwoThirdsSum (N+2) = negHalfTwoThirdsSum N +
      (-1 : ℝ)^N * (negHalfTwoThirdsWeight N - negHalfTwoThirdsWeight (N+1)) := by
  unfold negHalfTwoThirdsSum
  rw [show N+2 = (N+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
    pow_succ]
  ring

private theorem negHalfTwoThirdsSum_even_le (m : ℕ) :
    negHalfTwoThirdsSum (2*m+4) ≤ -1 := by
  induction m with
  | zero => norm_num [negHalfTwoThirdsSum, negHalfTwoThirdsWeight, Finset.sum_range_succ,
      Nat.centralBinom, Nat.choose]
  | succ m ih =>
    rw [show 2*(m+1)+4 = (2*m+4)+2 by omega, negHalfTwoThirdsSum_step]
    have hs : (-1 : ℝ)^(2*m+4) = 1 := by rw [pow_add, pow_mul]; norm_num
    rw [hs, one_mul]
    have h := negHalfTwoThirdsWeight_mono (Nat.le_succ (2*m+4))
    linarith

private theorem negHalfTwoThirdsSum_odd_ge (m : ℕ) :
    3 / 2 ≤ negHalfTwoThirdsSum (2*m+3) := by
  induction m with
  | zero => norm_num [negHalfTwoThirdsSum, negHalfTwoThirdsWeight, Finset.sum_range_succ,
      Nat.centralBinom, Nat.choose]
  | succ m ih =>
    rw [show 2*(m+1)+3 = (2*m+3)+2 by omega, negHalfTwoThirdsSum_step]
    have hs : (-1 : ℝ)^(2*m+3) = -1 := by rw [pow_add, pow_mul]; norm_num
    rw [hs]
    have h := negHalfTwoThirdsWeight_mono (Nat.le_succ (2*m+3))
    linarith

private theorem negHalfTwoThirdsSum_abs_ge {N : ℕ} (hN : 4 ≤ N) :
    1 ≤ |negHalfTwoThirdsSum N| := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have h := negHalfTwoThirdsSum_even_le (m-2)
    rw [show 2*(m-2)+4 = 2*m by omega] at h
    exact (by linarith : (1:ℝ) ≤ -negHalfTwoThirdsSum (2*m)).trans (neg_le_abs _)
  · have h := negHalfTwoThirdsSum_odd_ge (m-1)
    rw [show 2*(m-1)+3 = 2*m+1 by omega] at h
    exact (le_trans (by norm_num) h).trans (le_abs_self _)

private theorem real_binomialPartialSum_eq (a z : ℝ) (N : ℕ) :
    (binomialSeries ℝ a).partialSum N z = ∑ k ∈ Finset.range N, Ring.choose a k * z^k := by
  rw [FormalMultilinearSeries.partialSum]
  exact Finset.sum_congr rfl (fun k _ => by rw [binomialSeries_apply, smul_eq_mul]; simp)

/-- Pole normalization cannot attenuate the source at this point once its degree is at least four. -/
theorem norm_poleFactorSqrtApprox_twoThirds_ge_half {N : ℕ} (hN : 4 ≤ N) :
    (1 / 2 : ℝ) ≤ ‖poleFactorSqrtApprox N (2 / 3 : ℂ)‖ := by
  have hpoint : poleFactorCayley (2 / 3 : ℂ) = -2 := by
    norm_num [poleFactorCayley, GaloisForLFunctions.HTGeometry.cayleyRight]
  have hp : (binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-2 : ℂ) =
      (halfTwoThirdsSum N : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num,
      complex_boundary_binomialPartialSum_ofReal, real_binomialPartialSum_eq]
    rfl
  have hm : (binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (2 : ℂ) =
      (negHalfTwoThirdsSum N : ℂ) := by
    rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      complex_boundary_binomialPartialSum_ofReal, real_binomialPartialSum_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [choose_neg_half]
    change (-1 : ℝ)^k * (Nat.centralBinom k : ℝ) / 4^k * 2^k =
      (-1 : ℝ)^k * ((Nat.centralBinom k : ℝ) * (1 / 2 : ℝ)^k)
    calc
      _ = (-1 : ℝ)^k * (Nat.centralBinom k : ℝ) * ((2 : ℝ)/4)^k := by
        rw [div_pow]
        ring
      _ = _ := by norm_num; ring
  rw [poleFactorSqrtApprox, hpoint, neg_neg, hp, hm, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hplus : (1 / 2 : ℝ) ≤ |halfTwoThirdsSum N| :=
    (by linarith [halfTwoThirdsSum_le (N := N) (by omega)] :
      (1 / 2 : ℝ) ≤ -halfTwoThirdsSum N).trans (neg_le_abs _)
  have hminus := negHalfTwoThirdsSum_abs_ge hN
  simpa using mul_le_mul hplus hminus (by norm_num) (abs_nonneg _)

end RHTower

