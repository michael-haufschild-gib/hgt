import GaloisForLFunctions.RHTower.SuzukiCorFourSix
import GaloisForLFunctions.RHTower.XiEndpointReciprocalTraceReflection

/-!
# Paired Li coefficients as completed endpoint trace series

For a reciprocal endpoint coordinate `z = 1 / rho`, the paired Li atom has a cancellation that is
invisible in either one-sided Li sum:

`2 - (1 - z)^d - (1 - z)^(-d)`.

Its constant term vanishes, and its two linear terms cancel exactly.  The surviving expansion
therefore starts at reciprocal order two.  This module computes every coefficient explicitly,
proves absolute summability jointly over trace order and the multiplicity-exact Xi divisor, and
lands every positive-degree paired Li coefficient on the already constructed completed endpoint
trace tower:

`xiLiPaired d = sum_j liEndpointTraceWeight d j * xiRawReciprocalPowerTrace (j + 2)`.

Thus no conditionally convergent first reciprocal trace and no choice of zero ordering enters the
Li source interface.  The fixed source order is legitimate at every coefficient degree.
-/

open Complex

namespace RHTower

noncomputable section

/-- Weight of reciprocal trace order `j + 2` in paired Li degree `d`. -/
def liEndpointTraceWeight (d j : ℕ) : ℂ :=
  -((d.choose (j + 2) : ℂ) * (-1 : ℂ) ^ (j + 2) +
    ((j + 2 + (d - 1)).choose (d - 1) : ℂ))

theorem hasSum_liEndpointTraceWeight_mul_pow
    {d : ℕ} (hd : 1 ≤ d) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => liEndpointTraceWeight d j * z ^ (j + 2))
      (liTerm (1 - z) d) := by
  let p : ℕ → ℂ := fun k => (d.choose k : ℂ) * (-z) ^ k
  let g : ℕ → ℂ := fun k => ((k + (d - 1)).choose (d - 1) : ℂ) * z ^ k
  have hpSummable : Summable p := by
    apply summable_of_ne_finset_zero (s := Finset.range (d + 1))
    intro k hk
    have hk' : d + 1 ≤ k := by
      simpa only [Finset.mem_range, not_lt] using hk
    have hdk : d < k := by omega
    simp [p, Nat.choose_eq_zero_of_lt hdk]
  have hpTsum : (∑' k : ℕ, p k) = (1 - z) ^ d := by
    rw [tsum_eq_sum (s := Finset.range (d + 1)) (fun k hk => by
      have hk' : d + 1 ≤ k := by
        simpa only [Finset.mem_range, not_lt] using hk
      have hdk : d < k := by omega
      simp [p, Nat.choose_eq_zero_of_lt hdk])]
    have h := add_pow (-z) (1 : ℂ) d
    simpa [p, sub_eq_add_neg, mul_comm, add_comm] using h.symm
  have hp : HasSum p ((1 - z) ^ d) := by
    rw [← hpTsum]
    exact hpSummable.hasSum
  have hg : HasSum g (1 / (1 - z) ^ d) := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (d - 1) hz
    simpa [g, Nat.sub_add_cancel hd] using h
  have hsum : HasSum (fun k => p k + g k)
      ((1 - z) ^ d + 1 / (1 - z) ^ d) := hp.add hg
  have htail := (hasSum_nat_add_iff' 2).mpr hsum
  have hprefix : ∑ k ∈ Finset.range 2, (p k + g k) = 2 := by
    have hsymm : d.choose (d - 1) = d.choose 1 := Nat.choose_symm hd
    have hp0 : p 0 = 1 := by simp [p]
    have hg0 : g 0 = 1 := by simp [g]
    have hp1 : p 1 = -(d : ℂ) * z := by simp [p, Nat.choose_one_right]
    have hg1 : g 1 = (d : ℂ) * z := by
      have hidx : 1 + (d - 1) = d := by omega
      simp [g, hidx, hsymm, Nat.choose_one_right]
    norm_num [Finset.sum_range_succ, hp0, hg0, hp1, hg1]
  rw [hprefix] at htail
  have hweighted : HasSum
      (fun j : ℕ => liEndpointTraceWeight d j * z ^ (j + 2))
      (-((1 - z) ^ d + 1 / (1 - z) ^ d - 2)) := by
    apply htail.neg.congr_fun
    intro j
    simp only [p, g, liEndpointTraceWeight, neg_add_rev]
    rw [neg_pow]
    ring
  have htarget : liTerm (1 - z) d =
      -((1 - z) ^ d + 1 / (1 - z) ^ d - 2) := by
    unfold liTerm
    rw [inv_pow, div_eq_mul_inv]
    ring
  rw [htarget]
  exact hweighted

theorem summable_liEndpointTraceWeight_ratio (d : ℕ) :
    Summable (fun j : ℕ =>
      ((d.choose (j + 2) : ℝ) +
        (((j + 2) + (d - 1)).choose (d - 1) : ℝ)) * (9 / 10 : ℝ) ^ j) := by
  have hratio : ‖(9 / 10 : ℝ)‖ < 1 := by norm_num [Real.norm_eq_abs]
  have hfinite : Summable (fun j : ℕ =>
      (d.choose (j + 2) : ℝ) * (9 / 10 : ℝ) ^ j) := by
    apply summable_of_ne_finset_zero (s := Finset.range d)
    intro j hj
    have hjd : d ≤ j := by
      simpa only [Finset.mem_range, not_lt] using hj
    have hdlt : d < j + 2 := by omega
    simp [Nat.choose_eq_zero_of_lt hdlt]
  have hbase := summable_choose_mul_geometric_of_norm_lt_one (d - 1) hratio
  have hshift : Summable (fun j : ℕ =>
      ((((j + 2) + (d - 1)).choose (d - 1) : ℕ) : ℝ) *
        (9 / 10 : ℝ) ^ (j + 2)) := by
    simpa [add_assoc] using (summable_nat_add_iff 2).mpr hbase
  have htail : Summable (fun j : ℕ =>
      ((((j + 2) + (d - 1)).choose (d - 1) : ℕ) : ℝ) *
        (9 / 10 : ℝ) ^ j) := by
    have hmul := hshift.mul_left ((9 / 10 : ℝ) ^ 2)⁻¹
    refine hmul.congr ?_
    intro j
    rw [pow_add]
    norm_num
    ring
  exact (hfinite.add htail).congr (fun j => by ring)

set_option maxHeartbeats 800000 in
theorem summable_liEndpointTraceWeight_xiRawReciprocal_double
    (d : ℕ) :
    Summable (fun p : ℕ × XiZeroCopy =>
      liEndpointTraceWeight d p.1 *
        xiRawReciprocalCoordinate p.2 ^ (p.1 + 2)) := by
  let a : ℕ → ℝ := fun j =>
    ((d.choose (j + 2) : ℝ) +
      (((j + 2) + (d - 1)).choose (d - 1) : ℝ)) * (9 / 10 : ℝ) ^ j
  have ha : Summable a := by
    simpa only [a] using summable_liEndpointTraceWeight_ratio d
  have hmajor : Summable (fun p : ℕ × XiZeroCopy =>
      a p.1 * ‖xiRawReciprocalCoordinate p.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg
      (by positivity : 0 ≤ a p.1) (sq_nonneg _))]
    constructor
    · intro j
      exact summable_norm_xiRawReciprocalCoordinate_sq.mul_left (a j)
    · apply Summable.of_nonneg_of_le
          (fun j => tsum_nonneg fun _ => mul_nonneg
            (by positivity : 0 ≤ a j) (sq_nonneg _))
          (fun _ => le_rfl)
      convert ha.mul_right xiRawReciprocalHermitianMass using 1
      all_goals try rfl
      funext j
      rw [xiRawReciprocalHermitianMass, ← tsum_mul_left]
  apply Summable.of_norm_bounded hmajor
  rintro ⟨j, q⟩
  have hweight : ‖liEndpointTraceWeight d j‖ ≤
      (d.choose (j + 2) : ℝ) +
        (((j + 2) + (d - 1)).choose (d - 1) : ℝ) := by
    rw [liEndpointTraceWeight, norm_neg]
    calc
      ‖(d.choose (j + 2) : ℂ) * (-1 : ℂ) ^ (j + 2) +
          (((j + 2 + (d - 1)).choose (d - 1) : ℕ) : ℂ)‖
          ≤ ‖(d.choose (j + 2) : ℂ) * (-1 : ℂ) ^ (j + 2)‖ +
              ‖((((j + 2) + (d - 1)).choose (d - 1) : ℕ) : ℂ)‖ := norm_add_le _ _
      _ = (d.choose (j + 2) : ℝ) +
          (((j + 2) + (d - 1)).choose (d - 1) : ℝ) := by simp
  have hpow : ‖xiRawReciprocalCoordinate q‖ ^ j ≤ (9 / 10 : ℝ) ^ j :=
    pow_le_pow_left₀ (norm_nonneg _)
      (xiRawReciprocalCoordinate_norm_lt_nine_tenths q).le j
  rw [norm_mul, norm_pow, pow_add]
  calc
    ‖liEndpointTraceWeight d j‖ *
        (‖xiRawReciprocalCoordinate q‖ ^ j *
          ‖xiRawReciprocalCoordinate q‖ ^ 2)
      ≤ ((d.choose (j + 2) : ℝ) +
          (((j + 2) + (d - 1)).choose (d - 1) : ℝ)) *
            ((9 / 10 : ℝ) ^ j * ‖xiRawReciprocalCoordinate q‖ ^ 2) := by
        gcongr
    _ = a j * ‖xiRawReciprocalCoordinate q‖ ^ 2 := by simp [a]; ring

/-- The endpoint-trace expansion is absolutely summable in source order. -/
theorem summable_liEndpointTraceWeight_mul_rawTrace
    (d : ℕ) :
    Summable (fun j : ℕ =>
      liEndpointTraceWeight d j * xiRawReciprocalPowerTrace (j + 2)) := by
  have hf := (summable_liEndpointTraceWeight_xiRawReciprocal_double d).prod
  refine hf.congr ?_
  intro j
  rw [xiRawReciprocalPowerTrace, ← tsum_mul_left]

/-- Exact all-degree paired-Li landing on completed endpoint reciprocal traces. -/
theorem xiLiPaired_eq_tsum_liEndpointTraceWeight_mul_rawTrace
    {d : ℕ} (hd : 1 ≤ d) :
    xiLiPaired d = ∑' j : ℕ,
      liEndpointTraceWeight d j * xiRawReciprocalPowerTrace (j + 2) := by
  let f : ℕ → XiZeroCopy → ℂ := fun j q =>
    liEndpointTraceWeight d j * xiRawReciprocalCoordinate q ^ (j + 2)
  have hf : Summable (Function.uncurry f) := by
    change Summable (fun p : ℕ × XiZeroCopy =>
      liEndpointTraceWeight d p.1 *
        xiRawReciprocalCoordinate p.2 ^ (p.1 + 2))
    exact summable_liEndpointTraceWeight_xiRawReciprocal_double d
  have hpoint (q : XiZeroCopy) :
      ∑' j : ℕ, f j q =
        liTerm (xiRootW ((q.1 : XiDivisorSupport) : ℂ)) d := by
    have hz : ‖xiRawReciprocalCoordinate q‖ < 1 :=
      (xiRawReciprocalCoordinate_norm_lt_nine_tenths q).trans (by norm_num)
    have h := (hasSum_liEndpointTraceWeight_mul_pow hd hz).tsum_eq
    simpa [f, xiRootW, xiRawReciprocalCoordinate, div_eq_mul_inv] using h
  calc
    xiLiPaired d = ∑' q : XiZeroCopy,
        liTerm (xiRootW ((q.1 : XiDivisorSupport) : ℂ)) d :=
      (hasSum_liTerm_xiZeroCopy d).tsum_eq.symm
    _ = ∑' q : XiZeroCopy, ∑' j : ℕ, f j q := by
      apply tsum_congr
      exact fun q => (hpoint q).symm
    _ = ∑' j : ℕ, ∑' q : XiZeroCopy, f j q := by
      rw [hf.tsum_comm]
    _ = ∑' j : ℕ,
        liEndpointTraceWeight d j * xiRawReciprocalPowerTrace (j + 2) := by
      apply tsum_congr
      intro j
      rw [xiRawReciprocalPowerTrace, ← tsum_mul_left]


end

end RHTower
