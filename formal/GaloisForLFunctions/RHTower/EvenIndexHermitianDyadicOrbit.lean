import GaloisForLFunctions.RHTower.DirichletLMixedAdditiveEvenIndexLaw
import GaloisForLFunctions.HTGeometry.DyadicExponentGeometricSummable

/-!
# Dyadic orbit classification of the even-index Hermitian channel

A coefficient sequence obeying the single local recursion `a (2 * n) = c * a n` has an Abel series
that splits exactly into a free odd seed and a rescaled dyadic dilate,
`A x = O x + c * A (x ^ (2 : ℕ))` (`abelSeries_eq_oddSeed_add_const_mul_abelSeries_sq`).  Iterating the
recursion classifies the whole Abel series as the geometric orbit sum
`A r = ∑_j c ^ j * O (r ^ (2 ^ j))` (`hasSum_dyadicOrbit`), so the odd seed is a free parameter and
the recursion alone produces no upper estimate.

The same split converts the binary even-index parity Gram decomposition into an orthogonal channel
decomposition: the even additive channel is the sum of the odd-seed square and the dyadic dilate
square (`tsum_evenIndex_binary_eq_dyadicOrbitGram`).  For a completely multiplicative sequence with
`c = a 2` the two channels are `A r - c * A (r ^ (2 : ℕ))` and `c * A (r ^ (2 : ℕ))`
(`tsum_evenIndex_binary_eq_dyadicGram`), which for a real sequence with `c = -1` becomes the pair of
adjacent real squares `(A r + A (r ^ (2 : ℕ))) ^ (2 : ℕ) + A (r ^ (2 : ℕ)) ^ (2 : ℕ)`.
-/

open Complex Filter
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- The Abel (ordinary generating) series of a coefficient sequence. -/
def abelSeries (a : ℕ → ℂ) (x : ℂ) : ℂ := ∑' n : ℕ, a n * x ^ n

/-- The odd-index Abel seed `O x = ∑_{n odd} a n * x ^ n`, written through the halved index. -/
def oddSeed (a : ℕ → ℂ) (x : ℂ) : ℂ := x * ∑' q : ℕ, a (2 * q + 1) * (x ^ (2 : ℕ)) ^ q

variable {a : ℕ → ℂ} {c : ℂ}

/-- Under the dyadic recursion `a (2 * n) = c * a n` the even-index subseries is exactly `c` times
the full Abel series. -/
theorem tsum_even_eq_const_mul_abelSeries (hrec : ∀ n, a (2 * n) = c * a n) (x : ℂ) :
    (∑' q : ℕ, a (2 * q) * x ^ q) = c * abelSeries a x := by
  rw [abelSeries, ← tsum_mul_left]
  exact tsum_congr fun q => by rw [hrec q, mul_assoc]

/-- **Exact dyadic split.**  A sequence satisfying `a (2 * n) = c * a n` has Abel series
`A x = O x + c * A (x ^ (2 : ℕ))`, with `O` the free odd seed. -/
theorem abelSeries_eq_oddSeed_add_const_mul_abelSeries_sq
    (hrec : ∀ n, a (2 * n) = c * a n) {x : ℂ}
    (hx : Summable fun N : ℕ => ‖a N * x ^ N‖) :
    abelSeries a x = oddSeed a x + c * abelSeries a (x ^ (2 : ℕ)) := by
  have hsplit := generatingFunction_even_odd_split a x hx
  rw [tsum_even_eq_const_mul_abelSeries hrec (x ^ (2 : ℕ))] at hsplit
  simp only [abelSeries, oddSeed] at hsplit ⊢
  rw [hsplit]
  ring

/-- The odd seed is the exact defect of the Abel series against its dyadic dilate. -/
theorem oddSeed_eq_abelSeries_sub (hrec : ∀ n, a (2 * n) = c * a n) {x : ℂ}
    (hx : Summable fun N : ℕ => ‖a N * x ^ N‖) :
    oddSeed a x = abelSeries a x - c * abelSeries a (x ^ (2 : ℕ)) := by
  rw [abelSeries_eq_oddSeed_add_const_mul_abelSeries_sq hrec hx]
  ring

/-- **Orthogonal channel decomposition of the even additive channel.**  For a sequence with the
dyadic recursion, the binary even-index Hermitian Abel series is the sum of the odd-seed square and
the square of the rescaled dyadic dilate. -/
theorem tsum_evenIndex_binary_eq_dyadicOrbitGram
    (hrec : ∀ n, a (2 * n) = c * a n) (r : ℝ)
    (ha : Summable fun N : ℕ => ‖a N * (r : ℂ) ^ N‖) :
    (∑' q : ℕ, mixedAdditiveConvolutionPower a 1 (2 * q) * (r : ℂ) ^ (2 * q))
      = oddSeed a (r : ℂ) * (starRingEnd ℂ) (oddSeed a (r : ℂ))
        + (c * abelSeries a ((r : ℂ) ^ (2 : ℕ))) *
            (starRingEnd ℂ) (c * abelSeries a ((r : ℂ) ^ (2 : ℕ))) := by
  rw [tsum_evenIndex_binary_eq_evenOddGram a r ha,
    tsum_even_eq_const_mul_abelSeries hrec ((r : ℂ) ^ (2 : ℕ))]
  simp only [oddSeed, map_mul, Complex.conj_ofReal]
  ring

/-- **Dyadic Gram law.**  For a completely multiplicative sequence, with `c = a 2`, the even
additive channel is the sum of two adjacent dyadic squares. -/
theorem tsum_evenIndex_binary_eq_dyadicGram
    (hrec : ∀ n, a (2 * n) = c * a n) (r : ℝ)
    (ha : Summable fun N : ℕ => ‖a N * (r : ℂ) ^ N‖) :
    (∑' q : ℕ, mixedAdditiveConvolutionPower a 1 (2 * q) * (r : ℂ) ^ (2 * q))
      = (abelSeries a (r : ℂ) - c * abelSeries a ((r : ℂ) ^ (2 : ℕ))) *
            (starRingEnd ℂ) (abelSeries a (r : ℂ) - c * abelSeries a ((r : ℂ) ^ (2 : ℕ)))
        + (c * abelSeries a ((r : ℂ) ^ (2 : ℕ))) *
            (starRingEnd ℂ) (c * abelSeries a ((r : ℂ) ^ (2 : ℕ))) := by
  rw [tsum_evenIndex_binary_eq_dyadicOrbitGram hrec r ha,
    oddSeed_eq_abelSeries_sub hrec ha]

/-- A real coefficient sequence has a conjugation-invariant Abel series at real arguments. -/
theorem conj_abelSeries_ofReal (hreal : ∀ n, (starRingEnd ℂ) (a n) = a n) (x : ℝ) :
    (starRingEnd ℂ) (abelSeries a (x : ℂ)) = abelSeries a (x : ℂ) := by
  rw [abelSeries, starRingEnd_apply, tsum_star]
  refine tsum_congr fun n => ?_
  rw [← starRingEnd_apply, map_mul, map_pow, hreal n, Complex.conj_ofReal]

/-- **Two adjacent real squares.**  A real sequence with the dyadic recursion at `c = -1` — the
Liouville normalisation — has even additive channel `(A r + A (r ^ (2 : ℕ))) ^ (2 : ℕ) + A (r ^ (2 : ℕ)) ^ (2 : ℕ)`. -/
theorem tsum_evenIndex_binary_eq_dyadicGram_neg_one
    (hreal : ∀ n, (starRingEnd ℂ) (a n) = a n) (hrec : ∀ n, a (2 * n) = -a n) (r : ℝ)
    (ha : Summable fun N : ℕ => ‖a N * (r : ℂ) ^ N‖) :
    (∑' q : ℕ, mixedAdditiveConvolutionPower a 1 (2 * q) * (r : ℂ) ^ (2 * q))
      = (abelSeries a (r : ℂ) + abelSeries a ((r : ℂ) ^ (2 : ℕ))) ^ (2 : ℕ)
        + abelSeries a ((r : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hrec' : ∀ n, a (2 * n) = (-1 : ℂ) * a n := fun n => by rw [hrec n]; ring
  have hsq : ((r : ℂ) ^ (2 : ℕ)) = ((r ^ (2 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have hconj1 := conj_abelSeries_ofReal hreal r
  have hconj2 := conj_abelSeries_ofReal (a := a) hreal (r ^ (2 : ℕ))
  rw [← hsq] at hconj2
  rw [tsum_evenIndex_binary_eq_dyadicGram hrec' r ha]
  simp only [map_sub, map_mul, map_neg, map_one, hconj1, hconj2]
  ring

/-! ### The dyadic orbit

Iterating the exact split classifies the Abel series of a dyadically self-similar sequence as a
geometric orbit sum over the odd seed. -/

/-- Finite telescoping of the dyadic split. -/
theorem abelSeries_dyadic_telescope
    (hrec : ∀ n, a (2 * n) = c * a n)
    (hdisc : ∀ y : ℝ, 0 ≤ y → y < 1 → Summable fun N : ℕ => ‖a N * (y : ℂ) ^ N‖)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℕ) :
    abelSeries a (r : ℂ) =
      (∑ j ∈ Finset.range J, c ^ j * oddSeed a ((r : ℂ) ^ (2 ^ j)))
        + c ^ J * abelSeries a ((r : ℂ) ^ (2 ^ J)) := by
  induction J with
  | zero => simp
  | succ J ih =>
      have hy0 : (0 : ℝ) ≤ r ^ (2 ^ J) := pow_nonneg hr0 _
      have hy1 : r ^ (2 ^ J) < 1 := pow_lt_one₀ hr0 hr1 (by positivity)
      have hcast : ((r ^ (2 ^ J) : ℝ) : ℂ) = (r : ℂ) ^ (2 ^ J) := by push_cast; ring
      have hsum := hdisc (r ^ (2 ^ J)) hy0 hy1
      rw [hcast] at hsum
      have hstep := abelSeries_eq_oddSeed_add_const_mul_abelSeries_sq hrec hsum
      have hsq : ((r : ℂ) ^ (2 ^ J)) ^ (2 : ℕ) = (r : ℂ) ^ (2 ^ (J + 1)) := by
        rw [← pow_mul, ← pow_succ]
      rw [hsq] at hstep
      rw [Finset.sum_range_succ, ih, hstep]
      ring

set_option maxHeartbeats 1000000 in
/-- Linear radial bound for the Abel series of a sequence vanishing at `0`. -/
theorem norm_abelSeries_le_mul
    (ha0 : a 0 = 0)
    (hdisc : ∀ y : ℝ, 0 ≤ y → y < 1 → Summable fun N : ℕ => ‖a N * (y : ℂ) ^ N‖)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {y : ℝ} (hy0 : 0 ≤ y) (hyr : y ≤ r) :
    ‖abelSeries a (y : ℂ)‖ ≤ (∑' n : ℕ, ‖a (n + 1)‖ * r ^ n) * y := by
  have hyr1 : y < 1 := lt_of_le_of_lt hyr hr1
  have hnormEq : ∀ z : ℝ, 0 ≤ z → ∀ N : ℕ, ‖a N * (z : ℂ) ^ N‖ = ‖a N‖ * z ^ N := by
    intro z hz N
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
  have hsr : Summable fun N : ℕ => ‖a N‖ * r ^ N :=
    (hdisc r hr0.le hr1).congr fun N => hnormEq r hr0.le N
  have hshift : Summable fun n : ℕ => ‖a (n + 1)‖ * r ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hsr
  have hK : Summable fun n : ℕ => ‖a (n + 1)‖ * r ^ n := by
    refine (hshift.mul_left r⁻¹).congr fun n => ?_
    rw [pow_succ]
    field_simp
  have hsy : Summable fun N : ℕ => a N * (y : ℂ) ^ N := (hdisc y hy0 hyr1).of_norm
  have hsyShiftNorm : Summable fun n : ℕ => ‖a (n + 1) * (y : ℂ) ^ (n + 1)‖ :=
    (summable_nat_add_iff 1).2 (hdisc y hy0 hyr1)
  have hsyNorm : Summable fun n : ℕ => ‖a (n + 1)‖ * y ^ (n + 1) :=
    hsyShiftNorm.congr fun n => hnormEq y hy0 (n + 1)
  have hhead : abelSeries a (y : ℂ) = ∑' n : ℕ, a (n + 1) * (y : ℂ) ^ (n + 1) := by
    have hs := hsy.sum_add_tsum_nat_add 1
    rw [abelSeries, ← hs, Finset.sum_range_one, ha0, zero_mul, zero_add]
  calc ‖abelSeries a (y : ℂ)‖
      = ‖∑' n : ℕ, a (n + 1) * (y : ℂ) ^ (n + 1)‖ := by rw [hhead]
    _ ≤ ∑' n : ℕ, ‖a (n + 1) * (y : ℂ) ^ (n + 1)‖ := norm_tsum_le_tsum_norm hsyShiftNorm
    _ = ∑' n : ℕ, ‖a (n + 1)‖ * y ^ (n + 1) := tsum_congr fun n => hnormEq y hy0 (n + 1)
    _ ≤ ∑' n : ℕ, (‖a (n + 1)‖ * r ^ n) * y := by
        refine hsyNorm.tsum_le_tsum (fun n => ?_) (hK.mul_right y)
        have hpow : y ^ n ≤ r ^ n := pow_le_pow_left₀ hy0 hyr n
        have hstep : ‖a (n + 1)‖ * y ^ n ≤ ‖a (n + 1)‖ * r ^ n :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        calc ‖a (n + 1)‖ * y ^ (n + 1) = (‖a (n + 1)‖ * y ^ n) * y := by ring
          _ ≤ (‖a (n + 1)‖ * r ^ n) * y := mul_le_mul_of_nonneg_right hstep hy0
    _ = (∑' n : ℕ, ‖a (n + 1)‖ * r ^ n) * y := tsum_mul_right

set_option maxHeartbeats 1000000 in
/-- **Dyadic orbit classification.**  For `0 < r < 1` the Abel series of a dyadically self-similar
sequence vanishing at `0` is the geometric orbit sum of its odd seed along the dyadic dilates. -/
theorem hasSum_dyadicOrbit
    (ha0 : a 0 = 0) (hrec : ∀ n, a (2 * n) = c * a n)
    (hdisc : ∀ y : ℝ, 0 ≤ y → y < 1 → Summable fun N : ℕ => ‖a N * (y : ℂ) ^ N‖)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasSum (fun j : ℕ => c ^ j * oddSeed a ((r : ℂ) ^ (2 ^ j))) (abelSeries a (r : ℂ)) := by
  set K : ℝ := ∑' n : ℕ, ‖a (n + 1)‖ * r ^ n with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact tsum_nonneg fun n => by positivity
  have hcastPow : ∀ j : ℕ, ((r ^ (2 ^ j) : ℝ) : ℂ) = (r : ℂ) ^ (2 ^ j) := by
    intro j; push_cast; ring
  have hyle : ∀ j : ℕ, r ^ (2 ^ j) ≤ r := by
    intro j
    calc r ^ (2 ^ j) ≤ r ^ (1 : ℕ) := pow_le_pow_of_le_one hr0.le hr1.le Nat.one_le_two_pow
      _ = r := pow_one r
  have hy0 : ∀ j : ℕ, (0 : ℝ) ≤ r ^ (2 ^ j) := fun j => pow_nonneg hr0.le _
  have hy1 : ∀ j : ℕ, r ^ (2 ^ j) < 1 := fun j => lt_of_le_of_lt (hyle j) hr1
  have hbound : ∀ j : ℕ, ‖abelSeries a ((r : ℂ) ^ (2 ^ j))‖ ≤ K * r ^ (2 ^ j) := by
    intro j
    have h := norm_abelSeries_le_mul ha0 hdisc hr0 hr1 (y := r ^ (2 ^ j)) (hy0 j) (hyle j)
    rwa [hcastPow j] at h
  have hgeom := GaloisForLFunctions.HTGeometry.tendsto_geometric_mul_pow_two_pow
    (r := r) (d := ‖c‖) hr0.le hr1
  rw [abs_of_nonneg (norm_nonneg c)] at hgeom
  have hrem : Tendsto (fun J : ℕ => c ^ J * abelSeries a ((r : ℂ) ^ (2 ^ J))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun J => norm_nonneg _) (fun J => ?_)
      (by simpa using hgeom.const_mul K)
    rw [norm_mul, norm_pow]
    calc ‖c‖ ^ J * ‖abelSeries a ((r : ℂ) ^ (2 ^ J))‖
        ≤ ‖c‖ ^ J * (K * r ^ (2 ^ J)) :=
          mul_le_mul_of_nonneg_left (hbound J) (by positivity)
      _ = K * (‖c‖ ^ J * r ^ (2 ^ J)) := by ring
  have hoddBound : ∀ j : ℕ,
      ‖c ^ j * oddSeed a ((r : ℂ) ^ (2 ^ j))‖ ≤ (K * (1 + ‖c‖)) * (‖c‖ ^ j * r ^ (2 ^ j)) := by
    intro j
    have hsum := hdisc (r ^ (2 ^ j)) (hy0 j) (hy1 j)
    rw [hcastPow j] at hsum
    have hodd := oddSeed_eq_abelSeries_sub hrec hsum
    have hsq : ((r : ℂ) ^ (2 ^ j)) ^ (2 : ℕ) = ((r ^ (2 ^ j) * r ^ (2 ^ j) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hsq] at hodd
    have hyy : r ^ (2 ^ j) * r ^ (2 ^ j) ≤ r := by
      calc r ^ (2 ^ j) * r ^ (2 ^ j) ≤ 1 * r ^ (2 ^ j) :=
            mul_le_mul_of_nonneg_right (hy1 j).le (hy0 j)
        _ = r ^ (2 ^ j) := one_mul _
        _ ≤ r := hyle j
    have hb2 : ‖abelSeries a (((r ^ (2 ^ j) * r ^ (2 ^ j) : ℝ)) : ℂ)‖ ≤ K * r ^ (2 ^ j) := by
      have h := norm_abelSeries_le_mul ha0 hdisc hr0 hr1
        (y := r ^ (2 ^ j) * r ^ (2 ^ j)) (by positivity) hyy
      refine h.trans ?_
      have : r ^ (2 ^ j) * r ^ (2 ^ j) ≤ r ^ (2 ^ j) := by
        calc r ^ (2 ^ j) * r ^ (2 ^ j) ≤ 1 * r ^ (2 ^ j) :=
              mul_le_mul_of_nonneg_right (hy1 j).le (hy0 j)
          _ = r ^ (2 ^ j) := one_mul _
      exact mul_le_mul_of_nonneg_left this hK0
    have hodd_le : ‖oddSeed a ((r : ℂ) ^ (2 ^ j))‖ ≤ (K * (1 + ‖c‖)) * r ^ (2 ^ j) := by
      rw [hodd]
      calc ‖abelSeries a ((r : ℂ) ^ (2 ^ j)) -
              c * abelSeries a (((r ^ (2 ^ j) * r ^ (2 ^ j) : ℝ)) : ℂ)‖
          ≤ ‖abelSeries a ((r : ℂ) ^ (2 ^ j))‖ +
              ‖c * abelSeries a (((r ^ (2 ^ j) * r ^ (2 ^ j) : ℝ)) : ℂ)‖ := norm_sub_le _ _
        _ ≤ K * r ^ (2 ^ j) + ‖c‖ * (K * r ^ (2 ^ j)) := by
            refine add_le_add (hbound j) ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left hb2 (norm_nonneg c)
        _ = (K * (1 + ‖c‖)) * r ^ (2 ^ j) := by ring
    rw [norm_mul, norm_pow]
    calc ‖c‖ ^ j * ‖oddSeed a ((r : ℂ) ^ (2 ^ j))‖
        ≤ ‖c‖ ^ j * ((K * (1 + ‖c‖)) * r ^ (2 ^ j)) :=
          mul_le_mul_of_nonneg_left hodd_le (by positivity)
      _ = (K * (1 + ‖c‖)) * (‖c‖ ^ j * r ^ (2 ^ j)) := by ring
  have hsummable : Summable fun j : ℕ => c ^ j * oddSeed a ((r : ℂ) ^ (2 ^ j)) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) hoddBound ?_
    have hg := GaloisForLFunctions.HTGeometry.summable_geometric_mul_pow_two_pow
      (r := r) (d := ‖c‖) hr0.le hr1
    rw [abs_of_nonneg (norm_nonneg c)] at hg
    exact hg.mul_left _
  have hEq : ∀ J : ℕ, (∑ j ∈ Finset.range J, c ^ j * oddSeed a ((r : ℂ) ^ (2 ^ j))) =
      abelSeries a (r : ℂ) - c ^ J * abelSeries a ((r : ℂ) ^ (2 ^ J)) := by
    intro J
    rw [abelSeries_dyadic_telescope hrec hdisc hr0.le hr1 J]
    ring
  have hlim : Tendsto
      (fun J : ℕ => abelSeries a (r : ℂ) - c ^ J * abelSeries a ((r : ℂ) ^ (2 ^ J))) atTop
      (𝓝 (abelSeries a (r : ℂ) - 0)) := tendsto_const_nhds.sub hrem
  rw [sub_zero] at hlim
  exact (hsummable.hasSum_iff_tendsto_nat).2 (by simpa only [hEq] using hlim)

end

end RHTower
