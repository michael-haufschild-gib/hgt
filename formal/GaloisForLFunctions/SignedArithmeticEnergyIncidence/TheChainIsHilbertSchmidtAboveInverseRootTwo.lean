import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheChainIsHilbertSchmidtAboveDampingOne
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.FloorJumpsAboveTheSquareRootAreSparse
import GaloisForLFunctions.RHTower.GaussSpikeMass
import GaloisForLFunctions.RHTower.MobiusDiscretePacketEdgeEstimates

/-!
# The chain is Hilbert–Schmidt above damping `1/√2`

`TheChainIsHilbertSchmidtAboveDampingOne` bounds the centred chain by the size of a bounded
source.  Below damping one the source grows, `|P_η(q)| ≲ q^{1−η}` (`abs_centeredPrefix_le_rpow`),
and the kernel must be read more finely.  With `a = ⌊N/K⌋`, `a' = ⌊N/(K+1)⌋`, `J = a − a'`,
`s = a − N/K` (`centeredRow_eq`),

`C = (K/N)[(K^{−η} − (K+1)^{−η})(ρ s + P(a)) + (K+1)^{−η}(ρ(s − s') + (P(a) − P(a')))]`.

* **Jumps of the source** (`abs_centeredPrefix_sub_le`): `|P(a) − P(a')| ≤ J`, since the
  coefficients `c_η ∈ [0, 1]` and the density `ρ ∈ (0, 1]`.
* **Jumps of the floor** (`floorJump_card`): `J ≤ 2N/K²` below the square root, `J ≤ 1` above it,
  and above it the jumps are sparse (`FloorJumpsAboveTheSquareRootAreSparse`).
* **Hilbert–Schmidt bound** (`centeredOperator_l2_le_of_inverseRootTwo`): the mean-value and
  fractional parts are square summable for every `η > ½`; the short-interval part below the
  square root, bounded by `min(J, 2 C (N/K)^{1−η}) ≤ J^λ (2C(N/K)^{1−η})^{1−λ}`, is square
  summable for a suitable `λ` exactly when `η² > ½`.

So the centred chain is bounded in `ℓ²` on finitely supported sequences above damping `1/√2`.
The remaining obstruction between half damping and `1/√2` is the short-interval discrepancy of
`c_η − ρ` at height `N/K` on intervals of length `N/K²`.
-/

open Finset Filter Topology RHTower ArithmeticFunction
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The source below damping one -/

/-- `Σ_{j ≥ 0} (j + q + 1)^{−(1+η)} ≤ q^{−η}/η`, by telescoping `x^{−η}`. -/
theorem tsum_rpow_tail_le {η : ℝ} (hη : 0 < η) {q : ℕ} (hq : 1 ≤ q) :
    ∑' j : ℕ, ((j + q + 1 : ℕ) : ℝ) ^ (-(1 + η)) ≤ (q : ℝ) ^ (-η) / η := by
  refine Real.tsum_le_of_sum_range_le (fun j => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    fun J => ?_
  have hstep : ∀ j : ℕ, ((j + q + 1 : ℕ) : ℝ) ^ (-(1 + η)) ≤
      (((j + q : ℕ) : ℝ) ^ (-η) - ((j + 1 + q : ℕ) : ℝ) ^ (-η)) / η := by
    intro j
    have ha : (0 : ℝ) < ((j + q : ℕ) : ℝ) := by
      have : 1 ≤ j + q := by omega
      exact_mod_cast this
    have h := RHTower.DiscretePacket.le_rpow_neg_sub_rpow_neg ha
      (show ((j + q : ℕ) : ℝ) ≤ ((j + 1 + q : ℕ) : ℝ) by push_cast; linarith) hη.le
    rw [le_div_iff₀ hη]
    have e1 : ((j + 1 + q : ℕ) : ℝ) - ((j + q : ℕ) : ℝ) = 1 := by push_cast; ring
    have e2 : ((j + q + 1 : ℕ) : ℝ) = ((j + 1 + q : ℕ) : ℝ) := by push_cast; ring
    rw [e1, mul_one, show -(η + 1) = -(1 + η) by ring] at h
    rw [e2]
    linarith
  calc ∑ j ∈ range J, ((j + q + 1 : ℕ) : ℝ) ^ (-(1 + η))
      ≤ ∑ j ∈ range J, (((j + q : ℕ) : ℝ) ^ (-η) - ((j + 1 + q : ℕ) : ℝ) ^ (-η)) / η :=
        sum_le_sum fun j _ => hstep j
    _ = (((0 + q : ℕ) : ℝ) ^ (-η) - ((J + q : ℕ) : ℝ) ^ (-η)) / η := by
        rw [← sum_div]
        congr 1
        exact sum_range_sub' (fun j => ((j + q : ℕ) : ℝ) ^ (-η)) J
    _ ≤ (q : ℝ) ^ (-η) / η := by
        rw [zero_add]
        exact div_le_div_of_nonneg_right
          (by linarith [Real.rpow_nonneg (Nat.cast_nonneg (J + q)) (-η)]) hη.le

/-- **The sign-blind source bound below damping one**: `|P_η(q)| ≤ C_η q^{1−η}`,
`C_η = 1 + 1/(1−η) + 1/η`. -/
theorem abs_centeredPrefix_le_rpow {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (q : ℕ) :
    |pmPowerDampedCenteredDivisorPrefix η q| ≤ (1 + 1 / (1 - η) + 1 / η) * (q : ℝ) ^ (1 - η) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [pmPowerDampedCenteredDivisorPrefix_eq, Nat.cast_zero, Real.zero_rpow (by linarith)]
    simp
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpow : 1 ≤ (q : ℝ) ^ (1 - η) := Real.one_le_rpow hq1 (by linarith)
  set f : ℕ → ℝ := fun d => (moebius d : ℝ) * (d : ℝ) ^ (-(1 + η)) with hfdef
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hμ : ∀ d : ℕ, |(moebius d : ℝ)| ≤ 1 := fun d => by
    rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
  have hfb : ∀ d, ‖f d‖ ≤ (d : ℝ) ^ (-(1 + η)) := fun d => by
    rw [Real.norm_eq_abs, hfdef, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hμ d)
  have hfs : Summable f :=
    Summable.of_norm_bounded (Real.summable_nat_rpow.2 (by linarith)) hfb
  have hρ : (pmPowerDampedDivisorDensity η).re =
      ∑ d ∈ Icc 1 q, f d + ∑' j, f (j + (q + 1)) := by
    rw [density_re_eq_tsum h0, ← hfs.sum_add_tsum_nat_add (q + 1)]
    congr 1
    rw [range_eq_Ico, show Ico 0 (q + 1) = insert 0 (Icc 1 q) by
      ext d; simp only [mem_Ico, mem_insert, mem_Icc]; omega, sum_insert (by simp), hf0, zero_add]
  have hhead : ∀ d ∈ Icc 1 q, f d * q = (moebius d : ℝ) * (d : ℝ) ^ (-η) * ((q : ℝ) / d) := by
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by have := (mem_Icc.1 hd).1; positivity
    simp only [hfdef]
    rw [show -(1 + η) = -η - 1 by ring, Real.rpow_sub_one hd0]
    field_simp
  rw [pmPowerDampedCenteredDivisorPrefix_eq_floor_sum, hρ, add_mul, sum_mul,
    sum_congr rfl hhead]
  have e : (∑ d ∈ Icc 1 q, (moebius d : ℝ) * (d : ℝ) ^ (-η) * ((q / d : ℕ) : ℝ)) -
      (∑ d ∈ Icc 1 q, (moebius d : ℝ) * (d : ℝ) ^ (-η) * ((q : ℝ) / d) +
        (∑' j, f (j + (q + 1))) * q) =
      ∑ d ∈ Icc 1 q, (moebius d : ℝ) * (d : ℝ) ^ (-η) * (((q / d : ℕ) : ℝ) - (q : ℝ) / d) -
        (∑' j, f (j + (q + 1))) * q := by
    rw [← sub_sub, ← sum_sub_distrib]
    congr 1
    exact sum_congr rfl fun d _ => by ring
  rw [e]
  -- the head is at most `1 + q^{1−η}/(1−η)`
  have hH : |∑ d ∈ Icc 1 q, (moebius d : ℝ) * (d : ℝ) ^ (-η) *
      (((q / d : ℕ) : ℝ) - (q : ℝ) / d)| ≤ (1 + 1 / (1 - η)) * (q : ℝ) ^ (1 - η) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hsum := RHTower.sum_rpow_neg_head_le h0 h1 q
    refine le_trans (sum_le_sum fun d hd => ?_) (hsum.trans ?_)
    · have hd1 := (mem_Icc.1 hd).1
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      calc |(moebius d : ℝ)| * (d : ℝ) ^ (-η) * |((q / d : ℕ) : ℝ) - (q : ℝ) / d|
          ≤ 1 * (d : ℝ) ^ (-η) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hμ d) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
              (abs_natDiv_sub_div_le q d (by omega)) (abs_nonneg _) (by positivity)
        _ = (d : ℝ) ^ (-η) := by ring
    · have hd : 0 < 1 - η := by linarith
      rw [add_mul, one_mul, div_mul_eq_mul_div, one_mul]
      linarith
  -- the tail is at most `q^{1−η}/η`
  have hT : |(∑' j, f (j + (q + 1))) * q| ≤ 1 / η * (q : ℝ) ^ (1 - η) := by
    have hs2 : Summable fun j : ℕ => ((j + q + 1 : ℕ) : ℝ) ^ (-(1 + η)) := by
      have := (summable_nat_add_iff (q + 1)).2 (Real.summable_nat_rpow.2 (by linarith : -(1 + η) < -1))
      exact this.congr fun j => by push_cast; ring_nf
    have hb : ∀ j, ‖f (j + (q + 1))‖ ≤ ((j + q + 1 : ℕ) : ℝ) ^ (-(1 + η)) := fun j => by
      rw [show j + q + 1 = j + (q + 1) by ring]; exact hfb _
    have hsf : Summable fun j => f (j + (q + 1)) := Summable.of_norm_bounded hs2 hb
    have h1' : |∑' j, f (j + (q + 1))| ≤ (q : ℝ) ^ (-η) / η :=
      (norm_tsum_le_tsum_norm hsf.norm).trans
        ((hsf.norm.tsum_le_tsum hb hs2).trans (tsum_rpow_tail_le h0 hq))
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    rw [abs_mul, abs_of_pos hq0]
    have hexp : (q : ℝ) ^ (-η) * q = (q : ℝ) ^ (1 - η) := by
      rw [show 1 - η = -η + 1 by ring, Real.rpow_add_one hq0.ne']
    calc |∑' j, f (j + (q + 1))| * q ≤ (q : ℝ) ^ (-η) / η * q :=
          mul_le_mul_of_nonneg_right h1' hq0.le
      _ = 1 / η * (q : ℝ) ^ (1 - η) := by rw [← hexp]; ring
  calc _ ≤ |∑ d ∈ Icc 1 q, (moebius d : ℝ) * (d : ℝ) ^ (-η) *
        (((q / d : ℕ) : ℝ) - (q : ℝ) / d)| + |(∑' j, f (j + (q + 1))) * q| := abs_sub _ _
    _ ≤ (1 + 1 / (1 - η)) * (q : ℝ) ^ (1 - η) + 1 / η * (q : ℝ) ^ (1 - η) := add_le_add hH hT
    _ = _ := by ring

/-- The density is at most one. -/
theorem density_re_le_one {η : ℝ} (hη : 0 < η) : (pmPowerDampedDivisorDensity η).re ≤ 1 := by
  rw [pmPowerDampedDivisorDensity_re_eq hη]
  have hs := summable_realZetaTerm (s := 1 + η) (by linarith)
  have h1 : (1 : ℝ) ≤ realZetaSeries (1 + η) := by
    have := hs.le_tsum 0 fun j _ => Real.rpow_nonneg (by positivity) _
    simpa [realZetaSeries] using this
  rw [div_le_one (by linarith)]
  exact h1

/-- **Jumps of the source**: `|P(a) − P(a')| ≤ a − a'` for `a' ≤ a`. -/
theorem abs_centeredPrefix_sub_le {η : ℝ} (hη : 0 < η) {a a' : ℕ} (h : a' ≤ a) :
    |pmPowerDampedCenteredDivisorPrefix η a - pmPowerDampedCenteredDivisorPrefix η a'| ≤
      ((a - a' : ℕ) : ℝ) := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq, pmPowerDampedCenteredDivisorPrefix_eq]
  have hIcc : ∀ x : ℕ, Icc 1 x = Ioc 0 x := fun x => by ext d; simp only [mem_Icc, mem_Ioc]; omega
  rw [hIcc a, hIcc a', ← sum_Ioc_consecutive _ (Nat.zero_le a') h]
  set S := ∑ j ∈ Ioc a' a, pmPowerDampedDivisorCoeff η j
  have hS0 : 0 ≤ S := sum_nonneg fun j _ => pmPowerDampedDivisorCoeff_nonneg hη.le j
  have hS1 : S ≤ ((a - a' : ℕ) : ℝ) := by
    calc S ≤ ∑ _j ∈ Ioc a' a, (1 : ℝ) := sum_le_sum fun j _ => pmPowerDampedDivisorCoeff_le_one hη.le j
      _ = ((a - a' : ℕ) : ℝ) := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
  have hρ0 := RHTower.pmPowerDampedDivisorDensity_re_pos hη
  have hρ1 := density_re_le_one hη
  have hJ : ((a - a' : ℕ) : ℝ) = (a : ℝ) - a' := by push_cast [h]; ring
  rw [hJ] at hS1 ⊢
  have hd : (0 : ℝ) ≤ (a : ℝ) - a' := by have : (a' : ℝ) ≤ a := by exact_mod_cast h
                                         linarith
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The kernel below damping one -/

/-- `⌊N/K⌋ ≤ N/K` in the reals. -/
theorem natDiv_le_div (N K : ℕ) : ((N / K : ℕ) : ℝ) ≤ (N : ℝ) / K := Nat.cast_div_le

/-- `(K/N)·K^{−(η+1)}·(N/K)^{1−η} = N^{−η}/K`. -/
theorem kernel_rpow_eq {N K η : ℝ} (hN : 0 < N) (hK : 0 < K) :
    K / N * K ^ (-(η + 1)) * (N / K) ^ (1 - η) = N ^ (-η) / K := by
  rw [Real.div_rpow hN.le hK.le]
  have h1 : K * K ^ (-(η + 1)) = K ^ (-η) := by
    rw [mul_comm, ← Real.rpow_add_one hK.ne']; ring_nf
  have h2 : K ^ (-η) / K ^ (1 - η) = 1 / K := by
    rw [← Real.rpow_sub hK, show -η - (1 - η) = -1 by ring, Real.rpow_neg_one, one_div]
  have h3 : N ^ (1 - η) / N = N ^ (-η) := by
    rw [← Real.rpow_sub_one hN.ne']; ring_nf
  calc K / N * K ^ (-(η + 1)) * (N ^ (1 - η) / K ^ (1 - η))
      = (K * K ^ (-(η + 1)) / K ^ (1 - η)) * (N ^ (1 - η) / N) := by
        field_simp
    _ = N ^ (-η) / K := by rw [h1, h2, h3]; ring

/-- **Kernel majorant below damping one.**  With `a = ⌊N/K⌋`, `J = a − ⌊N/(K+1)⌋`:
`|C(n,k)| ≤ η C N^{−η}/K + η ρ K^{−η}/N + (K/N) K^{−η} (min(J, 2C(N/K)^{1−η}) + ρ min(2, J + N/K²))`. -/
theorem abs_centeredRow_le_majorant {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (n k : ℕ) :
    |arithmeticDampingCenteredRow η n k| ≤
      η * (1 + 1 / (1 - η) + 1 / η) * ((n + 1 : ℕ) : ℝ) ^ (-η) / ((k + 1 : ℕ) : ℝ) +
      η * (pmPowerDampedDivisorDensity η).re * ((k + 1 : ℕ) : ℝ) ^ (-η) / ((n + 1 : ℕ) : ℝ) +
      ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-η) *
        (min (((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)
            (2 * (1 + 1 / (1 - η) + 1 / η) *
              (((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ (1 - η)) +
          (pmPowerDampedDivisorDensity η).re *
            min 2 ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ) +
              ((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2)) := by
  set ρ := (pmPowerDampedDivisorDensity η).re
  set C₁ := 1 + 1 / (1 - η) + 1 / η
  set K : ℝ := ((k + 1 : ℕ) : ℝ) with hKdef
  set K' : ℝ := ((k + 1 + 1 : ℕ) : ℝ) with hK'def
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hK : 0 < K := by positivity
  have hK' : 0 < K' := by positivity
  have hN : 0 < N := by positivity
  have hKK' : K ≤ K' := by simp only [hKdef, hK'def]; push_cast; linarith
  have hρ0 : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos h0
  have hC₁ : 0 < C₁ := by have : 0 < 1 - η := by linarith
                          positivity
  set a := (n + 1) / (k + 1)
  set a' := (n + 1) / (k + 1 + 1)
  have haa' : a' ≤ a := Nat.div_le_div_left (by omega) (by omega)
  set J : ℝ := ((a - a' : ℕ) : ℝ) with hJdef
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  -- quotients and their fractional offsets
  have ha : (a : ℝ) ≤ N / K := natDiv_le_div _ _
  have ha' : (a' : ℝ) ≤ N / K' := natDiv_le_div _ _
  have hNK' : N / K' ≤ N / K := div_le_div_of_nonneg_left hN.le hK hKK'
  have hs : |(a : ℝ) - N / K| ≤ 1 := abs_natDiv_sub_div_le _ _ (by omega)
  have hs' : |(a' : ℝ) - N / K'| ≤ 1 := abs_natDiv_sub_div_le _ _ (by omega)
  -- the source at the two quotients
  have hpow : ∀ x : ℕ, (x : ℝ) ≤ N / K → (x : ℝ) ^ (1 - η) ≤ (N / K) ^ (1 - η) := fun x hx =>
    Real.rpow_le_rpow (Nat.cast_nonneg _) hx (by linarith)
  have hPa : |pmPowerDampedCenteredDivisorPrefix η a| ≤ C₁ * (N / K) ^ (1 - η) :=
    (abs_centeredPrefix_le_rpow h0 h1 a).trans
      (mul_le_mul_of_nonneg_left (hpow a ha) hC₁.le)
  have hPa' : |pmPowerDampedCenteredDivisorPrefix η a'| ≤ C₁ * (N / K) ^ (1 - η) :=
    (abs_centeredPrefix_le_rpow h0 h1 a').trans
      (mul_le_mul_of_nonneg_left (hpow a' (ha'.trans hNK')) hC₁.le)
  have hΔP : |pmPowerDampedCenteredDivisorPrefix η a - pmPowerDampedCenteredDivisorPrefix η a'| ≤
      min J (2 * C₁ * (N / K) ^ (1 - η)) := by
    refine le_min (abs_centeredPrefix_sub_le h0 haa') ?_
    calc _ ≤ |pmPowerDampedCenteredDivisorPrefix η a| + |pmPowerDampedCenteredDivisorPrefix η a'| :=
          abs_sub _ _
      _ ≤ _ := by linarith
  have hΔs : |((a : ℝ) - N / K) - ((a' : ℝ) - N / K')| ≤ min 2 (J + N / K ^ 2) := by
    refine le_min ((abs_sub _ _).trans (by linarith)) ?_
    have hJeq : J = (a : ℝ) - a' := by simp only [hJdef]; push_cast [haa']; ring
    have hdiff : N / K - N / K' ≤ N / K ^ 2 := by
      rw [div_sub_div _ _ hK.ne' hK'.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      have hK'e : K' = K + 1 := by simp only [hKdef, hK'def]; push_cast; ring
      rw [hK'e]
      nlinarith [mul_pos hN hK]
    have hdiff0 : 0 ≤ N / K - N / K' := by linarith
    rw [abs_le]
    constructor <;> nlinarith
  -- split the kernel identity
  have hR := centeredRow_eq η n k
  set X := ρ * ((a : ℝ) - N / K) + pmPowerDampedCenteredDivisorPrefix η a
  set X' := ρ * ((a' : ℝ) - N / K') + pmPowerDampedCenteredDivisorPrefix η a'
  have hsplit : arithmeticDampingCenteredRow η n k =
      K / N * ((K ^ (-η) - K' ^ (-η)) * X + K' ^ (-η) * (X - X')) := by rw [hR]; ring
  have hdiffpow : 0 ≤ K ^ (-η) - K' ^ (-η) :=
    sub_nonneg.2 (Real.rpow_le_rpow_of_nonpos hK hKK' (by linarith))
  have hdiffpow' : K ^ (-η) - K' ^ (-η) ≤ η * K ^ (-(η + 1)) := by
    have := RHTower.DiscretePacket.rpow_neg_sub_rpow_neg_le hK hKK' h0.le
    have e : K' - K = 1 := by simp only [hKdef, hK'def]; push_cast; ring
    rwa [e, mul_one] at this
  have hK'pow : K' ^ (-η) ≤ K ^ (-η) := Real.rpow_le_rpow_of_nonpos hK hKK' (by linarith)
  have hK'pow0 : 0 ≤ K' ^ (-η) := Real.rpow_nonneg hK'.le _
  have hX : |X| ≤ ρ + C₁ * (N / K) ^ (1 - η) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ hPa)
    rw [abs_mul, abs_of_pos hρ0]; exact mul_le_of_le_one_right hρ0.le hs
  have hXX : |X - X'| ≤ min J (2 * C₁ * (N / K) ^ (1 - η)) + ρ * min 2 (J + N / K ^ 2) := by
    have e : X - X' = ρ * (((a : ℝ) - N / K) - ((a' : ℝ) - N / K')) +
        (pmPowerDampedCenteredDivisorPrefix η a - pmPowerDampedCenteredDivisorPrefix η a') := by
      simp only [X, X']; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hρ0]
    linarith [mul_le_mul_of_nonneg_left hΔs hρ0.le]
  rw [hsplit, abs_mul, abs_of_pos (div_pos hK hN)]
  have hmain : |(K ^ (-η) - K' ^ (-η)) * X + K' ^ (-η) * (X - X')| ≤
      η * K ^ (-(η + 1)) * (ρ + C₁ * (N / K) ^ (1 - η)) +
        K ^ (-η) * (min J (2 * C₁ * (N / K) ^ (1 - η)) + ρ * min 2 (J + N / K ^ 2)) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hdiffpow]
      exact mul_le_mul hdiffpow' hX (abs_nonneg _) (by positivity)
    · rw [abs_mul, abs_of_nonneg hK'pow0]
      exact mul_le_mul hK'pow hXX (abs_nonneg _) (Real.rpow_nonneg hK.le _)
  have hT1 := kernel_rpow_eq (η := η) hN hK
  have hT2 : K / N * K ^ (-(η + 1)) = K ^ (-η) / N := by
    rw [div_mul_eq_mul_div, mul_comm K, ← Real.rpow_add_one hK.ne']; ring_nf
  calc K / N * |(K ^ (-η) - K' ^ (-η)) * X + K' ^ (-η) * (X - X')|
      ≤ K / N * (η * K ^ (-(η + 1)) * (ρ + C₁ * (N / K) ^ (1 - η)) +
          K ^ (-η) * (min J (2 * C₁ * (N / K) ^ (1 - η)) + ρ * min 2 (J + N / K ^ 2))) :=
        mul_le_mul_of_nonneg_left hmain (div_pos hK hN).le
    _ = η * C₁ * (K / N * K ^ (-(η + 1)) * (N / K) ^ (1 - η)) +
          η * ρ * (K / N * K ^ (-(η + 1))) +
          K / N * K ^ (-η) * (min J (2 * C₁ * (N / K) ^ (1 - η)) +
            ρ * min 2 (J + N / K ^ 2)) := by ring
    _ = _ := by rw [hT1, hT2]; ring

/-! ### The interpolation exponent -/

/-- The interpolation exponent `λ`, the midpoint of `(1/(2(1+η)), 1 − 1/(2η))`. -/
def interpExp (η : ℝ) : ℝ := (1 / (2 * (1 + η)) + (1 - 1 / (2 * η))) / 2

theorem interpExp_bounds {η : ℝ} (h0 : 0 < η) (h2 : 1 / 2 < η ^ 2) :
    0 < interpExp η ∧ interpExp η < 1 ∧ 1 < 2 * interpExp η * (1 + η) ∧
      1 < 2 * η * (1 - interpExp η) := by
  set a := 1 / (2 * (1 + η)) with hadef
  set b := 1 - 1 / (2 * η) with hbdef
  have hgap : a < b := by
    have e : b - a = (2 * η ^ 2 - 1) / (2 * η * (1 + η)) := by
      simp only [hadef, hbdef]; field_simp; ring
    have : 0 < (2 * η ^ 2 - 1) / (2 * η * (1 + η)) := div_pos (by linarith) (by positivity)
    linarith
  have ha : 0 < a := by positivity
  have hb : b < 1 := by have : 0 < 1 / (2 * η) := by positivity
                        linarith
  have hlam : interpExp η = (a + b) / 2 := rfl
  rw [hlam]
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · have e : a * (2 * (1 + η)) = 1 := by simp only [hadef]; field_simp
    nlinarith [mul_lt_mul_of_pos_right (show a < (a + b) / 2 by linarith)
      (by positivity : (0 : ℝ) < 2 * (1 + η))]
  · have e : 1 / (2 * η) * (2 * η) = 1 := by field_simp
    have hlt : 1 / (2 * η) < 1 - (a + b) / 2 := by
      have : (a + b) / 2 < b := by linarith
      simp only [hbdef] at this ⊢; linarith
    nlinarith [mul_lt_mul_of_pos_right hlt (by positivity : (0 : ℝ) < 2 * η)]

/-- `min x y ≤ x^λ y^{1−λ}` for `x, y ≥ 0`, `0 ≤ λ ≤ 1`. -/
theorem min_le_rpow_mul_rpow {x y l : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    min x y ≤ x ^ l * y ^ (1 - l) := by
  rcases le_total x y with hxy | hxy
  · rw [min_eq_left hxy]
    calc x = x ^ l * x ^ (1 - l) := by
          rcases hx.eq_or_lt with h | h
          · subst h
            rcases hl0.eq_or_lt with h' | h'
            · subst h'; simp
            · rw [Real.zero_rpow h'.ne', zero_mul]
          · rw [← Real.rpow_add h]; simp
      _ ≤ x ^ l * y ^ (1 - l) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy (by linarith))
            (Real.rpow_nonneg hx _)
  · rw [min_eq_right hxy]
    calc y = y ^ l * y ^ (1 - l) := by
          rcases hy.eq_or_lt with h | h
          · subst h
            rcases (sub_nonneg.2 hl1).eq_or_lt with h' | h'
            · rw [← h']; simp
              have : l = 1 := by linarith
              rw [this]; simp
            · rw [Real.zero_rpow h'.ne', mul_zero]
          · rw [← Real.rpow_add h]; simp
      _ ≤ x ^ l * y ^ (1 - l) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hy hxy hl0)
            (Real.rpow_nonneg hy _)

/-- `(K^{1−η}/N)(N/K²)^λ((N/K)^{1−η})^{1−λ} = N^{−η(1−λ)} K^{−λ(1+η)}`. -/
theorem interp_rpow_eq {N K η l : ℝ} (hN : 0 < N) (hK : 0 < K) :
    K ^ (1 - η) / N * ((N / K ^ 2) ^ l * ((N / K) ^ (1 - η)) ^ (1 - l)) =
      N ^ (-(η * (1 - l))) * K ^ (-(l * (1 + η))) := by
  obtain ⟨u, rfl⟩ : ∃ u, N = Real.exp u := ⟨Real.log N, (Real.exp_log hN).symm⟩
  obtain ⟨v, rfl⟩ : ∃ v, K = Real.exp v := ⟨Real.log K, (Real.exp_log hK).symm⟩
  rw [← Real.exp_nat_mul]
  simp only [← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-! ### The squared majorant -/

theorem sq_rpow_eq {x a : ℝ} (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; push_cast; ring_nf

theorem sq_inv_eq_rpow {x : ℝ} (hx : 0 < x) : (1 / x) ^ 2 = x ^ (-2 : ℝ) := by
  rw [Real.rpow_neg hx.le, one_div, inv_pow, Real.rpow_two]

theorem mul_rpow_neg_eq {x a : ℝ} (hx : 0 < x) : x * x ^ (-a) = x ^ (1 - a) := by
  rw [mul_comm, ← Real.rpow_add_one hx.ne']; ring_nf

/-- The region-wise squared majorant of the kernel (`A`: `K² ≤ N`, `B`: `K² > N`). -/
def chainMajorant (η : ℝ) (n k : ℕ) : ℝ :=
  3 * ((η * (1 + 1 / (1 - η) + 1 / η)) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-2 * η) *
        ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) +
      (η * (pmPowerDampedDivisorDensity η).re) ^ 2 * (((k + 1 : ℕ) : ℝ) ^ (-2 * η) *
        ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) +
  3 * (if (k + 1) * (k + 1) ≤ n + 1 then
      8 * (1 + 1 / (1 - η) + 1 / η) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-(2 * (η * (1 - interpExp η)))) *
          ((k + 1 : ℕ) : ℝ) ^ (-(2 * (interpExp η * (1 + η))))) +
        8 * (pmPowerDampedDivisorDensity η).re ^ 2 *
          (((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) * ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ))
    else
      2 * (1 + (pmPowerDampedDivisorDensity η).re) ^ 2 *
          (((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) * ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ) *
            ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ))) +
        2 * (pmPowerDampedDivisorDensity η).re ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-2 - 2 * η))

theorem add_sq_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

theorem add3_sq_le_three (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- Below the square root the floor jump is at most `2N/K²`. -/
theorem floorJump_le_of_sq_le {n k : ℕ} (hA : (k + 1) * (k + 1) ≤ n + 1) :
    ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)) ≤
      2 * (((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
  set K : ℝ := ((k + 1 : ℕ) : ℝ) with hKdef
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hK : 0 < K := by positivity
  have hN : 0 < N := by positivity
  have hK' : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) := by positivity
  have hle : (n + 1) / (k + 1 + 1) ≤ (n + 1) / (k + 1) := Nat.div_le_div_left (by omega) (by omega)
  have ha := natDiv_le_div (n + 1) (k + 1)
  have ha' := abs_natDiv_sub_div_le (n + 1) (k + 1 + 1) (by omega)
  rw [abs_le] at ha'
  have hdiff : N / K - N / ((k + 1 + 1 : ℕ) : ℝ) ≤ N / K ^ 2 := by
    rw [div_sub_div _ _ hK.ne' hK'.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    have hK'e : ((k + 1 + 1 : ℕ) : ℝ) = K + 1 := by simp only [hKdef]; push_cast; ring
    rw [hK'e]; nlinarith [mul_pos hN hK]
  have h1' : 1 ≤ N / K ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    simp only [hKdef, hNdef]; exact_mod_cast (by nlinarith : (k + 1) ^ 2 ≤ n + 1)
  push_cast [hle]
  linarith [ha'.1]

/-- Region `K² ≤ N`: interpolate the short-interval bound. -/
theorem regionA_sq_le {N K J C₁ ρ η l : ℝ} (hN : 0 < N) (hK : 0 < K) (hJ0 : 0 ≤ J)
    (hJA : J ≤ 2 * (N / K ^ 2)) (hC₁ : 1 ≤ C₁) (hρ0 : 0 < ρ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    (K ^ (1 - η) / N * (min J (2 * C₁ * (N / K) ^ (1 - η)) + ρ * min 2 (J + N / K ^ 2))) ^ 2 ≤
      8 * C₁ ^ 2 * (N ^ (-(2 * (η * (1 - l)))) * K ^ (-(2 * (l * (1 + η))))) +
        8 * ρ ^ 2 * (K ^ (2 - 2 * η) * N ^ (-2 : ℝ)) := by
  have hm := min_le_rpow_mul_rpow (x := N / K ^ 2) (y := (N / K) ^ (1 - η))
    (by positivity) (by positivity) hl0 hl1
  have hD3 : min J (2 * C₁ * (N / K) ^ (1 - η)) ≤
      2 * C₁ * ((N / K ^ 2) ^ l * ((N / K) ^ (1 - η)) ^ (1 - l)) := by
    have h2 : J ≤ 2 * C₁ * (N / K ^ 2) := by
      have : 0 ≤ N / K ^ 2 := by positivity
      nlinarith
    calc min J (2 * C₁ * (N / K) ^ (1 - η))
        ≤ min (2 * C₁ * (N / K ^ 2)) (2 * C₁ * (N / K) ^ (1 - η)) := min_le_min_right _ h2
      _ = 2 * C₁ * min (N / K ^ 2) ((N / K) ^ (1 - η)) := by
          rw [mul_min_of_nonneg _ _ (by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  have hp : 0 ≤ K ^ (1 - η) / N := by positivity
  have hx : K ^ (1 - η) / N * min J (2 * C₁ * (N / K) ^ (1 - η)) ≤
      2 * C₁ * (N ^ (-(η * (1 - l))) * K ^ (-(l * (1 + η)))) := by
    calc _ ≤ K ^ (1 - η) / N * (2 * C₁ * ((N / K ^ 2) ^ l * ((N / K) ^ (1 - η)) ^ (1 - l))) :=
          mul_le_mul_of_nonneg_left hD3 hp
      _ = 2 * C₁ * (K ^ (1 - η) / N * ((N / K ^ 2) ^ l * ((N / K) ^ (1 - η)) ^ (1 - l))) := by ring
      _ = _ := by rw [interp_rpow_eq hN hK]
  have hy : K ^ (1 - η) / N * (ρ * min 2 (J + N / K ^ 2)) ≤ 2 * ρ * (K ^ (1 - η) / N) := by
    have h := mul_le_mul_of_nonneg_left (min_le_left (2 : ℝ) (J + N / K ^ 2)) hρ0.le
    calc _ ≤ K ^ (1 - η) / N * (ρ * 2) := mul_le_mul_of_nonneg_left h hp
      _ = _ := by ring
  have hx0 : 0 ≤ K ^ (1 - η) / N * min J (2 * C₁ * (N / K) ^ (1 - η)) :=
    mul_nonneg hp (le_min hJ0 (by positivity))
  have hy0 : 0 ≤ K ^ (1 - η) / N * (ρ * min 2 (J + N / K ^ 2)) :=
    mul_nonneg hp (mul_nonneg hρ0.le (le_min (by norm_num) (by positivity)))
  have ex : (2 * C₁ * (N ^ (-(η * (1 - l))) * K ^ (-(l * (1 + η))))) ^ 2 =
      4 * C₁ ^ 2 * (N ^ (-(2 * (η * (1 - l)))) * K ^ (-(2 * (l * (1 + η))))) := by
    simp only [mul_pow]; rw [sq_rpow_eq hN, sq_rpow_eq hK]; ring_nf
  have ey : (2 * ρ * (K ^ (1 - η) / N)) ^ 2 = 4 * ρ ^ 2 * (K ^ (2 - 2 * η) * N ^ (-2 : ℝ)) := by
    rw [div_eq_mul_one_div]; simp only [mul_pow]; rw [sq_rpow_eq hK, sq_inv_eq_rpow hN]; ring_nf
  have hsum := add_sq_le_two (K ^ (1 - η) / N * min J (2 * C₁ * (N / K) ^ (1 - η)))
    (K ^ (1 - η) / N * (ρ * min 2 (J + N / K ^ 2)))
  have hxx := pow_le_pow_left₀ hx0 hx 2
  have hyy := pow_le_pow_left₀ hy0 hy 2
  rw [ex] at hxx
  rw [ey] at hyy
  rw [mul_add]
  linarith

/-- Region `K² > N`: at most one jump. -/
theorem regionB_sq_le {N K J C₁ ρ η : ℝ} (hN : 0 < N) (hK : 0 < K) (hJ0 : 0 ≤ J) (hJB : J ≤ 1)
    (hC₁ : 0 ≤ C₁) (hρ0 : 0 < ρ) :
    (K ^ (1 - η) / N * (min J (2 * C₁ * (N / K) ^ (1 - η)) + ρ * min 2 (J + N / K ^ 2))) ^ 2 ≤
      2 * (1 + ρ) ^ 2 * (K ^ (2 - 2 * η) * N ^ (-2 : ℝ) * J) +
        2 * ρ ^ 2 * K ^ (-2 - 2 * η) := by
  have hp : 0 ≤ K ^ (1 - η) / N := by positivity
  have hD3 : min J (2 * C₁ * (N / K) ^ (1 - η)) ≤ J := min_le_left _ _
  have hD4 : min 2 (J + N / K ^ 2) ≤ J + N / K ^ 2 := min_le_right _ _
  have hKK : K ^ (1 - η) / N * (N / K ^ 2) = K ^ (-1 - η) := by
    have : K ^ (1 - η) / K ^ 2 = K ^ (-1 - η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub hK]; push_cast; ring_nf
    rw [← this]; field_simp
  have hb : K ^ (1 - η) / N * (min J (2 * C₁ * (N / K) ^ (1 - η)) + ρ * min 2 (J + N / K ^ 2)) ≤
      (1 + ρ) * (K ^ (1 - η) / N * J) + ρ * K ^ (-1 - η) := by
    have h1 := mul_le_mul_of_nonneg_left hD3 hp
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD4 hρ0.le) hp
    have e : K ^ (1 - η) / N * (ρ * (J + N / K ^ 2)) =
        ρ * (K ^ (1 - η) / N * J) + ρ * (K ^ (1 - η) / N * (N / K ^ 2)) := by ring
    rw [hKK] at e
    nlinarith
  have hb0 : 0 ≤ K ^ (1 - η) / N *
      (min J (2 * C₁ * (N / K) ^ (1 - η)) + ρ * min 2 (J + N / K ^ 2)) := by
    refine mul_nonneg hp (add_nonneg ?_ (mul_nonneg hρ0.le ?_))
    · exact le_min hJ0 (by positivity)
    · exact le_min (by norm_num) (by positivity)
  have hJsq : (K ^ (1 - η) / N) ^ 2 * J ^ 2 ≤ K ^ (2 - 2 * η) * N ^ (-2 : ℝ) * J := by
    have hJJ : J ^ 2 ≤ J := by nlinarith
    have ex : (K ^ (1 - η) / N) ^ 2 = K ^ (2 - 2 * η) * N ^ (-2 : ℝ) := by
      rw [div_eq_mul_one_div]; simp only [mul_pow]; rw [sq_rpow_eq hK, sq_inv_eq_rpow hN]; ring_nf
    rw [ex]
    exact mul_le_mul_of_nonneg_left hJJ (by positivity)
  have ey : (K ^ (-1 - η)) ^ 2 = K ^ (-2 - 2 * η) := by rw [sq_rpow_eq hK]; ring_nf
  have hsq := pow_le_pow_left₀ hb0 hb 2
  have h2 := add_sq_le_two ((1 + ρ) * (K ^ (1 - η) / N * J)) (ρ * K ^ (-1 - η))
  simp only [mul_pow] at h2
  rw [ey] at h2
  have h3 := mul_le_mul_of_nonneg_left hJsq (sq_nonneg (1 + ρ))
  linarith

/-- **The kernel is dominated by its majorant** for `½ < η²` and `η < 1`. -/
theorem sq_centeredRow_le_majorant {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (h2 : 1 / 2 < η ^ 2)
    (n k : ℕ) : arithmeticDampingCenteredRow η n k ^ 2 ≤ chainMajorant η n k := by
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hρ0 := RHTower.pmPowerDampedDivisorDensity_re_pos h0
  have hC₁ : 1 ≤ 1 + 1 / (1 - η) + 1 / η := by
    have : 0 < 1 - η := by linarith
    have : 0 ≤ 1 / (1 - η) + 1 / η := by positivity
    linarith
  obtain ⟨hl0, hl1, -, -⟩ := interpExp_bounds h0 h2
  have hJ0 : (0 : ℝ) ≤ ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)) := Nat.cast_nonneg _
  have hmaj := abs_centeredRow_le_majorant h0 h1 n k
  rw [div_mul_eq_mul_div, mul_rpow_neg_eq hK] at hmaj
  have hsq := (pow_le_pow_left₀ (abs_nonneg _) hmaj 2).trans (add3_sq_le_three _ _ _)
  rw [sq_abs] at hsq
  have e1 : (η * (1 + 1 / (1 - η) + 1 / η) * ((n + 1 : ℕ) : ℝ) ^ (-η) / ((k + 1 : ℕ) : ℝ)) ^ 2 =
      (η * (1 + 1 / (1 - η) + 1 / η)) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-2 * η) *
        ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    rw [div_eq_mul_one_div, mul_pow, mul_pow, sq_rpow_eq hN, sq_inv_eq_rpow hK]; ring_nf
  have e2 : (η * (pmPowerDampedDivisorDensity η).re * ((k + 1 : ℕ) : ℝ) ^ (-η) /
      ((n + 1 : ℕ) : ℝ)) ^ 2 = (η * (pmPowerDampedDivisorDensity η).re) ^ 2 *
        (((k + 1 : ℕ) : ℝ) ^ (-2 * η) * ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    rw [div_eq_mul_one_div, mul_pow, mul_pow, sq_rpow_eq hK, sq_inv_eq_rpow hN]; ring_nf
  rw [e1, e2] at hsq
  unfold chainMajorant
  split_ifs with hA
  · have hR := regionA_sq_le (η := η) (C₁ := 1 + 1 / (1 - η) + 1 / η)
      (ρ := (pmPowerDampedDivisorDensity η).re) (l := interpExp η) hN hK hJ0
      (floorJump_le_of_sq_le hA) hC₁ hρ0 hl0.le hl1.le
    linarith
  · have hJB : ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)) ≤ 1 := by
      have := div_sub_div_succ_le_one (N := n + 1) (K := k + 1) (by push Not at hA; omega)
      exact_mod_cast this
    have hR := regionB_sq_le (η := η) (C₁ := 1 + 1 / (1 - η) + 1 / η) hN hK hJ0 hJB
      (by linarith) hρ0
    linarith

/-! ### Summing the majorant -/

/-- Partial sums of `(k+1)^{−s}` are at most `ζ(s)`. -/
theorem sum_range_rpow_le_zeta {s : ℝ} (hs : 1 < s) (M : ℕ) :
    ∑ k ∈ range M, ((k + 1 : ℕ) : ℝ) ^ (-s) ≤ realZetaSeries s := by
  have h := summable_realZetaTerm hs
  refine le_trans (le_of_eq (sum_congr rfl fun k _ => ?_))
    (h.sum_le_tsum (range M) fun k _ => Real.rpow_nonneg (by positivity) _)
  push_cast; rfl

/-- Product sums of two zeta tails. -/
theorem sum_sum_rpow_le {s t : ℝ} (hs : 1 < s) (ht : 1 < t) (T M : ℕ) :
    ∑ n ∈ range T, ∑ k ∈ range M, ((n + 1 : ℕ) : ℝ) ^ (-s) * ((k + 1 : ℕ) : ℝ) ^ (-t) ≤
      realZetaSeries s * realZetaSeries t := by
  rw [← sum_mul_sum]
  exact mul_le_mul (sum_range_rpow_le_zeta hs T) (sum_range_rpow_le_zeta ht M)
    (sum_nonneg fun k _ => Real.rpow_nonneg (by positivity) _)
    (le_trans (sum_nonneg fun n _ => Real.rpow_nonneg (by positivity) _)
      (sum_range_rpow_le_zeta hs T))

/-- `(Nat.sqrt N)^p ≤ N^{p/2}`. -/
theorem natSqrt_rpow_le {N : ℕ} {p : ℝ} (hp : 0 ≤ p) :
    ((Nat.sqrt N : ℕ) : ℝ) ^ p ≤ (N : ℝ) ^ (p / 2) := by
  have h1 : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast (by nlinarith [Nat.sqrt_le' N] : Nat.sqrt N ^ 2 ≤ N)
  calc ((Nat.sqrt N : ℕ) : ℝ) ^ p ≤ (Real.sqrt N) ^ p :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h1 hp
    _ = (N : ℝ) ^ (p / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg _)]; ring_nf

/-- Below the square root: `Σ_{K² ≤ N} K^{2−2η} ≤ N^{(3−2η)/2}`. -/
theorem sum_below_sqrt_le {η : ℝ} (h1 : η < 1) (n M : ℕ) :
    ∑ k ∈ range M, (if (k + 1) * (k + 1) ≤ n + 1 then ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) else 0) ≤
      ((n + 1 : ℕ) : ℝ) ^ ((3 - 2 * η) / 2) := by
  set r := Nat.sqrt (n + 1)
  have hp : 0 ≤ 2 - 2 * η := by linarith
  rw [← sum_filter]
  have hsub : (range M).filter (fun k => (k + 1) * (k + 1) ≤ n + 1) ⊆ range r := by
    intro k hk
    simp only [mem_filter, mem_range] at hk ⊢
    have : k + 1 ≤ r := Nat.le_sqrt.2 hk.2
    omega
  calc ∑ k ∈ (range M).filter (fun k => (k + 1) * (k + 1) ≤ n + 1), ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η)
      ≤ ∑ k ∈ range r, ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) :=
        sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => Real.rpow_nonneg (by positivity) _
    _ ≤ ∑ _k ∈ range r, ((r : ℕ) : ℝ) ^ (2 - 2 * η) := by
        refine sum_le_sum fun k hk => Real.rpow_le_rpow (by positivity) ?_ hp
        exact_mod_cast (by simpa using hk : k < r)
    _ = ((r : ℕ) : ℝ) * ((r : ℕ) : ℝ) ^ (2 - 2 * η) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ = ((r : ℕ) : ℝ) ^ (3 - 2 * η) := by
        rcases Nat.eq_zero_or_pos r with h | h
        · rw [h, Nat.cast_zero, zero_mul, Real.zero_rpow (by linarith)]
        · have hr0 : (0 : ℝ) < r := by exact_mod_cast h
          rw [show (3 : ℝ) - 2 * η = (2 - 2 * η) + 1 by ring, Real.rpow_add_one hr0.ne', mul_comm]
    _ ≤ _ := natSqrt_rpow_le (by linarith)

/-- Above the square root: `Σ_{K² > N} K^{2−2η} J ≤ (1 + 1/(2η−1)) N^{(3−2η)/2}`. -/
theorem sum_above_sqrt_le {η : ℝ} (h1 : η < 1) (hh : 1 / 2 < η) (n M : ℕ) :
    ∑ k ∈ range M, (if (k + 1) * (k + 1) ≤ n + 1 then 0 else
      ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) * ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ))) ≤
      (1 + 1 / (2 * η - 1)) * ((n + 1 : ℕ) : ℝ) ^ ((3 - 2 * η) / 2) := by
  set p := 2 - 2 * η
  have hp0 : 0 < p := by simp only [p]; linarith
  have hp1 : p < 1 := by simp only [p]; linarith
  -- only jumps contribute, each with weight one
  have hterm : ∀ k ∈ range M, (if (k + 1) * (k + 1) ≤ n + 1 then 0 else
      ((k + 1 : ℕ) : ℝ) ^ p * ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ))) ≤
      (if n + 1 < (k + 1) * (k + 1) ∧ (n + 1) / (k + 1 + 1) < (n + 1) / (k + 1) then
        ((k + 1 : ℕ) : ℝ) ^ p else 0) := by
    intro k _
    by_cases hA : (k + 1) * (k + 1) ≤ n + 1
    · rw [if_pos hA, if_neg (by omega)]
    · rw [if_neg hA]
      have hJ := div_sub_div_succ_le_one (N := n + 1) (K := k + 1) (by omega)
      by_cases hj : (n + 1) / (k + 1 + 1) < (n + 1) / (k + 1)
      · rw [if_pos ⟨by omega, hj⟩]
        have : ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)) ≤ 1 := by exact_mod_cast hJ
        exact mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _) this
      · rw [if_neg (fun h => hj h.2)]
        have : (n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) = 0 := by omega
        rw [this]; simp
  refine (sum_le_sum hterm).trans ?_
  -- reindex the jumps
  have hre : ∑ k ∈ range M, (if n + 1 < (k + 1) * (k + 1) ∧
      (n + 1) / (k + 1 + 1) < (n + 1) / (k + 1) then ((k + 1 : ℕ) : ℝ) ^ p else 0) =
      ∑ K ∈ floorJumps (n + 1) M, (K : ℝ) ^ p := by
    rw [floorJumps, sum_filter, show Icc 1 M = Ico 1 (M + 1) by ext; simp only [mem_Icc, mem_Ico]; omega,
      sum_Ico_eq_sum_range, show M + 1 - 1 = M by omega]
    exact sum_congr rfl fun k _ => by rw [add_comm 1 k]
  rw [hre]
  refine (sum_floorJump_le (n + 1) M hp0.le).trans ?_
  set r := Nat.sqrt (n + 1)
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsplit : ∑ m ∈ Icc 1 r, (((n + 1 : ℕ) : ℝ) / m) ^ p =
      ((n + 1 : ℕ) : ℝ) ^ p * ∑ m ∈ Icc 1 r, (m : ℝ) ^ (-p) := by
    rw [mul_sum]
    refine sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by have := (mem_Icc.1 hm).1; exact_mod_cast this
    rw [Real.div_rpow hN.le hm0.le, Real.rpow_neg hm0.le, div_eq_mul_inv]
  rw [hsplit]
  have hhead := RHTower.sum_rpow_neg_head_le hp0 hp1 r
  have hr := natSqrt_rpow_le (N := n + 1) (p := 1 - p) (by linarith)
  have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ ((1 - p) / 2) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n + 1)) (by linarith)
  have h2η : 1 - p = 2 * η - 1 := by simp only [p]; ring
  have hc : 0 < 2 * η - 1 := by linarith
  have hbound : ∑ m ∈ Icc 1 r, (m : ℝ) ^ (-p) ≤
      (1 + 1 / (2 * η - 1)) * ((n + 1 : ℕ) : ℝ) ^ ((1 - p) / 2) := by
    rw [h2η] at hhead hr hone ⊢
    have : (r : ℝ) ^ (2 * η - 1) / (2 * η - 1) ≤ ((n + 1 : ℕ) : ℝ) ^ ((2 * η - 1) / 2) / (2 * η - 1) :=
      div_le_div_of_nonneg_right hr hc.le
    rw [add_mul, one_mul, div_mul_eq_mul_div, one_mul]
    linarith
  have hexp : ((n + 1 : ℕ) : ℝ) ^ p * ((n + 1 : ℕ) : ℝ) ^ ((1 - p) / 2) =
      ((n + 1 : ℕ) : ℝ) ^ ((3 - 2 * η) / 2) := by
    rw [← Real.rpow_add hN]; simp only [p]; ring_nf
  calc ((n + 1 : ℕ) : ℝ) ^ p * ∑ m ∈ Icc 1 r, (m : ℝ) ^ (-p)
      ≤ ((n + 1 : ℕ) : ℝ) ^ p * ((1 + 1 / (2 * η - 1)) * ((n + 1 : ℕ) : ℝ) ^ ((1 - p) / 2)) :=
        mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hN.le _)
    _ = (1 + 1 / (2 * η - 1)) * (((n + 1 : ℕ) : ℝ) ^ p * ((n + 1 : ℕ) : ℝ) ^ ((1 - p) / 2)) := by
        ring
    _ = _ := by rw [hexp]

/-- Above the square root, each column meets fewer than `K²` rows: `Σ ≤ ζ(2η)`. -/
theorem sum_above_sqrt_tail_le {η : ℝ} (hh : 1 / 2 < η) (T M : ℕ) :
    ∑ n ∈ range T, ∑ k ∈ range M, (if (k + 1) * (k + 1) ≤ n + 1 then 0 else
      ((k + 1 : ℕ) : ℝ) ^ (-2 - 2 * η)) ≤ realZetaSeries (2 * η) := by
  rw [sum_comm]
  refine le_trans (sum_le_sum fun k _ => ?_) (sum_range_rpow_le_zeta (s := 2 * η) (by linarith) M)
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
  have hcard : (((range T).filter fun n => ¬ (k + 1) * (k + 1) ≤ n + 1).card : ℝ) ≤
      ((k + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
    have : ((range T).filter fun n => ¬ (k + 1) * (k + 1) ≤ n + 1).card ≤ (k + 1) * (k + 1) := by
      refine (card_le_card fun n hn => ?_).trans (card_range _).le
      simp only [mem_filter, mem_range] at hn ⊢; omega
    rw [Real.rpow_two]; exact_mod_cast (by nlinarith : _ ≤ (k + 1) ^ 2)
  calc (((range T).filter fun n => ¬ (k + 1) * (k + 1) ≤ n + 1).card : ℝ) *
        ((k + 1 : ℕ) : ℝ) ^ (-2 - 2 * η)
      ≤ ((k + 1 : ℕ) : ℝ) ^ (2 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-2 - 2 * η) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hK.le _)
    _ = ((k + 1 : ℕ) : ℝ) ^ (-(2 * η)) := by rw [← Real.rpow_add hK]; ring_nf

/-- The Hilbert–Schmidt constant of the chain below damping one. -/
def chainHSConstant (η : ℝ) : ℝ :=
  3 * ((η * (1 + 1 / (1 - η) + 1 / η)) ^ 2 * (realZetaSeries (2 * η) * realZetaSeries 2) +
      (η * (pmPowerDampedDivisorDensity η).re) ^ 2 * (realZetaSeries 2 * realZetaSeries (2 * η))) +
  3 * (8 * (1 + 1 / (1 - η) + 1 / η) ^ 2 *
        (realZetaSeries (2 * (η * (1 - interpExp η))) *
          realZetaSeries (2 * (interpExp η * (1 + η)))) +
      8 * (pmPowerDampedDivisorDensity η).re ^ 2 * realZetaSeries ((1 + 2 * η) / 2) +
      2 * (1 + (pmPowerDampedDivisorDensity η).re) ^ 2 * ((1 + 1 / (2 * η - 1)) *
        realZetaSeries ((1 + 2 * η) / 2)) +
      2 * (pmPowerDampedDivisorDensity η).re ^ 2 * realZetaSeries (2 * η))

/-- `N^{−2} N^{(3−2η)/2} = N^{−(1+2η)/2}`. -/
theorem rpow_neg_two_mul_rpow {N η : ℝ} (hN : 0 < N) :
    N ^ (-2 : ℝ) * N ^ ((3 - 2 * η) / 2) = N ^ (-((1 + 2 * η) / 2)) := by
  rw [← Real.rpow_add hN]; ring_nf

theorem sum_sum_linear (T M : ℕ) (a b c d e f : ℝ) (F1 F2 F3 F4 F5 F6 : ℕ → ℕ → ℝ) :
    ∑ n ∈ range T, ∑ k ∈ range M, (3 * (a * F1 n k + b * F2 n k) +
      3 * (c * F3 n k + d * F4 n k + e * F5 n k + f * F6 n k)) =
    3 * (a * ∑ n ∈ range T, ∑ k ∈ range M, F1 n k + b * ∑ n ∈ range T, ∑ k ∈ range M, F2 n k) +
    3 * (c * ∑ n ∈ range T, ∑ k ∈ range M, F3 n k + d * ∑ n ∈ range T, ∑ k ∈ range M, F4 n k +
      e * ∑ n ∈ range T, ∑ k ∈ range M, F5 n k + f * ∑ n ∈ range T, ∑ k ∈ range M, F6 n k) := by
  simp only [sum_add_distrib, mul_sum, mul_add]

/-- **The majorant is summable**: every partial double sum is at most `chainHSConstant η`. -/
theorem sum_chainMajorant_le {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (h2 : 1 / 2 < η ^ 2) (T M : ℕ) :
    ∑ n ∈ range T, ∑ k ∈ range M, chainMajorant η n k ≤ chainHSConstant η := by
  set ρ := (pmPowerDampedDivisorDensity η).re
  set C₁ := 1 + 1 / (1 - η) + 1 / η
  set l := interpExp η
  have hh : 1 / 2 < η := by nlinarith
  obtain ⟨-, -, hl2, hl3⟩ := interpExp_bounds h0 h2
  have hρ0 : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos h0
  have hs : 1 < (1 + 2 * η) / 2 := by linarith
  have hite : ∀ n k, chainMajorant η n k ≤
      3 * ((η * C₁) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-(2 * η)) * ((k + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) +
          (η * ρ) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((k + 1 : ℕ) : ℝ) ^ (-(2 * η)))) +
      3 * (8 * C₁ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-(2 * (η * (1 - l)))) *
            ((k + 1 : ℕ) : ℝ) ^ (-(2 * (l * (1 + η))))) +
          8 * ρ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * (if (k + 1) * (k + 1) ≤ n + 1 then
            ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) else 0)) +
          2 * (1 + ρ) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * (if (k + 1) * (k + 1) ≤ n + 1 then 0
            else ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) *
              ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)))) +
          2 * ρ ^ 2 * (if (k + 1) * (k + 1) ≤ n + 1 then 0 else
            ((k + 1 : ℕ) : ℝ) ^ (-2 - 2 * η))) := by
    intro n k
    have hNK1 : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-(2 * (η * (1 - l)))) *
        ((k + 1 : ℕ) : ℝ) ^ (-(2 * (l * (1 + η)))) := by positivity
    unfold chainMajorant
    rw [show (-2 : ℝ) * η = -(2 * η) by ring]
    split_ifs with hA
    · simp only [mul_zero, add_zero]
      nlinarith [mul_comm (((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) (((k + 1 : ℕ) : ℝ) ^ (-(2 * η)))]
    · have hJ0 : (0 : ℝ) ≤ ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ)) :=
        Nat.cast_nonneg _
      simp only [mul_zero]
      nlinarith [mul_comm (((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) (((k + 1 : ℕ) : ℝ) ^ (-(2 * η)))]
  refine (sum_le_sum fun n _ => sum_le_sum fun k _ => hite n k).trans ?_
  refine (le_of_eq (sum_sum_linear T M ((η * C₁) ^ 2) ((η * ρ) ^ 2) (8 * C₁ ^ 2) (8 * ρ ^ 2)
    (2 * (1 + ρ) ^ 2) (2 * ρ ^ 2)
    (fun n k => ((n + 1 : ℕ) : ℝ) ^ (-(2 * η)) * ((k + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)))
    (fun n k => ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((k + 1 : ℕ) : ℝ) ^ (-(2 * η)))
    (fun n k => ((n + 1 : ℕ) : ℝ) ^ (-(2 * (η * (1 - l)))) *
      ((k + 1 : ℕ) : ℝ) ^ (-(2 * (l * (1 + η)))))
    (fun n k => ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * (if (k + 1) * (k + 1) ≤ n + 1 then
      ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) else 0))
    (fun n k => ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * (if (k + 1) * (k + 1) ≤ n + 1 then 0
      else ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) *
        ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ))))
    (fun n k => if (k + 1) * (k + 1) ≤ n + 1 then 0 else
      ((k + 1 : ℕ) : ℝ) ^ (-2 - 2 * η)))).trans ?_
  -- the six families
  have hA1 := sum_sum_rpow_le (s := 2 * η) (t := 2) (by linarith) one_lt_two T M
  have hA2 := sum_sum_rpow_le (s := 2) (t := 2 * η) one_lt_two (by linarith) T M
  have hA3 := sum_sum_rpow_le (s := 2 * (η * (1 - l))) (t := 2 * (l * (1 + η)))
    (by linarith) (by linarith) T M
  have hB : ∑ n ∈ range T, ∑ k ∈ range M, ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) *
      (if (k + 1) * (k + 1) ≤ n + 1 then ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) else 0) ≤
      realZetaSeries ((1 + 2 * η) / 2) := by
    refine le_trans (sum_le_sum fun n _ => ?_) (sum_range_rpow_le_zeta hs T)
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [← mul_sum, ← rpow_neg_two_mul_rpow hN]
    exact mul_le_mul_of_nonneg_left (sum_below_sqrt_le h1 n M) (Real.rpow_nonneg hN.le _)
  have hC : ∑ n ∈ range T, ∑ k ∈ range M, ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) *
      (if (k + 1) * (k + 1) ≤ n + 1 then 0 else ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) *
        ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ))) ≤
      (1 + 1 / (2 * η - 1)) * realZetaSeries ((1 + 2 * η) / 2) := by
    have hc0 : 0 ≤ 1 + 1 / (2 * η - 1) := by
      have : 0 < 2 * η - 1 := by linarith
      positivity
    have hrow : ∀ n, ∑ k ∈ range M, ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) *
        (if (k + 1) * (k + 1) ≤ n + 1 then 0 else ((k + 1 : ℕ) : ℝ) ^ (2 - 2 * η) *
          ((((n + 1) / (k + 1) - (n + 1) / (k + 1 + 1) : ℕ) : ℝ))) ≤
        (1 + 1 / (2 * η - 1)) * ((n + 1 : ℕ) : ℝ) ^ (-((1 + 2 * η) / 2)) := by
      intro n
      have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      rw [← mul_sum]
      calc _ ≤ ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) *
            ((1 + 1 / (2 * η - 1)) * ((n + 1 : ℕ) : ℝ) ^ ((3 - 2 * η) / 2)) :=
            mul_le_mul_of_nonneg_left (sum_above_sqrt_le h1 hh n M) (Real.rpow_nonneg hN.le _)
        _ = (1 + 1 / (2 * η - 1)) * (((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) *
            ((n + 1 : ℕ) : ℝ) ^ ((3 - 2 * η) / 2)) := by ring
        _ = _ := by rw [rpow_neg_two_mul_rpow hN]
    calc _ ≤ ∑ n ∈ range T, (1 + 1 / (2 * η - 1)) * ((n + 1 : ℕ) : ℝ) ^ (-((1 + 2 * η) / 2)) :=
          sum_le_sum fun n _ => hrow n
      _ = (1 + 1 / (2 * η - 1)) * ∑ n ∈ range T, ((n + 1 : ℕ) : ℝ) ^ (-((1 + 2 * η) / 2)) := by
          rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_range_rpow_le_zeta hs T) hc0
  have hD := sum_above_sqrt_tail_le hh T M
  unfold chainHSConstant
  exact add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hA1 (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hA2 (sq_nonneg _))) (by norm_num))
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hA3 (by positivity))
      (mul_le_mul_of_nonneg_left hB (by positivity)))
      (mul_le_mul_of_nonneg_left hC (by positivity)))
      (mul_le_mul_of_nonneg_left hD (by positivity))) (by norm_num))

/-- **The chain is bounded in `ℓ²` above damping `1/√2`**: for `η² > ½`, `η < 1`, finitely
supported `b` and every horizon, `Σ_{n<T} (C_η b)(n)² ≤ M_η Σ_k b_k²`. -/
theorem centeredOperator_l2_le_of_inverseRootTwo {η : ℝ} (h0 : 0 < η) (h1 : η < 1)
    (h2 : 1 / 2 < η ^ 2) (b : C₀(ℕ, ℝ)) {N : ℕ} (hb : ∀ k, N ≤ k → b k = 0) (T : ℕ) :
    ∑ n ∈ range T, arithmeticDampingCenteredOperator h0 b n ^ 2 ≤
      chainHSConstant η * ∑ k ∈ range N, b k ^ 2 := by
  have happ : ∀ n, arithmeticDampingCenteredOperator h0 b n =
      ∑ k ∈ range N, arithmeticDampingCenteredRow η n k * b k := by
    intro n
    rw [arithmeticDampingCenteredOperator_apply]
    exact tsum_eq_sum fun k hk => by rw [hb k (by simpa using hk), mul_zero]
  have hrow : ∀ n, arithmeticDampingCenteredOperator h0 b n ^ 2 ≤
      (∑ k ∈ range N, arithmeticDampingCenteredRow η n k ^ 2) * ∑ k ∈ range N, b k ^ 2 := by
    intro n; rw [happ]; exact sum_mul_sq_le_sq_mul_sq _ _ _
  have hb0 : 0 ≤ ∑ k ∈ range N, b k ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  have hHS : ∑ n ∈ range T, ∑ k ∈ range N, arithmeticDampingCenteredRow η n k ^ 2 ≤
      chainHSConstant η :=
    (sum_le_sum fun n _ => sum_le_sum fun k _ => sq_centeredRow_le_majorant h0 h1 h2 n k).trans
      (sum_chainMajorant_le h0 h1 h2 T N)
  calc ∑ n ∈ range T, arithmeticDampingCenteredOperator h0 b n ^ 2
      ≤ ∑ n ∈ range T, (∑ k ∈ range N, arithmeticDampingCenteredRow η n k ^ 2) *
          ∑ k ∈ range N, b k ^ 2 := sum_le_sum fun n _ => hrow n
    _ = (∑ n ∈ range T, ∑ k ∈ range N, arithmeticDampingCenteredRow η n k ^ 2) *
          ∑ k ∈ range N, b k ^ 2 := by rw [← sum_mul]
    _ ≤ chainHSConstant η * ∑ k ∈ range N, b k ^ 2 := mul_le_mul_of_nonneg_right hHS hb0

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
