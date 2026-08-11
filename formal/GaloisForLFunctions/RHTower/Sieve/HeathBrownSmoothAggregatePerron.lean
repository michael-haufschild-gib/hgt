import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicShortIntervalPerron
import GaloisForLFunctions.RHTower.Sieve.PerronSummable

/-!
# Exact smooth aggregation of the dyadic Heath--Brown packet

Sharp finite-height Perron applied box by box sees coefficients beyond the target prefix.  Those
coefficients no longer enjoy the signed cancellation to von Mangoldt and create a support cascade.
Compactly supported Mellin smoothing removes that obstruction exactly: if the smoothing support is
inside the finite Heath--Brown identity range, every coefficient seen by the weight is already the
von Mangoldt coefficient, while the full Dirichlet polynomial still factorizes into its dyadic
Möbius, zeta, and logarithm products on the vertical line.

Thus aggregation may be performed before taking norms with no Perron truncation error and no
artificial tail.  This is the exact interface needed by a Maynard large-values estimate for the
whole signed packet.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- The complete finite packet L-series is the signed aggregate of all literal dyadic products. -/
theorem LSeries_heathBrownFiniteCompressedPacket_eq_sum_dyadicProducts
    (L X k : ℕ) (s : ℂ) :
    LSeries (complexCoeff (heathBrownFiniteCompressedPacket L X k)) s =
      ∑ m ∈ Finset.range k,
        ∑ q ∈ Finset.range (Nat.log 2 X + 1),
          ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
            ∑ a ∈ dyadicChoiceSet (k - m) L,
              heathBrownDyadicTermProduct L X k m a b q s := by
  rw [heathBrownFiniteCompressedPacket_eq_sum_terms, complexCoeff_sum,
    LSeries_sum (fun m hm => LSeriesSummable_heathBrownFiniteTerm L X k m s)]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [heathBrownFiniteTerm_eq_sum_dyadicBoxes, complexCoeff_sum]
  rw [LSeries_sum]
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [complexCoeff_sum, LSeries_sum]
    · refine Finset.sum_congr rfl fun b hb => ?_
      rw [complexCoeff_sum, LSeries_sum]
      · refine Finset.sum_congr rfl fun a ha => ?_
        exact LSeries_heathBrownDyadicTermBox L X k m a b q s
      · intro a ha
        exact LSeriesSummable_complexCoeff_heathBrownDyadicTermBox L X k m a b q s
    · intro b hb
      rw [complexCoeff_sum]
      exact LSeriesSummable.sum fun a ha =>
        LSeriesSummable_complexCoeff_heathBrownDyadicTermBox L X k m a b q s
  · intro q hq
    rw [complexCoeff_sum]
    exact LSeriesSummable.sum fun b hb => by
      rw [complexCoeff_sum]
      exact LSeriesSummable.sum fun a ha =>
        LSeriesSummable_complexCoeff_heathBrownDyadicTermBox L X k m a b q s

/-- A compactly supported smooth weight sees the finite Heath--Brown packet as von Mangoldt
pointwise.  No coefficient outside the identity range survives the weight. -/
theorem tsum_heathBrownFiniteCompressedPacket_smoothWeight_eq_vonMangoldt
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {N H : ℝ} (hH : 0 < H)
    (hsupport : N + H ≤ X) :
    (∑' n : ℕ, complexCoeff (heathBrownFiniteCompressedPacket L X k) n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
  apply tsum_congr
  intro n
  by_cases hnX : n ≤ X
  · have hncut : n < (L + 1) ^ k := hnX.trans_lt hXL
    rw [complexCoeff_apply, ← heathBrown_finite_compressed_identity L X k n hnX hncut]
  · have hXn : X < n := Nat.lt_of_not_ge hnX
    have hzero : GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) = 0 := by
      apply GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH
      have hcast : (X : ℝ) < (n : ℝ) := by exact_mod_cast hXn
      exact hsupport.trans hcast.le
    rw [hzero]
    simp

/-- **Exact smooth aggregate Perron identity.**  When the smoothing support lies below both
finite Heath--Brown cutoffs, the smoothed von Mangoldt sum is one vertical integral of the whole
signed dyadic product aggregate.  There is no boxwise truncation error and no support cascade. -/
theorem tsum_vonMangoldt_smoothWeight_eq_integral_heathBrownDyadicAggregate
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {N H σ : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + H ≤ X) (hσ : 1 < σ) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        ((vonMangoldt n : ℝ) : ℂ) *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        (∑ m ∈ Finset.range k,
          ∑ q ∈ Finset.range (Nat.log 2 X + 1),
            ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
              ∑ a ∈ dyadicChoiceSet (k - m) L,
                heathBrownDyadicTermProduct L X k m a b q
                  ((σ : ℂ) + (y : ℝ) * I)) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((σ : ℂ) + (y : ℝ) * I) := by
  let F := heathBrownFiniteCompressedPacket L X k
  have hF0 : complexCoeff F 0 = 0 := by simp [F, complexCoeff]
  have hsum : Summable fun n : ℕ => ‖complexCoeff F n‖ * (n : ℝ) ^ (-σ) :=
    summable_norm_mul_rpow_of_LSeriesSummable (by linarith)
      (LSeriesSummable_heathBrownFiniteCompressedPacket L X k (σ : ℂ))
  have hperron := tsum_mul_smoothWeight_eq_integral_summable
    (a := complexCoeff F) hF0 hN hH hσ hsum
  rw [← tsum_heathBrownFiniteCompressedPacket_smoothWeight_eq_vonMangoldt
    L X k hXL hH hsupport]
  rw [hperron]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  congr 1
  rw [tsum_cpow_neg_eq_LSeries hF0]
  exact LSeries_heathBrownFiniteCompressedPacket_eq_sum_dyadicProducts
    L X k ((σ : ℂ) + (y : ℝ) * I)

/-- **Exact smooth short-window aggregate.**  Subtracting adjacent smooth prefixes gives a weight
supported in `[N, N + 2H]`.  If that full window lies inside the finite identity range, its
von-Mangoldt mass is the difference of two exact aggregate Mellin integrals, still with no sharp
Perron truncation error. -/
theorem tsum_vonMangoldt_smoothWindow_eq_integral_heathBrownDyadicAggregate
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {N H σ : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X) (hσ : 1 < σ) :
    let P : ℂ → ℂ := fun s =>
      ∑ m ∈ Finset.range k,
        ∑ q ∈ Finset.range (Nat.log 2 X + 1),
          ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
            ∑ a ∈ dyadicChoiceSet (k - m) L,
              heathBrownDyadicTermProduct L X k m a b q s
    (2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        (((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ) -
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))) =
      (∫ y : ℝ, P ((σ : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
          ((σ : ℂ) + (y : ℝ) * I)) -
      ∫ y : ℝ, P ((σ : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((σ : ℂ) + (y : ℝ) * I) := by
  dsimp only
  have hplusSupport : (N + H) + H ≤ (X : ℝ) := by linarith
  have hbaseSupport : N + H ≤ (X : ℝ) := by linarith
  have hplus :=
    tsum_vonMangoldt_smoothWeight_eq_integral_heathBrownDyadicAggregate
      L X k hXL (N := N + H) (H := H) (σ := σ) (by linarith) hH hplusSupport hσ
  have hbase :=
    tsum_vonMangoldt_smoothWeight_eq_integral_heathBrownDyadicAggregate
      L X k hXL (N := N) (H := H) (σ := σ) hN hH hbaseSupport hσ
  let M : ℕ := ⌈N + 2 * H⌉₊ + 1
  have hM : N + 2 * H ≤ (M : ℝ) := by
    dsimp only [M]
    have hceil : N + 2 * H ≤ (⌈N + 2 * H⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  have hwindow :
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        (((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ) -
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))) =
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ)) -
      ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
    rw [tsum_eq_sum (s := Finset.range M) (fun n hn => by
      have hnM : M ≤ n := by
        simp only [Finset.mem_range] at hn
        omega
      have hnR : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnM
      have hzeroPlus :
          GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) = 0 := by
        apply GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH
        linarith
      have hzeroBase :
          GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) = 0 := by
        apply GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH
        linarith
      rw [hzeroPlus, hzeroBase]
      simp),
      GaloisForLFunctions.HTGeometry.tsum_mul_smoothWeight_eq_sum_range_real
        hH M (by linarith : (N + H) + H ≤ (M : ℝ)),
      GaloisForLFunctions.HTGeometry.tsum_mul_smoothWeight_eq_sum_range_real
        hH M (by linarith : N + H ≤ (M : ℝ)), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    ring
  have hsub := congrArg₂ (fun z w : ℂ => z - w) hplus hbase
  rw [← smul_sub, ← hwindow] at hsub
  exact hsub

end RHTower.Sieve
