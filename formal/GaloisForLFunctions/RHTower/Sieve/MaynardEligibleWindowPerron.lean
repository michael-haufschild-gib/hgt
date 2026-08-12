import GaloisForLFunctions.RHTower.Sieve.MaynardLowTotalWindowProjection

/-!
# Eligible aggregate in the exact smooth short-window Perron formula

The compressed Heath--Brown packet splits coefficient-exactly into eligible and low-total
packets.  Since the low packet has identical adjacent-prefix Mellin integrals, the short-window
formula may be written using only the eligible aggregate before any large-value selection.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Arithmetic packet containing exactly the boxes eligible for robust grouping. -/
def heathBrownEligiblePacket
    (L X k : ℕ) (T0 t : ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ∑ c : HeathBrownBoxChoice L X k,
    if IsHeathBrownBoxEligible L X k T0 t c then
      heathBrownDyadicTermBox L X k c.m c.a c.b c.q else 0

/-- Complete packet reindexed by the dependent box type. -/
def heathBrownFlatPacket (L X k : ℕ) : ArithmeticFunction ℝ :=
  ∑ c : HeathBrownBoxChoice L X k,
    heathBrownDyadicTermBox L X k c.m c.a c.b c.q

theorem heathBrownFlatPacket_eq_compressed
    (L X k : ℕ) :
    heathBrownFlatPacket L X k = heathBrownFiniteCompressedPacket L X k := by
  classical
  rw [heathBrownFlatPacket]
  calc
    (∑ c : HeathBrownBoxChoice L X k,
      heathBrownDyadicTermBox L X k c.m c.a c.b c.q) =
        ∑ m ∈ Finset.range k,
          ∑ q ∈ Finset.range (Nat.log 2 X + 1),
            ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
              ∑ a ∈ dyadicChoiceSet (k - m) L,
                heathBrownDyadicTermBox L X k m a b q :=
      sum_heathBrownBoxChoice_eq_nested L X k
        (fun m q b a => heathBrownDyadicTermBox L X k m a b q)
    _ = ∑ m ∈ Finset.range k, heathBrownFiniteTerm L X k m := by
      apply Finset.sum_congr rfl
      intro m hm
      exact (heathBrownFiniteTerm_eq_sum_dyadicBoxes L X k m).symm
    _ = heathBrownFiniteCompressedPacket L X k :=
      (heathBrownFiniteCompressedPacket_eq_sum_terms L X k).symm

/-- Coefficient-exact eligible/low split of the complete compressed packet. -/
theorem heathBrownFiniteCompressedPacket_eq_eligible_add_lowTotal
    (L X k : ℕ) (T0 t : ℝ) :
    heathBrownFiniteCompressedPacket L X k =
      heathBrownEligiblePacket L X k T0 t +
        heathBrownLowTotalPacket L X k T0 t := by
  rw [← heathBrownFlatPacket_eq_compressed]
  classical
  simp only [heathBrownFlatPacket, heathBrownEligiblePacket,
    heathBrownLowTotalPacket, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases h : IsHeathBrownBoxEligible L X k T0 t c <;> simp [h]

/-- L-series of the eligible packet is the eligible pointwise aggregate. -/
theorem LSeries_heathBrownEligiblePacket
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) :
    LSeries (complexCoeff (heathBrownEligiblePacket L X k T0 t)) s =
      heathBrownEligibleDyadicAggregate L X k T0 t s := by
  classical
  rw [heathBrownEligiblePacket, complexCoeff_sum, LSeries_sum]
  · simp only [heathBrownEligibleDyadicAggregate]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases h : IsHeathBrownBoxEligible L X k T0 t c
    · simp [h, heathBrownBoxTerm]
      exact LSeries_heathBrownDyadicTermBox L X k c.m c.a c.b c.q s
    · simp only [h, if_false]
      have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
        funext n
        simp [complexCoeff_apply]
      rw [hzero]
      exact congrFun LSeries_zero s
  · intro c _hc
    by_cases h : IsHeathBrownBoxEligible L X k T0 t c
    · simp only [h, if_true]
      exact LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
        L X k c.m c.a c.b c.q s
    · simp only [h, if_false]
      have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
        funext n
        simp [complexCoeff_apply]
      rw [hzero]
      exact LSeriesSummable_zero

theorem LSeriesSummable_heathBrownEligiblePacket
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) :
    LSeriesSummable (complexCoeff (heathBrownEligiblePacket L X k T0 t)) s := by
  classical
  rw [heathBrownEligiblePacket, complexCoeff_sum]
  apply LSeriesSummable.sum
  intro c _hc
  by_cases h : IsHeathBrownBoxEligible L X k T0 t c
  · simp only [h, if_true]
    exact LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
      L X k c.m c.a c.b c.q s
  · simp only [h, if_false]
    have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
      funext n
      simp [complexCoeff_apply]
    rw [hzero]
    exact LSeriesSummable_zero

private theorem arithmeticFunction_sum_apply_eligible
    {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ u, F i) n = ∑ i ∈ u, F i n := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [ArithmeticFunction.zero_apply]
  | @insert a u ha ih => simp [ha, ih, ArithmeticFunction.add_apply]

/-- Smoothed Perron identity for the complete eligible packet. -/
theorem smul_tsum_heathBrownEligiblePacket_smoothWeight_eq_integral
    (L X k : ℕ) (T0 t : ℝ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
      complexCoeff (heathBrownEligiblePacket L X k T0 t) n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        heathBrownEligibleDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  let F := heathBrownEligiblePacket L X k T0 t
  have hF0 : complexCoeff F 0 = 0 := by
    classical
    have hpacket : F 0 = 0 := by
      dsimp only [F]
      rw [heathBrownEligiblePacket, arithmeticFunction_sum_apply_eligible]
      apply Finset.sum_eq_zero
      intro c _hc
      by_cases h : IsHeathBrownBoxEligible L X k T0 t c
      · simp only [h, if_true]
        by_contra hterm
        have hmem := upperSupported_heathBrownDyadicTermBox
          L X k c.m c.a c.b c.q 0 hterm
        simp at hmem
      · simp [h]
    simp [complexCoeff_apply, hpacket]
  have hsum : Summable fun n : ℕ => ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) :=
    summable_norm_mul_rpow_of_LSeriesSummable (by linarith)
      (LSeriesSummable_heathBrownEligiblePacket L X k T0 t (sigma : ℂ))
  have hperron := tsum_mul_smoothWeight_eq_integral_summable
    (a := complexCoeff F) hF0 hN hH hsigma hsum
  rw [hperron]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  congr 1
  rw [tsum_cpow_neg_eq_LSeries hF0]
  exact LSeries_heathBrownEligiblePacket
    L X k T0 t ((sigma : ℂ) + (y : ℝ) * I)

private theorem summable_mul_smoothWeight_any
    (a : ℕ → ℂ) {N H : ℝ} (hH : 0 < H) :
    Summable fun n : ℕ => a n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌈N + H⌉₊ + 1)) fun n hn => ?_
  rw [Finset.mem_range] at hn
  have hge : N + H ≤ (n : ℝ) := by
    have h1 : (N + H : ℝ) ≤ (⌈N + H⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈N + H⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_not_lt hn
    push_cast at h2
    linarith
  rw [GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH hge]
  simp

/-- The coefficient-exact packet split survives every compactly supported smooth weight. -/
theorem tsum_heathBrownFiniteCompressedPacket_smoothWeight_eq_eligible_add_lowTotal
    (L X k : ℕ) (T0 t : ℝ) {N H : ℝ} (hH : 0 < H) :
    (∑' n : ℕ, complexCoeff (heathBrownFiniteCompressedPacket L X k) n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      (∑' n : ℕ, complexCoeff (heathBrownEligiblePacket L X k T0 t) n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) +
      ∑' n : ℕ, complexCoeff (heathBrownLowTotalPacket L X k T0 t) n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
  let W : ℕ → ℂ := fun n =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)
  have hcoeff (n : ℕ) :
      complexCoeff (heathBrownFiniteCompressedPacket L X k) n =
        complexCoeff (heathBrownEligiblePacket L X k T0 t) n +
          complexCoeff (heathBrownLowTotalPacket L X k T0 t) n := by
    have h := congrArg
      (fun F : ArithmeticFunction ℝ => complexCoeff F n)
      (heathBrownFiniteCompressedPacket_eq_eligible_add_lowTotal L X k T0 t)
    simpa [complexCoeff_apply, ArithmeticFunction.add_apply] using h
  have helig : Summable fun n : ℕ =>
      complexCoeff (heathBrownEligiblePacket L X k T0 t) n * W n :=
    summable_mul_smoothWeight_any _ hH
  have hlow : Summable fun n : ℕ =>
      complexCoeff (heathBrownLowTotalPacket L X k T0 t) n * W n :=
    summable_mul_smoothWeight_any _ hH
  change (∑' n : ℕ, complexCoeff (heathBrownFiniteCompressedPacket L X k) n * W n) =
    (∑' n : ℕ, complexCoeff (heathBrownEligiblePacket L X k T0 t) n * W n) +
      ∑' n : ℕ, complexCoeff (heathBrownLowTotalPacket L X k T0 t) n * W n
  calc
    (∑' n : ℕ, complexCoeff (heathBrownFiniteCompressedPacket L X k) n * W n) =
        ∑' n : ℕ,
          (complexCoeff (heathBrownEligiblePacket L X k T0 t) n * W n +
            complexCoeff (heathBrownLowTotalPacket L X k T0 t) n * W n) := by
      apply tsum_congr
      intro n
      rw [hcoeff]
      ring
    _ = _ := helig.tsum_add hlow

/-- One smoothed full-aggregate prefix is exactly eligible plus low-total prefixes. -/
theorem integral_heathBrownDyadicAggregate_eq_eligible_add_lowTotal
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) (T0 t : ℝ)
    {N H sigma : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hsupport : N + H ≤ X) (hsigma : 1 < sigma) :
    (∫ y : ℝ,
      (∑ m ∈ Finset.range k,
        ∑ q ∈ Finset.range (Nat.log 2 X + 1),
          ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
            ∑ a ∈ dyadicChoiceSet (k - m) L,
              heathBrownDyadicTermProduct L X k m a b q
                ((sigma : ℂ) + (y : ℝ) * I)) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
      (∫ y : ℝ,
        heathBrownEligibleDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I)) +
      ∫ y : ℝ,
        heathBrownLowTotalDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  let W : ℕ → ℂ := fun n =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)
  let Svm : ℂ := ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * W n
  let Sfull : ℂ := ∑' n : ℕ,
    complexCoeff (heathBrownFiniteCompressedPacket L X k) n * W n
  let Seligible : ℂ := ∑' n : ℕ,
    complexCoeff (heathBrownEligiblePacket L X k T0 t) n * W n
  let Slow : ℂ := ∑' n : ℕ,
    complexCoeff (heathBrownLowTotalPacket L X k T0 t) n * W n
  let Ifull : ℂ := ∫ y : ℝ,
    (∑ m ∈ Finset.range k,
      ∑ q ∈ Finset.range (Nat.log 2 X + 1),
        ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
          ∑ a ∈ dyadicChoiceSet (k - m) L,
            heathBrownDyadicTermProduct L X k m a b q
              ((sigma : ℂ) + (y : ℝ) * I)) *
      mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * I)
  let Ieligible : ℂ := ∫ y : ℝ,
    heathBrownEligibleDyadicAggregate L X k T0 t
        ((sigma : ℂ) + (y : ℝ) * I) *
      mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * I)
  let Ilow : ℂ := ∫ y : ℝ,
    heathBrownLowTotalDyadicAggregate L X k T0 t
        ((sigma : ℂ) + (y : ℝ) * I) *
      mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * I)
  have hfull : (2 * Real.pi : ℝ) • Svm = Ifull := by
    simpa [Svm, W, Ifull] using
      tsum_vonMangoldt_smoothWeight_eq_integral_heathBrownDyadicAggregate
        L X k hXL hN hH hsupport hsigma
  have hpacket : Sfull = Svm := by
    simpa [Sfull, Svm, W] using
      tsum_heathBrownFiniteCompressedPacket_smoothWeight_eq_vonMangoldt
        L X k hXL hH hsupport
  have hsplit : Sfull = Seligible + Slow := by
    simpa [Sfull, Seligible, Slow, W] using
      tsum_heathBrownFiniteCompressedPacket_smoothWeight_eq_eligible_add_lowTotal
        L X k T0 t hH
  have helig : (2 * Real.pi : ℝ) • Seligible = Ieligible := by
    simpa [Seligible, W, Ieligible] using
      smul_tsum_heathBrownEligiblePacket_smoothWeight_eq_integral
        L X k T0 t hN hH hsigma
  have hlow : (2 * Real.pi : ℝ) • Slow = Ilow := by
    simpa [Slow, W, Ilow] using
      smul_tsum_heathBrownLowTotalPacket_smoothWeight_eq_integral
        L X k T0 t hN hH hsigma
  change Ifull = Ieligible + Ilow
  calc
    Ifull = (2 * Real.pi : ℝ) • Svm := hfull.symm
    _ = (2 * Real.pi : ℝ) • Sfull := congrArg ((2 * Real.pi : ℝ) • ·) hpacket.symm
    _ = (2 * Real.pi : ℝ) • (Seligible + Slow) :=
      congrArg ((2 * Real.pi : ℝ) • ·) hsplit
    _ = (2 * Real.pi : ℝ) • Seligible + (2 * Real.pi : ℝ) • Slow := smul_add _ _ _
    _ = Ieligible + Ilow := congrArg₂ (· + ·) helig hlow

/-- **Exact eligible-only smooth short-window formula.**  Low-total boxes are annihilated by the
adjacent-prefix projection, so no pointwise low-box estimate or positive-total premise remains. -/
theorem tsum_vonMangoldt_smoothWindow_eq_integral_heathBrownEligibleDyadicAggregate
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H sigma : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X)
    (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        (((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ) -
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))) =
      (∫ y : ℝ,
        heathBrownEligibleDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I)) -
      ∫ y : ℝ,
        heathBrownEligibleDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  have hwindow :=
    tsum_vonMangoldt_smoothWindow_eq_integral_heathBrownDyadicAggregate
      L X k hXL hN hH hsupport hsigma
  dsimp only at hwindow
  have hplusSupport : (N + H) + H ≤ (X : ℝ) := by linarith
  have hbaseSupport : N + H ≤ (X : ℝ) := by linarith
  have hplus := integral_heathBrownDyadicAggregate_eq_eligible_add_lowTotal
    L X k hXL T0 t (N := N + H) (H := H) (sigma := sigma)
      (by linarith) hH hplusSupport hsigma
  have hbase := integral_heathBrownDyadicAggregate_eq_eligible_add_lowTotal
    L X k hXL T0 t (N := N) (H := H) (sigma := sigma)
      hN hH hbaseSupport hsigma
  have hlow :=
    integral_heathBrownLowTotalDyadicAggregate_adjacent_smoothWeight_eq
      L X k hT0 hscale hN hH hsigma
  rw [hplus, hbase, hlow] at hwindow
  simpa only [add_sub_add_right_eq_sub] using hwindow

end RHTower.Sieve
