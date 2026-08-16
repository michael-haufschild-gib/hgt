import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceLargeValues

/-!
# Exact physical-slice recutting of Route T's signed adjacent defect

Observation-cone coefficients equal von Mangoldt only inside the physical window; the full
Dirichlet aggregates are not pointwise equal.  Finite-support Perron inversion nevertheless lets
us recut each complete vertical integral to the floor-exact physical von Mangoldt slice before
cell extraction.  The adjacent target--reference defect therefore enters the additive-length
large-value receiver without discarding its sign or importing coefficients outside physical
support.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Arithmetic-function form of the literal von Mangoldt slice on `(A,B]`. -/
def routeTVonMangoldtSlicePacket (A B : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if A < n ∧ n ≤ B then vonMangoldt n else 0, by simp⟩

@[simp] theorem complexCoeff_routeTVonMangoldtSlicePacket (A B n : ℕ) :
    complexCoeff (routeTVonMangoldtSlicePacket A B) n =
      routeTVonMangoldtSliceSequence A B n := by
  rw [routeTVonMangoldtSlicePacket, complexCoeff_apply,
    routeTVonMangoldtSliceSequence]
  by_cases h : A < n ∧ n ≤ B <;> simp [h]

/-- The literal slice packet has exact finite upper support `B`. -/
theorem upperSupported_routeTVonMangoldtSlicePacket (A B : ℕ) :
    UpperSupported (routeTVonMangoldtSlicePacket A B) B := by
  intro n hn
  change (if A < n ∧ n ≤ B then vonMangoldt n else 0) ≠ 0 at hn
  split_ifs at hn with h
  · exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  · exact (hn rfl).elim

/-- On the Perron line, the slice packet is the finite polynomial used by the local-energy
receiver. -/
theorem LSeries_routeTVonMangoldtSlicePacket_eq_dirPoly (A B : ℕ) (y : ℝ) :
    LSeries (complexCoeff (routeTVonMangoldtSlicePacket A B))
        ((1 : ℂ) + (y : ℝ) * I) =
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) := by
  rw [LSeries_eq_sum_term_of_support (a := complexCoeff
    (routeTVonMangoldtSlicePacket A B)) (fun n hn =>
      upperSupported_routeTVonMangoldtSlicePacket A B n
        (Complex.ofReal_injective.ne_iff.mp hn))]
  rw [← sum_Ioc_twisted_vonMangoldt_eq_dirPoly A B y]
  have hsub : Finset.Ioc A B ⊆ Finset.Icc 1 B := by
    intro n hn
    have hnAB := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hnAB.2⟩
  have hzero : ∀ n ∈ Finset.Icc 1 B, n ∉ Finset.Ioc A B →
      LSeries.term (complexCoeff (routeTVonMangoldtSlicePacket A B))
        ((1 : ℂ) + (y : ℝ) * I) n = 0 := by
    intro n hn hnIoc
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [LSeries.term_of_ne_zero hnpos.ne', complexCoeff_routeTVonMangoldtSlicePacket]
    have hz : ¬ (A < n ∧ n ≤ B) := by
      intro h
      exact hnIoc (Finset.mem_Ioc.mpr h)
    simp [routeTVonMangoldtSliceSequence, hz]
  rw [← Finset.sum_subset hsub hzero]
  apply Finset.sum_congr rfl
  intro n hn
  have hnAB := Finset.mem_Ioc.mp hn
  rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), twistedSummand,
    complexCoeff_routeTVonMangoldtSlicePacket]
  rw [routeTVonMangoldtSliceSequence, if_pos hnAB]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]

/-- After multiplication by any narrower adjacent window, every observed aggregate coefficient
equals the floor-exact physical von Mangoldt slice coefficient. -/
theorem complexCoeff_observed_mul_routeWeight_eq_slicePacket
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T t N R W : ℝ}
    (hT : 1 < T)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T ^ t ≤ N)
    (hN : 0 < N) (hW : 0 < W) (hWR : W ≤ R)
    (hsupportR : N + 2 * R ≤ X) (n : ℕ) :
    complexCoeff (heathBrownObservedEligiblePacket L X k T t N R) n *
        ((routeTSmoothWindowWeight N W (n : ℝ) : ℝ) : ℂ) =
      complexCoeff
          (routeTVonMangoldtSlicePacket ⌊N⌋₊ ⌊N + 2 * R⌋₊) n *
        ((routeTSmoothWindowWeight N W (n : ℝ) : ℝ) : ℂ) := by
  by_cases hnlow : (n : ℝ) ≤ N
  · have hplus := smoothWeight_eq_one hW (show (n : ℝ) ≤ N + W by linarith)
    have hbase := smoothWeight_eq_one hW hnlow
    have hzero : routeTSmoothWindowWeight N W (n : ℝ) = 0 := by
      rw [routeTSmoothWindowWeight, hplus, hbase, sub_self]
    rw [hzero, Complex.ofReal_zero, mul_zero, mul_zero]
  · have hnN : N < (n : ℝ) := lt_of_not_ge hnlow
    by_cases hnend : (n : ℝ) < N + 2 * W
    · have hR : 0 < R := hW.trans_le hWR
      have hnEndR : (n : ℝ) < N + 2 * R := by linarith
      have hnXlt : n < X := by exact_mod_cast hnEndR.trans_le hsupportR
      have hnX : n ≤ X := hnXlt.le
      have hobs := complexCoeff_heathBrownObservedEligiblePacket_eq_vonMangoldt
        L X k hXL hT hscale hnN hnEndR hnX
      have hfloorLow : ⌊N⌋₊ < n := by
        exact_mod_cast (Nat.floor_le hN.le).trans_lt hnN
      have hfloorHigh : n ≤ ⌊N + 2 * R⌋₊ := by
        exact Nat.le_floor hnEndR.le
      rw [hobs, complexCoeff_routeTVonMangoldtSlicePacket,
        routeTVonMangoldtSliceSequence, if_pos ⟨hfloorLow, hfloorHigh⟩]
    · have hnend' : N + 2 * W ≤ (n : ℝ) := le_of_not_gt hnend
      have hplus := smoothWeight_eq_zero hW
        (show N + W + W ≤ (n : ℝ) by linarith)
      have hbase := smoothWeight_eq_zero hW
        (show N + W ≤ (n : ℝ) by linarith)
      have hzero : routeTSmoothWindowWeight N W (n : ℝ) = 0 := by
        rw [routeTSmoothWindowWeight, hplus, hbase, sub_self]
      rw [hzero, Complex.ofReal_zero, mul_zero, mul_zero]

/-- Raw finite-support Perron integral recut from the observation aggregate to the physical
von Mangoldt slice. -/
theorem integral_observed_mul_routeTMellin_eq_physicalSlice
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T t N R W : ℝ}
    (hT : 1 < T)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T ^ t ≤ N)
    (hN : 0 < N) (hW : 0 < W) (hWR : W ≤ R)
    (hsupportR : N + 2 * R ≤ X) :
    (∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((1 : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
          ((1 : ℂ) + (y : ℝ) * I)) =
      ∫ y : ℝ,
        dirPoly ⌊N + 2 * R⌋₊
            (routeTVonMangoldtSliceCoeff ⌊N⌋₊ ⌊N + 2 * R⌋₊) (-y) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
            ((1 : ℂ) + (y : ℝ) * I) := by
  let A : ℕ := ⌊N⌋₊
  let B : ℕ := ⌊N + 2 * R⌋₊
  let F : ArithmeticFunction ℝ := routeTVonMangoldtSlicePacket A B
  have hold := smul_tsum_mul_routeTSmoothWindowWeight_eq_integral_of_upperSupported
    (upperSupported_heathBrownObservedEligiblePacket L X k T t N R)
    hN hW (by norm_num : (0 : ℝ) < 1)
  have hnew := smul_tsum_mul_routeTSmoothWindowWeight_eq_integral_of_upperSupported
    (upperSupported_routeTVonMangoldtSlicePacket A B)
    hN hW (by norm_num : (0 : ℝ) < 1)
  have hsum :
      (∑' n : ℕ,
        complexCoeff (heathBrownObservedEligiblePacket L X k T t N R) n *
          ((routeTSmoothWindowWeight N W (n : ℝ) : ℝ) : ℂ)) =
      ∑' n : ℕ, complexCoeff F n *
          ((routeTSmoothWindowWeight N W (n : ℝ) : ℝ) : ℂ) := by
    apply tsum_congr
    intro n
    dsimp only [F, A, B]
    exact complexCoeff_observed_mul_routeWeight_eq_slicePacket
      L X k hXL hT hscale hN hW hWR hsupportR n
  rw [hsum] at hold
  calc
    (∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((1 : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
          ((1 : ℂ) + (y : ℝ) * I)) =
      ∫ y : ℝ,
        LSeries (complexCoeff
          (heathBrownObservedEligiblePacket L X k T t N R))
            ((1 : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
            ((1 : ℂ) + (y : ℝ) * I) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [LSeries_heathBrownObservedEligiblePacket]
    _ = ∫ y : ℝ,
        LSeries (complexCoeff F) ((1 : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
            ((1 : ℂ) + (y : ℝ) * I) := hold.symm.trans hnew
    _ = ∫ y : ℝ,
        dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
            ((1 : ℂ) + (y : ℝ) * I) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [show F = routeTVonMangoldtSlicePacket A B by rfl,
          LSeries_routeTVonMangoldtSlicePacket_eq_dirPoly]
    _ = _ := by rfl

/-- Width-normalized one-window form of exact physical-slice recutting. -/
theorem integral_observed_mul_routeTNormalizedMellin_eq_physicalSlice
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T t N R W : ℝ}
    (hT : 1 < T)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T ^ t ≤ N)
    (hN : 0 < N) (hW : 0 < W) (hWR : W ≤ R)
    (hsupportR : N + 2 * R ≤ X) :
    (∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((1 : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N W
          ((1 : ℂ) + (y : ℝ) * I)) =
      ∫ y : ℝ,
        dirPoly ⌊N + 2 * R⌋₊
            (routeTVonMangoldtSliceCoeff ⌊N⌋₊ ⌊N + 2 * R⌋₊) (-y) *
          routeTNormalizedSmoothWindowMellin N W
            ((1 : ℂ) + (y : ℝ) * I) := by
  have hraw := integral_observed_mul_routeTMellin_eq_physicalSlice
    L X k hXL hT hscale hN hW hWR hsupportR
  calc
    (∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((1 : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N W
          ((1 : ℂ) + (y : ℝ) * I)) =
      (W : ℂ)⁻¹ * ∫ y : ℝ,
        heathBrownObservedEligibleDyadicAggregate L X k T t N R
            ((1 : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
            ((1 : ℂ) + (y : ℝ) * I) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [routeTNormalizedSmoothWindowMellin]
        ring
    _ = (W : ℂ)⁻¹ * ∫ y : ℝ,
        dirPoly ⌊N + 2 * R⌋₊
            (routeTVonMangoldtSliceCoeff ⌊N⌋₊ ⌊N + 2 * R⌋₊) (-y) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
            ((1 : ℂ) + (y : ℝ) * I) := by rw [hraw]
    _ = ∫ y : ℝ,
        dirPoly ⌊N + 2 * R⌋₊
            (routeTVonMangoldtSliceCoeff ⌊N⌋₊ ⌊N + 2 * R⌋₊) (-y) *
          routeTNormalizedSmoothWindowMellin N W
            ((1 : ℂ) + (y : ℝ) * I) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [routeTNormalizedSmoothWindowMellin]
        ring

/-- **Signed physical-slice bridge.** The complete normalized target--reference defect of the
observed Heath--Brown aggregate is exactly the same defect formed from one literal finite
von Mangoldt slice.  No pointwise equality outside physical support is asserted or needed. -/
theorem integral_observed_mul_adjacentNormalizedMellin_eq_physicalSlice
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T t N H R : ℝ}
    (hT : 1 < T)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T ^ t ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hsupportR : N + 2 * R ≤ X) :
    (∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((1 : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))) =
      ∫ y : ℝ,
        dirPoly ⌊N + 2 * R⌋₊
            (routeTVonMangoldtSliceCoeff ⌊N⌋₊ ⌊N + 2 * R⌋₊) (-y) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)) := by
  let A : ℕ := ⌊N⌋₊
  let B : ℕ := ⌊N + 2 * R⌋₊
  let F : ArithmeticFunction ℝ := routeTVonMangoldtSlicePacket A B
  have hObsR0 := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_heathBrownObservedEligiblePacket L X k T t N R)
    hN hR (by norm_num : (0 : ℝ) < 1)
  have hObsH0 := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_heathBrownObservedEligiblePacket L X k T t N R)
    hN hH (by norm_num : (0 : ℝ) < 1)
  have hObsR : Integrable (fun y : ℝ =>
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((1 : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * I)) := by
    refine hObsR0.congr (Eventually.of_forall fun y => ?_)
    change LSeries (complexCoeff
        (heathBrownObservedEligiblePacket L X k T t N R))
          ((1 : ℂ) + (y : ℝ) * I) * _ =
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((1 : ℂ) + (y : ℝ) * I) * _
    rw [LSeries_heathBrownObservedEligiblePacket]
    norm_num
  have hObsH : Integrable (fun y : ℝ =>
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((1 : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I)) := by
    refine hObsH0.congr (Eventually.of_forall fun y => ?_)
    change LSeries (complexCoeff
        (heathBrownObservedEligiblePacket L X k T t N R))
          ((1 : ℂ) + (y : ℝ) * I) * _ =
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((1 : ℂ) + (y : ℝ) * I) * _
    rw [LSeries_heathBrownObservedEligiblePacket]
    norm_num
  have hSliceR0 := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_routeTVonMangoldtSlicePacket A B) hN hR (by norm_num : (0 : ℝ) < 1)
  have hSliceH0 := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_routeTVonMangoldtSlicePacket A B) hN hH (by norm_num : (0 : ℝ) < 1)
  have hSliceR : Integrable (fun y : ℝ =>
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
        routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * I)) := by
    refine hSliceR0.congr (Eventually.of_forall fun y => ?_)
    change LSeries (complexCoeff (routeTVonMangoldtSlicePacket A B))
        ((1 : ℂ) + (y : ℝ) * I) * _ =
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) * _
    rw [LSeries_routeTVonMangoldtSlicePacket_eq_dirPoly]
    norm_num
  have hSliceH : Integrable (fun y : ℝ =>
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I)) := by
    refine hSliceH0.congr (Eventually.of_forall fun y => ?_)
    change LSeries (complexCoeff (routeTVonMangoldtSlicePacket A B))
        ((1 : ℂ) + (y : ℝ) * I) * _ =
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) * _
    rw [LSeries_routeTVonMangoldtSlicePacket_eq_dirPoly]
    norm_num
  simp_rw [mul_sub]
  rw [integral_sub hObsR hObsH,
    integral_observed_mul_routeTNormalizedMellin_eq_physicalSlice
      L X k hXL hT hscale hN hR le_rfl hsupportR,
    integral_observed_mul_routeTNormalizedMellin_eq_physicalSlice
      L X k hXL hT hscale hN hH hHR hsupportR,
    integral_sub hSliceR hSliceH]

end RHTower.Sieve
