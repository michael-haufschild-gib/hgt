import GaloisForLFunctions.RHTower.Sieve.MaynardZeroReserveSupportNull

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- A box meets the literal observation cone of the widest adjacent window. -/
def IsHeathBrownBoxObservedRelevant
    (N R : ℝ) (X k : ℕ) {L : ℕ} (box : HeathBrownBoxChoice L X k) : Prop :=
  IsHeathBrownBoxWindowRelevant N X k box ∧
    (groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) < N + 2 * R

/-- Eligible packet recut to boxes visible before the widest physical window ends. -/
def heathBrownObservedEligiblePacket
    (L X k : ℕ) (T t N R : ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ∑ box : HeathBrownBoxChoice L X k,
    if IsHeathBrownBoxEligible L X k T t box ∧
        IsHeathBrownBoxObservedRelevant N R X k box then
      heathBrownDyadicTermBox L X k box.m box.a box.b box.q
    else 0

/-- L-series aggregate over the literal observation cone. -/
def heathBrownObservedEligibleDyadicAggregate
    (L X k : ℕ) (T t N R : ℝ) (s : ℂ) : ℂ := by
  classical
  exact ∑ box : HeathBrownBoxChoice L X k,
    if IsHeathBrownBoxEligible L X k T t box ∧
        IsHeathBrownBoxObservedRelevant N R X k box then
      heathBrownBoxTerm L X k box s
    else 0

private theorem arithmeticFunction_sum_apply_observed
    {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ u, F i) n = ∑ i ∈ u, F i n := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [ArithmeticFunction.zero_apply]
  | @insert a u ha ih => simp [ha, ih, ArithmeticFunction.add_apply]

theorem LSeries_heathBrownObservedEligiblePacket
    (L X k : ℕ) (T t N R : ℝ) (s : ℂ) :
    LSeries (complexCoeff (heathBrownObservedEligiblePacket L X k T t N R)) s =
      heathBrownObservedEligibleDyadicAggregate L X k T t N R s := by
  classical
  rw [heathBrownObservedEligiblePacket, complexCoeff_sum, LSeries_sum]
  · simp only [heathBrownObservedEligibleDyadicAggregate]
    apply Finset.sum_congr rfl
    intro box _hbox
    by_cases h : IsHeathBrownBoxEligible L X k T t box ∧
        IsHeathBrownBoxObservedRelevant N R X k box
    · simp [h, heathBrownBoxTerm]
      exact LSeries_heathBrownDyadicTermBox L X k box.m box.a box.b box.q s
    · simp only [h, if_false]
      have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
        funext n
        simp [complexCoeff_apply]
      rw [hzero]
      exact congrFun LSeries_zero s
  · intro box _hbox
    by_cases h : IsHeathBrownBoxEligible L X k T t box ∧
        IsHeathBrownBoxObservedRelevant N R X k box
    · simp only [h]
      exact LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
        L X k box.m box.a box.b box.q s
    · simp only [h, if_false]
      have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
        funext n
        simp [complexCoeff_apply]
      rw [hzero]
      exact LSeriesSummable_zero

/-- The observation-cone packet retains the old fixed support bound. -/
theorem upperSupported_heathBrownObservedEligiblePacket
    (L X k : ℕ) (T t N R : ℝ) :
    UpperSupported (heathBrownObservedEligiblePacket L X k T t N R)
      (2 ^ (2 * k) * X) := by
  classical
  intro n hn
  rw [heathBrownObservedEligiblePacket, arithmeticFunction_sum_apply_observed] at hn
  by_contra hnmem
  apply hn
  apply Finset.sum_eq_zero
  intro box _hbox
  by_cases hbox : IsHeathBrownBoxEligible L X k T t box ∧
      IsHeathBrownBoxObservedRelevant N R X k box
  · simp only [hbox]
    by_contra hterm
    have hlocal := upperSupported_heathBrownDyadicTermBox
      L X k box.m box.a box.b box.q n hterm
    have hm : box.m < k := box.1.isLt
    have hj : 1 ≤ k - box.m := Nat.sub_pos_of_lt hm
    have hlower : heathBrownDyadicCoreLower
        (k - box.m) box.a box.b box.q ≤ X := by
      rw [← groupedDyadicLower_heathBrownBoxFactorExponent_eq_coreLower]
      exact hbox.2.1.1
    have hupperLocal := heathBrownDyadicCoreUpper_le_of_lower_le
      hj box.a box.b box.q hlower
    have hpow : 2 ^ (2 * (k - box.m)) ≤ 2 ^ (2 * k) :=
      Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
    have hupper : heathBrownDyadicCoreUpper
        (k - box.m) box.a box.b box.q ≤ 2 ^ (2 * k) * X :=
      hupperLocal.trans (Nat.mul_le_mul_right X hpow)
    exact hnmem (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hlocal).1, (Finset.mem_Icc.mp hlocal).2.trans hupper⟩)
  · simp [hbox]

/-- Recutting at the widest physical endpoint changes no coefficient after multiplication by any
narrower adjacent-window weight. -/
theorem complexCoeff_windowRelevant_mul_routeWeight_eq_observed
    (L X k : ℕ) (T t N R : ℝ) {W : ℝ}
    (hW : 0 < W) (hWR : W ≤ R) (n : ℕ) :
    complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T t N) n *
        ((routeTSmoothWindowWeight N W (n : ℝ) : ℝ) : ℂ) =
      complexCoeff (heathBrownObservedEligiblePacket L X k T t N R) n *
        ((routeTSmoothWindowWeight N W (n : ℝ) : ℝ) : ℂ) := by
  classical
  rw [complexCoeff_apply, complexCoeff_apply]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [heathBrownWindowRelevantEligiblePacket,
    heathBrownObservedEligiblePacket,
    arithmeticFunction_sum_apply_observed,
    arithmeticFunction_sum_apply_observed]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro box _hbox
  by_cases hold : IsHeathBrownBoxEligible L X k T t box ∧
      IsHeathBrownBoxWindowRelevant N X k box
  · by_cases hvisible : (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) < N + 2 * R
    · have hnew : IsHeathBrownBoxEligible L X k T t box ∧
          IsHeathBrownBoxObservedRelevant N R X k box :=
        ⟨hold.1, hold.2, hvisible⟩
      simp [hold, hnew]
    · have hnew : ¬ (IsHeathBrownBoxEligible L X k T t box ∧
          IsHeathBrownBoxObservedRelevant N R X k box) := by
        intro h
        exact hvisible h.2.2
      have hlower : N + 2 * R ≤ (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) :=
        le_of_not_gt hvisible
      by_cases hterm : heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n = 0
      · simp [hold, IsHeathBrownBoxObservedRelevant, hvisible, hterm]
      · have hnlow := vanishesBelow_heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n
        have hnedge : heathBrownDyadicCoreLower
            (k - box.m) box.a box.b box.q ≤ n := by
          by_contra hnot
          exact hterm (hnlow (Nat.lt_of_not_ge hnot))
        have hnreal : N + 2 * W ≤ (n : ℝ) := by
          have hWR' : N + 2 * W ≤ N + 2 * R := by linarith
          have hedge : N + 2 * R ≤
              (heathBrownDyadicCoreLower
                (k - box.m) box.a box.b box.q : ℝ) := by
            rw [← groupedDyadicLower_heathBrownBoxFactorExponent_eq_coreLower]
            exact hlower
          exact hWR'.trans (hedge.trans (by exact_mod_cast hnedge))
        have hplus := smoothWeight_eq_zero hW
          (show N + W + W ≤ (n : ℝ) by linarith)
        have hbase := smoothWeight_eq_zero hW
          (show N + W ≤ (n : ℝ) by linarith)
        have hzero : routeTSmoothWindowWeight N W (n : ℝ) = 0 := by
          rw [routeTSmoothWindowWeight, hplus, hbase, sub_self]
        simp [hold, IsHeathBrownBoxObservedRelevant, hvisible, hzero]
  · have hnew : ¬ (IsHeathBrownBoxEligible L X k T t box ∧
        IsHeathBrownBoxObservedRelevant N R X k box) := by
      intro h
      exact hold ⟨h.1, h.2.1⟩
    simp [hold, hnew]

/-- Below the widest physical endpoint, observation-cone recutting preserves each coefficient,
not merely its product with a window weight. -/
theorem complexCoeff_windowRelevant_eq_observed_of_lt_endpoint
    (L X k : ℕ) (T t N R : ℝ) {n : ℕ}
    (hn : (n : ℝ) < N + 2 * R) :
    complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T t N) n =
      complexCoeff (heathBrownObservedEligiblePacket L X k T t N R) n := by
  classical
  rw [complexCoeff_apply, complexCoeff_apply]
  apply congrArg Complex.ofReal
  rw [heathBrownWindowRelevantEligiblePacket,
    heathBrownObservedEligiblePacket,
    arithmeticFunction_sum_apply_observed,
    arithmeticFunction_sum_apply_observed]
  apply Finset.sum_congr rfl
  intro box _hbox
  by_cases hold : IsHeathBrownBoxEligible L X k T t box ∧
      IsHeathBrownBoxWindowRelevant N X k box
  · by_cases hvisible : (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) < N + 2 * R
    · have hnew : IsHeathBrownBoxEligible L X k T t box ∧
          IsHeathBrownBoxObservedRelevant N R X k box :=
        ⟨hold.1, hold.2, hvisible⟩
      simp [hold, hnew]
    · have hnew : ¬ (IsHeathBrownBoxEligible L X k T t box ∧
          IsHeathBrownBoxObservedRelevant N R X k box) := by
        intro h
        exact hvisible h.2.2
      have hobs : ¬ IsHeathBrownBoxObservedRelevant N R X k box := by
        intro h
        exact hvisible h.2
      have hlower : N + 2 * R ≤ (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) :=
        le_of_not_gt hvisible
      have hterm : heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n = 0 := by
        apply vanishesBelow_heathBrownDyadicTermBox
        have hreal : (n : ℝ) <
            (heathBrownDyadicCoreLower
              (k - box.m) box.a box.b box.q : ℝ) := by
          rw [← groupedDyadicLower_heathBrownBoxFactorExponent_eq_coreLower]
          exact hn.trans_le hlower
        exact_mod_cast hreal
      simp [hold, hobs, hterm]
  · have hnew : ¬ (IsHeathBrownBoxEligible L X k T t box ∧
        IsHeathBrownBoxObservedRelevant N R X k box) := by
      intro h
      exact hold ⟨h.1, h.2.1⟩
    simp [hold, hnew]

/-- The existing window-relevant packet is coefficient-exactly von Mangoldt throughout the open
physical window before the cutoff.  This is the pointwise form hidden inside Perron exactness. -/
theorem complexCoeff_heathBrownWindowRelevantEligiblePacket_eq_vonMangoldt
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T t N : ℝ}
    (hT : 1 < T)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T ^ t ≤ N)
    {n : ℕ} (hnN : N < (n : ℝ)) (hnX : n ≤ X) :
    complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T t N) n =
      ((vonMangoldt n : ℝ) : ℂ) := by
  have hwindow :=
    heathBrownPerronRelevantEligiblePacket_apply_eq_windowRelevant_of_lt
      L X k T t hnN
  have hperron := heathBrownEligiblePacket_apply_eq_perronRelevant
    L X k T t hnX
  have hlow : complexCoeff (heathBrownLowTotalPacket L X k T t) n = 0 := by
    by_contra hne
    have hnle := complexCoeff_heathBrownLowTotalPacket_nonzero_le
      L X k hT hscale hne
    linarith
  have hsplit := congrArg
    (fun F : ArithmeticFunction ℝ => complexCoeff F n)
    (heathBrownFiniteCompressedPacket_eq_eligible_add_lowTotal L X k T t)
  have hcompressed :
      complexCoeff (heathBrownFiniteCompressedPacket L X k) n =
        ((vonMangoldt n : ℝ) : ℂ) := by
    rw [complexCoeff_apply,
      ← heathBrown_finite_compressed_identity L X k n hnX (hnX.trans_lt hXL)]
  have hwindowC :
      complexCoeff (heathBrownPerronRelevantEligiblePacket L X k T t) n =
        complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T t N) n := by
    simpa only [complexCoeff_apply] using congrArg Complex.ofReal hwindow
  have hperronC :
      complexCoeff (heathBrownEligiblePacket L X k T t) n =
        complexCoeff (heathBrownPerronRelevantEligiblePacket L X k T t) n := by
    simpa only [complexCoeff_apply] using congrArg Complex.ofReal hperron
  rw [← hwindowC, ← hperronC]
  have helig : complexCoeff (heathBrownEligiblePacket L X k T t) n =
      complexCoeff (heathBrownFiniteCompressedPacket L X k) n := by
    have hsplit' : complexCoeff (heathBrownFiniteCompressedPacket L X k) n =
        complexCoeff (heathBrownEligiblePacket L X k T t) n +
          complexCoeff (heathBrownLowTotalPacket L X k T t) n := by
      simpa [complexCoeff_apply, ArithmeticFunction.add_apply, ofReal_add] using hsplit
    rw [hlow, add_zero] at hsplit'
    exact hsplit'.symm
  rw [helig, hcompressed]

/-- **Observation-cone coefficient collapse.** Every coefficient that can be seen by the widest
adjacent window is literally von Mangoldt; box combinatorics survive only outside physical
support. -/
theorem complexCoeff_heathBrownObservedEligiblePacket_eq_vonMangoldt
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T t N R : ℝ}
    (hT : 1 < T)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T ^ t ≤ N)
    {n : ℕ} (hnN : N < (n : ℝ)) (hnEnd : (n : ℝ) < N + 2 * R)
    (hnX : n ≤ X) :
    complexCoeff (heathBrownObservedEligiblePacket L X k T t N R) n =
      ((vonMangoldt n : ℝ) : ℂ) := by
  rw [← complexCoeff_windowRelevant_eq_observed_of_lt_endpoint
    L X k T t N R hnEnd]
  exact complexCoeff_heathBrownWindowRelevantEligiblePacket_eq_vonMangoldt
    L X k hXL hT hscale hnN hnX

/-- Raw adjacent Perron integral is unchanged by literal observation-cone recutting. -/
theorem integral_windowRelevant_mul_routeTMellin_eq_observed
    (L X k : ℕ) (T t N R : ℝ) {W sigma : ℝ}
    (hN : 0 < N) (hW : 0 < W) (hWR : W ≤ R) (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
    ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by
  have hold := smul_tsum_mul_routeTSmoothWindowWeight_eq_integral_of_upperSupported
    (upperSupported_heathBrownWindowRelevantEligiblePacket L X k T t N)
    hN hW hsigma
  have hnew := smul_tsum_mul_routeTSmoothWindowWeight_eq_integral_of_upperSupported
    (upperSupported_heathBrownObservedEligiblePacket L X k T t N R)
    hN hW hsigma
  have hsum :
      (∑' n : ℕ,
        complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T t N) n *
          ((routeTSmoothWindowWeight N W (n : ℝ) : ℝ) : ℂ)) =
      ∑' n : ℕ,
        complexCoeff (heathBrownObservedEligiblePacket L X k T t N R) n *
          ((routeTSmoothWindowWeight N W (n : ℝ) : ℝ) : ℂ) := by
    apply tsum_congr
    exact complexCoeff_windowRelevant_mul_routeWeight_eq_observed
      L X k T t N R hW hWR
  rw [hsum] at hold
  calc
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
      ∫ y : ℝ,
        LSeries (complexCoeff
          (heathBrownWindowRelevantEligiblePacket L X k T t N))
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [LSeries_heathBrownWindowRelevantEligiblePacket]
    _ = ∫ y : ℝ,
        LSeries (complexCoeff
          (heathBrownObservedEligiblePacket L X k T t N R))
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := hold.symm.trans hnew
    _ = ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [LSeries_heathBrownObservedEligiblePacket]

/-- Width-normalized form of exact observation-cone recutting. -/
theorem integral_windowRelevant_mul_routeTNormalizedMellin_eq_observed
    (L X k : ℕ) (T t N R : ℝ) {W sigma : ℝ}
    (hN : 0 < N) (hW : 0 < W) (hWR : W ≤ R) (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N W
          ((sigma : ℂ) + (y : ℝ) * I)) =
    ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N W
          ((sigma : ℂ) + (y : ℝ) * I) := by
  have hraw := integral_windowRelevant_mul_routeTMellin_eq_observed
    L X k T t N R hN hW hWR hsigma
  calc
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N W
          ((sigma : ℂ) + (y : ℝ) * I)) =
      (W : ℂ)⁻¹ * ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [routeTNormalizedSmoothWindowMellin]
        ring
    _ = (W : ℂ)⁻¹ * ∫ y : ℝ,
        heathBrownObservedEligibleDyadicAggregate L X k T t N R
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((routeTSmoothWindowWeight N W x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by rw [hraw]
    _ = ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N W
          ((sigma : ℂ) + (y : ℝ) * I) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [routeTNormalizedSmoothWindowMellin]
        ring

/-- The complete adjacent normalized defect is unchanged by recutting to its widest observation
cone. -/
theorem integral_windowRelevant_mul_adjacentNormalizedMellin_eq_observed
    (L X k : ℕ) (T t N R : ℝ) {H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))) =
    ∫ y : ℝ,
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hOldR := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
    L X k T t N hN hR hsigma
  have hOldH := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
    L X k T t N hN hH hsigma
  have hNewR := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_heathBrownObservedEligiblePacket L X k T t N R)
      hN hR hsigma
  have hNewH := integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
    (upperSupported_heathBrownObservedEligiblePacket L X k T t N R)
      hN hH hsigma
  simp_rw [mul_sub]
  rw [integral_sub hOldR hOldH,
    integral_windowRelevant_mul_routeTNormalizedMellin_eq_observed
      L X k T t N R hN hR le_rfl hsigma,
    integral_windowRelevant_mul_routeTNormalizedMellin_eq_observed
      L X k T t N R hN hH hHR hsigma]
  have hNewR' : Integrable (fun y : ℝ =>
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N R
          ((sigma : ℂ) + (y : ℝ) * I)) := by
    refine hNewR.congr (Eventually.of_forall fun y => ?_)
    exact congrArg
      (fun z : ℂ => z * routeTNormalizedSmoothWindowMellin N R
        ((sigma : ℂ) + (y : ℝ) * I))
      (LSeries_heathBrownObservedEligiblePacket L X k T t N R
        ((sigma : ℂ) + (y : ℝ) * I))
  have hNewH' : Integrable (fun y : ℝ =>
      heathBrownObservedEligibleDyadicAggregate L X k T t N R
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I)) := by
    refine hNewH.congr (Eventually.of_forall fun y => ?_)
    exact congrArg
      (fun z : ℂ => z * routeTNormalizedSmoothWindowMellin N H
        ((sigma : ℂ) + (y : ℝ) * I))
      (LSeries_heathBrownObservedEligiblePacket L X k T t N R
        ((sigma : ℂ) + (y : ℝ) * I))
  exact (integral_sub hNewR' hNewH').symm

/-- The literal lower support edge is the base-`T` power of total dyadic box exponent. -/
theorem groupedDyadicLower_eq_rpow_heathBrownBoxTotalExponent
    {L X k : ℕ} {T : ℝ} (hT : 1 < T) (box : HeathBrownBoxChoice L X k) :
    ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) =
      T ^ heathBrownBoxTotalExponent L X k T box := by
  simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
    (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT
      (heathBrownBoxFactorExponent box.a box.b box.q)
      (Finset.univ : Finset (HeathBrownBoxFactorIndex k box.m)))

/-- Physical observation makes total box exponent strictly smaller than every ambient exponent
whose power reaches the widest window endpoint. -/
theorem observed_heathBrownBox_totalExponent_lt
    {L X k : ℕ} {T mu N R : ℝ} (hT : 1 < T)
    (hendpoint : N + 2 * R ≤ T ^ mu) (box : HeathBrownBoxChoice L X k)
    (hbox : IsHeathBrownBoxObservedRelevant N R X k box) :
    heathBrownBoxTotalExponent L X k T box < mu := by
  have hD := groupedDyadicLower_eq_rpow_heathBrownBoxTotalExponent hT box
  apply (Real.strictMono_rpow_of_base_gt_one hT).lt_iff_lt.mp
  rw [← hD]
  exact hbox.2.trans_le hendpoint

/-- **Exact support-enhanced derivative reserve.** The old moving reserve omitted physical support
slack. The exact first-receiver gap is its sum with `2*(mu-tau)*(1-alpha)`. -/
theorem derivativeComplementHeight_eq_first_sub_supportReserve
    {mu tau alpha s : ℝ} :
    maynardDerivativeComplementHeightExponent tau alpha s =
      mu * (1 - alpha) -
        ((1 - mu * (1 - alpha) + s) +
          2 * (mu - tau) * (1 - alpha)) := by
  simp only [maynardDerivativeComplementHeightExponent]
  ring

/-- Every physically observed box has strictly positive support-enhanced reserve throughout the
derivative branch, including the former exact zero-reserve boundary. -/
theorem observed_supportEnhancedDerivativeReserve_pos
    {mu tau alpha s : ℝ} (halpha : alpha < 1) (htau : tau < mu)
    (hs : 0 ≤ s) (hthreshold : mu * (1 - alpha) ≤ 1) :
    0 < (1 - mu * (1 - alpha) + s) +
      2 * (mu - tau) * (1 - alpha) := by
  have hfirst : 0 ≤ 1 - mu * (1 - alpha) + s := by linarith
  have hsecond : 0 < 2 * (mu - tau) * (1 - alpha) := by positivity
  linarith

/-- **Reserve-or-support dichotomy.** At every requested exponent margin `eps`, either physical
support slack pays that margin in the derivative receiver, or the box lower edge lies beyond the
corresponding near-cutoff threshold.  This is the exact interface for treating the latter branch
by short additive-support energy instead of pretending strict reserve is uniform. -/
theorem supportEnhancedDerivativeReserve_or_coreLower_near_cutoff
    {L X k : ℕ} {T mu alpha s eps : ℝ} (hT : 1 < T)
    (halpha : alpha ≤ 1) (hs : 0 ≤ s)
    (hthreshold : mu * (1 - alpha) ≤ 1)
    (box : HeathBrownBoxChoice L X k) :
    let tau := heathBrownBoxTotalExponent L X k T box
    2 * eps * (1 - alpha) ≤
        (1 - mu * (1 - alpha) + s) +
          2 * (mu - tau) * (1 - alpha) ∨
      T ^ (mu - eps) <
        (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) := by
  dsimp only
  let tau := heathBrownBoxTotalExponent L X k T box
  have hbase : 0 ≤ 1 - mu * (1 - alpha) + s := by linarith
  have hnonneg : 0 ≤ 1 - alpha := by linarith
  by_cases hgap : eps ≤ mu - tau
  · left
    have hmul : 2 * eps * (1 - alpha) ≤
        2 * (mu - tau) * (1 - alpha) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hnonneg
    linarith
  · right
    have hexp : mu - eps < tau := by linarith
    have hrpow := (Real.strictMono_rpow_of_base_gt_one hT).lt_iff_lt.mpr hexp
    rw [← groupedDyadicLower_eq_rpow_heathBrownBoxTotalExponent hT box] at hrpow
    exact hrpow

end RHTower.Sieve
