import GaloisForLFunctions.RHTower.Sieve.MaynardWindowRelevantAggregate

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

private theorem arithmeticFunction_sum_apply_window
    {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ u, F i) n = ∑ i ∈ u, F i n := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [ArithmeticFunction.zero_apply]
  | @insert a u ha ih => simp [ha, ih, ArithmeticFunction.add_apply]

def heathBrownWindowRelevantEligiblePacket
    (L X k : ℕ) (T0 t N : ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ∑ box : HeathBrownBoxChoice L X k,
    if IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxWindowRelevant N X k box then
      heathBrownDyadicTermBox L X k box.m box.a box.b box.q
    else 0

theorem LSeries_heathBrownWindowRelevantEligiblePacket
    (L X k : ℕ) (T0 t N : ℝ) (s : ℂ) :
    LSeries (complexCoeff
      (heathBrownWindowRelevantEligiblePacket L X k T0 t N)) s =
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N s := by
  classical
  rw [heathBrownWindowRelevantEligiblePacket, complexCoeff_sum, LSeries_sum]
  · simp only [heathBrownWindowRelevantEligibleDyadicAggregate]
    apply Finset.sum_congr rfl
    intro box _hbox
    by_cases h : IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxWindowRelevant N X k box
    · simp [h, heathBrownBoxTerm]
      exact LSeries_heathBrownDyadicTermBox
        L X k box.m box.a box.b box.q s
    · simp only [h, if_false]
      have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
        funext n
        simp [complexCoeff_apply]
      rw [hzero]
      exact congrFun LSeries_zero s
  · intro box _hbox
    by_cases h : IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxWindowRelevant N X k box
    · simp only [h]
      exact LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
        L X k box.m box.a box.b box.q s
    · simp only [h, if_false]
      have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
        funext n
        simp [complexCoeff_apply]
      rw [hzero]
      exact LSeriesSummable_zero

theorem LSeriesSummable_heathBrownWindowRelevantEligiblePacket
    (L X k : ℕ) (T0 t N : ℝ) (s : ℂ) :
    LSeriesSummable
      (complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T0 t N)) s := by
  classical
  rw [heathBrownWindowRelevantEligiblePacket, complexCoeff_sum]
  apply LSeriesSummable.sum
  intro box _hbox
  by_cases h : IsHeathBrownBoxEligible L X k T0 t box ∧
      IsHeathBrownBoxWindowRelevant N X k box
  · simp only [h]
    exact LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
      L X k box.m box.a box.b box.q s
  · simp only [h, if_false]
    have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
      funext n
      simp [complexCoeff_apply]
    rw [hzero]
    exact LSeriesSummable_zero

theorem smul_tsum_heathBrownWindowRelevantEligiblePacket_smoothWeight_eq_integral
    (L X k : ℕ) (T0 t N0 : ℝ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
      complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T0 t N0) n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N0
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  let F := heathBrownWindowRelevantEligiblePacket L X k T0 t N0
  have hF0 : complexCoeff F 0 = 0 := by
    classical
    have hpacket : F 0 = 0 := by
      dsimp only [F]
      rw [heathBrownWindowRelevantEligiblePacket,
        arithmeticFunction_sum_apply_window]
      apply Finset.sum_eq_zero
      intro box _hbox
      by_cases h : IsHeathBrownBoxEligible L X k T0 t box ∧
          IsHeathBrownBoxWindowRelevant N0 X k box
      · simp only [h]
        by_contra hterm
        have hmem := upperSupported_heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q 0 hterm
        simp at hmem
      · simp [h]
    simp [complexCoeff_apply, hpacket]
  have hsum : Summable fun n : ℕ => ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) :=
    summable_norm_mul_rpow_of_LSeriesSummable (by linarith)
      (LSeriesSummable_heathBrownWindowRelevantEligiblePacket
        L X k T0 t N0 (sigma : ℂ))
  have hperron := tsum_mul_smoothWeight_eq_integral_summable
    (a := complexCoeff F) hF0 hN hH hsigma hsum
  rw [hperron]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  congr 1
  rw [tsum_cpow_neg_eq_LSeries hF0]
  exact LSeries_heathBrownWindowRelevantEligiblePacket
    L X k T0 t N0 ((sigma : ℂ) + (y : ℝ) * I)

theorem heathBrownPerronRelevantEligiblePacket_apply_eq_windowRelevant_of_lt
    (L X k : ℕ) (T0 t : ℝ) {N : ℝ} {n : ℕ} (hn : N < n) :
    heathBrownPerronRelevantEligiblePacket L X k T0 t n =
      heathBrownWindowRelevantEligiblePacket L X k T0 t N n := by
  classical
  rw [heathBrownPerronRelevantEligiblePacket,
    heathBrownWindowRelevantEligiblePacket,
    arithmeticFunction_sum_apply_window, arithmeticFunction_sum_apply_window]
  apply Finset.sum_congr rfl
  intro box _hbox
  by_cases hold : IsHeathBrownBoxEligible L X k T0 t box ∧
      IsHeathBrownBoxPerronRelevant X k box
  · by_cases hu : N < (groupedDyadicUpper
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ)
    · have hnew : IsHeathBrownBoxEligible L X k T0 t box ∧
          IsHeathBrownBoxWindowRelevant N X k box := ⟨hold.1, hold.2, hu⟩
      simp [hold, hnew]
    · have hupper : (heathBrownDyadicCoreUpper
          (k - box.m) box.a box.b box.q : ℝ) ≤ N := by
        rw [← groupedDyadicUpper_heathBrownBoxFactorExponent_eq_coreUpper]
        exact le_of_not_gt hu
      have hzero : heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n = 0 := by
        by_contra hne
        have hmem := upperSupported_heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n hne
        have hnupper := (Finset.mem_Icc.mp hmem).2
        have hnN : (n : ℝ) ≤ N :=
          (by exact_mod_cast hnupper : (n : ℝ) ≤
            (heathBrownDyadicCoreUpper (k - box.m) box.a box.b box.q : ℝ)).trans hupper
        linarith
      have hnew : ¬ (IsHeathBrownBoxEligible L X k T0 t box ∧
          IsHeathBrownBoxWindowRelevant N X k box) := by
        intro h
        exact hu h.2.2
      simp [hold.1, hold.2, hu, IsHeathBrownBoxWindowRelevant, hzero]
  · have hnew : ¬ (IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxWindowRelevant N X k box) := by
      intro h
      exact hold ⟨h.1, h.2.1⟩
    simp [hold, hnew]

private theorem summable_mul_smoothWeight_window
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

/-- The adjacent coefficient sum is unchanged by deleting boxes wholly below its lower edge. -/
theorem tsum_heathBrownPerronRelevantEligiblePacket_adjacent_eq_windowRelevant
    (L X k : ℕ) (T0 t : ℝ) {N H : ℝ} (hH : 0 < H) :
    (∑' n : ℕ, complexCoeff
        (heathBrownPerronRelevantEligiblePacket L X k T0 t) n *
      (((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ) -
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))) =
    ∑' n : ℕ, complexCoeff
        (heathBrownWindowRelevantEligiblePacket L X k T0 t N) n *
      (((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ) -
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
  apply tsum_congr
  intro n
  by_cases hn : (n : ℝ) ≤ N
  · rw [GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hn,
      GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH (by linarith)]
    simp
  · rw [complexCoeff_apply, complexCoeff_apply,
      heathBrownPerronRelevantEligiblePacket_apply_eq_windowRelevant_of_lt
        L X k T0 t (lt_of_not_ge hn)]

/-- **Two-sided adjacent Perron recut.**  Only boxes whose coefficient support meets the physical
window remain in either vertical integral. -/
theorem integral_heathBrownPerronRelevantEligibleDyadicAggregate_adjacent_eq_windowRelevant
    (L X k : ℕ) (T0 t : ℝ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 1 < sigma) :
    (∫ y : ℝ,
      heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) -
    (∫ y : ℝ,
      heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) -
    ∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I) := by
  let old : ℕ → ℂ := fun n =>
    complexCoeff (heathBrownPerronRelevantEligiblePacket L X k T0 t) n
  let new : ℕ → ℂ := fun n =>
    complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T0 t N) n
  let Wplus : ℕ → ℂ := fun n =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H (n : ℝ) : ℝ) : ℂ)
  let Wbase : ℕ → ℂ := fun n =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)
  have holdPlus : Summable fun n => old n * Wplus n :=
    summable_mul_smoothWeight_window _ hH
  have holdBase : Summable fun n => old n * Wbase n :=
    summable_mul_smoothWeight_window _ hH
  have hnewPlus : Summable fun n => new n * Wplus n :=
    summable_mul_smoothWeight_window _ hH
  have hnewBase : Summable fun n => new n * Wbase n :=
    summable_mul_smoothWeight_window _ hH
  have hsum : (∑' n, old n * Wplus n) - ∑' n, old n * Wbase n =
      (∑' n, new n * Wplus n) - ∑' n, new n * Wbase n := by
    rw [← holdPlus.tsum_sub holdBase, ← hnewPlus.tsum_sub hnewBase]
    simpa [old, new, Wplus, Wbase, mul_sub] using
      tsum_heathBrownPerronRelevantEligiblePacket_adjacent_eq_windowRelevant
        L X k T0 t hH
  have holdPlusP0 :=
    smul_tsum_heathBrownPerronRelevantEligiblePacket_smoothWeight_eq_integral
      L X k T0 t (N := N + H) (H := H) (sigma := sigma)
        (by linarith) hH hsigma
  have holdBaseP0 :=
    smul_tsum_heathBrownPerronRelevantEligiblePacket_smoothWeight_eq_integral
      L X k T0 t (N := N) (H := H) (sigma := sigma) hN hH hsigma
  have hnewPlusP0 :=
    smul_tsum_heathBrownWindowRelevantEligiblePacket_smoothWeight_eq_integral
      L X k T0 t N (N := N + H) (H := H) (sigma := sigma)
        (by linarith) hH hsigma
  have hnewBaseP0 :=
    smul_tsum_heathBrownWindowRelevantEligiblePacket_smoothWeight_eq_integral
      L X k T0 t N (N := N) (H := H) (sigma := sigma) hN hH hsigma
  have holdPlusP : (2 * Real.pi : ℝ) • (∑' n, old n * Wplus n) =
      ∫ y : ℝ,
        heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
    simpa [old, Wplus] using holdPlusP0
  have holdBaseP : (2 * Real.pi : ℝ) • (∑' n, old n * Wbase n) =
      ∫ y : ℝ,
        heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
    simpa [old, Wbase] using holdBaseP0
  have hnewPlusP : (2 * Real.pi : ℝ) • (∑' n, new n * Wplus n) =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
    simpa [new, Wplus] using hnewPlusP0
  have hnewBaseP : (2 * Real.pi : ℝ) • (∑' n, new n * Wbase n) =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
    simpa [new, Wbase] using hnewBaseP0
  have hsumSmul := congrArg (fun z : ℂ => (2 * Real.pi : ℝ) • z) hsum
  rw [smul_sub, holdPlusP, holdBaseP, smul_sub, hnewPlusP, hnewBaseP] at hsumSmul
  exact hsumSmul

/-- **Exact physical-window Perron formula.**  Every selected box now has lower edge in
`(N / 2^(2k), X]`; neither adjacent-null support sector remains in the pointwise aggregate. -/
theorem tsum_vonMangoldt_smoothWindow_eq_integral_heathBrownWindowRelevantEligibleAggregate
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H sigma : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X)
    (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        (((GaloisForLFunctions.HTGeometry.smoothWeight
            (N + H) H (n : ℝ) : ℝ) : ℂ) -
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))) =
      (∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I)) -
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  rw [tsum_vonMangoldt_smoothWindow_eq_integral_heathBrownPerronRelevantEligibleAggregate
    L X k hXL hT0 hscale hN hH hsupport hsigma]
  exact
    integral_heathBrownPerronRelevantEligibleDyadicAggregate_adjacent_eq_windowRelevant
      L X k T0 t hN hH hsigma

end RHTower.Sieve
