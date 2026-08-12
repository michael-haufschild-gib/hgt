import GaloisForLFunctions.RHTower.Sieve.MaynardEndpointZetaLogDeficit

/-!
# Near-maximal endpoint boxes concentrate logarithmic mass in Möbius atoms

The endpoint-long zeta/log factors have a fixed local deficit, whereas Maynard's endpoint band has
a vanishing global gap.  Exact weighted-product bookkeeping therefore forces almost all endpoint-
long logarithmic mass into the only surviving kind: Möbius factors.

This is stronger than a factor dichotomy.  It proves a quantitative mass concentration law and
isolates the remaining Route-T obstruction as a pure Möbius-block cancellation theorem.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

/-- Generic endpoint concentration law.  If at least `19/20` of the weight lies in `long`, every
non-surviving long index has deficit `Delta`, and the full weighted amplitude is above `1-eta`,
then the surviving long indices carry the displayed mass. -/
theorem near_maximal_endpoint_mass_concentrates_in_survivors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w a slack : ι → ℝ) (long : Finset ι) (survives : ι → Prop)
    [DecidablePred survives] {eta Delta E : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hDelta : 0 ≤ Delta)
    (hslack : ∀ i, 0 ≤ slack i)
    (hall : ∀ i, a i ≤ 1 + slack i)
    (hbad : ∀ i ∈ long, ¬ survives i → a i ≤ 1 - Delta)
    (hlong : (19 / 20 : ℝ) * ∑ i, w i ≤ ∑ i ∈ long, w i)
    (hslackMass : ∑ i, slack i * w i ≤ E * ∑ i, w i)
    (hglobal : (1 - eta) * ∑ i, w i < ∑ i, a i * w i) :
    ((19 / 20 : ℝ) * Delta - eta - E) * ∑ i, w i <
      Delta * ∑ i ∈ long.filter survives, w i := by
  classical
  let survivor : Finset ι := long.filter survives
  let bad : Finset ι := long.filter fun i => ¬ survives i
  have hterm : ∀ i, a i * w i ≤
      w i + slack i * w i - (if i ∈ bad then Delta * w i else 0) := by
    intro i
    by_cases hi : i ∈ bad
    · have hilong : i ∈ long := (Finset.mem_filter.mp hi).1
      have hins : ¬ survives i := (Finset.mem_filter.mp hi).2
      have hmul := mul_le_mul_of_nonneg_right (hbad i hilong hins) (hw i)
      have hslackTerm : 0 ≤ slack i * w i := mul_nonneg (hslack i) (hw i)
      simp only [if_pos hi]
      nlinarith
    · simp only [if_neg hi, sub_zero]
      have hmul := mul_le_mul_of_nonneg_right (hall i) (hw i)
      nlinarith
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  have hpenalty :
      ∑ i, (if i ∈ bad then Delta * w i else 0) =
        Delta * ∑ i ∈ bad, w i := by
    calc
      ∑ i, (if i ∈ bad then Delta * w i else 0) =
          ∑ i ∈ bad, Delta * w i := by simp
      _ = Delta * ∑ i ∈ bad, w i := by rw [Finset.mul_sum]
  have hupper : ∑ i, a i * w i ≤
      ∑ i, w i + E * ∑ i, w i - Delta * ∑ i ∈ bad, w i := by
    calc
      ∑ i, a i * w i ≤
          (∑ i, w i) + (∑ i, slack i * w i) -
            Delta * ∑ i ∈ bad, w i := by
        rw [← hpenalty]
        simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib] using hsum
      _ ≤ ∑ i, w i + E * ∑ i, w i - Delta * ∑ i ∈ bad, w i := by
        linarith
  have hbadMass : Delta * ∑ i ∈ bad, w i < (eta + E) * ∑ i, w i := by
    linarith
  have hsplit : ∑ i ∈ long, w i =
      ∑ i ∈ survivor, w i + ∑ i ∈ bad, w i := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr
      · ext i
        simp [survivor, bad]
        tauto
      · intro i hi
        rfl
    · apply Finset.disjoint_left.mpr
      intro i his hib
      exact (Finset.mem_filter.mp hib).2 (Finset.mem_filter.mp his).2
  have hmass : (19 / 20 : ℝ) * ∑ i, w i ≤
      ∑ i ∈ survivor, w i + ∑ i ∈ bad, w i := by
    rwa [← hsplit]
  have hscaleMass : Delta * ((19 / 20 : ℝ) * ∑ i, w i) ≤
      Delta * (∑ i ∈ survivor, w i + ∑ i ∈ bad, w i) :=
    mul_le_mul_of_nonneg_left hmass hDelta
  dsimp [survivor] at hscaleMass ⊢
  dsimp [bad] at hbadMass
  nlinarith

/-- **Literal degree-`60` Möbius concentration law.**  A near-maximal eligible box whose
endpoint-long zeta/log atoms have local deficit `Delta` must place the stated amount of its exact
logarithmic length in endpoint-long Möbius atoms. -/
theorem maynard_heathBrownBox_near_endpoint_mobius_concentration
    {L X : ℕ} (box : HeathBrownBoxChoice L X 60)
    (hL : 1 ≤ L) (hX : 1 ≤ X)
    {T c y alpha eta Delta E : ℝ}
    (hT : 1 < T) (hc : 0 ≤ c) (hDelta : 0 ≤ Delta)
    (hzetaLog : ∀ j : PositiveHeathBrownBoxFactorIndex box,
      (heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q j)) →
      (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
        heathBrownBoxFactorKind 60 box.m j = .log) →
      maynardAmplitude c
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
          ‖heathBrownBoxFactorValue L X 60 box
              ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤
        1 - Delta)
    (hslackMass :
      ∑ i : HeathBrownBoxFactorIndex 60 box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind 60 box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
        E * Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ))
    (hlarge :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖)
    (hnear : 1 - eta < alpha) :
    ((19 / 20 : ℝ) * Delta - eta - E) *
        Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) <
      Delta *
        ∑ i ∈ (Finset.univ.filter fun i : PositiveHeathBrownBoxFactorIndex box =>
          heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
              dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q i) ∧
            heathBrownBoxFactorKind 60 box.m i = .moebius),
          Real.log
            (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) := by
  classical
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  have hlog : 1 ≤ box.q :=
    heathBrownBox_log_exponent_pos_of_large_core box s (by simpa [s] using hlarge)
  let I := PositiveHeathBrownBoxFactorIndex box
  let q : I → ℕ := fun i => heathBrownBoxFactorExponent box.a box.b box.q i
  let kind : I → HeathBrownFactorKind := fun i => heathBrownBoxFactorKind 60 box.m i
  let N : I → ℝ := fun i => (((2 ^ q i : ℕ) : ℝ))
  let Z : I → ℂ := fun i => heathBrownBoxFactorValue L X 60 box s i
  let W : I → ℝ := fun i => ‖Z i‖
  let slack : I → ℝ := fun i => heathBrownFactorAmplitudeSlack (kind i) (q i)
  let w : I → ℝ := fun i => Real.log (N i)
  let long : Finset I := Finset.univ.filter fun i =>
    heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
      dyadicLogExponent T (q i)
  let survives : I → Prop := fun i => kind i = .moebius
  let logIndex : I := ⟨Sum.inr (Sum.inr ()), hlog⟩
  letI : Nonempty I := ⟨logIndex⟩
  have hN : ∀ i, 1 < N i := by
    intro i
    dsimp [N, q]
    exact_mod_cast (show 1 < 2 ^
        heathBrownBoxFactorExponent box.a box.b box.q
          (i : HeathBrownBoxFactorIndex 60 box.m) by
      exact pow_lt_pow_right₀ (by norm_num) i.property)
  have hNprod : (∏ i, N i) =
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    change (∏ i : I, (((2 ^ q i : ℕ) : ℝ))) =
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
    norm_cast
    exact prod_positive_heathBrownBoxFactorLength_eq_groupedLower box
  have hZprod : (∏ i, Z i) =
      heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s := by
    simpa [Z, I] using
      prod_positive_heathBrownBoxFactorValue_eq_core box hL hX hlog s
  have hWprod : (∏ i, W i) =
      ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s‖ := by
    rw [← hZprod]
    simp [W]
  have hNprodPos : 0 < ∏ i, N i :=
    Finset.prod_pos fun i _ => (hN i).trans' zero_lt_one
  have hthreshold : 0 < (∏ i, N i) ^ (alpha - c) :=
    Real.rpow_pos_of_pos hNprodPos _
  have hWprodPos : 0 < ∏ i, W i := by
    rw [hWprod]
    exact hthreshold.trans_le (by simpa [hNprod, s] using hlarge)
  have hW : ∀ i, 0 < W i := by
    intro i
    by_contra hi
    have hi0 : W i = 0 := le_antisymm (le_of_not_gt hi) (norm_nonneg _)
    have hzero : ∏ r, W r = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi0
    rw [hzero] at hWprodPos
    exact (lt_irrefl 0) hWprodPos
  have hw : ∀ i, 0 ≤ w i := fun i => Real.log_nonneg (hN i).le
  have hslack : ∀ i, 0 ≤ slack i := by
    intro i
    exact heathBrownFactorAmplitudeSlack_nonneg (kind i) i.property
  let a : I → ℝ := fun i => maynardAmplitude c (N i) (W i)
  have hall : ∀ i, a i ≤ 1 + slack i := by
    intro i
    exact maynard_heathBrownFactor_amplitude_le_one_add_slack
      L X (q i) (kind i) hc i.property (hW i)
  have hbad : ∀ i ∈ long, ¬ survives i → a i ≤ 1 - Delta := by
    intro i hi hnot
    have hilong := (Finset.mem_filter.mp hi).2
    have hkind : kind i = .zeta ∨ kind i = .log := by
      cases hk : kind i with
      | moebius => exact (hnot hk).elim
      | zeta => exact Or.inl rfl
      | log => exact Or.inr rfl
    exact hzetaLog i (by simpa [q] using hilong) (by simpa [kind] using hkind)
  have hlogNw : ∀ i, w i =
      dyadicLogExponent T (q i) * Real.log T := by
    intro i
    have hr := rpow_dyadicLogExponent hT (q i)
    dsimp [w]
    calc
      Real.log (N i) = Real.log (T ^ dyadicLogExponent T (q i)) := by rw [hr]
      _ = dyadicLogExponent T (q i) * Real.log T := by
        rw [Real.log_rpow (by linarith)]
  have hcardEq : Fintype.card (HeathBrownBoxFactorIndex 60 box.m) =
      2 * (60 - box.m) := card_heathBrownBoxFactorIndex box.1.isLt
  have hcardOriginal : Fintype.card (HeathBrownBoxFactorIndex 60 box.m) ≤ 2 * 60 := by
    rw [hcardEq]
    omega
  have hcardI : Fintype.card I ≤
      Fintype.card (HeathBrownBoxFactorIndex 60 box.m) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have htotalPositive : heathBrownBoxTotalExponent L X 60 T box =
      ∑ i : I, dyadicLogExponent T (q i) := by
    let u : Finset (HeathBrownBoxFactorIndex 60 box.m) :=
      Finset.univ.filter fun i =>
        1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i
    have hu (i : HeathBrownBoxFactorIndex 60 box.m) : i ∈ u ↔
        1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i := by
      simp [u]
    have hreindex := Finset.sum_subtype
      (F := Subtype.fintype fun i : HeathBrownBoxFactorIndex 60 box.m =>
        1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i)
      u hu (fun i => dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i))
    rw [heathBrownBoxTotalExponent]
    symm
    calc
      ∑ i : I, dyadicLogExponent T (q i) =
          ∑ i ∈ u, dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) := by
        simpa [I, q] using hreindex.symm
      _ = ∑ i : HeathBrownBoxFactorIndex 60 box.m,
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _hi hiu
        have hqi : heathBrownBoxFactorExponent box.a box.b box.q i = 0 := by
          have : ¬ 1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i := by
            simpa [u] using hiu
          omega
        simp [hqi, dyadicLogExponent, Real.logb]
  have hmassWeight := nineteen_twentieths_total_le_sum_endpoint_long_weights
    60 (by norm_num) (fun i : I => dyadicLogExponent T (q i))
      (fun i => dyadicLogExponent_nonneg hT (q i)) (hcardI.trans hcardOriginal)
  have hlongMass : (19 / 20 : ℝ) * ∑ i, w i ≤ ∑ i ∈ long, w i := by
    have hmulg := mul_le_mul_of_nonneg_right hmassWeight (Real.log_nonneg hT.le)
    simp_rw [hlogNw]
    calc
      (19 / 20 : ℝ) * ∑ i, dyadicLogExponent T (q i) * Real.log T =
          ((19 / 20 : ℝ) * ∑ i, dyadicLogExponent T (q i)) * Real.log T := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ (∑ i ∈ long, dyadicLogExponent T (q i)) * Real.log T := by
        simpa [long, htotalPositive] using hmulg
      _ = ∑ i ∈ long, dyadicLogExponent T (q i) * Real.log T := by
        rw [Finset.sum_mul]
  have hlogTotal : Real.log (∏ i, N i) = ∑ i, w i := by
    dsimp [w]
    exact Real.log_prod (fun i _ => ne_of_gt (lt_trans zero_lt_one (hN i)))
  have hslackMass' : ∑ i, slack i * w i ≤ E * ∑ i, w i := by
    rw [← hlogTotal, hNprod]
    have htrim := sum_positive_heathBrownBoxFactorAmplitudeSlack_eq box hlog
    calc
      ∑ i, slack i * w i =
          ∑ i : HeathBrownBoxFactorIndex 60 box.m,
            heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind 60 box.m i)
                (heathBrownBoxFactorExponent box.a box.b box.q i) *
              Real.log
                (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) := by
          simpa [slack, w, N, q, kind, I] using htrim
      _ ≤ E * Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := hslackMass
  have hweighted := maynardGlobalAmplitude_weighted_mean (c := c) N W hN hW rfl rfl
  have hglobalAmp : alpha ≤ maynardGlobalAmplitude c (∏ i, N i) (∏ i, W i) := by
    apply le_maynardAmplitude_of_rpow_le
    · calc
        1 = ∏ _i : I, (1 : ℝ) := by simp
        _ < ∏ i, N i := Finset.prod_lt_prod_of_nonempty
          (fun _i _hi => by norm_num) (fun i _hi => hN i) Finset.univ_nonempty
    · rw [hNprod, hWprod]
      simpa [s] using hlarge
  have hglobal : (1 - eta) * ∑ i, w i < ∑ i, a i * w i := by
    have hlogprod : 0 < Real.log (∏ i, N i) := Real.log_pos (by
      calc
        1 = ∏ _i : I, (1 : ℝ) := by simp
        _ < ∏ i, N i := Finset.prod_lt_prod_of_nonempty
          (fun _i _hi => by norm_num) (fun i _hi => hN i) Finset.univ_nonempty)
    have hamp : 1 - eta < maynardGlobalAmplitude c (∏ i, N i) (∏ i, W i) :=
      hnear.trans_le hglobalAmp
    have hmul := mul_lt_mul_of_pos_right hamp hlogprod
    rw [hweighted] at hmul
    simpa [a, ← hlogTotal] using hmul
  have hconcentration := near_maximal_endpoint_mass_concentrates_in_survivors
    w a slack long survives hw hDelta hslack hall hbad hlongMass hslackMass' hglobal
  rw [← hlogTotal, hNprod] at hconcentration
  simpa only [long, survives, w, N, q, kind, Finset.filter_filter] using hconcentration

end RHTower.Sieve
