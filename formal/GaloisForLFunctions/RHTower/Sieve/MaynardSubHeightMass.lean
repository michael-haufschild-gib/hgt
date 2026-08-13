import GaloisForLFunctions.RHTower.Sieve.MaynardSubHeightGroupSelection
import GaloisForLFunctions.RHTower.Sieve.MaynardKuzminLandauAmplitude
import GaloisForLFunctions.RHTower.Sieve.MaynardEndpointMass
import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusEndpoint

/-!
# High amplitude forces sub-height logarithmic mass

The `81/190` Kuzmin--Landau deficit is too large for a high-amplitude product to concentrate its
mass in factors above the height.  This module isolates the exact weighted principle: if the
sub-height mass were below the grouping threshold, the over-height subset would occupy at least
`1-t` of the total mass and force a fixed global amplitude deficit.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Weighted amplitude principle forcing at least `t` mass below the height threshold `1`. -/
theorem subHeight_mass_ge_of_large_weighted_amplitude
    {ι : Type*} [Fintype ι]
    (w a slack : ι → ℝ) {t Delta E alpha : ℝ}
    (ht : 0 < t) (hw : ∀ i, 0 ≤ w i)
    (htotal : t ≤ ∑ i, w i)
    (hDelta : 0 ≤ Delta) (hslack : ∀ i, 0 ≤ slack i)
    (hall : ∀ i, a i ≤ 1 + slack i)
    (hover : ∀ i, 1 ≤ w i → a i ≤ 1 - Delta)
    (hslackMass : ∑ i, slack i * w i ≤ E * ∑ i, w i)
    (hglobal : alpha * ∑ i, w i ≤ ∑ i, a i * w i)
    (halpha : 1 - ((1 - t) * Delta - E) < alpha) :
    t ≤ ∑ i ∈ (Finset.univ.filter fun i => w i < 1), w i := by
  classical
  let good : Finset ι := Finset.univ.filter fun i => w i < 1
  let high : Finset ι := Finset.univ.filter fun i => ¬w i < 1
  by_contra hnot
  have hgood : ∑ i ∈ good, w i < t := by
    exact lt_of_not_ge (by simpa [good] using hnot)
  have hsplit : ∑ i, w i = (∑ i ∈ good, w i) + ∑ i ∈ high, w i := by
    dsimp only [good, high]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => w i < 1) w).symm
  have hhighNonempty : high.Nonempty := by
    by_contra hempty
    have hhighEmpty : high = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hhighEmpty, sum_empty, add_zero] at hsplit
    linarith
  obtain ⟨j, hj⟩ := hhighNonempty
  have hwj : 1 ≤ w j := le_of_not_gt (by
    simpa [high] using (Finset.mem_filter.mp hj).2)
  have hjSum : w j ≤ ∑ i ∈ high, w i :=
    Finset.single_le_sum (fun i hi => hw i) hj
  have htotalOne : 1 ≤ ∑ i, w i := by
    rw [hsplit]
    have hgood0 : 0 ≤ ∑ i ∈ good, w i :=
      Finset.sum_nonneg fun i _ => hw i
    linarith
  have ht0 : 0 ≤ t := ht.le
  have hgoodScaled : ∑ i ∈ good, w i ≤ t * ∑ i, w i := by
    have htOne : t ≤ t * ∑ i, w i := by
      nlinarith
    exact hgood.le.trans htOne
  have hoverMass :
      (1 - t) * ∑ i, w i ≤ ∑ i ∈ high, w i := by
    rw [hsplit] at hgoodScaled ⊢
    linarith
  have hterm : ∀ i, a i * w i ≤
      w i + slack i * w i -
        (if i ∈ high then Delta * w i else 0) := by
    intro i
    by_cases hi : i ∈ high
    · have hwi : 1 ≤ w i := le_of_not_gt (by
        simpa [high] using (Finset.mem_filter.mp hi).2)
      have hmul := mul_le_mul_of_nonneg_right (hover i hwi) (hw i)
      have hslackTerm : 0 ≤ slack i * w i :=
        mul_nonneg (hslack i) (hw i)
      simp only [if_pos hi]
      nlinarith
    · have hmul := mul_le_mul_of_nonneg_right (hall i) (hw i)
      simp only [if_neg hi, sub_zero]
      nlinarith
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  have hpenalty :
      ∑ i, (if i ∈ high then Delta * w i else 0) =
        Delta * ∑ i ∈ high, w i := by
    calc
      ∑ i, (if i ∈ high then Delta * w i else 0) =
          ∑ i ∈ high, Delta * w i := by simp
      _ = Delta * ∑ i ∈ high, w i := by rw [Finset.mul_sum]
  have hdeltaMass :
      Delta * ((1 - t) * ∑ i, w i) ≤
        Delta * ∑ i ∈ high, w i :=
    mul_le_mul_of_nonneg_left hoverMass hDelta
  have hupper :
      ∑ i, a i * w i ≤
        (1 - ((1 - t) * Delta - E)) * ∑ i, w i := by
    calc
      ∑ i, a i * w i ≤
          (∑ i, w i) + (∑ i, slack i * w i) -
            Delta * ∑ i ∈ high, w i := by
        rw [← hpenalty]
        simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib] using hsum
      _ ≤ (∑ i, w i) + E * ∑ i, w i -
            Delta * ∑ i ∈ high, w i := by linarith
      _ ≤ (∑ i, w i) + E * ∑ i, w i -
            Delta * ((1 - t) * ∑ i, w i) :=
        sub_le_sub_left hdeltaMass _
      _ = (1 - ((1 - t) * Delta - E)) * ∑ i, w i := by ring
  have hpositive : 0 < ∑ i, w i := ht.trans_le htotal
  have hstrict := mul_lt_mul_of_pos_right halpha hpositive
  linarith

/-- Route-T numerical margin: amplitude `3/4` lies far above the exclusion forced by insufficient
sub-height mass, uniformly over the full `mu` range. -/
theorem routeT_three_quarters_above_subHeight_exclusion
    {mu : ℝ} (hmu : mu ≤ 19 / 9) :
    1 - ((1 - mu / 120) * (81 / 190 : ℝ) - 1 / 100) < 3 / 4 := by
  nlinarith

/-- Literal positive-length Heath--Brown box form of the weighted sub-height mass principle. -/
theorem maynard_heathBrownBox_subHeight_mass
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (hL : 1 ≤ L) (hX : 1 ≤ X)
    {T t c y alpha Delta E : ℝ}
    (hT : 1 < T) (ht : 0 < t) (hc : 0 ≤ c)
    (htotal : t ≤ ∑ i : PositiveHeathBrownBoxFactorIndex box,
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i))
    (hDelta : 0 ≤ Delta)
    (hover : ∀ i : PositiveHeathBrownBoxFactorIndex box,
      1 ≤ dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) →
      maynardAmplitude c
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))
          ‖heathBrownBoxFactorValue L X k box
              ((c : ℂ) + (y : ℝ) * Complex.I) i‖ ≤ 1 - Delta)
    (hslackMass :
      ∑ i : HeathBrownBoxFactorIndex k box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
        E * Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ))
    (hlarge :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
          (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖)
    (halpha : 1 - ((1 - t) * Delta - E) < alpha) :
    t ≤ ∑ i ∈ (Finset.univ.filter
        fun i : PositiveHeathBrownBoxFactorIndex box =>
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) < 1),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) := by
  classical
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  have hlog : 1 ≤ box.q :=
    heathBrownBox_log_exponent_pos_of_large_core box s (by simpa [s] using hlarge)
  let I := PositiveHeathBrownBoxFactorIndex box
  let q : I → ℕ := fun i => heathBrownBoxFactorExponent box.a box.b box.q i
  let kind : I → HeathBrownFactorKind := fun i => heathBrownBoxFactorKind k box.m i
  let N : I → ℝ := fun i => (((2 ^ q i : ℕ) : ℝ))
  let Z : I → ℂ := fun i => heathBrownBoxFactorValue L X k box s i
  let W : I → ℝ := fun i => ‖Z i‖
  let slack : I → ℝ := fun i => heathBrownFactorAmplitudeSlack (kind i) (q i)
  let w : I → ℝ := fun i => dyadicLogExponent T (q i)
  let a : I → ℝ := fun i => maynardAmplitude c (N i) (W i)
  let logIndex : I := ⟨Sum.inr (Sum.inr ()), hlog⟩
  letI : Nonempty I := ⟨logIndex⟩
  have hN : ∀ i, 1 < N i := by
    intro i
    dsimp [N, q]
    exact_mod_cast (show 1 < 2 ^
        heathBrownBoxFactorExponent box.a box.b box.q
          (i : HeathBrownBoxFactorIndex k box.m) by
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
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s := by
    simpa [Z, I] using
      prod_positive_heathBrownBoxFactorValue_eq_core box hL hX hlog s
  have hWprod : (∏ i, W i) =
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ := by
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
  have hw : ∀ i, 0 ≤ w i := fun i => dyadicLogExponent_nonneg hT (q i)
  have hslack : ∀ i, 0 ≤ slack i := by
    intro i
    exact heathBrownFactorAmplitudeSlack_nonneg (kind i) i.property
  have hall : ∀ i, a i ≤ 1 + slack i := by
    intro i
    exact maynard_heathBrownFactor_amplitude_le_one_add_slack
      L X (q i) (kind i) hc i.property (hW i)
  have hover' : ∀ i, 1 ≤ w i → a i ≤ 1 - Delta := by
    intro i hi
    simpa [a, w, N, W, Z, q, s] using hover i (by simpa [w, q] using hi)
  have hlogNw : ∀ i, Real.log (N i) = w i * Real.log T := by
    intro i
    have hr := rpow_dyadicLogExponent hT (q i)
    calc
      Real.log (N i) = Real.log (T ^ dyadicLogExponent T (q i)) := by
        rw [hr]
      _ = dyadicLogExponent T (q i) * Real.log T := by
        rw [Real.log_rpow (by linarith)]
      _ = w i * Real.log T := by rfl
  have hlogTotal : Real.log (∏ i, N i) = (∑ i, w i) * Real.log T := by
    rw [Real.log_prod (fun i _ => ne_of_gt (lt_trans zero_lt_one (hN i)))]
    simp_rw [hlogNw]
    rw [Finset.sum_mul]
  have hslackLog :
      (∑ i, slack i * w i) * Real.log T ≤
        (E * ∑ i, w i) * Real.log T := by
    calc
      (∑ i, slack i * w i) * Real.log T =
          ∑ i, slack i * Real.log (N i) := by
        simp_rw [hlogNw]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i : HeathBrownBoxFactorIndex k box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) := by
        have htrim := sum_positive_heathBrownBoxFactorAmplitudeSlack_eq box hlog
        simpa [slack, N, q, kind, I] using htrim
      _ ≤ E * Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := hslackMass
      _ = (E * ∑ i, w i) * Real.log T := by
        rw [← hNprod, hlogTotal]
        ring
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hslackMass' : ∑ i, slack i * w i ≤ E * ∑ i, w i :=
    le_of_mul_le_mul_right hslackLog hlogT
  have hweighted := maynardGlobalAmplitude_weighted_mean (c := c) N W hN hW rfl rfl
  have hNprodOne : 1 < ∏ i, N i := by
    calc
      1 = ∏ _i : I, (1 : ℝ) := by simp
      _ < ∏ i, N i := Finset.prod_lt_prod_of_nonempty
        (fun _i _hi => by norm_num) (fun i _hi => hN i) Finset.univ_nonempty
  have hglobalAmp : alpha ≤ maynardGlobalAmplitude c (∏ i, N i) (∏ i, W i) := by
    apply le_maynardAmplitude_of_rpow_le
    · exact hNprodOne
    · rw [hNprod, hWprod]
      simpa [s] using hlarge
  have hglobalLog :
      alpha * Real.log (∏ i, N i) ≤ ∑ i, a i * Real.log (N i) := by
    have hmul := mul_le_mul_of_nonneg_right hglobalAmp
      (Real.log_nonneg hNprodOne.le)
    rw [hweighted] at hmul
    simpa [a] using hmul
  have hglobalScaled :
      (alpha * ∑ i, w i) * Real.log T ≤
        (∑ i, a i * w i) * Real.log T := by
    calc
      (alpha * ∑ i, w i) * Real.log T =
          alpha * Real.log (∏ i, N i) := by rw [hlogTotal]; ring
      _ ≤ ∑ i, a i * Real.log (N i) := hglobalLog
      _ = (∑ i, a i * w i) * Real.log T := by
        simp_rw [hlogNw]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hglobal : alpha * ∑ i, w i ≤ ∑ i, a i * w i :=
    le_of_mul_le_mul_right hglobalScaled hlogT
  have hmass := subHeight_mass_ge_of_large_weighted_amplitude
    w a slack ht hw (by simpa [w, q] using htotal)
      hDelta hslack hall hover' hslackMass' hglobal halpha
  simpa [w, q, I] using hmass

/-- Unconditional eventual sub-height mass law for every selected degree-60 Route-T box at
amplitude at least `3/4`.  Over-height Möbius atoms are excluded by the canonical cutoff; every
remaining over-height atom receives the `81/190` Kuzmin--Landau deficit. -/
theorem eventually_maynard_perronRelevant_box_subHeight_mass :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, 1 ≤ L →
        ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          (∀ i : HeathBrownBoxFactorIndex 60 box.m,
            heathBrownBoxFactorKind 60 box.m i = .moebius →
              dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                  2 * (mu / 120)) →
          ∀ c y alpha : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T → 3 / 4 ≤ alpha →
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
              (alpha - c) ≤
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
          mu / 120 ≤ ∑ i ∈ (Finset.univ.filter
              fun i : PositiveHeathBrownBoxFactorIndex box =>
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) < 1),
            dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) := by
  filter_upwards [eventually_maynard_overHeight_zeta_amplitude_deficit,
    eventually_maynard_overHeight_log_amplitude_deficit,
    eventually_sum_heathBrownBoxFactorAmplitudeSlack_mul_log_le
      (by norm_num : (0 : ℝ) < 1 / 9000),
    Filter.eventually_gt_atTop (1 : ℝ)] with T hzeta hlogFactor hslack hT
  intro X hX mu hmuLo hmuHi hXscale L hL box helig hmobius
    c y alpha hc hylo hyhi halpha hlarge
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  have hqlog : 1 ≤ box.q :=
    heathBrownBox_log_exponent_pos_of_large_core box s (by simpa [s] using hlarge)
  let Z : HeathBrownBoxFactorIndex 60 box.m → ℂ := fun i =>
    heathBrownBoxFactorValue L X 60 box s i
  have hD0 : 0 <
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    exact lt_of_lt_of_le zero_lt_one (by
      exact_mod_cast one_le_groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q))
  have hcorePos : 0 <
      ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s‖ := by
    have hthreshold : 0 <
        ((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
            (alpha - c) := Real.rpow_pos_of_pos hD0 _
    exact hthreshold.trans_le (by simpa [s] using hlarge)
  have hprodZ : (∏ i, Z i) =
      heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s := by
    simpa [Z, heathBrownBoxFactorValue] using heathBrownBoxFactorProduct_eq_core
      L X 60 box.m box.a box.b box.q s
  have hfactorPos : ∀ i : HeathBrownBoxFactorIndex 60 box.m, 0 < ‖Z i‖ := by
    intro i
    have hZi : Z i ≠ 0 := by
      intro hzero
      have hpzero : ∏ j, Z j = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hzero
      rw [hprodZ] at hpzero
      rw [hpzero, norm_zero] at hcorePos
      exact (lt_irrefl 0) hcorePos
    exact norm_pos_iff.mpr hZi
  have hover : ∀ i : PositiveHeathBrownBoxFactorIndex box,
      1 ≤ dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) →
      maynardAmplitude c
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))
          ‖heathBrownBoxFactorValue L X 60 box s i‖ ≤
        1 - 81 / 190 := by
    intro i hi
    let qi : ℕ := heathBrownBoxFactorExponent box.a box.b box.q i
    have hkind : heathBrownBoxFactorKind 60 box.m i = .zeta ∨
        heathBrownBoxFactorKind 60 box.m i = .log := by
      cases hk : heathBrownBoxFactorKind 60 box.m i with
      | moebius =>
          have hshort := hmobius i hk
          have : 2 * (mu / 120) < 1 := by linarith
          exact (not_lt_of_ge hi (hshort.trans_lt this)).elim
      | zeta => exact Or.inl rfl
      | log => exact Or.inr rfl
    have hqiX := box.factorExponent_le_log_X_of_zeta_or_log i hkind
    have hTN : T ≤ (((2 ^ qi : ℕ) : ℝ)) := by
      have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hi
      have hr := rpow_dyadicLogExponent hT qi
      simpa [Real.rpow_one, qi] using hpow.trans_eq hr
    have hV : 0 < ‖heathBrownBoxFactorValue L X 60 box s i‖ := by
      simpa [Z] using hfactorPos i
    rcases hkind with hkind | hkind
    · have hz := hzeta X hX mu hmuHi hXscale qi
        (by simpa [qi] using hqiX) c y hc hylo hyhi
        (by simpa [qi] using hTN)
      simpa [s, qi, heathBrownBoxFactorValue, heathBrownFactorBase, hkind] using
        hz (by simpa [s, qi, heathBrownBoxFactorValue,
          heathBrownFactorBase, hkind] using hV)
    · have hl := hlogFactor X hX mu hmuHi hXscale qi
        (by simpa [qi] using hqiX) c y hc hylo hyhi
        (by simpa [qi] using hTN)
      simpa [s, qi, heathBrownBoxFactorValue, heathBrownFactorBase, hkind] using
        hl (by simpa [s, qi, heathBrownBoxFactorValue,
          heathBrownFactorBase, hkind] using hV)
  let total : ℝ := heathBrownBoxTotalExponent L X 60 T box
  let D : ℝ :=
    ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
  have htotal : mu / 120 ≤ total := by
    simpa [IsHeathBrownBoxEligible, total] using helig
  have htotalMin : (1 / 90 : ℝ) ≤ total := by linarith
  have hD : D = T ^ total := by
    dsimp [D, total]
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT
        (heathBrownBoxFactorExponent box.a box.b box.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex 60 box.m)))
  have hlogD : Real.log D = total * Real.log T := by
    rw [hD, Real.log_rpow (lt_trans zero_lt_one hT)]
  have hlogT0 : 0 ≤ Real.log T := (Real.log_pos hT).le
  have hslackRaw := hslack X hX mu hmuHi hXscale L 60 box hqlog
  have hslackMass :
      ∑ i : HeathBrownBoxFactorIndex 60 box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind 60 box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
        (1 / 100 : ℝ) * Real.log D := by
    calc
      _ ≤ (1 / 9000 : ℝ) * Real.log T := hslackRaw
      _ ≤ (1 / 100 : ℝ) * (total * Real.log T) := by
        have hmul := mul_le_mul_of_nonneg_right htotalMin hlogT0
        nlinarith
      _ = (1 / 100 : ℝ) * Real.log D := by rw [hlogD]
  have htotalPositive : mu / 120 ≤
      ∑ i : PositiveHeathBrownBoxFactorIndex box,
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i) := by
    rw [sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent box]
    exact htotal
  apply maynard_heathBrownBox_subHeight_mass
    (Delta := (81 / 190 : ℝ)) (E := (1 / 100 : ℝ)) box hL hX hT
    (by linarith : 0 < mu / 120) hc htotalPositive
    (by norm_num : (0 : ℝ) ≤ 81 / 190) (by simpa [s] using hover)
    (by simpa [D] using hslackMass) hlarge
  exact (routeT_three_quarters_above_subHeight_exclusion hmuHi).trans_le halpha

/-- The same over-height deficit in the multiplicative form needed for exact complement excision:
at every amplitude `alpha ≥ 3/4`, each over-height atom is below its own `N^(alpha-c)` threshold. -/
theorem eventually_maynard_perronRelevant_box_overHeight_small :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, 1 ≤ L →
        ∀ box : HeathBrownBoxChoice L X 60,
          (∀ i : HeathBrownBoxFactorIndex 60 box.m,
            heathBrownBoxFactorKind 60 box.m i = .moebius →
              dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                  2 * (mu / 120)) →
          ∀ c y alpha : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T → 3 / 4 ≤ alpha →
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
              (alpha - c) ≤
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
          ∀ i : PositiveHeathBrownBoxFactorIndex box,
            1 ≤ dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) →
            ‖heathBrownBoxFactorValue L X 60 box
                ((c : ℂ) + (y : ℝ) * Complex.I) i‖ ≤
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ^
                (alpha - c) := by
  filter_upwards [eventually_maynard_overHeight_zeta_amplitude_deficit,
    eventually_maynard_overHeight_log_amplitude_deficit,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hzeta hlogFactor hT
  intro X hX mu hmuHi hXscale L hL box hmobius
    c y alpha hc hylo hyhi halpha hlarge i hi
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  let qi : ℕ := heathBrownBoxFactorExponent box.a box.b box.q i
  let Z : HeathBrownBoxFactorIndex 60 box.m → ℂ := fun j =>
    heathBrownBoxFactorValue L X 60 box s j
  have hD0 : 0 <
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    exact lt_of_lt_of_le zero_lt_one (by
      exact_mod_cast one_le_groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q))
  have hcorePos : 0 <
      ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s‖ := by
    have hthreshold : 0 <
        ((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
            (alpha - c) := Real.rpow_pos_of_pos hD0 _
    exact hthreshold.trans_le (by simpa [s] using hlarge)
  have hprodZ : (∏ j, Z j) =
      heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s := by
    simpa [Z, heathBrownBoxFactorValue] using heathBrownBoxFactorProduct_eq_core
      L X 60 box.m box.a box.b box.q s
  have hZi : Z i ≠ 0 := by
    intro hzero
    have hpzero : ∏ j, Z j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (i : HeathBrownBoxFactorIndex 60 box.m)) hzero
    rw [hprodZ] at hpzero
    rw [hpzero, norm_zero] at hcorePos
    exact (lt_irrefl 0) hcorePos
  have hV : 0 < ‖heathBrownBoxFactorValue L X 60 box s i‖ := by
    exact norm_pos_iff.mpr (by simpa [Z] using hZi)
  have hkind : heathBrownBoxFactorKind 60 box.m i = .zeta ∨
      heathBrownBoxFactorKind 60 box.m i = .log := by
    cases hk : heathBrownBoxFactorKind 60 box.m i with
    | moebius =>
        have hshort := hmobius i hk
        have : 2 * (mu / 120) < 1 := by linarith
        exact (not_lt_of_ge hi (hshort.trans_lt this)).elim
    | zeta => exact Or.inl rfl
    | log => exact Or.inr rfl
  have hqiX := box.factorExponent_le_log_X_of_zeta_or_log i hkind
  have hTN : T ≤ (((2 ^ qi : ℕ) : ℝ)) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hi
    have hr := rpow_dyadicLogExponent hT qi
    simpa [Real.rpow_one, qi] using hpow.trans_eq hr
  have hamp : maynardAmplitude c (((2 ^ qi : ℕ) : ℝ))
      ‖heathBrownBoxFactorValue L X 60 box s i‖ ≤ 1 - 81 / 190 := by
    rcases hkind with hkind | hkind
    · have hz := hzeta X hX mu hmuHi hXscale qi
        (by simpa [qi] using hqiX) c y hc hylo hyhi
        (by simpa [qi] using hTN)
      simpa [s, qi, heathBrownBoxFactorValue, heathBrownFactorBase, hkind] using
        hz (by simpa [s, qi, heathBrownBoxFactorValue,
          heathBrownFactorBase, hkind] using hV)
    · have hl := hlogFactor X hX mu hmuHi hXscale qi
        (by simpa [qi] using hqiX) c y hc hylo hyhi
        (by simpa [qi] using hTN)
      simpa [s, qi, heathBrownBoxFactorValue, heathBrownFactorBase, hkind] using
        hl (by simpa [s, qi, heathBrownBoxFactorValue,
          heathBrownFactorBase, hkind] using hV)
  have hN : (1 : ℝ) < (((2 ^ qi : ℕ) : ℝ)) := by
    exact_mod_cast (show 1 < 2 ^ qi by
      exact pow_lt_pow_right₀ (by norm_num) i.property)
  have hampAlpha : maynardAmplitude c (((2 ^ qi : ℕ) : ℝ))
      ‖heathBrownBoxFactorValue L X 60 box s i‖ ≤ alpha := by
    have : (1 - 81 / 190 : ℝ) < 3 / 4 := by norm_num
    exact hamp.trans (this.le.trans halpha)
  have hid := rpow_maynardAmplitude_sub_abscissa (c := c) hN hV
  have hbound : ‖heathBrownBoxFactorValue L X 60 box s i‖ ≤
      (((2 ^ qi : ℕ) : ℝ)) ^ (alpha - c) := calc
    ‖heathBrownBoxFactorValue L X 60 box s i‖ =
        (((2 ^ qi : ℕ) : ℝ)) ^
          (maynardAmplitude c (((2 ^ qi : ℕ) : ℝ))
            ‖heathBrownBoxFactorValue L X 60 box s i‖ - c) := hid.symm
    _ ≤ (((2 ^ qi : ℕ) : ℝ)) ^ (alpha - c) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (sub_le_sub_right hampAlpha c)
  simpa [s, qi] using hbound

end RHTower.Sieve
