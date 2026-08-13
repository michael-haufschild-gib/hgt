import GaloisForLFunctions.RHTower.Sieve.MaynardWindowRelevantPerron
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment
import GaloisForLFunctions.RHTower.Sieve.MaynardLowTotalBound
import GaloisForLFunctions.RHTower.Sieve.LSeriesTrivialSize

/-!
# Fixed-polylogarithmic low-ordinate bound for the window-relevant packet

The pole-annihilating reference/target kernel saves only a power-log PNT factor.  A pointwise
`n^epsilon` divisor bound would erase that saving.  This file instead sums the fixed divisor
moment before estimating the vertical polynomial.  Window relevance supplies a two-sided physical
support sandwich, so the real-axis weight costs only the fixed degree width.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

private theorem arithmeticFunction_sum_apply_packetBound
    {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ u, F i) n = ∑ i ∈ u, F i n := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [ArithmeticFunction.zero_apply]
  | @insert a u ha ih => simp [ha, ih, ArithmeticFunction.add_apply]

/-- Every box meeting the physical prefix has support below the same fixed-degree enlargement
`2^(2k) X`; therefore so does their signed eligible aggregate. -/
theorem upperSupported_heathBrownWindowRelevantEligiblePacket
    (L X k : ℕ) (T0 t N : ℝ) :
    UpperSupported (heathBrownWindowRelevantEligiblePacket L X k T0 t N)
      (2 ^ (2 * k) * X) := by
  classical
  intro n hn
  rw [heathBrownWindowRelevantEligiblePacket,
    arithmeticFunction_sum_apply_packetBound] at hn
  by_contra hnmem
  apply hn
  apply Finset.sum_eq_zero
  intro box _hbox
  by_cases hbox : IsHeathBrownBoxEligible L X k T0 t box ∧
      IsHeathBrownBoxWindowRelevant N X k box
  · simp only [hbox]
    by_contra hterm
    have hlocal := upperSupported_heathBrownDyadicTermBox
      L X k box.m box.a box.b box.q n hterm
    have hm : box.m < k := box.1.isLt
    have hj : 1 ≤ k - box.m := Nat.sub_pos_of_lt hm
    have hlower : heathBrownDyadicCoreLower
        (k - box.m) box.a box.b box.q ≤ X := by
      rw [← groupedDyadicLower_heathBrownBoxFactorExponent_eq_coreLower]
      exact hbox.2.1
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

/-- Every nonzero coefficient of the window-relevant packet lies strictly above the common
physical lower edge `N / 2^(2k)`. -/
theorem lowerSupport_heathBrownWindowRelevantEligiblePacket
    (L X k : ℕ) (T0 t N : ℝ) {n : ℕ}
    (hn : complexCoeff
      (heathBrownWindowRelevantEligiblePacket L X k T0 t N) n ≠ 0) :
    N / (2 ^ (2 * k) : ℝ) < (n : ℝ) := by
  classical
  by_contra hnot
  have hnUpper : (n : ℝ) ≤ N / (2 ^ (2 * k) : ℝ) := le_of_not_gt hnot
  have hpacket :
      heathBrownWindowRelevantEligiblePacket L X k T0 t N n = 0 := by
    rw [heathBrownWindowRelevantEligiblePacket,
      arithmeticFunction_sum_apply_packetBound]
    apply Finset.sum_eq_zero
    intro box _hbox
    by_cases hbox : IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxWindowRelevant N X k box
    · simp only [hbox, if_true]
      apply vanishesBelow_heathBrownDyadicTermBox
      have hlower := windowRelevant_heathBrownBox_coreLower_gt hbox.2
      have hnReal : (n : ℝ) <
          (heathBrownDyadicCoreLower
            (k - box.m) box.a box.b box.q : ℝ) := by
        rw [← groupedDyadicLower_heathBrownBoxFactorExponent]
        exact hnUpper.trans_lt hlower
      exact_mod_cast hnReal
    · simp [hbox]
  apply hn
  simp [complexCoeff_apply, hpacket]

/-- One fixed divisor power controls every literal coefficient in the complete degree-`k`
window-relevant packet.  The only remaining multiplicity is the explicit box count. -/
theorem norm_complexCoeff_heathBrownWindowRelevantEligiblePacket_le
    (L X k : ℕ) (T0 t N : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ‖complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T0 t N) n‖ ≤
      (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
        ((2 ^ k : ℕ) : ℝ) *
          ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (n : ℝ)) := by
  classical
  have hdivNat : 1 ≤ n.divisors.card := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩)
  have hdiv : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by exact_mod_cast hdivNat
  have hterm : ∀ box : HeathBrownBoxChoice L X k,
      ‖(if IsHeathBrownBoxEligible L X k T0 t box ∧
            IsHeathBrownBoxWindowRelevant N X k box then
          heathBrownDyadicTermBox L X k box.m box.a box.b box.q
        else 0) n‖ ≤
        ((2 ^ k : ℕ) : ℝ) *
          ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (n : ℝ)) := by
    intro box
    by_cases hbox : IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxWindowRelevant N X k box
    · simp only [hbox, if_true]
      have hbase :=
        norm_complexCoeff_heathBrownDyadicTermBox_le_divisors_pow_mul_log
          L X k box.m box.a box.b box.q hn
      have hchooseNat : k.choose box.m ≤ 2 ^ k := Nat.choose_le_two_pow k box.m
      have hchoose : (k.choose box.m : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
        exact_mod_cast hchooseNat
      have hm : box.m < k := box.1.isLt
      have hexponent :
          (k - box.m) + (k - box.m - 1) + 2 ≤ 2 * k + 1 := by omega
      have hpow :
          (n.divisors.card : ℝ) ^
              ((k - box.m) + (k - box.m - 1) + 2) ≤
            (n.divisors.card : ℝ) ^ (2 * k + 1) :=
        pow_le_pow_right₀ hdiv hexponent
      have hlog : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hn)
      have hreal :
          ‖heathBrownDyadicTermBox L X k box.m box.a box.b box.q n‖ ≤
            ((2 ^ k : ℕ) : ℝ) *
              ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (n : ℝ)) := by
        have hbaseReal :
            ‖heathBrownDyadicTermBox L X k box.m box.a box.b box.q n‖ ≤
              (k.choose box.m : ℝ) *
                ((n.divisors.card : ℝ) ^
                    ((k - box.m) + (k - box.m - 1) + 2) *
                  Real.log (n : ℝ)) := by
          simpa [complexCoeff_apply, Complex.norm_real, Real.norm_eq_abs] using hbase
        exact hbaseReal.trans <| by
          exact mul_le_mul hchoose
            (mul_le_mul_of_nonneg_right hpow hlog)
            (mul_nonneg (pow_nonneg (by positivity) _) hlog)
            (by positivity)
      exact hreal
    · have hlog : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hn)
      simp [hbox, mul_nonneg (pow_nonneg (by positivity) _) hlog]
  rw [complexCoeff_apply, heathBrownWindowRelevantEligiblePacket,
    arithmeticFunction_sum_apply_packetBound, Complex.norm_real]
  calc
    ‖∑ box : HeathBrownBoxChoice L X k,
        (if IsHeathBrownBoxEligible L X k T0 t box ∧
              IsHeathBrownBoxWindowRelevant N X k box then
            heathBrownDyadicTermBox L X k box.m box.a box.b box.q
          else 0) n‖ ≤
        ∑ box : HeathBrownBoxChoice L X k,
          ‖(if IsHeathBrownBoxEligible L X k T0 t box ∧
                IsHeathBrownBoxWindowRelevant N X k box then
              heathBrownDyadicTermBox L X k box.m box.a box.b box.q
            else 0) n‖ := norm_sum_le _ _
    _ ≤ ∑ _box : HeathBrownBoxChoice L X k,
        (((2 ^ k : ℕ) : ℝ) *
          ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (n : ℝ))) := by
      exact Finset.sum_le_sum fun box _ => hterm box
    _ = (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
        ((2 ^ k : ℕ) : ℝ) *
          ((n.divisors.card : ℝ) ^ (2 * k + 1) * Real.log (n : ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Summing before estimating replaces the nonuniform `n^epsilon` loss by one explicit fixed
polylogarithm. -/
theorem sum_norm_complexCoeff_heathBrownWindowRelevantEligiblePacket_le_fixedPolylog
    (L X k : ℕ) (T0 t N : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 1 M,
        ‖complexCoeff
          (heathBrownWindowRelevantEligiblePacket L X k T0 t N) n‖ ≤
      (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
        ((2 ^ k : ℕ) : ℝ) * Real.log (M : ℝ) *
          ((M : ℝ) *
            (1 + Real.log (M : ℝ)) ^ (2 ^ (2 * k + 1) - 1)) := by
  have hlogM : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM)
  let C : ℝ := (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
    ((2 ^ k : ℕ) : ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hterm : ∀ n ∈ Finset.Icc 1 M,
      ‖complexCoeff
          (heathBrownWindowRelevantEligiblePacket L X k T0 t N) n‖ ≤
        C * Real.log (M : ℝ) *
          (n.divisors.card : ℝ) ^ (2 * k + 1) := by
    intro n hnmem
    have hnIcc := Finset.mem_Icc.mp hnmem
    have hcoeff :=
      norm_complexCoeff_heathBrownWindowRelevantEligiblePacket_le
        L X k T0 t N hnIcc.1
    have hlog : Real.log (n : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by exact_mod_cast hnIcc.1) (by exact_mod_cast hnIcc.2)
    have hdiv0 : 0 ≤ (n.divisors.card : ℝ) ^ (2 * k + 1) := by positivity
    dsimp only [C]
    calc
      ‖complexCoeff
          (heathBrownWindowRelevantEligiblePacket L X k T0 t N) n‖ ≤
          (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
            ((2 ^ k : ℕ) : ℝ) *
              ((n.divisors.card : ℝ) ^ (2 * k + 1) *
                Real.log (n : ℝ)) := hcoeff
      _ ≤ (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
            ((2 ^ k : ℕ) : ℝ) *
              ((n.divisors.card : ℝ) ^ (2 * k + 1) *
                Real.log (M : ℝ)) := by
          gcongr
      _ = (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
            ((2 ^ k : ℕ) : ℝ) * Real.log (M : ℝ) *
              (n.divisors.card : ℝ) ^ (2 * k + 1) := by ring
  have hmoment := sum_card_divisors_pow_le_polylog (2 * k + 1) M hM
  calc
    ∑ n ∈ Finset.Icc 1 M,
        ‖complexCoeff
          (heathBrownWindowRelevantEligiblePacket L X k T0 t N) n‖ ≤
        ∑ n ∈ Finset.Icc 1 M,
          C * Real.log (M : ℝ) *
            (n.divisors.card : ℝ) ^ (2 * k + 1) :=
      Finset.sum_le_sum hterm
    _ = C * Real.log (M : ℝ) *
        (∑ n ∈ Finset.Icc 1 M,
          (n.divisors.card : ℝ) ^ (2 * k + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ C * Real.log (M : ℝ) *
        ((M : ℝ) *
          (1 + Real.log (M : ℝ)) ^ (2 ^ (2 * k + 1) - 1)) :=
      mul_le_mul_of_nonneg_left hmoment (mul_nonneg hC hlogM)
    _ = _ := rfl

/-- Explicit fixed-polylogarithmic envelope for the window-relevant aggregate. -/
def heathBrownWindowRelevantFixedPolylogBound
    (L X k : ℕ) (N sigma : ℝ) : ℝ :=
  (N / (2 ^ (2 * k) : ℝ)) ^ (-sigma) *
    ((Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
      ((2 ^ k : ℕ) : ℝ) *
        Real.log ((2 ^ (2 * k) * X : ℕ) : ℝ) *
          (((2 ^ (2 * k) * X : ℕ) : ℝ) *
            (1 + Real.log ((2 ^ (2 * k) * X : ℕ) : ℝ)) ^
              (2 ^ (2 * k + 1) - 1)))

/-- Uniform low-ordinate bound for the actual window-relevant aggregate.  At `sigma = 1` and
`X` comparable to `N`, its power dependence cancels completely; only fixed polylogarithms and the
fixed degree-width remain. -/
theorem norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
    (L X k : ℕ) (hX : 1 ≤ X) (T0 t N sigma y : ℝ)
    (hN : 0 < N) (hsigma : 0 ≤ sigma) :
    ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
        ((sigma : ℂ) + (y : ℝ) * I)‖ ≤
      heathBrownWindowRelevantFixedPolylogBound L X k N sigma := by
  let F := heathBrownWindowRelevantEligiblePacket L X k T0 t N
  let M : ℕ := 2 ^ (2 * k) * X
  let D : ℝ := N / (2 ^ (2 * k) : ℝ)
  have hM : 1 ≤ M := by
    dsimp only [M]
    simpa only [one_mul] using
      Nat.mul_le_mul (Nat.one_le_two_pow) hX
  have hD : 0 < D := by dsimp only [D]; positivity
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hsupp : ∀ n : ℕ, complexCoeff F n ≠ 0 → n ∈ Finset.Icc 1 M := by
    intro n hn
    have hnF : F n ≠ 0 := by
      intro hzero
      apply hn
      simp [complexCoeff_apply, hzero]
    dsimp only [F] at hnF
    exact upperSupported_heathBrownWindowRelevantEligiblePacket L X k T0 t N n hnF
  have hweight : ∀ n ∈ Finset.Icc 1 M,
      ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) ≤
        D ^ (-sigma) * ‖complexCoeff F n‖ := by
    intro n hnmem
    by_cases hn : complexCoeff F n = 0
    · have hFn : F n = 0 := by
        rw [complexCoeff_apply] at hn
        exact Complex.ofReal_eq_zero.mp hn
      simp [hn, hFn]
    · have hlower := lowerSupport_heathBrownWindowRelevantEligiblePacket
          L X k T0 t N hn
      have hpow : (n : ℝ) ^ (-sigma) ≤ D ^ (-sigma) :=
        Real.rpow_le_rpow_of_nonpos hD hlower.le (by linarith)
      calc
        ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) ≤
            ‖complexCoeff F n‖ * D ^ (-sigma) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = D ^ (-sigma) * ‖complexCoeff F n‖ := by ring
  have hseries := norm_LSeries_le_sum_of_support hs0 hsupp sigma y
  rw [LSeries_heathBrownWindowRelevantEligiblePacket] at hseries
  calc
    ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
        ((sigma : ℂ) + (y : ℝ) * I)‖ ≤
        ∑ n ∈ Finset.Icc 1 M,
          ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) := hseries
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
          D ^ (-sigma) * ‖complexCoeff F n‖ :=
      Finset.sum_le_sum hweight
    _ = D ^ (-sigma) *
        (∑ n ∈ Finset.Icc 1 M, ‖complexCoeff F n‖) := by
      rw [Finset.mul_sum]
    _ ≤ D ^ (-sigma) *
        ((Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
          ((2 ^ k : ℕ) : ℝ) * Real.log (M : ℝ) *
            ((M : ℝ) *
              (1 + Real.log (M : ℝ)) ^ (2 ^ (2 * k + 1) - 1))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_norm_complexCoeff_heathBrownWindowRelevantEligiblePacket_le_fixedPolylog
          L X k T0 t N hM)
        (Real.rpow_nonneg hD.le _)
    _ = _ := rfl

end RHTower.Sieve

end
