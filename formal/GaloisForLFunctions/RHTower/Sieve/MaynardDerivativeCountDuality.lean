import GaloisForLFunctions.RHTower.Sieve.MaynardComplementaryMontgomeryScalar
import GaloisForLFunctions.RHTower.Sieve.MaynardWindowRelevantAggregate
import GaloisForLFunctions.RHTower.Sieve.MaynardLowOrdinateKuzminLandauAmplitude

/-!
# Derivative--count duality on the low-ordinate Route-T band

Converting the Kuzmin--Landau factor `T⁻¹` into a uniform length-amplitude deficit loses the
geometry at the single-giant seam.  Retaining that factor before applying a complementary
mean-square estimate produces two exponents

`-1 + 2 * tau * (1 - alpha) - s` and `-2 + 2 * tau * (1 - alpha)`,

where `tau` is total box length and `s` is complementary length, both in base `T`.  Above the
trivial-count threshold `mu * (1 - alpha) <= 1`, both exponents lie in Route T's first receiver.
Below it, cardinality at most height already lies in that receiver.  Thus the derivative saving
and trivial count meet at the exact boundary; the former giant seam is an artefact of converting
height saving to a fixed local amplitude before counting.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped zeta

/-- A physical-window-relevant box has total base-`T` logarithmic length at most `mu` whenever
the physical cutoff is at most `T^mu`.  This is the exact upper scale needed by the duality
exponents; no dyadic-width loss occurs. -/
theorem windowRelevant_heathBrownBox_totalExponent_le
    {L X k : ℕ} {T mu N0 : ℝ} (hT : 1 < T)
    (hXscale : (X : ℝ) <= T ^ mu) (box : HeathBrownBoxChoice L X k)
    (hbox : IsHeathBrownBoxWindowRelevant N0 X k box) :
    heathBrownBoxTotalExponent L X k T box <= mu := by
  let total : ℝ := heathBrownBoxTotalExponent L X k T box
  have hD :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) =
        T ^ total := by
    dsimp [total]
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT
        (heathBrownBoxFactorExponent box.a box.b box.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex k box.m)))
  have hpow : T ^ total <= T ^ mu := by
    rw [← hD]
    exact (windowRelevant_heathBrownBox_coreLower_le hbox).trans hXscale
  exact (Real.strictMono_rpow_of_base_gt_one hT).le_iff_le.mp hpow

/-- Exact logarithmic form of a height saving.  A bound `C T⁻¹ N^(1-c)` with
`C <= T^eps` subtracts `1-eps` from the factor's amplitude-times-height weight.  Unlike a fixed
length-amplitude conversion, this keeps the full additive `log T` gain. -/
theorem maynardAmplitude_mul_heightWeight_le_sub_of_height_saving
    {T N C V c eps w : ℝ}
    (hT : 1 < T) (hw : 1 <= w) (hN_eq : N = T ^ w)
    (hC : C <= T ^ eps) (hV : 0 < V)
    (hbound : V <= C / T * N ^ (1 - c)) :
    maynardAmplitude c N V * w <= w - (1 - eps) := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hTN : T <= N := by
    rw [hN_eq]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hT.le hw)
  have hN1 : 1 < N := hT.trans_le hTN
  have hN0 : 0 < N := lt_trans zero_lt_one hN1
  have hdiv : C / T <= T ^ eps / T :=
    div_le_div_of_nonneg_right hC hT0.le
  have hdivEq : T ^ eps / T = T ^ (eps - 1) := by
    calc
      T ^ eps / T = T ^ eps / T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (eps - 1) := (Real.rpow_sub hT0 _ _).symm
  have hupper : V <= T ^ (eps - 1) * N ^ (1 - c) := by
    calc
      V <= C / T * N ^ (1 - c) := hbound
      _ <= (T ^ eps / T) * N ^ (1 - c) :=
        mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg hN0.le _)
      _ = T ^ (eps - 1) * N ^ (1 - c) := by rw [hdivEq]
  have hlogUpper := Real.log_le_log hV hupper
  have hTpow : T ^ (eps - 1) ≠ 0 := (Real.rpow_pos_of_pos hT0 _).ne'
  have hNpow : N ^ (1 - c) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  rw [Real.log_mul hTpow hNpow, Real.log_rpow hT0,
    Real.log_rpow hN0] at hlogUpper
  have hlogN : Real.log N = w * Real.log T := by
    rw [hN_eq, Real.log_rpow hT0]
  have hampLog := maynardAmplitude_mul_log (c := c) (V := V) hN1
  have hscaled :
      (maynardAmplitude c N V * w) * Real.log T <=
        (w - (1 - eps)) * Real.log T := by
    rw [mul_assoc, ← hlogN, hampLog]
    rw [hlogN]
    rw [hlogN] at hlogUpper
    calc
      c * (w * Real.log T) + Real.log V <=
          c * (w * Real.log T) +
            ((eps - 1) * Real.log T + (1 - c) * (w * Real.log T)) :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_left hlogUpper (c * (w * Real.log T)))
      _ = (w - (1 - eps)) * Real.log T := by ring
  exact le_of_mul_le_mul_right hscaled (Real.log_pos hT)

/-- Full low-ordinate zeta law with the Kuzmin--Landau saving retained in exact height weight.
Every over-height atom subtracts `9/10` from the weighted amplitude sum, independently of its
length. -/
theorem eventually_maynard_lowOrdinate_overHeight_zeta_weighted_deficit :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 <= X → ∀ mu : ℝ, mu <= 8 → (X : ℝ) <= T ^ mu →
        ∀ q : ℕ, q <= Nat.log 2 X → ∀ c y : ℝ, 0 <= c → T <= y → y <= 2 * T →
          T <= ((2 ^ q : ℕ) : ℝ) →
          0 < ‖LSeries (complexCoeff
            (arithmeticDyadicBlock
              (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
                ((c : ℂ) + (y : ℂ) * Complex.I)‖ →
          maynardAmplitude c (((2 ^ q : ℕ) : ℝ))
              ‖LSeries (complexCoeff
                (arithmeticDyadicBlock
                  (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
                    ((c : ℂ) + (y : ℂ) * Complex.I)‖ *
              dyadicLogExponent T q <=
            dyadicLogExponent T q - 9 / 10 := by
  filter_upwards [eventually_maynardLowOrdinateKuzminLandau_polylog_absorbed] with T hready
  intro X hX mu hmu hXscale q hq c y hc hylo hyhi hTN hV
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let C : ℝ := 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X
  let w : ℝ := dyadicLogExponent T q
  have hr := rpow_dyadicLogExponent hready.1 q
  have hNeq : N = T ^ w := by simpa [N, w] using hr.symm
  have hw : 1 <= w := by
    apply (Real.strictMono_rpow_of_base_gt_one hready.1).le_iff_le.mp
    rw [Real.rpow_one, ← hNeq]
    exact hTN
  have hraw := norm_LSeries_zetaDyadicBlock_le_over_height
    hX hq (lt_trans zero_lt_one hready.1) hc hylo hyhi hTN
  have hE : 1 <= maynardLongPolylogEnvelope X :=
    one_le_maynardLongPolylogEnvelope X
  have hbaseC : 6 * Real.pi + 1 <= C := by
    dsimp [C]
    nlinarith [Real.pi_pos]
  have hbound :
      ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
          ((c : ℂ) + (y : ℂ) * Complex.I)‖ <=
        C / T * N ^ (1 - c) := by
    simpa [N] using hraw.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hbaseC
        (lt_trans zero_lt_one hready.1).le)
      (Real.rpow_nonneg (by positivity : 0 <= N) _))
  have hweighted := maynardAmplitude_mul_heightWeight_le_sub_of_height_saving
    hready.1 hw hNeq (hready.2 X hX mu hmu hXscale) hV hbound
  norm_num at hweighted ⊢
  simpa [N, w] using hweighted

/-- Full low-ordinate logarithmic-factor law in the same exact height-weighted form. -/
theorem eventually_maynard_lowOrdinate_overHeight_log_weighted_deficit :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 <= X → ∀ mu : ℝ, mu <= 8 → (X : ℝ) <= T ^ mu →
        ∀ q : ℕ, q <= Nat.log 2 X → ∀ c y : ℝ, 0 <= c → T <= y → y <= 2 * T →
          T <= ((2 ^ q : ℕ) : ℝ) →
          0 < ‖LSeries (complexCoeff
            (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
              ((c : ℂ) + (y : ℂ) * Complex.I)‖ →
          maynardAmplitude c (((2 ^ q : ℕ) : ℝ))
              ‖LSeries (complexCoeff
                (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
                  ((c : ℂ) + (y : ℂ) * Complex.I)‖ *
              dyadicLogExponent T q <=
            dyadicLogExponent T q - 9 / 10 := by
  filter_upwards [eventually_maynardLowOrdinateKuzminLandau_polylog_absorbed] with T hready
  intro X hX mu hmu hXscale q hq c y hc hylo hyhi hTN hV
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let C : ℝ := 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X
  let w : ℝ := dyadicLogExponent T q
  have hr := rpow_dyadicLogExponent hready.1 q
  have hNeq : N = T ^ w := by simpa [N, w] using hr.symm
  have hw : 1 <= w := by
    apply (Real.strictMono_rpow_of_base_gt_one hready.1).le_iff_le.mp
    rw [Real.rpow_one, ← hNeq]
    exact hTN
  have hbound := norm_LSeries_logDyadicBlock_le_over_height
    hX hq (lt_trans zero_lt_one hready.1) hc hylo hyhi hTN
  have hweighted := maynardAmplitude_mul_heightWeight_le_sub_of_height_saving
    hready.1 hw hNeq (hready.2 X hX mu hmu hXscale) hV (by
      simpa [C, N] using hbound)
  norm_num at hweighted ⊢
  simpa [N, w] using hweighted

/-- Additive-height version of the sub-height mass principle.  If every over-height atom removes
the same amount `eta` from amplitude-times-height weight, failure of the requested sub-height mass
produces at least one such atom and hence the full additive penalty `eta`. -/
theorem subHeight_mass_ge_of_additive_height_penalty
    {ι : Type*} [Fintype ι]
    (w a slack : ι → ℝ) {t eta E alpha mu : ℝ}
    (ht : 0 < t) (hmu : 0 < mu) (hetaE : E < eta)
    (hw : ∀ i, 0 <= w i)
    (htotalLo : t <= ∑ i, w i) (htotalHi : ∑ i, w i <= mu)
    (hslack : ∀ i, 0 <= slack i)
    (hall : ∀ i, a i <= 1 + slack i)
    (hover : ∀ i, 1 <= w i → a i * w i <= w i - eta)
    (hslackMass : ∑ i, slack i * w i <= E)
    (hglobal : alpha * ∑ i, w i <= ∑ i, a i * w i)
    (halpha : 1 - (eta - E) / mu < alpha) :
    t <= ∑ i ∈ (Finset.univ.filter fun i => w i < 1), w i := by
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
  have hwj : 1 <= w j := le_of_not_gt (by
    simpa [high] using (Finset.mem_filter.mp hj).2)
  have hjpenalty : a j * w j <= w j - eta := hover j hwj
  have hterm : ∀ i, a i * w i <=
      w i + slack i * w i - (if i = j then eta else 0) := by
    intro i
    by_cases hij : i = j
    · subst i
      simp only [ite_true]
      have hslackTerm : 0 <= slack j * w j :=
        mul_nonneg (hslack j) (hw j)
      linarith
    · simp only [if_neg hij, sub_zero]
      calc
        a i * w i <= (1 + slack i) * w i :=
          mul_le_mul_of_nonneg_right (hall i) (hw i)
        _ = w i + slack i * w i := by ring
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  have hpenalty : ∑ i, (if i = j then eta else 0) = eta := by simp
  have hupper : ∑ i, a i * w i <= ∑ i, w i + E - eta := by
    calc
      ∑ i, a i * w i <=
          (∑ i, w i) + (∑ i, slack i * w i) -
            ∑ i, (if i = j then eta else 0) := by
        simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib] using hsum
      _ <= ∑ i, w i + E - eta := by rw [hpenalty]; linarith
  have hdeficit : eta - E <= (1 - alpha) * ∑ i, w i := by
    linarith
  have htotalPos : 0 < ∑ i, w i := ht.trans_le htotalLo
  have halphaOne : alpha < 1 := by
    nlinarith
  have hscaled : (1 - alpha) * ∑ i, w i <= (1 - alpha) * mu :=
    mul_le_mul_of_nonneg_left htotalHi (by linarith)
  have hratio : 1 - alpha < (eta - E) / mu := by linarith
  have hstrict : (1 - alpha) * mu < eta - E :=
    (lt_div_iff₀ hmu).mp hratio
  linarith

/-- Literal positive-length Heath--Brown box form of the additive height-penalty principle. -/
theorem maynard_heathBrownBox_subHeight_mass_of_additive_height_penalty
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (hL : 1 <= L) (hX : 1 <= X)
    {T t c y alpha eta E mu : ℝ}
    (hT : 1 < T) (ht : 0 < t) (hmu : 0 < mu) (hetaE : E < eta)
    (hc : 0 <= c)
    (htotalLo : t <= ∑ i : PositiveHeathBrownBoxFactorIndex box,
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i))
    (htotalHi : (∑ i : PositiveHeathBrownBoxFactorIndex box,
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) <= mu)
    (hover : ∀ i : PositiveHeathBrownBoxFactorIndex box,
      1 <= dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) →
      maynardAmplitude c
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))
          ‖heathBrownBoxFactorValue L X k box
              ((c : ℂ) + (y : ℝ) * Complex.I) i‖ *
            dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) <=
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i) - eta)
    (hslackMass :
      ∑ i : HeathBrownBoxFactorIndex k box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) <=
        E * Real.log T)
    (hlarge :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
          (alpha - c) <=
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖)
    (halpha : 1 - (eta - E) / mu < alpha) :
    t <= ∑ i ∈ (Finset.univ.filter
        fun i : PositiveHeathBrownBoxFactorIndex box =>
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) < 1),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) := by
  classical
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  have hlog : 1 <= box.q :=
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
  have hw : ∀ i, 0 <= w i := fun i => dyadicLogExponent_nonneg hT (q i)
  have hslack : ∀ i, 0 <= slack i := by
    intro i
    exact heathBrownFactorAmplitudeSlack_nonneg (kind i) i.property
  have hall : ∀ i, a i <= 1 + slack i := by
    intro i
    exact maynard_heathBrownFactor_amplitude_le_one_add_slack
      L X (q i) (kind i) hc i.property (hW i)
  have hover' : ∀ i, 1 <= w i → a i * w i <= w i - eta := by
    intro i hi
    simpa [a, w, N, W, Z, q, s] using hover i (by simpa [w, q] using hi)
  have hlogNw : ∀ i, Real.log (N i) = w i * Real.log T := by
    intro i
    have hr := rpow_dyadicLogExponent hT (q i)
    calc
      Real.log (N i) = Real.log (T ^ dyadicLogExponent T (q i)) := by rw [hr]
      _ = dyadicLogExponent T (q i) * Real.log T := by
        rw [Real.log_rpow (by linarith)]
      _ = w i * Real.log T := by rfl
  have hslackScaled :
      (∑ i, slack i * w i) * Real.log T <= E * Real.log T := by
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
      _ <= E * Real.log T := hslackMass
  have hslackMass' : ∑ i, slack i * w i <= E :=
    le_of_mul_le_mul_right hslackScaled (Real.log_pos hT)
  have hweighted := maynardGlobalAmplitude_weighted_mean (c := c) N W hN hW rfl rfl
  have hNprodOne : 1 < ∏ i, N i := by
    calc
      1 = ∏ _i : I, (1 : ℝ) := by simp
      _ < ∏ i, N i := Finset.prod_lt_prod_of_nonempty
        (fun _i _hi => by norm_num) (fun i _hi => hN i) Finset.univ_nonempty
  have hglobalAmp : alpha <= maynardGlobalAmplitude c (∏ i, N i) (∏ i, W i) := by
    apply le_maynardAmplitude_of_rpow_le
    · exact hNprodOne
    · rw [hNprod, hWprod]
      simpa [s] using hlarge
  have hglobalLog :
      alpha * Real.log (∏ i, N i) <= ∑ i, a i * Real.log (N i) := by
    have hmul := mul_le_mul_of_nonneg_right hglobalAmp
      (Real.log_nonneg hNprodOne.le)
    rw [hweighted] at hmul
    simpa [a] using hmul
  have hlogTotal : Real.log (∏ i, N i) = (∑ i, w i) * Real.log T := by
    rw [Real.log_prod (fun i _ => ne_of_gt (lt_trans zero_lt_one (hN i)))]
    simp_rw [hlogNw]
    rw [Finset.sum_mul]
  have hglobalScaled :
      (alpha * ∑ i, w i) * Real.log T <=
        (∑ i, a i * w i) * Real.log T := by
    calc
      (alpha * ∑ i, w i) * Real.log T =
          alpha * Real.log (∏ i, N i) := by rw [hlogTotal]; ring
      _ <= ∑ i, a i * Real.log (N i) := hglobalLog
      _ = (∑ i, a i * w i) * Real.log T := by
        simp_rw [hlogNw]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hglobal : alpha * ∑ i, w i <= ∑ i, a i * w i :=
    le_of_mul_le_mul_right hglobalScaled (Real.log_pos hT)
  have hmass := subHeight_mass_ge_of_additive_height_penalty
    w a slack ht hmu hetaE hw (by simpa [w, q] using htotalLo)
      (by simpa [w, q] using htotalHi) hslack hall hover'
      hslackMass' hglobal halpha
  simpa [w, q, I] using hmass

/-- `log(12 log T)` is eventually below every fixed positive fraction of `log T`. -/
theorem eventually_log_twelve_mul_log_le {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.log (12 * Real.log T) <= eps * Real.log T := by
  have hU : Filter.Tendsto (fun T : ℝ => 12 * Real.log T)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) Real.tendsto_log_atTop
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto hU).def
    (show 0 < eps / 12 by positivity)
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 0] with T hs hlog
  have hU0 : 0 <= 12 * Real.log T := mul_nonneg (by norm_num) hlog
  change |Real.log (12 * Real.log T)| <= (eps / 12) * |12 * Real.log T| at hs
  rw [abs_of_nonneg hU0] at hs
  calc
    Real.log (12 * Real.log T) <= |Real.log (12 * Real.log T)| := le_abs_self _
    _ <= (eps / 12) * (12 * Real.log T) := hs
    _ = eps * Real.log T := by ring

/-- Low-ordinate analogue of the logarithmic slack estimate, uniform for `X <= T^mu`,
`mu <= 8`. -/
theorem eventually_log_maynardLongPolylogEnvelope_le_lowOrdinate
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 <= X → ∀ mu : ℝ, mu <= 8 → (X : ℝ) <= T ^ mu →
        Real.log (maynardLongPolylogEnvelope X) <= eps * Real.log T := by
  filter_upwards [eventually_log_twelve_mul_log_le heps,
    Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hsmall hT hlogT
  intro X hX mu hmu hXscale
  have hE := maynardLongPolylogEnvelope_le_twelve_log_of_mu_le_eight
    hX hT hlogT hmu hXscale
  have hEpos : 0 < maynardLongPolylogEnvelope X :=
    lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X)
  have hlogE : Real.log (maynardLongPolylogEnvelope X) <=
      Real.log (12 * Real.log T) := Real.log_le_log hEpos hE
  exact hlogE.trans hsmall

/-- Complete literal-box logarithmic slack remains `o(log T)` throughout the full low-ordinate
band. -/
theorem eventually_sum_heathBrownBoxFactorAmplitudeSlack_mul_log_le_lowOrdinate
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 <= X → ∀ mu : ℝ, mu <= 8 → (X : ℝ) <= T ^ mu →
        ∀ L k : ℕ, ∀ box : HeathBrownBoxChoice L X k, 1 <= box.q →
          ∑ i : HeathBrownBoxFactorIndex k box.m,
              heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
                (heathBrownBoxFactorExponent box.a box.b box.q i) *
                Real.log
                  (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) <=
            eps * Real.log T := by
  filter_upwards [eventually_log_maynardLongPolylogEnvelope_le_lowOrdinate heps] with T hT
  intro X hX mu hmu hXscale L k box hq
  rw [sum_heathBrownBoxFactorAmplitudeSlack_mul_log box.a box.b hq]
  exact (log_heathBrown_log_trivialConstant_le_log_polylogEnvelope box hX hq).trans
    (hT X hX mu hmu hXscale)

/-- Full low-ordinate literal-box sub-height selection above the exact additive-height boundary.
The old uniform `9/80` local deficit is not used: one over-height zeta/log atom contributes the
full `9/10` height penalty, while the logarithmic atom's total slack costs only `1/100`. -/
theorem eventually_maynard_lowOrdinate_box_subHeight_mass_of_high_amplitude :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 <= X → ∀ mu : ℝ, 4 / 3 <= mu → mu <= 8 →
        (X : ℝ) <= T ^ mu →
        ∀ L : ℕ, 1 <= L →
        ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          IsHeathBrownBoxWindowRelevant (X / (2 ^ 120 : ℝ)) X 60 box →
          (∀ i : HeathBrownBoxFactorIndex 60 box.m,
            heathBrownBoxFactorKind 60 box.m i = .moebius →
              dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q i) <=
                  2 * (mu / 120)) →
          ∀ c y alpha : ℝ, 0 <= c → T <= y → y <= 2 * T →
          1 - (89 / 100 : ℝ) / mu < alpha →
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
              (alpha - c) <=
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
          mu / 120 <= ∑ i ∈ (Finset.univ.filter
              fun i : PositiveHeathBrownBoxFactorIndex box =>
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) < 1),
            dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) := by
  filter_upwards [eventually_maynard_lowOrdinate_overHeight_zeta_weighted_deficit,
    eventually_maynard_lowOrdinate_overHeight_log_weighted_deficit,
    eventually_sum_heathBrownBoxFactorAmplitudeSlack_mul_log_le_lowOrdinate
      (by norm_num : (0 : ℝ) < 1 / 100),
    Filter.eventually_gt_atTop (1 : ℝ)] with T hzeta hlogFactor hslack hT
  intro X hX mu hmuLo hmuHi hXscale L hL box helig hwindow hmobius
    c y alpha hc hylo hyhi halpha hlarge
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  have hqlog : 1 <= box.q :=
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
      1 <= dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) →
      maynardAmplitude c
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))
          ‖heathBrownBoxFactorValue L X 60 box s i‖ *
            dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) <=
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i) - 9 / 10 := by
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
    have hTN : T <= (((2 ^ qi : ℕ) : ℝ)) := by
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
  have htotalLo : mu / 120 <=
      ∑ i : PositiveHeathBrownBoxFactorIndex box,
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i) := by
    rw [sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent box]
    simpa [IsHeathBrownBoxEligible] using helig
  have htotalHi :
      (∑ i : PositiveHeathBrownBoxFactorIndex box,
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i)) <= mu := by
    rw [sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent box]
    exact windowRelevant_heathBrownBox_totalExponent_le hT hXscale box hwindow
  have hslackMass := hslack X hX mu hmuHi hXscale L 60 box hqlog
  apply maynard_heathBrownBox_subHeight_mass_of_additive_height_penalty
    (eta := (9 / 10 : ℝ)) (E := (1 / 100 : ℝ)) (mu := mu)
    box hL hX hT (by linarith : 0 < mu / 120) (by linarith : 0 < mu)
      (by norm_num : (1 / 100 : ℝ) < 9 / 10) hc htotalLo htotalHi
      (by simpa [s] using hover) hslackMass hlarge
  norm_num at halpha ⊢
  exact halpha

/-- Height-dominated term after excising one Kuzmin--Landau factor and applying one complementary
mean square. -/
def maynardDerivativeComplementHeightExponent
    (tau alpha s : ℝ) : ℝ :=
  -1 + 2 * tau * (1 - alpha) - s

/-- Length-dominated term after the same derivative-factor excision. -/
def maynardDerivativeComplementLengthExponent
    (tau alpha : ℝ) : ℝ :=
  -2 + 2 * tau * (1 - alpha)

/-- Above the trivial-count boundary, the height-dominated complementary term is already inside
the first Maynard receiver. -/
theorem derivativeComplementHeight_le_first_of_supertrivial
    {mu tau alpha s : ℝ}
    (halpha : alpha <= 1) (htau : tau <= mu) (hs : 0 <= s)
    (hthreshold : mu * (1 - alpha) <= 1) :
    maynardDerivativeComplementHeightExponent tau alpha s <=
      mu * (1 - alpha) := by
  have hdelta : 0 <= 1 - alpha := by linarith
  have htaudelta : tau * (1 - alpha) <= mu * (1 - alpha) :=
    mul_le_mul_of_nonneg_right htau hdelta
  dsimp only [maynardDerivativeComplementHeightExponent]
  linarith

/-- Above the trivial-count boundary, the length-dominated complementary term is also inside the
first Maynard receiver. -/
theorem derivativeComplementLength_le_first_of_supertrivial
    {mu tau alpha : ℝ}
    (halpha : alpha <= 1) (htau : tau <= mu)
    (hthreshold : mu * (1 - alpha) <= 1) :
    maynardDerivativeComplementLengthExponent tau alpha <=
      mu * (1 - alpha) := by
  have hdelta : 0 <= 1 - alpha := by linarith
  have htaudelta : tau * (1 - alpha) <= mu * (1 - alpha) :=
    mul_le_mul_of_nonneg_right htau hdelta
  dsimp only [maynardDerivativeComplementLengthExponent]
  linarith

/-- Exact exponent-level closure of both terms generated by derivative-factor excision. -/
theorem derivativeComplement_exponents_le_first_of_supertrivial
    {mu tau alpha s : ℝ}
    (halpha : alpha <= 1) (htau : tau <= mu) (hs : 0 <= s)
    (hthreshold : mu * (1 - alpha) <= 1) :
    maynardDerivativeComplementHeightExponent tau alpha s <=
        mu * (1 - alpha) /\
      maynardDerivativeComplementLengthExponent tau alpha <=
        mu * (1 - alpha) := by
  exact ⟨derivativeComplementHeight_le_first_of_supertrivial
      halpha htau hs hthreshold,
    derivativeComplementLength_le_first_of_supertrivial
      halpha htau hthreshold⟩

/-- Below the derivative-count branch, literal cardinality at most height is exactly the first
Maynard alternative. -/
theorem routeT_trivial_cardinality_first_of_subtrivial
    {R T mu alpha : ℝ}
    (hT : 1 <= T) (hR : R <= T)
    (hthreshold : 1 <= mu * (1 - alpha)) :
    R <= T ^ (mu * (1 - alpha)) := by
  have hpow : T <= T ^ (mu * (1 - alpha)) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hT hthreshold)
  exact hR.trans hpow

/-- Complete scalar dichotomy.  There is no uncovered amplitude strip: trivial cardinality and
derivative--complement counting meet at `mu * (1 - alpha) = 1`. -/
theorem routeT_trivial_or_derivativeComplement_first
    {mu tau alpha s : ℝ}
    (halpha : alpha <= 1) (htau : tau <= mu) (hs : 0 <= s) :
    1 <= mu * (1 - alpha) \/
      (maynardDerivativeComplementHeightExponent tau alpha s <=
          mu * (1 - alpha) /\
        maynardDerivativeComplementLengthExponent tau alpha <=
          mu * (1 - alpha)) := by
  by_cases hthreshold : 1 <= mu * (1 - alpha)
  · exact Or.inl hthreshold
  · exact Or.inr (derivativeComplement_exponents_le_first_of_supertrivial
      halpha htau hs (le_of_not_ge hthreshold))

/-- On the full low-ordinate Perron range every Möbius atom is strictly below height.  The
degree-60 cutoff has exponent `mu / 60`, while `mu <= 8`; hence an over-height giant can only be a
zeta or logarithmic atom. -/
theorem lowOrdinate_moebius_factor_strictly_subHeight
    {L X k : ℕ} {T t mu : ℝ} (box : HeathBrownBoxChoice L X k)
    (hT : 1 < T) (hL : 1 <= L) (hcut : (L : ℝ) <= T ^ (2 * t))
    (hmu : mu <= 8) (ht : t = mu / 120)
    (i : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m i = .moebius) :
    dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) < 1 := by
  have hshort := box.moebius_factor_dyadicLogExponent_le
    hT hL hcut i hkind
  rw [ht] at hshort
  linarith

/-- Exact kind classification for a low-ordinate over-height atom.  No analytic estimate enters:
it follows only from the Heath--Brown cutoff geometry. -/
theorem lowOrdinate_factorKind_eq_zeta_or_log_of_overHeight
    {L X k : ℕ} {T t mu : ℝ} (box : HeathBrownBoxChoice L X k)
    (hT : 1 < T) (hL : 1 <= L) (hcut : (L : ℝ) <= T ^ (2 * t))
    (hmu : mu <= 8) (ht : t = mu / 120)
    (i : HeathBrownBoxFactorIndex k box.m)
    (hlong : 1 <= dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q i)) :
    heathBrownBoxFactorKind k box.m i = .zeta ∨
      heathBrownBoxFactorKind k box.m i = .log := by
  cases hkind : heathBrownBoxFactorKind k box.m i with
  | moebius =>
      have hshort := lowOrdinate_moebius_factor_strictly_subHeight
        box hT hL hcut hmu ht i hkind
      exact (not_lt_of_ge hlong hshort).elim
  | zeta => exact Or.inl rfl
  | log => exact Or.inr rfl

/-- **Conditional low-ordinate reserve away from the giant seam.**  Here `s` is the logarithmic
length of the *complement*, not the excised factor.  If that complement itself has at least one
full height of mass, both derivative--complement terms lie `2/25` inside the first receiver
throughout the amplitude band `alpha >= 19/25`.  The endpoint is sharp for this argument:
`8 * (1 - 19/25) = 48/25`, leaving `2 - 48/25 = 2/25`.

The single-giant seam instead has complement mass below height, so its hypotheses do not supply
`s >= 1`; see `not_giantSeam_implies_twoTwentyFifth_heightReserve`. -/
theorem lowOrdinate_derivativeComplement_exponents_le_first_sub_reserve
    {mu tau alpha s : ℝ}
    (hmuHi : mu <= 8)
    (halphaLo : 19 / 25 <= alpha) (halphaHi : alpha <= 1)
    (htau : tau <= mu) (hs : 1 <= s) :
    maynardDerivativeComplementHeightExponent tau alpha s <=
        mu * (1 - alpha) - 2 / 25 /\
      maynardDerivativeComplementLengthExponent tau alpha <=
        mu * (1 - alpha) - 2 / 25 := by
  have hdelta0 : 0 <= 1 - alpha := by linarith
  have hdeltaHi : 1 - alpha <= 6 / 25 := by linarith
  have htaudelta : tau * (1 - alpha) <= mu * (1 - alpha) :=
    mul_le_mul_of_nonneg_right htau hdelta0
  have hmudelta : mu * (1 - alpha) <= 8 * (6 / 25 : ℝ) :=
    mul_le_mul hmuHi hdeltaHi hdelta0 (by norm_num)
  constructor <;>
    dsimp only [maynardDerivativeComplementHeightExponent,
      maynardDerivativeComplementLengthExponent] <;> linarith

/-- Receiver form of the seam reserve.  Any literal analytic argument which produces the two
canonical derivative--complement powers may keep an arbitrary common cost `Q`; both powers are
simultaneously dominated before that cost is absorbed. -/
theorem lowOrdinate_derivativeComplement_count_le_first_sub_reserve
    {R Q T mu tau alpha s : ℝ}
    (hT : 1 <= T) (hQ : 0 <= Q)
    (hmuHi : mu <= 8)
    (halphaLo : 19 / 25 <= alpha) (halphaHi : alpha <= 1)
    (htau : tau <= mu) (hs : 1 <= s)
    (hcount : R <= Q *
      (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
        T ^ maynardDerivativeComplementLengthExponent tau alpha)) :
    R <= (2 * Q) * T ^ (mu * (1 - alpha) - 2 / 25) := by
  obtain ⟨hheight, hlength⟩ :=
    lowOrdinate_derivativeComplement_exponents_le_first_sub_reserve
      hmuHi halphaLo halphaHi htau hs
  have hheightPow := Real.rpow_le_rpow_of_exponent_le hT hheight
  have hlengthPow := Real.rpow_le_rpow_of_exponent_le hT hlength
  calc
    R <= Q *
        (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
          T ^ maynardDerivativeComplementLengthExponent tau alpha) := hcount
    _ <= Q *
        (T ^ (mu * (1 - alpha) - 2 / 25) +
          T ^ (mu * (1 - alpha) - 2 / 25)) := by gcongr
    _ = (2 * Q) * T ^ (mu * (1 - alpha) - 2 / 25) := by ring

/-- After one fixed-polylog absorption, the low-ordinate derivative branch enters the normalized
first receiver with a still-strict `1/25` power margin.  This is the exact boundary statement
needed by `IsRouteTMaynardTwoAlternative`; no equality case survives. -/
theorem lowOrdinate_derivativeComplement_normalized_first
    {R Q T mu tau alpha s : ℝ} {q : ℕ}
    (hT : 1 <= T) (hQ : 0 <= Q)
    (hmuHi : mu <= 8)
    (halphaLo : 19 / 25 <= alpha) (halphaHi : alpha <= 1)
    (htau : tau <= mu) (hs : 1 <= s)
    (hcount : R <= Q *
      (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
        T ^ maynardDerivativeComplementLengthExponent tau alpha))
    (hcost : (2 * Q) * (Real.log T) ^ q <= T ^ (1 / 25 : ℝ)) :
    R * (Real.log T) ^ q <=
      T ^ (mu * (1 - alpha) - 1 / 25) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog0 : 0 <= Real.log T := Real.log_nonneg hT
  have hraw := lowOrdinate_derivativeComplement_count_le_first_sub_reserve
    hT hQ hmuHi halphaLo halphaHi htau hs hcount
  have hpow0 : 0 <= T ^ (mu * (1 - alpha) - 2 / 25) :=
    Real.rpow_nonneg hT0.le _
  calc
    R * (Real.log T) ^ q <=
        ((2 * Q) * T ^ (mu * (1 - alpha) - 2 / 25)) *
          (Real.log T) ^ q :=
      mul_le_mul_of_nonneg_right hraw (pow_nonneg hlog0 q)
    _ = ((2 * Q) * (Real.log T) ^ q) *
        T ^ (mu * (1 - alpha) - 2 / 25) := by ring
    _ <= T ^ (1 / 25 : ℝ) *
        T ^ (mu * (1 - alpha) - 2 / 25) :=
      mul_le_mul_of_nonneg_right hcost hpow0
    _ = T ^ (mu * (1 - alpha) - 1 / 25) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring

/-- **Exact moving reserve.**  Without a lower bound on complement mass, the height term retains
precisely the available boundary distance `1 - mu*(1-alpha)` plus complement mass `s`.  This is
the correct invariant for the single-giant seam. -/
theorem derivativeComplementHeight_le_first_sub_movingReserve
    {mu tau alpha s : ℝ}
    (halpha : alpha <= 1) (htau : tau <= mu) :
    maynardDerivativeComplementHeightExponent tau alpha s <=
      mu * (1 - alpha) - (1 - mu * (1 - alpha) + s) := by
  have hdelta : 0 <= 1 - alpha := by linarith
  have hmul : tau * (1 - alpha) <= mu * (1 - alpha) :=
    mul_le_mul_of_nonneg_right htau hdelta
  dsimp only [maynardDerivativeComplementHeightExponent]
  linarith

/-- **Zero-reserve rigidity.**  In the derivative branch, equality with the first receiver can
occur only at simultaneous scale saturation, exact trivial-count boundary, and zero complement
mass.  Hence every nondegenerate complement has a strict (possibly moving) power reserve. -/
theorem derivativeComplementHeight_eq_first_boundary_rigidity
    {mu tau alpha s : ℝ}
    (halpha : alpha <= 1) (htau : tau <= mu) (hs : 0 <= s)
    (hthreshold : mu * (1 - alpha) <= 1)
    (heq : maynardDerivativeComplementHeightExponent tau alpha s =
      mu * (1 - alpha)) :
    mu * (1 - alpha) = 1 ∧ s = 0 ∧ tau * (1 - alpha) = 1 := by
  have hdelta : 0 <= 1 - alpha := by linarith
  have hmul : tau * (1 - alpha) <= mu * (1 - alpha) :=
    mul_le_mul_of_nonneg_right htau hdelta
  dsimp only [maynardDerivativeComplementHeightExponent] at heq
  constructor
  · linarith
  constructor <;> linarith

/-- The three boundary equalities are also sufficient for zero reserve. -/
theorem derivativeComplementHeight_eq_first_of_boundary
    {mu tau alpha s : ℝ}
    (hmu : mu * (1 - alpha) = 1) (hs : s = 0)
    (htau : tau * (1 - alpha) = 1) :
    maynardDerivativeComplementHeightExponent tau alpha s =
      mu * (1 - alpha) := by
  dsimp only [maynardDerivativeComplementHeightExponent]
  linarith

/-- **Closed falsifier for the former C53 inference.**  Single-giant geometry (`r>1`, complement
`0<=s<1`) does not imply a uniform `2/25` height reserve.  At the fully admissible scalar point
`mu=tau=r=5`, `alpha=4/5`, `s=0`, the derivative height exponent equals the first receiver
exactly.  Thus over-height type rigidity cannot pay fixed polylogarithms by itself. -/
theorem not_giantSeam_implies_twoTwentyFifth_heightReserve :
    ¬ ∀ mu tau alpha r s : ℝ,
      19 / 9 < mu → mu <= 8 →
      19 / 25 <= alpha → alpha <= 997 / 1000 →
      tau <= mu → tau = r + s → 1 < r → 0 <= s → s < 1 →
      maynardDerivativeComplementHeightExponent tau alpha s <=
        mu * (1 - alpha) - 2 / 25 := by
  intro h
  have hbad := h 5 5 (4 / 5) 5 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [maynardDerivativeComplementHeightExponent] at hbad

/-- Exact scalar excision of a pointwise derivative-bounded factor.  The factor's `T⁻¹` saving
appears as `T / C` in the complementary product threshold and is not weakened to a fixed local
amplitude deficit. -/
theorem derivativeFactor_excision
    {D N T C W R c alpha : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hC : 0 < C) (hR : 0 <= R)
    (hlong : W <= C / T * N ^ (1 - c))
    (hlarge : D ^ (alpha - c) <= W * R) :
    (T / C) * D ^ (alpha - c) * N ^ (c - 1) <= R := by
  have hNpow : 0 < N ^ (1 - c) := Real.rpow_pos_of_pos hN _
  have hNinv : 0 < N ^ (c - 1) := Real.rpow_pos_of_pos hN _
  have hTC : 0 < T / C := div_pos hT hC
  have hlong' : W <= (C / T) * N ^ (1 - c) := by simpa using hlong
  have hscaled := mul_le_mul_of_nonneg_right hlarge hTC.le
  have hupper := mul_le_mul_of_nonneg_right hlong' hR
  have hchain : (T / C) * D ^ (alpha - c) <= N ^ (1 - c) * R := by
    calc
      (T / C) * D ^ (alpha - c) <= (T / C) * (W * R) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
      _ <= (T / C) * ((C / T * N ^ (1 - c)) * R) := by
        exact mul_le_mul_of_nonneg_left hupper hTC.le
      _ = N ^ (1 - c) * R := by
        field_simp [hT.ne', hC.ne']
  have hscaledInv := mul_le_mul_of_nonneg_right hchain hNinv.le
  calc
    (T / C) * D ^ (alpha - c) * N ^ (c - 1) <=
        (N ^ (1 - c) * R) * N ^ (c - 1) := by
      simpa [mul_assoc] using hscaledInv
    _ = (N ^ (1 - c) * N ^ (c - 1)) * R := by ring
    _ = R := by
      rw [← Real.rpow_add hN]
      simp

/-- Literal finite-set composition of derivative-factor excision with Montgomery mean square for
the complementary Heath--Brown product.  This theorem retains every analytic constant and the
full `T0 / C` gain; no amplitude coloring or fixed-deficit conversion intervenes. -/
theorem derivativeExcised_montgomery_heathBrown_grouped_finset
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {c G : ℝ} (hc : 0 <= c)
    (henergy : ∑ j : Fin (groupedDyadicUpper q),
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 <= G)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta H : ℝ}
    (hdelta : 0 < delta) (hH : 0 <= H)
    (hgap : ∀ i, lam i + delta <= lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 <= lam r ∧ lam r + delta / 2 <= H)
    {D N T0 C alpha : ℝ}
    (hD : 0 < D) (hN : 0 < N) (hT0 : 0 < T0) (hC : 0 < C)
    (W : ℕ → ℝ)
    (hlong : ∀ r ∈ S, W r <= C / T0 * N ^ (1 - c))
    (hlarge : ∀ r ∈ S,
      D ^ (alpha - c) <= W r *
        ‖∏ i, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) :
    (S.card : ℝ) *
        (((T0 / C) * D ^ (alpha - c) * N ^ (c - 1)) ^ 2) <=
      (H + 4 * (groupedDyadicUpper q : ℝ) *
          (1 + Real.log (groupedDyadicUpper q))) *
        (1 / delta + 2 * Real.log (groupedDyadicUpper q)) *
        (((groupedDyadicLower q : ℝ) ^ (-c)) ^ 2 * G) := by
  let V : ℝ := (T0 / C) * D ^ (alpha - c) * N ^ (c - 1)
  have hV : 0 < V := by
    dsimp [V]
    positivity
  have hcomplement : ∀ r ∈ S, V <=
      ‖∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i)))
          ((c : ℂ) + (lam r : ℝ) * Complex.I)‖ := by
    intro r hr
    exact derivativeFactor_excision hN hT0 hC (norm_nonneg _)
      (hlong r hr) (hlarge r hr)
  have hcount := montgomery_heathBrown_grouped_large_values_finset
    L X kind q hc henergy hdelta hH hV hgap hband hcomplement
  simpa [V] using hcount

end RHTower.Sieve
