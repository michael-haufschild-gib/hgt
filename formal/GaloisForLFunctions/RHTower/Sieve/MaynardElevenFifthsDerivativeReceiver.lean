import GaloisForLFunctions.RHTower.Sieve.MaynardLowOrdinateDerivativeReceiver

noncomputable section
namespace RHTower.Sieve

/-- Below height ratio `11/5`, derivative excision has a uniform reserve even when the
erase-complement has zero logarithmic mass. This is the low-height escape from the giant-seam
zero-reserve obstruction. -/
theorem routeT_elevenFifths_derivativeComplement_exponents_le_first_sub_reserve
    {mu tau alpha s : ℝ}
    (hmuHi : mu ≤ 11 / 5)
    (halphaLo : 19 / 25 ≤ alpha) (halphaHi : alpha ≤ 1)
    (htau : tau ≤ mu) (hs : 0 ≤ s) :
    maynardDerivativeComplementHeightExponent tau alpha s ≤
        mu * (1 - alpha) - 59 / 125 ∧
      maynardDerivativeComplementLengthExponent tau alpha ≤
        mu * (1 - alpha) - 59 / 125 := by
  have hdelta0 : 0 ≤ 1 - alpha := by linarith
  have hdeltaHi : 1 - alpha ≤ 6 / 25 := by linarith
  have htaudelta : tau * (1 - alpha) ≤ mu * (1 - alpha) :=
    mul_le_mul_of_nonneg_right htau hdelta0
  have hmudelta : mu * (1 - alpha) ≤ (11 / 5 : ℝ) * (6 / 25) :=
    mul_le_mul hmuHi hdeltaHi hdelta0 (by norm_num)
  constructor <;>
    dsimp only [maynardDerivativeComplementHeightExponent,
      maynardDerivativeComplementLengthExponent] <;> linarith

/-- Canonical two-term derivative count enters the first receiver with the full `59/125`
low-height reserve. -/
theorem routeT_elevenFifths_derivativeComplement_count_le_first_sub_reserve
    {R Q T mu tau alpha s : ℝ}
    (hT : 1 ≤ T) (hQ : 0 ≤ Q)
    (hmuHi : mu ≤ 11 / 5)
    (halphaLo : 19 / 25 ≤ alpha) (halphaHi : alpha ≤ 1)
    (htau : tau ≤ mu) (hs : 0 ≤ s)
    (hcount : R ≤ Q *
      (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
        T ^ maynardDerivativeComplementLengthExponent tau alpha)) :
    R ≤ (2 * Q) * T ^ (mu * (1 - alpha) - 59 / 125) := by
  obtain ⟨hheight, hlength⟩ :=
    routeT_elevenFifths_derivativeComplement_exponents_le_first_sub_reserve
      hmuHi halphaLo halphaHi htau hs
  have hheightPow := Real.rpow_le_rpow_of_exponent_le hT hheight
  have hlengthPow := Real.rpow_le_rpow_of_exponent_le hT hlength
  calc
    R ≤ Q *
        (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
          T ^ maynardDerivativeComplementLengthExponent tau alpha) := hcount
    _ ≤ Q *
        (T ^ (mu * (1 - alpha) - 59 / 125) +
          T ^ (mu * (1 - alpha) - 59 / 125)) := by gcongr
    _ = (2 * Q) * T ^ (mu * (1 - alpha) - 59 / 125) := by ring

/-- Paying the corpus's complete derivative-receiver cost `T^(1/25)` still leaves the explicit
first-receiver reserve `54/125`. -/
theorem routeT_elevenFifths_derivativeComplement_normalized_first
    {R Q T mu tau alpha s : ℝ} {q : ℕ}
    (hT : 1 ≤ T) (hQ : 0 ≤ Q)
    (hmuHi : mu ≤ 11 / 5)
    (halphaLo : 19 / 25 ≤ alpha) (halphaHi : alpha ≤ 1)
    (htau : tau ≤ mu) (hs : 0 ≤ s)
    (hcount : R ≤ Q *
      (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
        T ^ maynardDerivativeComplementLengthExponent tau alpha))
    (hcost : (2 * Q) * (Real.log T) ^ q ≤ T ^ (1 / 25 : ℝ)) :
    R * (Real.log T) ^ q ≤
      T ^ (mu * (1 - alpha) - 54 / 125) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hraw := routeT_elevenFifths_derivativeComplement_count_le_first_sub_reserve
    hT hQ hmuHi halphaLo halphaHi htau hs hcount
  have hpow0 : 0 ≤ T ^ (mu * (1 - alpha) - 59 / 125) :=
    Real.rpow_nonneg hT0.le _
  calc
    R * (Real.log T) ^ q ≤
        ((2 * Q) * T ^ (mu * (1 - alpha) - 59 / 125)) *
          (Real.log T) ^ q :=
      mul_le_mul_of_nonneg_right hraw (pow_nonneg hlog0 q)
    _ = ((2 * Q) * (Real.log T) ^ q) *
        T ^ (mu * (1 - alpha) - 59 / 125) := by ring
    _ ≤ T ^ (1 / 25 : ℝ) *
        T ^ (mu * (1 - alpha) - 59 / 125) :=
      mul_le_mul_of_nonneg_right hcost hpow0
    _ = T ^ (mu * (1 - alpha) - 54 / 125) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring

/-- Literal degree-60 derivative-excised box count at the exact height ceiling `11/5`.
All finite-set, coefficient-energy, width, and logarithmic costs are discharged. -/
theorem eventually_routeT_elevenFifths_derivativeExcised_box_first (qReceiver : ℕ) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {L X : ℕ} {mu N0 c alpha delta C : ℝ},
      ∀ (box : HeathBrownBoxChoice L X 60),
      ∀ (j : HeathBrownBoxFactorIndex 60 box.m),
      1 ≤ X → (X : ℝ) ≤ T ^ mu → mu ≤ 11 / 5 →
      0 ≤ c → 19 / 25 ≤ alpha → alpha ≤ 1 →
      1 ≤ delta → delta ≤ 2 * T →
      0 < C → C ≤ 600 * Real.log T →
      ∀ (S : Finset ℕ), ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ n ∈ S, T ≤ lam n ∧ lam n ≤ 2 * T) →
      IsHeathBrownBoxWindowRelevant N0 X 60 box →
      (∀ n ∈ S,
        ‖heathBrownBoxFactorValue L X 60 box
            ((c : ℂ) + (lam n : ℝ) * Complex.I) j‖ ≤
          C / T *
            (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
              (1 - c)) →
      (∀ n ∈ S,
        (((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)) ^
            (alpha - c) ≤
          ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
            ((c : ℂ) + (lam n : ℝ) * Complex.I)‖) →
      (S.card : ℝ) * (Real.log T) ^ qReceiver ≤
        T ^ (mu * (1 - alpha) - 54 / 125) := by
  filter_upwards [eventually_maynardLowOrdinateDerivative_fixedCost_absorbed qReceiver,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hcost hT
  intro L X mu N0 c alpha delta C box j hX hXscale hmuHi hc
    halphaLo halphaHi hdelta hdeltaHi hC hCcap S lam hgap hband hwindow
    hlong hlarge
  let I := {i : HeathBrownBoxFactorIndex 60 box.m //
    i ∈ (Finset.univ.erase j)}
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent box.a box.b box.q i
  let U : ℝ := (groupedDyadicUpper q : ℝ)
  let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
  let tau : ℝ := heathBrownBoxTotalExponent L X 60 T box
  let s : ℝ := ∑ i ∈ (Finset.univ.erase j),
    dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q i)
  let Q : ℝ := C ^ 2 *
    (12 * maynardLowOrdinateComplementWidthConstant ^ 2 *
      (1 + Real.log U) ^ (E + 2))
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hmuEight : mu ≤ 8 := by linarith
  have hderivativeBand : ∀ n ∈ S,
      delta / 2 ≤ lam n ∧ lam n + delta / 2 ≤ 3 * T := by
    intro n hn
    have hnBand := hband n hn
    constructor <;> linarith
  have hcountRaw := derivativeExcised_montgomery_heathBrownBox_to_canonical
    box j hc hdelta (by positivity : 0 ≤ 3 * T) le_rfl hgap
      hderivativeBand hT hC hlong hlarge
  have hcount : (S.card : ℝ) ≤ Q *
      (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
        T ^ maynardDerivativeComplementLengthExponent tau alpha) := by
    simpa only [I, q, U, E, tau, s, Q] using hcountRaw
  have htau : tau ≤ mu := by
    dsimp only [tau]
    exact windowRelevant_heathBrownBox_totalExponent_le hT hXscale box hwindow
  have hs : 0 ≤ s := by
    dsimp only [s]
    exact Finset.sum_nonneg fun i _ => dyadicLogExponent_nonneg hT _
  have hU1 : 1 ≤ U := by
    dsimp only [U]
    exact_mod_cast one_le_groupedDyadicUpper q
  have hUscale : U ≤
      maynardLowOrdinateComplementWidthConstant * T ^ (8 : ℕ) := by
    dsimp only [U, q, I]
    simpa using windowRelevant_heathBrownBox_complement_upper_le_width_mul_T8
      box j hT hmuEight hXscale hwindow
  have hE : E ≤ maynardLowOrdinateComplementPolylogExponent := by
    dsimp only [E, I]
    simpa using heathBrownBoxFactor_complement_polylogExponent_le box j
  have hcostQ : (2 * Q) * (Real.log T) ^ qReceiver ≤ T ^ (1 / 25 : ℝ) := by
    simpa only [Q] using hcost C U E hC.le hCcap hU1 hUscale hE
  exact routeT_elevenFifths_derivativeComplement_normalized_first
    hT.le (by positivity) hmuHi halphaLo halphaHi htau hs hcount hcostQ


set_option maxHeartbeats 1000000 in
/-- Every fixed over-height zeta/log box fibre satisfies the `11/5` first receiver. The
Kuzmin--Landau premise and its complete polylogarithmic coefficient are discharged internally. -/
theorem eventually_routeT_elevenFifths_overHeight_box_first (qReceiver : ℕ) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {L X : ℕ} {mu N0 c alpha delta : ℝ},
      ∀ (box : HeathBrownBoxChoice L X 60),
      ∀ (j : HeathBrownBoxFactorIndex 60 box.m),
      1 ≤ X → (X : ℝ) ≤ T ^ mu → mu ≤ 11 / 5 →
      0 ≤ c → 19 / 25 ≤ alpha → alpha ≤ 1 →
      1 ≤ delta → delta ≤ 2 * T →
      (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
        heathBrownBoxFactorKind 60 box.m j = .log) →
      1 ≤ dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q j) →
      ∀ (S : Finset ℕ), ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ n ∈ S, T ≤ lam n ∧ lam n ≤ 2 * T) →
      IsHeathBrownBoxWindowRelevant N0 X 60 box →
      (∀ n ∈ S,
        (((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)) ^
            (alpha - c) ≤
          ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
            ((c : ℂ) + (lam n : ℝ) * Complex.I)‖) →
      (S.card : ℝ) * (Real.log T) ^ qReceiver ≤
        T ^ (mu * (1 - alpha) - 54 / 125) := by
  filter_upwards [eventually_routeT_elevenFifths_derivativeExcised_box_first qReceiver,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hreceiver hlogT hT
  intro L X mu N0 c alpha delta box j hX hXscale hmuHi hc halphaLo
    halphaHi hdelta hdeltaHi hkind hover S lam hgap hband hwindow hlarge
  let C : ℝ := 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hmuEight : mu ≤ 8 := by linarith
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (mul_pos (by norm_num) (by positivity [Real.pi_pos]))
      (lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X))
  have hEnvelope := maynardLongPolylogEnvelope_le_twelve_log_of_mu_le_eight
    hX hT0 hlogT hmuEight hXscale
  have hcoeff : 2 * (6 * Real.pi + 1) ≤ 50 := by
    nlinarith [Real.pi_le_four]
  have hCcap : C ≤ 600 * Real.log T := by
    dsimp only [C]
    calc
      2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X ≤
          50 * maynardLongPolylogEnvelope X :=
        mul_le_mul_of_nonneg_right hcoeff
          (zero_le_one.trans (one_le_maynardLongPolylogEnvelope X))
      _ ≤ 50 * (12 * Real.log T) :=
        mul_le_mul_of_nonneg_left hEnvelope (by norm_num)
      _ = 600 * Real.log T := by ring
  let qj : ℕ := heathBrownBoxFactorExponent box.a box.b box.q j
  let N : ℝ := ((2 ^ qj : ℕ) : ℝ)
  have hqj : qj ≤ Nat.log 2 X := by
    dsimp only [qj]
    exact box.factorExponent_le_log_X_of_zeta_or_log j hkind
  have hTN : T ≤ N := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hover
    have hr := rpow_dyadicLogExponent hT qj
    dsimp only [N]
    simpa only [Real.rpow_one] using hpow.trans_eq hr
  have hlong : ∀ n ∈ S,
      ‖heathBrownBoxFactorValue L X 60 box
          ((c : ℂ) + (lam n : ℝ) * Complex.I) j‖ ≤
        C / T * N ^ (1 - c) := by
    intro n hn
    have hnBand := hband n hn
    rcases hkind with hkind | hkind
    · have hz := norm_LSeries_zetaDyadicBlock_le_over_height
        hX hqj hT0 hc hnBand.1 hnBand.2 hTN
      have hbase : (6 * Real.pi + 1) ≤ C := by
        dsimp only [C]
        have henv : 1 ≤ maynardLongPolylogEnvelope X :=
          one_le_maynardLongPolylogEnvelope X
        nlinarith [Real.pi_pos]
      have hcoefDiv : (6 * Real.pi + 1) / T ≤ C / T :=
        div_le_div_of_nonneg_right hbase hT0.le
      calc
        ‖heathBrownBoxFactorValue L X 60 box
            ((c : ℂ) + (lam n : ℝ) * Complex.I) j‖ ≤
            (6 * Real.pi + 1) / T * N ^ (1 - c) := by
          simpa only [heathBrownBoxFactorValue, heathBrownFactorBase, hkind,
            qj, N] using hz
        _ ≤ C / T * N ^ (1 - c) :=
          mul_le_mul_of_nonneg_right hcoefDiv (Real.rpow_nonneg (by positivity) _)
    · have hlog := norm_LSeries_logDyadicBlock_le_over_height
        hX hqj hT0 hc hnBand.1 hnBand.2 hTN
      simpa only [heathBrownBoxFactorValue, heathBrownFactorBase, hkind,
        qj, N, C] using hlog
  exact hreceiver box j hX hXscale hmuHi hc halphaLo halphaHi hdelta hdeltaHi
    hC hCcap S lam hgap hband hwindow
      (by simpa only [qj, N] using hlong) hlarge

end RHTower.Sieve
