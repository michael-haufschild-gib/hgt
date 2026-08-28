import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProposition22Parameters
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricCeilRootedDilation
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenCompressedRetainedBoxCount

/-!
# Paper-parameter side conditions for Proposition 2.2

Elementary asymptotic and adic facts used only to instantiate the already proved exact
decomposition, classification, count, support, and mean-square theorems.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

/-- The real lower sieve cutoff is below every fixed positive power. -/
theorem eventually_mtLowerCutoff_le_rpow {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, mtLowerCutoff X ≤ X ^ η := by
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (max 1 (1 / η))
  filter_upwards [hll, Filter.eventually_gt_atTop (Real.exp (Real.exp 1))]
      with X hllX hX
  have hXpos : 0 < X := (Real.exp_pos _).trans hX
  have hlogX : 0 < Real.log X := Real.log_pos (by
    have : (1 : ℝ) < Real.exp (Real.exp 1) := by
      have h := Real.exp_lt_exp.mpr (Real.exp_pos 1)
      simpa only [Real.exp_zero] using h
    exact this.trans hX)
  have hloglog : 1 ≤ Real.log (Real.log X) :=
    (le_max_left _ _).trans hllX
  have hinv : 1 / η ≤ Real.log (Real.log X) :=
    (le_max_right _ _).trans hllX
  have hηloglog : 1 ≤ η * Real.log (Real.log X) := by
    have := (div_le_iff₀ hη).mp hinv
    simpa [one_div, mul_comm] using this
  have hloglogCube : Real.log (Real.log X) ≤ (Real.log (Real.log X)) ^ 3 := by
    nlinarith [sq_nonneg (Real.log (Real.log X)),
      mul_self_le_mul_self (by linarith : 0 ≤ (1 : ℝ)) hloglog]
  have hden : 1 ≤ η * (Real.log (Real.log X)) ^ 3 :=
    hηloglog.trans (mul_le_mul_of_nonneg_left hloglogCube hη.le)
  have hquot : Real.log X / (Real.log (Real.log X)) ^ 3 ≤ η * Real.log X := by
    have hcube : 0 < (Real.log (Real.log X)) ^ 3 := pow_pos (by linarith) 3
    apply (div_le_iff₀ hcube).2
    nlinarith
  rw [mtLowerCutoff, mtLowerLogCutoff, Real.rpow_def_of_pos hXpos]
  exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hquot)

/-- The rounded natural lower cutoff costs at most a factor two over any fixed positive power. -/
theorem eventually_cast_mtLowerCutoffNat_le_two_mul_rpow
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, (mtLowerCutoffNat X : ℝ) ≤ 2 * X ^ η := by
  filter_upwards [eventually_mtLowerCutoff_le_rpow hη,
    Filter.eventually_ge_atTop (1 : ℝ)] with X hcut hX
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hpow : 1 ≤ X ^ η := Real.one_le_rpow hX hη.le
  rw [mtLowerCutoffNat]
  calc
    ((Nat.ceil (mtLowerCutoff X) : ℕ) : ℝ) ≤
        (Nat.floor (mtLowerCutoff X) : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one (mtLowerCutoff X)
    _ ≤ mtLowerCutoff X + 1 := by
      gcongr
      exact Nat.floor_le (Real.exp_nonneg _)
    _ ≤ X ^ η + 1 := by simpa [add_comm] using add_le_add_right hcut 1
    _ ≤ 2 * X ^ η := by linarith

/-- Lower endpoints of upper-closed adic blocks increase with their index. -/
theorem mtUpperAdicScale_mono {δ : ℝ} (hδ : 0 < δ) :
    Monotone (mtUpperAdicScale δ) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · simp [mtUpperAdicScale, hj]
    · have hbase : 1 ≤ (1 + δ) ^ (j - 1) := one_le_pow₀ (by linarith)
      have hinv : (1 + δ)⁻¹ ≤ 1 :=
        (inv_le_one₀ (by linarith : 0 < 1 + δ)).2 (by linarith)
      simpa [mtUpperAdicScale, hj] using hinv.trans hbase
  · have hj : j ≠ 0 := by omega
    simp only [mtUpperAdicScale, hi, hj]
    exact pow_le_pow_right₀ (by linarith) (Nat.sub_le_sub_right hij 1)

/-- Every adic lower endpoint through the terminal index lies below the terminal integer. -/
theorem mtUpperAdicScale_lt_of_le_index
    {δ : ℝ} (hδ : 0 < δ) {m e : ℕ} (hm : 0 < m)
    (he : e ≤ mtUpperAdicIndex δ m) :
    mtUpperAdicScale δ e < (m : ℝ) :=
  (mtUpperAdicScale_mono hδ he).trans_lt (mtUpperAdicIndex_block hδ hm).1

/-- All scale-only facts needed to instantiate Proposition 2.2 at one sufficiently large `X`. -/
structure MTProposition22CutoffConditions (A : ℕ) (X epsilon : ℝ) : Prop where
  X_two : 2 ≤ X
  lower_two : 2 ≤ mtLowerCutoffNat X
  trunc_pos : 0 < mtTruncationNat X
  delta_pos : 0 < mtPaperWidth A X
  delta_le_one : mtPaperWidth A X ≤ 1
  previous_delta_nonneg : 0 ≤ mtPaperWidth (A - 1) X
  previous_delta_le_one : mtPaperWidth (A - 1) X ≤ 1
  progress : 1 ≤ mtPaperWidth A X * ((mtLowerCutoffNat X - 1 : ℕ) : ℝ)
  lower_real_one : 1 < mtLowerCutoff X
  lower_le_z : mtLowerCutoffNat X ≤ mtProposition22ZNat X
  z_le_D : mtProposition22ZNat X ≤ mtProposition22DNat X epsilon
  lower_le_Q : mtLowerCutoffNat X ≤ mtProposition22QNat X
  Q_le_three_sqrt : (mtProposition22QNat X : ℝ) ≤ 3 * X ^ (1 / 2 : ℝ)
  Q_le_X : (mtProposition22QNat X : ℝ) ≤ X
  D_le_X : (mtProposition22DNat X epsilon : ℝ) ≤ X
  root_le_X : mtProposition22ZReal X ≤ X
  root_nat_le_X : (mtProposition22ZNat X : ℝ) ≤ X
  root_room : (mtLowerCutoffNat X : ℝ) * (1 + mtPaperWidth A X) <
    mtProposition22ZReal X
  trunc_small : (mtTruncationNat X : ℝ) ≤ X ^ (epsilon / 4)
  trunc_le_two_X : (mtTruncationNat X : ℝ) ≤ 2 * X

/-- For `0 < ε ≤ 1/100`, literal rounded paper cutoffs satisfy every required ordering and cap. -/
theorem eventually_mtProposition22CutoffConditions
    (A : ℕ) {epsilon : ℝ} (hepsilon0 : 0 < epsilon)
    (hepsilon : epsilon ≤ 1 / 100) :
    ∀ᶠ X : ℝ in atTop, MTProposition22CutoffConditions A X epsilon := by
  let d : ℝ := 1 / 4 - 2 * epsilon
  have hdZ : (2 / 11 : ℝ) ≤ d := by
    dsimp [d]
    linarith
  have hdLower : (1 / 11 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdZ
  have hdPos : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 11) hdZ
  have hdOne : d < 1 := by dsimp [d]; linarith
  have heQuarter : 0 < epsilon / 4 := div_pos hepsilon0 (by norm_num)
  have heQuarterOne : epsilon / 4 ≤ 1 := by linarith
  have hpowRoom := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 11)).eventually_gt_atTop 4
  have hpowLowerZ :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 11)).eventually_ge_atTop 2
  have hpowLowerD :=
    (tendsto_rpow_atTop (sub_pos.mpr hdLower)).eventually_ge_atTop 2
  have hpowQ :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop 3
  have hpowD :=
    (tendsto_rpow_atTop (sub_pos.mpr hdOne)).eventually_ge_atTop 2
  filter_upwards [eventually_mtC1_integer_schedule,
    eventually_cast_mtLowerCutoffNat_le_two_mul_rpow
      (by norm_num : (0 : ℝ) < 1 / 11),
    eventually_mtTruncationNat_le_rpow_quarter hepsilon0,
    eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one A,
    hpowRoom, hpowLowerZ, hpowLowerD, hpowQ, hpowD,
    Filter.eventually_ge_atTop (Real.exp (Real.exp 1)),
    Filter.eventually_ge_atTop (Real.exp 1),
    Filter.eventually_ge_atTop (4 : ℝ)]
      with X hschedule hlower htrunc hprogress hroom hLowerZ hLowerD hQ hD hX
        hXexp hXfour
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have hXone : 1 ≤ X := by linarith
  have hXtwo : 2 ≤ X := by linarith
  have hlogOne : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hXexp
    simpa only [Real.log_exp] using hmono
  have hdeltaPos : 0 < mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hlogOne) _
  have hdeltaOne : mtPaperWidth A X ≤ 1 := by
    rw [mtPaperWidth]
    simpa using Real.rpow_le_rpow_of_exponent_le hlogOne
      (neg_nonpos.mpr (Nat.cast_nonneg (10 * A)))
  have hprev0 : 0 ≤ mtPaperWidth (A - 1) X := by
    rw [mtPaperWidth]
    positivity
  have hprevOne : mtPaperWidth (A - 1) X ≤ 1 := by
    rw [mtPaperWidth]
    simpa using Real.rpow_le_rpow_of_exponent_le hlogOne
      (neg_nonpos.mpr (Nat.cast_nonneg (10 * (A - 1))))
  have hlowerRealOne : 1 < mtLowerCutoff X := by
    rw [mtLowerCutoff]
    have hlogPos : 0 < Real.log X := by linarith
    have hllPos : 0 < Real.log (Real.log X) := by
      have hlogXexp : Real.exp 1 ≤ Real.log X := by
        have hmono := Real.log_le_log (Real.exp_pos (Real.exp 1)) hX
        simpa only [Real.log_exp] using hmono
      have hmono := Real.log_le_log (Real.exp_pos 1) hlogXexp
      have : (1 : ℝ) ≤ Real.log (Real.log X) := by simpa only [Real.log_exp] using hmono
      linarith
    have : 0 < mtLowerLogCutoff X := by
      exact div_pos hlogPos (pow_pos hllPos 3)
    simpa only [← Real.exp_zero] using Real.exp_lt_exp.mpr this
  have hpow11Pos : 0 < X ^ (1 / 11 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hlowerZReal : (mtLowerCutoffNat X : ℝ) ≤ mtProposition22ZReal X := by
    calc
      (mtLowerCutoffNat X : ℝ) ≤ 2 * X ^ (1 / 11 : ℝ) := hlower
      _ ≤ X ^ (1 / 11 : ℝ) * X ^ (1 / 11 : ℝ) := by gcongr
      _ = mtProposition22ZReal X := by
        rw [← Real.rpow_add hXpos]
        norm_num [mtProposition22ZReal]
  have hlowerZ : mtLowerCutoffNat X ≤ mtProposition22ZNat X := by
    rw [mtProposition22ZNat]
    have hcast : (mtLowerCutoffNat X : ℝ) ≤
        (Nat.ceil (mtProposition22ZReal X) : ℝ) :=
      hlowerZReal.trans (Nat.le_ceil _)
    exact_mod_cast hcast
  have hzDReal : mtProposition22ZReal X ≤ mtProposition22DReal X epsilon := by
    dsimp [mtProposition22ZReal, mtProposition22DReal, d]
    exact Real.rpow_le_rpow_of_exponent_le hXone hdZ
  have hzD : mtProposition22ZNat X ≤ mtProposition22DNat X epsilon := by
    dsimp [mtProposition22ZNat, mtProposition22DNat]
    exact Nat.ceil_mono hzDReal
  have hzQReal : mtProposition22ZReal X ≤ mtProposition22QReal X := by
    dsimp [mtProposition22ZReal, mtProposition22QReal]
    have hexp : X ^ (2 / 11 : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
    nlinarith [Real.rpow_nonneg (zero_le_one.trans hXone) (1 / 2 : ℝ)]
  have hzQ : mtProposition22ZNat X ≤ mtProposition22QNat X := by
    dsimp [mtProposition22ZNat, mtProposition22QNat]
    exact Nat.ceil_mono hzQReal
  have hlowerQ : mtLowerCutoffNat X ≤ mtProposition22QNat X := hlowerZ.trans hzQ
  have hQceil : (mtProposition22QNat X : ℝ) ≤ 3 * X ^ (1 / 2 : ℝ) := by
    rw [mtProposition22QNat]
    have hsqrtOne : 1 ≤ X ^ (1 / 2 : ℝ) := Real.one_le_rpow hXone (by norm_num)
    calc
      ((Nat.ceil (2 * X ^ (1 / 2 : ℝ)) : ℕ) : ℝ) ≤
          2 * X ^ (1 / 2 : ℝ) + 1 := by
        calc
          _ ≤ (Nat.floor (2 * X ^ (1 / 2 : ℝ)) : ℝ) + 1 := by
            exact_mod_cast Nat.ceil_le_floor_add_one (2 * X ^ (1 / 2 : ℝ))
          _ ≤ 2 * X ^ (1 / 2 : ℝ) + 1 := by
            gcongr
            exact Nat.floor_le (by positivity)
      _ ≤ 3 * X ^ (1 / 2 : ℝ) := by linarith
  have hQX : (mtProposition22QNat X : ℝ) ≤ X := by
    calc
      _ ≤ 3 * X ^ (1 / 2 : ℝ) := hQceil
      _ ≤ X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := by gcongr
      _ = X := by rw [← Real.rpow_add hXpos]; norm_num
  have hDrealOne : 1 ≤ mtProposition22DReal X epsilon := by
    dsimp [mtProposition22DReal, d]
    exact Real.one_le_rpow hXone hdPos.le
  have hDpowOne : 1 ≤ X ^ d := by
    simpa [mtProposition22DReal, d] using hDrealOne
  have hDceil : (mtProposition22DNat X epsilon : ℝ) ≤
      2 * X ^ d := by
    rw [mtProposition22DNat]
    calc
      ((Nat.ceil (X ^ d) : ℕ) : ℝ) ≤ X ^ d + 1 := by
        calc
          _ ≤ (Nat.floor (X ^ d) : ℝ) + 1 := by
            exact_mod_cast Nat.ceil_le_floor_add_one (X ^ d)
          _ ≤ X ^ d + 1 := by
            gcongr
            exact Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hXone) _)
      _ ≤ 2 * X ^ d := by linarith
  have hDX : (mtProposition22DNat X epsilon : ℝ) ≤ X := by
    calc
      _ ≤ 2 * X ^ d := hDceil
      _ ≤ X ^ (1 - d) * X ^ d := by gcongr
      _ = X := by rw [← Real.rpow_add hXpos]; ring_nf; norm_num
  have hrootX : mtProposition22ZReal X ≤ X := by
    dsimp [mtProposition22ZReal]
    exact Real.rpow_le_self_of_one_le hXone (by norm_num)
  have hrootNatX : (mtProposition22ZNat X : ℝ) ≤ X :=
    (by exact_mod_cast hzD : (mtProposition22ZNat X : ℝ) ≤
      (mtProposition22DNat X epsilon : ℝ)).trans hDX
  have hroom' : (mtLowerCutoffNat X : ℝ) * (1 + mtPaperWidth A X) <
      mtProposition22ZReal X := by
    calc
      (mtLowerCutoffNat X : ℝ) * (1 + mtPaperWidth A X) ≤
          (2 * X ^ (1 / 11 : ℝ)) * 2 := by gcongr <;> linarith
      _ = 4 * X ^ (1 / 11 : ℝ) := by ring
      _ < X ^ (1 / 11 : ℝ) * X ^ (1 / 11 : ℝ) := by
        exact mul_lt_mul_of_pos_right hroom hpow11Pos
      _ = mtProposition22ZReal X := by
        rw [← Real.rpow_add hXpos]
        norm_num [mtProposition22ZReal]
  have htruncTwoX : (mtTruncationNat X : ℝ) ≤ 2 * X := by
    calc
      _ ≤ X ^ (epsilon / 4) := htrunc
      _ ≤ X := Real.rpow_le_self_of_one_le hXone heQuarterOne
      _ ≤ 2 * X := by linarith
  exact {
    X_two := hXtwo
    lower_two := hschedule.1
    trunc_pos := hschedule.2.1
    delta_pos := hdeltaPos
    delta_le_one := hdeltaOne
    previous_delta_nonneg := hprev0
    previous_delta_le_one := hprevOne
    progress := hprogress
    lower_real_one := hlowerRealOne
    lower_le_z := hlowerZ
    z_le_D := hzD
    lower_le_Q := hlowerQ
    Q_le_three_sqrt := hQceil
    Q_le_X := hQX
    D_le_X := hDX
    root_le_X := hrootX
    root_nat_le_X := hrootNatX
    root_room := hroom'
    trunc_small := htrunc
    trunc_le_two_X := htruncTwoX
  }

/-- Canonical first-above-cutoff schedule, literal real root, and grid-free dilation certificate. -/
theorem eventually_exists_mtProposition22CeilRootedSchedule
    (A : ℕ) {epsilon : ℝ} (hepsilon0 : 0 < epsilon)
    (hepsilon : epsilon ≤ 1 / 100) :
    ∀ᶠ X : ℝ in atTop,
      MTProposition22CutoffConditions A X epsilon ∧
      ∃ (start : ℕ) (hdelta : 0 < mtPaperWidth A X)
        (hz₀ : (mtLowerCutoffNat X : ℝ) ≤
          mtGeometricLevel (mtPaperWidth A X) start 0)
        (hroot : mtGeometricLevel (mtPaperWidth A X) start 0 <
          mtProposition22ZReal X),
        ∃ _cert : MTGridFreeDilationCertificate
          (MTFiniteIterationSourceData.ofMinimalGeometricCeilRootedSchedule
            (mtLowerCutoffNat X) (mtTruncationNat X) start
            (mtProposition22ZReal X) (mtPaperWidth A X)
            hdelta hz₀ hroot) A X, True := by
  filter_upwards [eventually_mtProposition22CutoffConditions A hepsilon0 hepsilon,
    eventually_exists_minimalGeometricCeilRootedDilationCertificate A]
      with X hcuts hcertX
  let start := mtFirstGeometricStart (mtPaperWidth A X) (mtLowerCutoffNat X)
  have hbracket := mtFirstGeometricStart_bracket hcuts.delta_pos
    (one_le_two.trans hcuts.lower_two)
  have hz₀ : (mtLowerCutoffNat X : ℝ) ≤
      mtGeometricLevel (mtPaperWidth A X) start 0 := hbracket.1.le
  have hroot : mtGeometricLevel (mtPaperWidth A X) start 0 <
      mtProposition22ZReal X := hbracket.2.trans_lt hcuts.root_room
  obtain ⟨cert, hcert⟩ := hcertX start (mtProposition22ZReal X)
    hz₀ hbracket.2 hroot hcuts.root_nat_le_X hcuts.delta_pos
  exact ⟨hcuts, start, hcuts.delta_pos, hz₀, hroot, cert, hcert⟩

end

end RHTower.Sieve
