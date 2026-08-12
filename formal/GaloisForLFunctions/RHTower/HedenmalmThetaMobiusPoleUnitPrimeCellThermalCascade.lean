import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitColdFirstShellValuation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Prime-cell thermal cascade of the normalized Möbius source

P-G41--P-G44 identify the two endpoint jets of the finite squarefree Möbius Gram.  This module
resolves the intervening Euler geometry before the prime product is taken.

Every prime factor is a two-state Hellinger cell.  Along a nontrivial midpoint thermal path its
defect is not monotone: it has one interior peak and returns to the vacuum.  Peak scales are
strictly ordered by the prime odds.  Thus the critical Hardy defect is an ultraviolet accumulation
of transient prime cells, while the P-G44 prime-two law is the last infrared exit.

This is an unconditional source classification, not an RH proof.  It shows that neither endpoint
monotonicity nor cancellation of a finite set of Euler cells can be the missing Route-P producer.
-/

open Filter Set Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Squared Hellinger Gram of two Bernoulli laws whose geometric-mean odds are `A` and whose
oriented odds ratio is `T²`. -/
def bernoulliMidpointGramSq (A T : ℝ) : ℝ :=
  (1 + A) ^ 2 / ((1 + A * T) * (1 + A / T))

/-- Projective odds of failure of the Bernoulli midpoint Gram. -/
def bernoulliMidpointDefectOdds (A T : ℝ) : ℝ :=
  A * (T - 1) ^ 2 / (T * (1 + A) ^ 2)

/-- Exact local Julia identity: reciprocal Gram excess equals defect odds. -/
theorem one_div_bernoulliMidpointGramSq_sub_one
    {A T : ℝ} (hT : T ≠ 0) (hA : 1 + A ≠ 0) :
    1 / bernoulliMidpointGramSq A T - 1 =
      bernoulliMidpointDefectOdds A T := by
  rw [bernoulliMidpointGramSq, bernoulliMidpointDefectOdds]
  field_simp
  ring

/-- Every nontrivial positive prime cell has strictly subunit Gram. -/
theorem bernoulliMidpointGramSq_mem_Ioo_zero_one
    {A T : ℝ} (hA : 0 < A) (hT : 1 < T) :
    bernoulliMidpointGramSq A T ∈ Ioo 0 1 := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hAT : 0 < A * T := mul_pos hA hT0
  have hAdT : 0 < A / T := div_pos hA hT0
  have hden : 0 < (1 + A * T) * (1 + A / T) :=
    mul_pos (by linarith) (by linarith)
  constructor
  · exact div_pos (sq_pos_of_pos (by linarith)) hden
  · rw [bernoulliMidpointGramSq, div_lt_one hden]
    have hgap : 0 < A * (T - 1) ^ 2 / T :=
      div_pos (mul_pos hA (sq_pos_of_pos (sub_pos.mpr hT))) hT0
    have hid :
        (1 + A * T) * (1 + A / T) - (1 + A) ^ 2 =
          A * (T - 1) ^ 2 / T := by
      field_simp
      ring
    linarith

/-- Thermal midpoint mass.  Here `q` is base prime odds, `r>1` is aperture eccentricity, and
`T>1` is oriented thermal ratio. -/
def thermalBernoulliMidpointMass (q r T : ℝ) : ℝ := q * T ^ (-r)

/-- Prime-cell defect odds along a thermal midpoint path. -/
def thermalBernoulliMidpointDefectOdds (q r T : ℝ) : ℝ :=
  bernoulliMidpointDefectOdds (thermalBernoulliMidpointMass q r T) T

/-- Algebraic balance whose sign orients the prime-cell thermal flow. -/
def thermalBernoulliPeakBalance (q r T : ℝ) : ℝ :=
  ((r + 1) - (r - 1) * T) +
    thermalBernoulliMidpointMass q r T * ((r + 1) * T - (r - 1))

/-- Exact derivative factorization of one thermal prime cell. -/
theorem hasDerivAt_thermalBernoulliMidpointDefectOdds
    {q r T : ℝ} (hq : 0 < q) (hT : 1 < T) :
    HasDerivAt (thermalBernoulliMidpointDefectOdds q r)
      (thermalBernoulliMidpointDefectOdds q r T *
        thermalBernoulliPeakBalance q r T /
          (T * (T - 1) * (1 + thermalBernoulliMidpointMass q r T))) T := by
  have hT0 : T ≠ 0 := (lt_trans zero_lt_one hT).ne'
  have hpow :
      T ^ (-r - 1) = T ^ (-r) / T := by
    rw [show -r - 1 = -r + (-1 : ℝ) by ring, Real.rpow_add (lt_trans zero_lt_one hT),
      Real.rpow_neg_one]
    rfl
  have hmass : HasDerivAt (thermalBernoulliMidpointMass q r)
      (q * ((-r) * T ^ (-r - 1))) T := by
    exact (Real.hasDerivAt_rpow_const (p := -r) (Or.inl hT0)).const_mul q
  have hden : T * (1 + thermalBernoulliMidpointMass q r T) ^ 2 ≠ 0 := by
    refine mul_ne_zero hT0 (pow_ne_zero 2 ?_)
    have hmassPos : 0 < thermalBernoulliMidpointMass q r T :=
      mul_pos hq (Real.rpow_pos_of_pos (lt_trans zero_lt_one hT) _)
    linarith
  unfold thermalBernoulliMidpointDefectOdds bernoulliMidpointDefectOdds
  have hnum := hmass.mul (((hasDerivAt_id T).sub_const 1).pow 2)
  have hdenDeriv := (hasDerivAt_id T).mul
    (((hasDerivAt_const (x := T) (c := (1 : ℝ))).add hmass).pow 2)
  convert hnum.div hdenDeriv hden using 1 <;> try rfl
  simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, one_mul, zero_add,
    Nat.cast_ofNat]
  rw [hpow]
  simp only [thermalBernoulliPeakBalance, thermalBernoulliMidpointMass]
  have hone : 1 + q * T ^ (-r) ≠ 0 := by
    have : 0 < q * T ^ (-r) :=
      mul_pos hq (Real.rpow_pos_of_pos (lt_trans zero_lt_one hT) _)
    linarith
  field_simp [hT0, hone]
  ring

/-- The peak equation is a collision between decreasing thermal mass and an increasing rational
aperture ratio. -/
def thermalBernoulliPeakRatio (r T : ℝ) : ℝ :=
  ((r - 1) * T - (r + 1)) / ((r + 1) * T - (r - 1))

/-- Above the aperture threshold, vanishing balance is exactly mass/ratio collision. -/
theorem thermalBernoulliPeakBalance_eq_zero_iff
    {q r T : ℝ} (hr : 1 < r) (hT : (r + 1) / (r - 1) < T) :
    thermalBernoulliPeakBalance q r T = 0 ↔
      thermalBernoulliMidpointMass q r T = thermalBernoulliPeakRatio r T := by
  have hrm : 0 < r - 1 := sub_pos.mpr hr
  have hden : 0 < (r + 1) * T - (r - 1) := by
    have := (mul_lt_mul_of_pos_left hT hrm)
    field_simp at this
    nlinarith
  rw [thermalBernoulliPeakBalance, thermalBernoulliPeakRatio]
  constructor
  · intro h
    apply (eq_div_iff hden.ne').2
    linarith
  · intro h
    apply (eq_div_iff hden.ne').1 at h
    linarith

/-- Division-free balance is the positive peak denominator times mass-minus-ratio. -/
theorem thermalBernoulliPeakBalance_eq_den_mul_sub
    {q r T : ℝ} (hr : 1 < r) (hT : (r + 1) / (r - 1) < T) :
    thermalBernoulliPeakBalance q r T =
      ((r + 1) * T - (r - 1)) *
        (thermalBernoulliMidpointMass q r T - thermalBernoulliPeakRatio r T) := by
  have hrm : 0 < r - 1 := sub_pos.mpr hr
  have hden : (r + 1) * T - (r - 1) ≠ 0 := by
    have := mul_lt_mul_of_pos_left hT hrm
    field_simp [hrm.ne'] at this
    nlinarith
  rw [thermalBernoulliPeakBalance, thermalBernoulliPeakRatio]
  field_simp [hden]
  ring

/-- Rational peak ratio is strictly increasing above its aperture threshold. -/
theorem thermalBernoulliPeakRatio_strictMonoOn {r : ℝ} (hr : 1 < r) :
    StrictMonoOn (thermalBernoulliPeakRatio r) (Ioi ((r + 1) / (r - 1))) := by
  intro T₁ hT₁ T₂ hT₂ hlt
  have hrm : 0 < r - 1 := sub_pos.mpr hr
  have hd₁ : 0 < (r + 1) * T₁ - (r - 1) := by
    have := mul_lt_mul_of_pos_left hT₁ hrm
    field_simp at this
    nlinarith
  have hd₂ : 0 < (r + 1) * T₂ - (r - 1) := by
    have := mul_lt_mul_of_pos_left hT₂ hrm
    field_simp at this
    nlinarith
  rw [thermalBernoulliPeakRatio, thermalBernoulliPeakRatio]
  rw [div_lt_div_iff₀ hd₁ hd₂]
  nlinarith

/-- At fixed positive odds, thermal midpoint mass is strictly decreasing in `T`. -/
theorem thermalBernoulliMidpointMass_strictAntiOn
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    StrictAntiOn (thermalBernoulliMidpointMass q r) (Ioi 0) := by
  intro T₁ hT₁ T₂ hT₂ hlt
  rw [thermalBernoulliMidpointMass, thermalBernoulliMidpointMass]
  exact mul_lt_mul_of_pos_left
    (Real.strictAntiOn_rpow_Ioi_of_exponent_neg (neg_neg_of_pos hr) hT₁ hT₂ hlt) hq

/-- A thermal prime cell has at most one interior peak. -/
theorem thermalBernoulliPeak_unique
    {q r T₁ T₂ : ℝ} (hq : 0 < q) (hr : 1 < r)
    (hT₁ : (r + 1) / (r - 1) < T₁)
    (hT₂ : (r + 1) / (r - 1) < T₂)
    (h₁ : thermalBernoulliPeakBalance q r T₁ = 0)
    (h₂ : thermalBernoulliPeakBalance q r T₂ = 0) :
    T₁ = T₂ := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hthresh : 0 < (r + 1) / (r - 1) := div_pos (by linarith) (by linarith)
  have hm₁ := (thermalBernoulliPeakBalance_eq_zero_iff hr hT₁).1 h₁
  have hm₂ := (thermalBernoulliPeakBalance_eq_zero_iff hr hT₂).1 h₂
  rcases lt_trichotomy T₁ T₂ with hlt | heq | hgt
  · have hmass := thermalBernoulliMidpointMass_strictAntiOn hq hr0
      (lt_trans hthresh hT₁) (lt_trans hthresh hT₂) hlt
    have hratio := thermalBernoulliPeakRatio_strictMonoOn hr hT₁ hT₂ hlt
    rw [hm₁, hm₂] at hmass
    exact False.elim (not_lt_of_ge hratio.le hmass)
  · exact heq
  · have hmass := thermalBernoulliMidpointMass_strictAntiOn hq hr0
      (lt_trans hthresh hT₂) (lt_trans hthresh hT₁) hgt
    have hratio := thermalBernoulliPeakRatio_strictMonoOn hr hT₂ hT₁ hgt
    rw [hm₂, hm₁] at hmass
    exact False.elim (not_lt_of_ge hratio.le hmass)

/-- Every positive thermal Bernoulli cell has one interior peak. -/
theorem existsUnique_thermalBernoulliPeak
    {q r : ℝ} (hq : 0 < q) (hr : 1 < r) :
    ∃! T : ℝ, (r + 1) / (r - 1) < T ∧
      thermalBernoulliPeakBalance q r T = 0 := by
  let threshold := (r + 1) / (r - 1)
  let T₀ := threshold + 1
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hrm : 0 < r - 1 := sub_pos.mpr hr
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    exact div_pos (by linarith) hrm
  have hT₀ : threshold < T₀ := by dsimp [T₀]; linarith
  have hratioThreshold : thermalBernoulliPeakRatio r threshold = 0 := by
    rw [thermalBernoulliPeakRatio]
    have hden : (r + 1) * threshold - (r - 1) ≠ 0 := by
      dsimp [threshold]
      field_simp [hrm.ne']
      nlinarith
    apply div_eq_zero_iff.mpr
    left
    dsimp [threshold]
    field_simp [hrm.ne']
    ring
  have hratioT₀ : 0 < thermalBernoulliPeakRatio r T₀ := by
    rw [thermalBernoulliPeakRatio]
    apply div_pos
    · dsimp [T₀, threshold]
      field_simp [hrm.ne']
      nlinarith
    · have hden := mul_lt_mul_of_pos_left hT₀ hrm
      dsimp [threshold] at hden
      field_simp [hrm.ne'] at hden
      nlinarith
  have hmassLimit :
      Tendsto (thermalBernoulliMidpointMass q r) atTop (𝓝 0) := by
    change Tendsto (fun T : ℝ => q * T ^ (-r)) atTop _
    simpa using (tendsto_rpow_neg_atTop hr0).const_mul q
  have hsmall : ∀ᶠ T : ℝ in atTop,
      thermalBernoulliMidpointMass q r T < thermalBernoulliPeakRatio r T₀ :=
    (tendsto_order.1 hmassLimit).2 _ hratioT₀
  obtain ⟨T₁, hT₀T₁, hmassT₁⟩ :=
    ((eventually_ge_atTop T₀).and hsmall).exists
  have hthresholdT₁ : threshold ≤ T₁ := le_trans hT₀.le hT₀T₁
  have hratioMono :
      thermalBernoulliPeakRatio r T₀ ≤ thermalBernoulliPeakRatio r T₁ :=
    (thermalBernoulliPeakRatio_strictMonoOn hr).monotoneOn hT₀
      (lt_of_lt_of_le hT₀ hT₀T₁) hT₀T₁
  let f : ℝ → ℝ := fun T =>
    thermalBernoulliMidpointMass q r T - thermalBernoulliPeakRatio r T
  have hfThreshold : 0 < f threshold := by
    change 0 < thermalBernoulliMidpointMass q r threshold -
      thermalBernoulliPeakRatio r threshold
    rw [hratioThreshold, sub_zero, thermalBernoulliMidpointMass]
    exact mul_pos hq (Real.rpow_pos_of_pos hthreshold _)
  have hfT₁ : f T₁ < 0 := by
    dsimp [f]
    linarith
  have hcontMass : ContinuousOn (thermalBernoulliMidpointMass q r)
      (Icc threshold T₁) := by
    change ContinuousOn (fun T : ℝ => q * T ^ (-r)) (Icc threshold T₁)
    exact continuousOn_const.mul
      (continuousOn_id.rpow_const fun T hT =>
        Or.inl (ne_of_gt (lt_of_lt_of_le hthreshold hT.1)))
  have hcontRatio : ContinuousOn (thermalBernoulliPeakRatio r)
      (Icc threshold T₁) := by
    change ContinuousOn
      (fun T : ℝ => ((r - 1) * T - (r + 1)) / ((r + 1) * T - (r - 1)))
      (Icc threshold T₁)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro T hT
    have hbaseDen : 0 < (r + 1) * threshold - (r - 1) := by
      dsimp [threshold]
      field_simp [hrm.ne']
      nlinarith
    have hrp : 0 < r + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hT.1 hrp.le]
  have hcont : ContinuousOn f (Icc threshold T₁) :=
    hcontMass.sub hcontRatio
  obtain ⟨T, hTmem, hTf⟩ := intermediate_value_Icc' hthresholdT₁ hcont
    (mem_Icc.mpr ⟨hfT₁.le, hfThreshold.le⟩)
  have hTstrict : threshold < T := by
    rcases hTmem with ⟨hTle, _⟩
    exact lt_of_le_of_ne hTle fun heq => by
      subst T
      rw [hTf] at hfThreshold
      exact lt_irrefl 0 hfThreshold
  have hbalance : thermalBernoulliPeakBalance q r T = 0 := by
    apply (thermalBernoulliPeakBalance_eq_zero_iff hr hTstrict).2
    dsimp [f] at hTf
    linarith
  refine ⟨T, ⟨hTstrict, hbalance⟩, ?_⟩
  intro U hU
  exact thermalBernoulliPeak_unique hq hr hU.1 hTstrict hU.2 hbalance

/-- The unique peak separates the increasing and decreasing thermal phases. -/
theorem thermalBernoulliPeakBalance_sign_of_root
    {q r Tstar : ℝ} (hq : 0 < q) (hr : 1 < r)
    (hTstar : (r + 1) / (r - 1) < Tstar)
    (hstar : thermalBernoulliPeakBalance q r Tstar = 0) :
    (∀ T, (r + 1) / (r - 1) < T → T < Tstar →
        0 < thermalBernoulliPeakBalance q r T) ∧
      (∀ T, Tstar < T → thermalBernoulliPeakBalance q r T < 0) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hthreshold : 0 < (r + 1) / (r - 1) :=
    div_pos (by linarith) (sub_pos.mpr hr)
  have hmassStar := (thermalBernoulliPeakBalance_eq_zero_iff hr hTstar).1 hstar
  constructor
  · intro T hT hlt
    rw [thermalBernoulliPeakBalance_eq_den_mul_sub hr hT]
    apply mul_pos
    · have hrm : 0 < r - 1 := sub_pos.mpr hr
      have := mul_lt_mul_of_pos_left hT hrm
      field_simp [hrm.ne'] at this
      nlinarith
    · have hm := thermalBernoulliMidpointMass_strictAntiOn hq hr0
        (lt_trans hthreshold hT) (lt_trans hthreshold hTstar) hlt
      have hratio := thermalBernoulliPeakRatio_strictMonoOn hr hT hTstar hlt
      rw [hmassStar] at hm
      linarith
  · intro T hlt
    have hT := lt_trans hTstar hlt
    rw [thermalBernoulliPeakBalance_eq_den_mul_sub hr hT]
    apply mul_neg_of_pos_of_neg
    · have hrm : 0 < r - 1 := sub_pos.mpr hr
      have := mul_lt_mul_of_pos_left hT hrm
      field_simp [hrm.ne'] at this
      nlinarith
    · have hm := thermalBernoulliMidpointMass_strictAntiOn hq hr0
        (lt_trans hthreshold hTstar) (lt_trans hthreshold hT) hlt
      have hratio := thermalBernoulliPeakRatio_strictMonoOn hr hTstar hT hlt
      rw [hmassStar] at hm
      linarith

/-- Consequently the local defect odds increase strictly before the unique peak and decrease
strictly afterward. -/
theorem deriv_thermalBernoulliMidpointDefectOdds_sign_of_root
    {q r Tstar : ℝ} (hq : 0 < q) (hr : 1 < r)
    (hTstar : (r + 1) / (r - 1) < Tstar)
    (hstar : thermalBernoulliPeakBalance q r Tstar = 0) :
    (∀ T, (r + 1) / (r - 1) < T → T < Tstar →
        0 < deriv (thermalBernoulliMidpointDefectOdds q r) T) ∧
      (∀ T, Tstar < T →
        deriv (thermalBernoulliMidpointDefectOdds q r) T < 0) := by
  obtain ⟨hbefore, hafter⟩ :=
    thermalBernoulliPeakBalance_sign_of_root hq hr hTstar hstar
  have hthreshold : 1 < (r + 1) / (r - 1) := by
    have hrm : 0 < r - 1 := sub_pos.mpr hr
    rw [one_lt_div hrm]
    linarith
  constructor
  · intro T hT hlt
    rw [(hasDerivAt_thermalBernoulliMidpointDefectOdds hq
      (lt_trans hthreshold hT)).deriv]
    have hTpos : 0 < T := lt_trans zero_lt_one (lt_trans hthreshold hT)
    have hTone : 1 < T := lt_trans hthreshold hT
    have hmass : 0 < thermalBernoulliMidpointMass q r T := by
      exact mul_pos hq (Real.rpow_pos_of_pos hTpos _)
    have hodds : 0 < thermalBernoulliMidpointDefectOdds q r T := by
      rw [thermalBernoulliMidpointDefectOdds, bernoulliMidpointDefectOdds]
      exact div_pos (mul_pos hmass (sq_pos_of_pos (sub_pos.mpr hTone)))
        (mul_pos hTpos (sq_pos_of_pos (by linarith)))
    have hden : 0 < T * (T - 1) * (1 + thermalBernoulliMidpointMass q r T) := by
      exact mul_pos (mul_pos hTpos (sub_pos.mpr hTone)) (by linarith)
    exact div_pos (mul_pos hodds (hbefore T hT hlt)) hden
  · intro T hlt
    have hT := lt_trans hTstar hlt
    rw [(hasDerivAt_thermalBernoulliMidpointDefectOdds hq
      (lt_trans hthreshold hT)).deriv]
    have hTpos : 0 < T := lt_trans zero_lt_one (lt_trans hthreshold hT)
    have hTone : 1 < T := lt_trans hthreshold hT
    have hmass : 0 < thermalBernoulliMidpointMass q r T := by
      exact mul_pos hq (Real.rpow_pos_of_pos hTpos _)
    have hodds : 0 < thermalBernoulliMidpointDefectOdds q r T := by
      rw [thermalBernoulliMidpointDefectOdds, bernoulliMidpointDefectOdds]
      exact div_pos (mul_pos hmass (sq_pos_of_pos (sub_pos.mpr hTone)))
        (mul_pos hTpos (sq_pos_of_pos (by linarith)))
    have hden : 0 < T * (T - 1) * (1 + thermalBernoulliMidpointMass q r T) := by
      exact mul_pos (mul_pos hTpos (sub_pos.mpr hTone)) (by linarith)
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hodds (hafter T hlt)) hden

/-- Larger prime odds peak later in the oriented thermal ratio. -/
theorem thermalBernoulliPeak_strictMono_odds
    {q₁ q₂ r T₁ T₂ : ℝ} (hq₁ : 0 < q₁) (hq : q₁ < q₂) (hr : 1 < r)
    (hT₁ : (r + 1) / (r - 1) < T₁)
    (hT₂ : (r + 1) / (r - 1) < T₂)
    (h₁ : thermalBernoulliPeakBalance q₁ r T₁ = 0)
    (h₂ : thermalBernoulliPeakBalance q₂ r T₂ = 0) :
    T₁ < T₂ := by
  have hq₂ : 0 < q₂ := lt_trans hq₁ hq
  have hm₁ := (thermalBernoulliPeakBalance_eq_zero_iff hr hT₁).1 h₁
  have hm₂ := (thermalBernoulliPeakBalance_eq_zero_iff hr hT₂).1 h₂
  by_contra hnot
  have hle : T₂ ≤ T₁ := le_of_not_gt hnot
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hthresh : 0 < (r + 1) / (r - 1) := div_pos (by linarith) (by linarith)
  have hpow : 0 < T₂ ^ (-r) := by
    exact Real.rpow_pos_of_pos (lt_trans hthresh hT₂) _
  have hmassOdds :
      thermalBernoulliMidpointMass q₁ r T₂ <
        thermalBernoulliMidpointMass q₂ r T₂ := by
    rw [thermalBernoulliMidpointMass, thermalBernoulliMidpointMass]
    exact mul_lt_mul_of_pos_right hq hpow
  have hmassT :
      thermalBernoulliMidpointMass q₁ r T₁ ≤
        thermalBernoulliMidpointMass q₁ r T₂ := by
    exact (thermalBernoulliMidpointMass_strictAntiOn hq₁ hr0).antitoneOn
      (lt_trans hthresh hT₂) (lt_trans hthresh hT₁) hle
  have hratio : thermalBernoulliPeakRatio r T₂ ≤ thermalBernoulliPeakRatio r T₁ :=
    (thermalBernoulliPeakRatio_strictMonoOn hr).monotoneOn hT₂ hT₁ hle
  rw [hm₁] at hmassT
  rw [hm₂] at hmassOdds
  rw [← hm₁, ← hm₂] at hratio
  linarith

/-- Literal prime Euler factor of the finite squarefree midpoint Gram. -/
def squarefreeMobiusPrimeCellGramSq (p : Nat.Primes) (epsilon x z : ℝ) : ℝ :=
  let y := (x + z) / 2
  (1 + (p : ℝ) ^ (-(1 + y * epsilon))) ^ 2 /
    ((1 + (p : ℝ) ^ (-(1 + x * epsilon))) *
      (1 + (p : ℝ) ^ (-(1 + z * epsilon))))

/-- The literal prime factor is exactly the abstract Bernoulli midpoint cell on the forced
thermal path. -/
theorem squarefreeMobiusPrimeCellGramSq_eq_bernoulliMidpointGramSq
    (p : Nat.Primes) {epsilon x z : ℝ} (hxz : x ≠ z) :
    let delta := (z - x) / 2
    let y := (x + z) / 2
    let T := (p : ℝ) ^ (delta * epsilon)
    squarefreeMobiusPrimeCellGramSq p epsilon x z =
      bernoulliMidpointGramSq
        (thermalBernoulliMidpointMass ((p : ℝ) ^ (-1 : ℝ)) (y / delta) T) T := by
  dsimp only
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp0 : 0 ≤ (p : ℝ) := hp.le
  have hdelta : (z - x) / 2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr hxz.symm) (by norm_num)
  let delta := (z - x) / 2
  let y := (x + z) / 2
  let T := (p : ℝ) ^ (delta * epsilon)
  have hT : 0 < T := Real.rpow_pos_of_pos hp _
  have hmass :
      thermalBernoulliMidpointMass ((p : ℝ) ^ (-1 : ℝ)) (y / delta) T =
        (p : ℝ) ^ (-(1 + y * epsilon)) := by
    rw [thermalBernoulliMidpointMass]
    have hpow : T ^ (-(y / delta)) =
        (p : ℝ) ^ ((delta * epsilon) * (-(y / delta))) := by
      exact (Real.rpow_mul hp.le (delta * epsilon) (-(y / delta))).symm
    rw [hpow, ← Real.rpow_add hp]
    congr 1
    dsimp [delta, y] at hdelta ⊢
    field_simp [hdelta]
    ring
  have hleft :
      thermalBernoulliMidpointMass ((p : ℝ) ^ (-1 : ℝ)) (y / delta) T * T =
        (p : ℝ) ^ (-(1 + x * epsilon)) := by
    rw [hmass]
    change (p : ℝ) ^ (-(1 + y * epsilon)) *
        (p : ℝ) ^ (delta * epsilon) = _
    rw [← Real.rpow_add hp]
    congr 1
    dsimp [delta, y]
    ring
  have hright :
      thermalBernoulliMidpointMass ((p : ℝ) ^ (-1 : ℝ)) (y / delta) T / T =
        (p : ℝ) ^ (-(1 + z * epsilon)) := by
    rw [hmass, div_eq_mul_inv, ← Real.rpow_neg hp.le]
    change (p : ℝ) ^ (-(1 + y * epsilon)) *
        (p : ℝ) ^ (-(delta * epsilon)) = _
    rw [← Real.rpow_add hp]
    congr 1
    dsimp [delta, y]
    ring
  have hleft' :
      (p : ℝ) ^ (-(1 + y * epsilon)) * T =
        (p : ℝ) ^ (-(1 + x * epsilon)) := by
    simpa [hmass] using hleft
  have hright' :
      (p : ℝ) ^ (-(1 + y * epsilon)) / T =
        (p : ℝ) ^ (-(1 + z * epsilon)) := by
    simpa [hmass] using hright
  rw [squarefreeMobiusPrimeCellGramSq, bernoulliMidpointGramSq, hmass, hleft', hright']

/-- On every positive nontrivial aperture path, each literal prime cell leaves saturation at every
positive finite temperature and returns only at an endpoint. -/
theorem squarefreeMobiusPrimeCellGramSq_mem_Ioo_zero_one
    (p : Nat.Primes) {epsilon x z : ℝ}
    (hepsilon : 0 < epsilon) (hxz : x < z) :
    squarefreeMobiusPrimeCellGramSq p epsilon x z ∈ Ioo 0 1 := by
  let delta := (z - x) / 2
  let y := (x + z) / 2
  let T := (p : ℝ) ^ (delta * epsilon)
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hT : 1 < T := by
    exact Real.one_lt_rpow hp (mul_pos hdelta hepsilon)
  have hmass : 0 <
      thermalBernoulliMidpointMass ((p : ℝ) ^ (-1 : ℝ)) (y / delta) T := by
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one hT) _)
  rw [squarefreeMobiusPrimeCellGramSq_eq_bernoulliMidpointGramSq p
    (ne_of_lt hxz)]
  exact bernoulliMidpointGramSq_mem_Ioo_zero_one hmass hT

/-- Conditional peak ordering in literal prime labels.  Existence is analytic; once peaks are
present, larger primes peak strictly closer to the critical boundary in thermal-ratio order. -/
theorem squarefreeMobiusPrimeCellPeak_ordered
    {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) {r Tp Tq : ℝ} (hr : 1 < r)
    (hTp : (r + 1) / (r - 1) < Tp)
    (hTq : (r + 1) / (r - 1) < Tq)
    (hp : thermalBernoulliPeakBalance ((p : ℝ) ^ (-1 : ℝ)) r Tp = 0)
    (hq : thermalBernoulliPeakBalance ((q : ℝ) ^ (-1 : ℝ)) r Tq = 0) :
    Tq < Tp := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast q.prop.pos
  have hpqr : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hinv : (q : ℝ) ^ (-1 : ℝ) < (p : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, Real.rpow_neg_one]
    simpa [one_div] using one_div_lt_one_div_of_lt hp0 hpqr
  exact thermalBernoulliPeak_strictMono_odds
    (Real.rpow_pos_of_pos hq0 _) hinv hr hTq hTp hq hp

end

end RHTower.HedenmalmThetaSource
