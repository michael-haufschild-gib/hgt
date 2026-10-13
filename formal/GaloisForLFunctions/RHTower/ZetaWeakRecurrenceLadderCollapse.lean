import GaloisForLFunctions.RHTower.ZetaStrongRecurrenceReceiver
import GaloisForLFunctions.RHTower.ZerosApproachLineLowerSideLag
import GaloisForLFunctions.RHTower.GaussianCentralGapLargeHeightFiniteOffLine

/-!
# Weak self-recurrence of `ζ` collapses the large-height ladder

For a closed disc `K` in the strip `½ < Re s < 1` and `ε > 0`, a *return shift* is a `τ` with
`sup_K |ζ(s + iτ) − ζ(s)| < ε` (`zetaReturnSet`).  Bagchi's strong recurrence asks for return
shifts of positive density and implies RH; around an off-line zero the return shifts in fact have
density zero (`exists_zetaSelfReturn_density_zero`).  Here we only ask for return shifts beyond
every height (`ZetaWeaklyRecurrent`), with no density.

* **Transport** (`exists_zeta_zero_far_of_weaklyRecurrent`).  Under weak recurrence, for every zero
  `ρ₀` with `½ < Re ρ₀ < 1` and every `δ > 0` there are zeros `w` of `ζ` with `Re w > Re ρ₀ − δ`,
  `Re w < 1` and arbitrarily large ordinate.  A return shift moves the zero by the minimum modulus
  principle (`exists_zero_of_mem_zetaReturnSet`) on an isolating disc of radius `≤ δ`.
* **The asymptotic abscissa is the abscissa** (`finite_re_gt_iff_forall_re_le_of_weaklyRecurrent`).
  Under weak recurrence, for every `h ≥ 0` only finitely many zeros have `Re ρ > ½ + h` iff none
  does.

**Theorem** (`riemannHypothesis_iff_zerosApproachLine_of_weaklyRecurrent`,
`riemannHypothesis_iff_finiteOffLine_of_weaklyRecurrent`,
`riemannHypothesis_iff_eventualHadamardPositivity_of_weaklyRecurrent`).  Under weak recurrence, RH,
finitely many off-line zeros and zeros approaching the line are equivalent; so is eventual
Hadamard positivity.  Every height-local receiver whose large-height form reads the asymptotic
abscissa then reads the global abscissa
(`eventualHadamardPositivityRight_iff_forall_re_le_of_weaklyRecurrent`,
`eventualFilteredCentralGapRate_iff_filteredCentralGapRate_of_weaklyRecurrent`), and the bounded
large-height Gaussian central-gap budget is RH
(`riemannHypothesis_iff_eventualFilteredCentralGapBudget_of_weaklyRecurrent`).

**Interface** (`AsymptoticAbscissaLaw`,
`riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`).  Call *asymptotic
abscissa law* the statement that for every `h ≥ 0` finitely many zeros right of `½ + h` means no
zero right of `½ + h`, i.e. the limit superior of `Re ρ − ½` along growing heights equals its
supremum.  Then RH ⟺ ZAL ∧ the asymptotic abscissa law, and weak recurrence implies the law
(`asymptoticAbscissaLaw_of_weaklyRecurrent`).

**Equivalence** (`riemannHypothesis_iff_zerosApproachLine_and_zeroDiscWeaklyRecurrent`).  Only
discs around off-line zeros are used (`ZetaZeroDiscWeaklyRecurrent`), and that condition is vacuous
under RH.  So RH ⟺ ZAL ∧ weak recurrence around off-line zeros.

So weak self-recurrence is exactly the input that makes the large-height ladder
RH ⟹ FOL ⟹ ZAL collapse: the large-height receivers forget the zeros of bounded height, and weak
recurrence copies every off-line zero to unbounded heights.  It is implied by Bagchi's strong
recurrence (`ZetaDiscRecurrent.zetaWeaklyRecurrent`), and, unlike it, it is not refuted by the
density-zero law around off-line zeros.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

open BacklundConverse LindelofSparse

/-- **Weak self-recurrence of `ζ`.**  For every closed disc in `½ < Re s < 1` and every `ε > 0`,
return shifts exist beyond every height. -/
def ZetaWeaklyRecurrent : Prop :=
  ∀ (c : ℂ) (r : ℝ), 0 < r → (∀ s ∈ closedBall c r, 1 / 2 < s.re ∧ s.re < 1) → ∀ ε > 0,
    ∀ T₀ : ℝ, ∃ τ : ℝ, T₀ ≤ τ ∧ τ ∈ zetaReturnSet (closedBall c r) ε

/-- **Weak self-recurrence around off-line zeros.**  For every zero `ρ₀` with `½ < Re ρ₀ < 1`, every
closed disc around `ρ₀` in the strip and every `ε > 0`, return shifts exist beyond every height.
Under RH there is no such zero, so the condition holds vacuously. -/
def ZetaZeroDiscWeaklyRecurrent : Prop :=
  ∀ ρ₀ : ℂ, riemannZeta ρ₀ = 0 → 1 / 2 < ρ₀.re → ρ₀.re < 1 → ∀ r : ℝ, 0 < r →
    (∀ s ∈ closedBall ρ₀ r, 1 / 2 < s.re ∧ s.re < 1) → ∀ ε > 0,
      ∀ T₀ : ℝ, ∃ τ : ℝ, T₀ ≤ τ ∧ τ ∈ zetaReturnSet (closedBall ρ₀ r) ε

theorem ZetaWeaklyRecurrent.zeroDisc (h : ZetaWeaklyRecurrent) : ZetaZeroDiscWeaklyRecurrent :=
  fun ρ₀ _ _ _ r hr hK ε hε T₀ => h ρ₀ r hr hK ε hε T₀

/-- **Disc recurrence (positive upper density) implies weak recurrence.** -/
theorem ZetaDiscRecurrent.zetaWeaklyRecurrent (h : ZetaDiscRecurrent) : ZetaWeaklyRecurrent := by
  intro c r hr hK ε hε T₀
  obtain ⟨κ, hκ, hfreq⟩ := h c r hr hK ε hε
  by_contra hno
  push Not at hno
  -- all return shifts lie below `T₀`, so their measure in `[0, T]` is at most `max T₀ 0`
  have hsub : ∀ T : ℝ, zetaReturnSet (closedBall c r) ε ∩ Icc 0 T ⊆ Icc 0 (max T₀ 0) := by
    intro T τ ⟨hτ, hτT⟩
    refine ⟨hτT.1, ?_⟩
    by_contra hgt
    push Not at hgt
    exact (hno τ (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hgt))) hτ
  obtain ⟨T, hT, hTbig⟩ := (hfreq.and_eventually (eventually_gt_atTop ((max T₀ 0 + 1) / κ))).exists
  have hvol := (hT.trans (measure_mono (hsub T))).trans_eq (Real.volume_Icc)
  rw [ENNReal.ofReal_le_ofReal_iff (by have := le_max_right T₀ 0; linarith)] at hvol
  have : max T₀ 0 + 1 < κ * T := by
    rw [div_lt_iff₀ hκ] at hTbig; linarith
  linarith

/-- **An isolating disc of prescribed small radius around an off-line zero.** -/
theorem exists_zetaIsolatingDisc_le {ρ₀ : ℂ} (h1 : 1 / 2 < ρ₀.re) (h2 : ρ₀.re < 1) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ r > 0, r ≤ δ ∧ r ≤ (ρ₀.re - 1 / 2) / 2 ∧ r ≤ (1 - ρ₀.re) / 2 ∧
      ∃ m > 0, ∀ z ∈ sphere ρ₀ r, m ≤ ‖riemannZeta z‖ := by
  have hρ1 : ρ₀ ≠ 1 := by intro h; rw [h] at h2; simp at h2
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have han : AnalyticAt ℂ riemannZeta ρ₀ := hdiff.analyticAt (isOpen_ne.mem_nhds hρ1)
  have hne : ∀ᶠ z in 𝓝[≠] ρ₀, riemannZeta z ≠ 0 := by
    refine han.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h => ?_
    exact analyticOrderAt_riemannZeta_ne_top_of_ne_one hρ1 (analyticOrderAt_eq_top.mpr h)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hne)
  set r := min (min (r₁ / 2) δ) (min ((ρ₀.re - 1 / 2) / 2) ((1 - ρ₀.re) / 2)) with hrdef
  have hr : 0 < r := lt_min (lt_min (by linarith) hδ) (lt_min (by linarith) (by linarith))
  have hrr₁ : r < r₁ := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hrδ : r ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hr2 : r ≤ (ρ₀.re - 1 / 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ (1 - ρ₀.re) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsph : ∀ z ∈ sphere ρ₀ r, riemannZeta z ≠ 0 ∧ z ≠ 1 := by
    intro z hz
    have hd : dist z ρ₀ = r := mem_sphere.mp hz
    have hzρ : z ≠ ρ₀ := by intro h; rw [h, dist_self] at hd; linarith
    refine ⟨hball (by rw [hd]; exact hrr₁) hzρ, fun h => ?_⟩
    have hre := abs_re_le_norm (z - ρ₀)
    rw [← dist_eq_norm, hd, h, sub_re, one_re] at hre
    have := le_abs_self (1 - ρ₀.re)
    linarith
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere ρ₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    (fun z hz => (differentiableAt_riemannZeta (hsph z hz).2).continuousAt.continuousWithinAt.norm)
  exact ⟨r, hr, hrδ, hr2, hr3, ‖riemannZeta z₁‖, norm_pos_iff.mpr (hsph z₁ hz₁).1,
    fun z hz => hmin hz⟩

/-- **Weak recurrence around an off-line zero transports it to arbitrarily large heights.** -/
theorem exists_zeta_zero_far_of_zeroDiscWeaklyRecurrent (hW : ZetaZeroDiscWeaklyRecurrent)
    {ρ₀ : ℂ} (hρ₀ : riemannZeta ρ₀ = 0) (h1 : 1 / 2 < ρ₀.re) (h2 : ρ₀.re < 1) {δ : ℝ} (hδ : 0 < δ)
    (T₀ : ℝ) :
    ∃ w : ℂ, riemannZeta w = 0 ∧ ρ₀.re - δ < w.re ∧ 1 / 2 < w.re ∧ w.re < 1 ∧ T₀ ≤ w.im := by
  obtain ⟨r, hr, hrδ, hr2, hr3, m, hm0, hm⟩ := exists_zetaIsolatingDisc_le h1 h2 hδ
  have hK : ∀ s ∈ closedBall ρ₀ r, 1 / 2 < s.re ∧ s.re < 1 := by
    intro s hs
    have h := abs_le.mp ((abs_re_le_norm (s - ρ₀)).trans (mem_closedBall_iff_norm.mp hs))
    rw [sub_re] at h
    constructor <;> linarith [h.1, h.2]
  obtain ⟨τ, hτT, hτ⟩ := hW ρ₀ hρ₀ h1 h2 r hr hK (m / 2) (by positivity) (T₀ - ρ₀.im + r)
  obtain ⟨z, hz, hzero⟩ :=
    exists_zero_of_mem_zetaReturnSet hr (fun s hs => (hK s hs).2) hρ₀ hm hτ
  have hzn : ‖z - ρ₀‖ < r := mem_ball_iff_norm.mp hz
  have hre := abs_lt.mp ((abs_re_le_norm (z - ρ₀)).trans_lt hzn)
  have him := abs_lt.mp ((abs_im_le_norm (z - ρ₀)).trans_lt hzn)
  rw [sub_re] at hre
  rw [sub_im] at him
  refine ⟨z + τ * I, hzero, ?_, ?_, ?_, ?_⟩
  · simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    linarith
  · simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    linarith
  · simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    linarith
  · simp only [add_im, mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one]
    linarith

/-- **Weak recurrence transports an off-line zero to arbitrarily large heights.** -/
theorem exists_zeta_zero_far_of_weaklyRecurrent (hW : ZetaWeaklyRecurrent) {ρ₀ : ℂ}
    (hρ₀ : riemannZeta ρ₀ = 0) (h1 : 1 / 2 < ρ₀.re) (h2 : ρ₀.re < 1) {δ : ℝ} (hδ : 0 < δ)
    (T₀ : ℝ) :
    ∃ w : ℂ, riemannZeta w = 0 ∧ ρ₀.re - δ < w.re ∧ 1 / 2 < w.re ∧ w.re < 1 ∧ T₀ ≤ w.im :=
  exists_zeta_zero_far_of_zeroDiscWeaklyRecurrent hW.zeroDisc hρ₀ h1 h2 hδ T₀

/-- A zero of `ζ` in the open strip is a zero copy of `ξ`. -/
theorem exists_xiZeroCopy_of_zeta_eq_zero_strip {w : ℂ} (hw : riemannZeta w = 0) (h0 : 0 < w.re)
    (h1 : w.re < 1) : ∃ q : XiZeroCopy, (q.1 : ℂ) = w := by
  refine exists_xiZeroCopy_of_xi_eq_zero (xi_eq_zero_of_zeta_eq_zero hw ?_ ?_)
  · rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp only [mul_re, neg_re, re_ofNat, add_re, natCast_re, one_re, neg_im, im_ofNat, add_im,
      natCast_im, one_im, add_zero, mul_zero, sub_zero, neg_zero] at this
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h; rw [h, one_re] at h1; exact lt_irrefl 1 h1

/-- **Under weak recurrence around off-line zeros the asymptotic abscissa is the abscissa.** -/
theorem finite_re_gt_iff_forall_re_le_of_zeroDiscWeaklyRecurrent
    (hW : ZetaZeroDiscWeaklyRecurrent) {h : ℝ}
    (hh : 0 ≤ h) :
    {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + h := by
  constructor
  · intro hF q₀
    by_contra hlt
    push Not at hlt
    obtain ⟨H, hH⟩ := (hF.image fun q => |(q.1 : ℂ).im|).bddAbove
    set ρ₀ : ℂ := (q₀.1 : ℂ) with hρ₀def
    have hζ : riemannZeta ρ₀ = 0 := by
      have hxi := xi_xiZeroCopy_eq_zero q₀
      have hne1 : ρ₀ ≠ 1 := by
        intro h1; have := xiZeroCopy_re_lt_one q₀; rw [← hρ₀def, h1, one_re] at this
        exact lt_irrefl 1 this
      exact (xi_eq_zero_iff (by linarith) hne1).mp hxi
    obtain ⟨w, hw0, hwre, hwre', hwre1, hwim⟩ :=
      exists_zeta_zero_far_of_zeroDiscWeaklyRecurrent hW hζ
      (by linarith) (xiZeroCopy_re_lt_one q₀) (δ := ρ₀.re - (1 / 2 + h)) (by linarith) (|H| + 1)
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hw0 (by linarith) hwre1
    have hqF : q ∈ {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re} := by
      simp only [mem_setOf_eq]; rw [hq]; linarith
    have hqH : |(q.1 : ℂ).im| ≤ H := hH ⟨q, hqF, rfl⟩
    rw [hq] at hqH
    have := le_abs_self w.im
    have := le_abs_self H
    linarith
  · intro hall
    refine Set.finite_empty.subset fun q hq => ?_
    simp only [mem_setOf_eq] at hq
    exact absurd (hall q) (not_le.mpr hq)

/-- **Under weak recurrence the asymptotic abscissa is the abscissa.** -/
theorem finite_re_gt_iff_forall_re_le_of_weaklyRecurrent (hW : ZetaWeaklyRecurrent) {h : ℝ}
    (hh : 0 ≤ h) :
    {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + h :=
  finite_re_gt_iff_forall_re_le_of_zeroDiscWeaklyRecurrent hW.zeroDisc hh

/-- **Under weak recurrence, zeros approaching the line force RH.** -/
theorem riemannHypothesis_of_zerosApproachLine_of_weaklyRecurrent (hW : ZetaWeaklyRecurrent)
    (hZ : ZerosApproachLine) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro s hs1 hs2 hs0
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hs0 (by linarith) hs2
  set h : ℝ := (s.re - 1 / 2) / 2 with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  have hall := (finite_re_gt_iff_forall_re_le_of_weaklyRecurrent hW hh0.le).mp
    (finite_re_gt_of_zerosApproachLine hZ hh0) q₀
  rw [hq₀] at hall
  rw [hh] at hall
  linarith

/-- **Under weak recurrence, RH is "zeros approach the line".** -/
theorem riemannHypothesis_iff_zerosApproachLine_of_weaklyRecurrent (hW : ZetaWeaklyRecurrent) :
    RiemannHypothesis ↔ ZerosApproachLine :=
  ⟨zerosApproachLine_of_riemannHypothesis,
    riemannHypothesis_of_zerosApproachLine_of_weaklyRecurrent hW⟩

/-- **Under weak recurrence, RH is "finitely many off-line zeros".** -/
theorem riemannHypothesis_iff_finiteOffLine_of_weaklyRecurrent (hW : ZetaWeaklyRecurrent) :
    RiemannHypothesis ↔ FiniteOffLine := by
  refine ⟨fun hRH => ?_, fun hF => riemannHypothesis_of_zerosApproachLine_of_weaklyRecurrent hW
    (zerosApproachLine_of_finiteOffLine hF)⟩
  refine Set.finite_empty.subset fun q hq => ?_
  have hq' : (xiSpectralPoint q).im ≠ 0 := hq
  apply hq'
  rw [spectral_im_eq, xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q, sub_self]

/-- **Under weak recurrence, RH is eventual Hadamard positivity.** -/
theorem riemannHypothesis_iff_eventualHadamardPositivity_of_weaklyRecurrent
    (hW : ZetaWeaklyRecurrent) : RiemannHypothesis ↔ EventualHadamardPositivity := by
  rw [eventualHadamardPositivity_iff_zerosApproachLine]
  exact riemannHypothesis_iff_zerosApproachLine_of_weaklyRecurrent hW

/-- **Under weak recurrence the large-height Hadamard abscissa is the global one.**  For `h ≥ 0`,
`Re (ξ'/ξ) ≥ 0` on `Re s > ½ + h` above some height iff every zero has `Re ρ ≤ ½ + h`. -/
theorem eventualHadamardPositivityRight_iff_forall_re_le_of_weaklyRecurrent
    (hW : ZetaWeaklyRecurrent) {h : ℝ} (hh : 0 ≤ h) :
    EventualHadamardPositivityRight (1 / 2 + h) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + h := by
  rw [eventualHadamardPositivityRight_iff hh]
  exact finite_re_gt_iff_forall_re_le_of_weaklyRecurrent hW hh

/-- **Under weak recurrence the large-height Gaussian central-gap rate is the all-height rate.** -/
theorem eventualFilteredCentralGapRate_iff_filteredCentralGapRate_of_weaklyRecurrent
    (hW : ZetaWeaklyRecurrent) {h : ℝ} (hh : 0 ≤ h) :
    EventualFilteredCentralGapRate (h + h ^ 2 / 8) ↔ FilteredCentralGapRate (h + h ^ 2 / 8) := by
  rw [eventualFilteredCentralGapRate_iff_finite_re_gt hh, filteredCentralGapRate_iff_re_le hh]
  exact finite_re_gt_iff_forall_re_le_of_weaklyRecurrent hW hh

/-- **Under weak recurrence the bounded large-height Gaussian central-gap budget is RH.** -/
theorem riemannHypothesis_iff_eventualFilteredCentralGapBudget_of_weaklyRecurrent
    (hW : ZetaWeaklyRecurrent) : RiemannHypothesis ↔ EventualFilteredCentralGapBudget := by
  rw [eventualFilteredCentralGapBudget_iff_finiteOffLine]
  exact riemannHypothesis_iff_finiteOffLine_of_weaklyRecurrent hW

/-- **The asymptotic abscissa law.**  For every `h ≥ 0`, finitely many zeros right of `½ + h`
forces no zero right of `½ + h`. -/
def AsymptoticAbscissaLaw : Prop :=
  ∀ h : ℝ, 0 ≤ h → {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite →
    ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + h

/-- Weak recurrence implies the asymptotic abscissa law. -/
theorem asymptoticAbscissaLaw_of_weaklyRecurrent (hW : ZetaWeaklyRecurrent) :
    AsymptoticAbscissaLaw := fun _ hh =>
  (finite_re_gt_iff_forall_re_le_of_weaklyRecurrent hW hh).mp

/-- **RH is "zeros approach the line" plus the asymptotic abscissa law.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw :
    RiemannHypothesis ↔ ZerosApproachLine ∧ AsymptoticAbscissaLaw := by
  constructor
  · intro hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, fun h hh _ q => ?_⟩
    rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q]
    linarith
  · rintro ⟨hZ, hA⟩
    rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
    intro s hs1 hs2 hs0
    obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hs0 (by linarith) hs2
    set h : ℝ := (s.re - 1 / 2) / 2 with hh
    have hh0 : 0 < h := by rw [hh]; linarith
    have hall := hA h hh0.le (finite_re_gt_of_zerosApproachLine hZ hh0) q₀
    rw [hq₀, hh] at hall
    linarith

/-- Weak recurrence around off-line zeros implies the asymptotic abscissa law. -/
theorem asymptoticAbscissaLaw_of_zeroDiscWeaklyRecurrent (hW : ZetaZeroDiscWeaklyRecurrent) :
    AsymptoticAbscissaLaw := fun _ hh =>
  (finite_re_gt_iff_forall_re_le_of_zeroDiscWeaklyRecurrent hW hh).mp

/-- **RH is "zeros approach the line" plus weak recurrence around off-line zeros.**  The second
condition is vacuous under RH. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_zeroDiscWeaklyRecurrent :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ZetaZeroDiscWeaklyRecurrent := by
  constructor
  · intro hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, fun ρ₀ hρ₀ h1 h2 _ _ _ _ _ _ => ?_⟩
    exact absurd hρ₀
      ((riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mp hRH) ρ₀ h1 h2)
  · rintro ⟨hZ, hW⟩
    exact riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨hZ, asymptoticAbscissaLaw_of_zeroDiscWeaklyRecurrent hW⟩

end

end RHTower
