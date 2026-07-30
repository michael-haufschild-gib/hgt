import GaloisForLFunctions.RHTower.CCMRectangularNegativeChannelSpectrum
import Mathlib.NumberTheory.LSeries.Convergence

/-!
# Exact Dirichlet abscissa of the negative fixed-window Weil carrier

For every fixed positive rectangular window and every admissible tail, the absolute-convergence
abscissa of the nonnegative Dirichlet series formed from the actual negative Weil mass is an
intrinsic horizontal-divisor invariant.

* under RH the coefficient sequence vanishes, so its abscissa is `-infinity`;
* under false RH its abscissa is exactly `1 + xiRightTransverseSup`;
* every nonnegative exact split has maximum channel abscissa equal to the same number;
* a positive majorant, or a positive two-channel cover, with shifted Dirichlet energy is enough
  to force the corresponding horizontal zero-free region.

Thus the transverse exponent cannot be diluted between positive principal/residual channels.
No pointwise equality is needed in the source-facing direction: domination suffices.
-/

open Complex Filter Function Set LSeries

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000

/-- The fixed-window negative-mass coefficient sequence, regarded as complex coefficients. -/
def xiRectangularWeilTailNegativeDirichletCoefficient
    (L : ℝ) (N : ℕ) (n : ℕ) : ℂ :=
  ((xiRectangularWeilTailNegativePart L N n : ℝ) : ℂ)

/-- The right transverse supremum is nonnegative, including the empty right-divisor case. -/
theorem xiRightTransverseSup_nonneg : 0 ≤ xiRightTransverseSup := by
  by_cases hne : Nonempty XiRightZeroCopy
  · exact (xiRightTransverseSup_pos hne).le
  · letI : IsEmpty XiRightZeroCopy := ⟨fun q => hne ⟨q⟩⟩
    rw [xiRightTransverseSup, xiRightTransverseSet]
    have hrange : Set.range (fun q : XiRightZeroCopy =>
        (xiRightCenteredZero q).re) = ∅ := Set.range_eq_empty_iff.mpr inferInstance
    rw [hrange, Real.sSup_empty]

/-- The actual negative mass and the zero channel form an exact positive split. -/
theorem xiRectangular_negativePart_self_zero_split (L : ℝ) (N : ℕ) :
    XiRectangularNegativeChannelSplit L N
      (xiRectangularWeilTailNegativePart L N) 0 := by
  intro n
  exact ⟨xiRectangularWeilTailNegativePart_nonneg L N n, le_rfl, by simp⟩

/-- **Intrinsic negative-energy spectrum.**  The transverse divisor exponent is at most `alpha`
if and only if the actual negative-mass Dirichlet series converges at every real abscissa
strictly larger than `1 + alpha`. -/
theorem xiRightTransverseSup_le_iff_negativePartEnergyAbove
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    xiRightTransverseSup ≤ alpha ↔
      XiRectangularNegativeChannelEnergyAbove alpha
        (xiRectangularWeilTailNegativePart L N) := by
  let hsplit := xiRectangular_negativePart_self_zero_split L N
  constructor
  · intro hsup
    exact ((xiRightTransverseSup_le_iff_negativeChannelSpectrum
      hL halpha hN hsplit).mp hsup).1
  · intro henergy
    apply (xiRightTransverseSup_le_iff_negativeChannelSpectrum
      hL halpha hN hsplit).mpr
    refine ⟨henergy, ?_⟩
    intro delta _hdelta
    refine ⟨0, le_rfl, fun n => ?_⟩
    simp only [Pi.zero_apply, zero_mul]
    exact le_rfl

/-- One real point of convergence bounds the transverse supremum by that abscissa minus one. -/
theorem xiRightTransverseSup_le_sub_one_of_negativePart_summable
    {L sigma : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hsigma : 1 < sigma)
    (hsum : LSeriesSummable
      (xiRectangularWeilTailNegativeDirichletCoefficient L N)
      (sigma : ℂ)) :
    xiRightTransverseSup ≤ sigma - 1 := by
  apply (xiRightTransverseSup_le_iff_negativePartEnergyAbove
    hL (by linarith) hN).mpr
  intro epsilon hepsilon
  apply hsum.of_re_le_re
  simp only [ofReal_re]
  linarith

/-- Above `1 + xiRightTransverseSup`, the negative-mass Dirichlet series always converges. -/
theorem xiRectangularNegativePart_summable_above_transverseSup
    {L sigma : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hsigma : 1 + xiRightTransverseSup < sigma) :
    LSeriesSummable
      (xiRectangularWeilTailNegativeDirichletCoefficient L N)
      (sigma : ℂ) := by
  have henergy :=
    (xiRightTransverseSup_le_iff_negativePartEnergyAbove
      hL xiRightTransverseSup_nonneg hN).mp le_rfl
  let epsilon : ℝ := sigma - (1 + xiRightTransverseSup)
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have hsum := henergy epsilon hepsilon
  have harg : 1 + xiRightTransverseSup + epsilon = sigma := by
    dsimp only [epsilon]
    ring
  simpa only [harg] using! hsum

/-- The negative-mass series diverges at every real abscissa strictly between one and
`1 + xiRightTransverseSup`.  The hypotheses themselves force a positive transverse supremum. -/
theorem not_xiRectangularNegativePart_summable_below_transverseSup
    {L sigma : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hone : 1 < sigma)
    (hbelow : sigma < 1 + xiRightTransverseSup) :
    ¬ LSeriesSummable
      (xiRectangularWeilTailNegativeDirichletCoefficient L N)
      (sigma : ℂ) := by
  intro hsum
  have hsup := xiRightTransverseSup_le_sub_one_of_negativePart_summable
    hL hN hone hsum
  linarith

/-- The negative-mass Dirichlet abscissa is at most the shifted transverse supremum. -/
theorem xiRectangularNegativePart_abscissa_le_transverseSup
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (xiRectangularWeilTailNegativeDirichletCoefficient L N) ≤
      ((1 + xiRightTransverseSup : ℝ) : EReal) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro sigma hsigma
  exact xiRectangularNegativePart_summable_above_transverseSup hL hN hsigma

/-- Under false RH, no smaller absolute-convergence abscissa is possible. -/
theorem transverseSup_le_xiRectangularNegativePart_abscissa_of_not_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis) :
    ((1 + xiRightTransverseSup : ℝ) : EReal) ≤
      LSeries.abscissaOfAbsConv
        (xiRectangularWeilTailNegativeDirichletCoefficient L N) := by
  by_contra hnotle
  have habslt :
      LSeries.abscissaOfAbsConv
          (xiRectangularWeilTailNegativeDirichletCoefficient L N) <
        ((1 + xiRightTransverseSup : ℝ) : EReal) :=
    lt_of_not_ge hnotle
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot
  have hone : ((1 : ℝ) : EReal) <
      ((1 + xiRightTransverseSup : ℝ) : EReal) := by
    exact_mod_cast (by linarith [xiRightTransverseSup_pos hne] :
      (1 : ℝ) < 1 + xiRightTransverseSup)
  have hmax :
      max
          (LSeries.abscissaOfAbsConv
            (xiRectangularWeilTailNegativeDirichletCoefficient L N))
          ((1 : ℝ) : EReal) <
        ((1 + xiRightTransverseSup : ℝ) : EReal) :=
    max_lt habslt hone
  obtain ⟨sigma, hmaxSigma, hsigmaBelow⟩ :=
    EReal.exists_between_coe_real hmax
  have habsSigma :
      LSeries.abscissaOfAbsConv
          (xiRectangularWeilTailNegativeDirichletCoefficient L N) <
        (sigma : EReal) :=
    (le_max_left _ _).trans_lt hmaxSigma
  have honeSigma : (1 : ℝ) < sigma := by
    exact_mod_cast ((le_max_right
      (LSeries.abscissaOfAbsConv
        (xiRectangularWeilTailNegativeDirichletCoefficient L N))
      ((1 : ℝ) : EReal)).trans_lt hmaxSigma)
  have hsigmaTransverse : sigma < 1 + xiRightTransverseSup := by
    exact_mod_cast hsigmaBelow
  have hsum : LSeriesSummable
      (xiRectangularWeilTailNegativeDirichletCoefficient L N)
      (sigma : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa only [ofReal_re] using habsSigma)
  exact (not_xiRectangularNegativePart_summable_below_transverseSup
    hL hN honeSigma hsigmaTransverse) hsum

/-- **Exact abscissa theorem.**  Under false RH, every fixed positive window and admissible tail
has negative-mass absolute-convergence abscissa exactly `1 + xiRightTransverseSup`. -/
theorem xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis) :
    LSeries.abscissaOfAbsConv
        (xiRectangularWeilTailNegativeDirichletCoefficient L N) =
      ((1 + xiRightTransverseSup : ℝ) : EReal) := by
  exact le_antisymm
    (xiRectangularNegativePart_abscissa_le_transverseSup hL hN)
    (transverseSup_le_xiRectangularNegativePart_abscissa_of_not_rh hL hN hnot)

/-- Under RH, the negative carrier is identically zero and its absolute-convergence abscissa is
`-infinity`. -/
theorem xiRectangularNegativePart_abscissa_eq_bot_of_rh
    {L : ℝ} (hL : 0 < L) (N : ℕ)
    (hRH : RiemannHypothesis) :
    LSeries.abscissaOfAbsConv
        (xiRectangularWeilTailNegativeDirichletCoefficient L N) = ⊥ := by
  have hcoeff : xiRectangularWeilTailNegativeDirichletCoefficient L N = 0 := by
    funext n
    simp only [xiRectangularWeilTailNegativeDirichletCoefficient,
      xiRectangularWeilTailNegativePart_eq_zero_of_riemannHypothesis hL hRH,
      ofReal_zero, Pi.zero_apply]
  rw [hcoeff]
  apply le_antisymm
  · apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
    intro sigma _hsigma
    exact LSeriesSummable_zero
  · exact bot_le

/-- Full unconditional dichotomy for the negative-mass abscissa. -/
theorem xiRectangularNegativePart_abscissa_dichotomy
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    (RiemannHypothesis ∧
        LSeries.abscissaOfAbsConv
          (xiRectangularWeilTailNegativeDirichletCoefficient L N) = ⊥) ∨
      (¬ RiemannHypothesis ∧
        LSeries.abscissaOfAbsConv
          (xiRectangularWeilTailNegativeDirichletCoefficient L N) =
            ((1 + xiRightTransverseSup : ℝ) : EReal)) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl ⟨hRH,
      xiRectangularNegativePart_abscissa_eq_bot_of_rh hL N hRH⟩
  · exact Or.inr ⟨hRH,
      xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh
        hL hN hRH⟩

/-- **Window--tail universality.**  The negative-mass absolute-convergence abscissa is independent
of the positive rectangular width and of the admissible deleted prefix. -/
theorem xiRectangularNegativePart_abscissa_independent_of_window_tail
    {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    {N₁ N₂ : ℕ}
    (hN₁ : ∀ n : ℕ, N₁ ≤ n →
      1 ≤ n ∧ L₁ ≤ Real.log n / 2)
    (hN₂ : ∀ n : ℕ, N₂ ≤ n →
      1 ≤ n ∧ L₂ ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (xiRectangularWeilTailNegativeDirichletCoefficient L₁ N₁) =
      LSeries.abscissaOfAbsConv
        (xiRectangularWeilTailNegativeDirichletCoefficient L₂ N₂) := by
  by_cases hRH : RiemannHypothesis
  · rw [xiRectangularNegativePart_abscissa_eq_bot_of_rh hL₁ N₁ hRH,
      xiRectangularNegativePart_abscissa_eq_bot_of_rh hL₂ N₂ hRH]
  · rw [xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh
        hL₁ hN₁ hRH,
      xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh
        hL₂ hN₂ hRH]

/-! ## Exact positive-split conservation -/

/-- At every real abscissa, a nonnegative exact split is summable exactly when both channels
are summable. -/
theorem negativeChannelSplit_summable_iff
    {L sigma : ℝ} {N : ℕ} {a b : ℕ → ℝ}
    (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    LSeriesSummable
        (xiRectangularWeilTailNegativeDirichletCoefficient L N) (sigma : ℂ) ↔
      LSeriesSummable (fun n => ((a n : ℝ) : ℂ)) (sigma : ℂ) ∧
        LSeriesSummable (fun n => ((b n : ℝ) : ℂ)) (sigma : ℂ) := by
  constructor
  · intro hsum
    constructor
    · apply LSeriesSummable_of_nonneg_of_le
        (fun n => (hsplit n).1)
        (xiRectangularWeilTailNegativePart_nonneg L N)
        (fun n => by have hs := hsplit n; linarith)
        hsum
    · apply LSeriesSummable_of_nonneg_of_le
        (fun n => (hsplit n).2.1)
        (xiRectangularWeilTailNegativePart_nonneg L N)
        (fun n => by have hs := hsplit n; linarith)
        hsum
  · rintro ⟨ha, hb⟩
    have hcoeff : xiRectangularWeilTailNegativeDirichletCoefficient L N =
        (fun n => ((a n : ℝ) : ℂ)) + (fun n => ((b n : ℝ) : ℂ)) := by
      funext n
      simp only [xiRectangularWeilTailNegativeDirichletCoefficient,
        Pi.add_apply, ← ofReal_add, (hsplit n).2.2]
    rw [hcoeff]
    exact ha.add hb

private theorem abscissaOfAbsConv_le_of_real_summability_imp
    {f g : ℕ → ℂ}
    (h : ∀ sigma : ℝ, LSeriesSummable g (sigma : ℂ) →
      LSeriesSummable f (sigma : ℂ)) :
    LSeries.abscissaOfAbsConv f ≤ LSeries.abscissaOfAbsConv g := by
  unfold LSeries.abscissaOfAbsConv
  apply sInf_le_sInf
  rintro y ⟨sigma, hsigma, rfl⟩
  exact ⟨sigma, h sigma hsigma, rfl⟩

/-- **Positive-channel abscissa conservation.**  The abscissa of the total negative carrier is
the maximum of the abscissae of any two nonnegative exact channels. -/
theorem negativeChannelSplit_abscissa_eq_max
    {L : ℝ} {N : ℕ} {a b : ℕ → ℝ}
    (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    LSeries.abscissaOfAbsConv
        (xiRectangularWeilTailNegativeDirichletCoefficient L N) =
      max
        (LSeries.abscissaOfAbsConv (fun n => ((a n : ℝ) : ℂ)))
        (LSeries.abscissaOfAbsConv (fun n => ((b n : ℝ) : ℂ))) := by
  apply le_antisymm
  · have hcoeff : xiRectangularWeilTailNegativeDirichletCoefficient L N =
        (fun n => ((a n : ℝ) : ℂ)) + (fun n => ((b n : ℝ) : ℂ)) := by
      funext n
      simp only [xiRectangularWeilTailNegativeDirichletCoefficient,
        Pi.add_apply, ← ofReal_add, (hsplit n).2.2]
    rw [hcoeff]
    exact LSeries.abscissaOfAbsConv_binop_le
      (fun _ha _hb => _ha.add _hb) _ _
  · apply max_le
    · apply abscissaOfAbsConv_le_of_real_summability_imp
      intro sigma hsum
      exact (negativeChannelSplit_summable_iff hsplit).mp hsum |>.1
    · apply abscissaOfAbsConv_le_of_real_summability_imp
      intro sigma hsum
      exact (negativeChannelSplit_summable_iff hsplit).mp hsum |>.2

/-- Under false RH, every exact positive split pays the full shifted transverse abscissa in at
least one channel. -/
theorem negativeChannelSplit_max_abscissa_eq_transverseSup_of_not_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis)
    {a b : ℕ → ℝ}
    (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    max
        (LSeries.abscissaOfAbsConv (fun n => ((a n : ℝ) : ℂ)))
        (LSeries.abscissaOfAbsConv (fun n => ((b n : ℝ) : ℂ))) =
      ((1 + xiRightTransverseSup : ℝ) : EReal) := by
  rw [← negativeChannelSplit_abscissa_eq_max hsplit]
  exact xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh
    hL hN hnot

/-- The maximum positive-channel abscissa is universal across windows, cutoffs, and exact
positive allocations. -/
theorem negativeChannelSplit_max_abscissa_independent
    {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    {N₁ N₂ : ℕ}
    (hN₁ : ∀ n : ℕ, N₁ ≤ n →
      1 ≤ n ∧ L₁ ≤ Real.log n / 2)
    (hN₂ : ∀ n : ℕ, N₂ ≤ n →
      1 ≤ n ∧ L₂ ≤ Real.log n / 2)
    {a₁ b₁ a₂ b₂ : ℕ → ℝ}
    (hsplit₁ : XiRectangularNegativeChannelSplit L₁ N₁ a₁ b₁)
    (hsplit₂ : XiRectangularNegativeChannelSplit L₂ N₂ a₂ b₂) :
    max
        (LSeries.abscissaOfAbsConv (fun n => ((a₁ n : ℝ) : ℂ)))
        (LSeries.abscissaOfAbsConv (fun n => ((b₁ n : ℝ) : ℂ))) =
      max
        (LSeries.abscissaOfAbsConv (fun n => ((a₂ n : ℝ) : ℂ)))
        (LSeries.abscissaOfAbsConv (fun n => ((b₂ n : ℝ) : ℂ))) := by
  rw [← negativeChannelSplit_abscissa_eq_max hsplit₁,
    ← negativeChannelSplit_abscissa_eq_max hsplit₂]
  exact xiRectangularNegativePart_abscissa_independent_of_window_tail
    hL₁ hL₂ hN₁ hN₂

/-! ## Source-facing domination criteria -/

/-- A nonnegative source majorant of the actual negative mass with shifted Dirichlet energy. -/
def XiRectangularNegativeEnergyMajorantAbove
    (L : ℝ) (N : ℕ) (alpha : ℝ) (m : ℕ → ℝ) : Prop :=
  (∀ n : ℕ,
    0 ≤ m n ∧ xiRectangularWeilTailNegativePart L N n ≤ m n) ∧
  XiRectangularNegativeChannelEnergyAbove alpha m

/-- **Order-ideal spectrum.**  Exact source identification is unnecessary for the estimate:
the horizontal bound is equivalent to the existence of any positive shifted-energy majorant of
the actual negative mass. -/
theorem xiRightTransverseSup_le_iff_exists_negativeEnergyMajorantAbove
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    xiRightTransverseSup ≤ alpha ↔
      ∃ m : ℕ → ℝ, XiRectangularNegativeEnergyMajorantAbove L N alpha m := by
  constructor
  · intro hsup
    refine ⟨xiRectangularWeilTailNegativePart L N, ?_, ?_⟩
    · exact fun n => ⟨xiRectangularWeilTailNegativePart_nonneg L N n, le_rfl⟩
    · exact (xiRightTransverseSup_le_iff_negativePartEnergyAbove
        hL halpha hN).mp hsup
  · rintro ⟨m, hm, hmEnergy⟩
    apply (xiRightTransverseSup_le_iff_negativePartEnergyAbove
      hL halpha hN).mpr
    intro epsilon hepsilon
    exact LSeriesSummable_of_nonneg_of_le
      (xiRectangularWeilTailNegativePart_nonneg L N)
      (fun n => (hm n).1)
      (fun n => (hm n).2)
      (hmEnergy epsilon hepsilon)

/-- A positive two-channel source cover of the actual negative mass.  Unlike an exact split, the
two channels may overestimate the target. -/
def XiRectangularNegativeTwoChannelCover
    (L : ℝ) (N : ℕ) (a b : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    0 ≤ a n ∧ 0 ≤ b n ∧
      xiRectangularWeilTailNegativePart L N n ≤ a n + b n

/-- **Source-consumable two-channel spectrum.**  A horizontal zero-free region is equivalent to
the existence of a positive principal/residual cover in which both channels have shifted
Dirichlet energy. -/
theorem xiRightTransverseSup_le_iff_exists_twoChannelEnergyCoverAbove
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    xiRightTransverseSup ≤ alpha ↔
      ∃ a b : ℕ → ℝ,
        XiRectangularNegativeTwoChannelCover L N a b ∧
        XiRectangularNegativeChannelEnergyAbove alpha a ∧
        XiRectangularNegativeChannelEnergyAbove alpha b := by
  constructor
  · intro hsup
    refine ⟨xiRectangularWeilTailNegativePart L N, 0, ?_, ?_, ?_⟩
    · intro n
      simp only [Pi.zero_apply, add_zero]
      exact ⟨xiRectangularWeilTailNegativePart_nonneg L N n, le_rfl, le_rfl⟩
    · exact (xiRightTransverseSup_le_iff_negativePartEnergyAbove
        hL halpha hN).mp hsup
    · intro epsilon _hepsilon
      exact LSeriesSummable_zero
  · rintro ⟨a, b, hcover, haEnergy, hbEnergy⟩
    apply (xiRightTransverseSup_le_iff_negativePartEnergyAbove
      hL halpha hN).mpr
    intro epsilon hepsilon
    have hab : LSeriesSummable
        ((fun n => ((a n : ℝ) : ℂ)) + (fun n => ((b n : ℝ) : ℂ)))
        (((1 + alpha + epsilon : ℝ) : ℂ)) :=
      (haEnergy epsilon hepsilon).add (hbEnergy epsilon hepsilon)
    have hsum : LSeriesSummable
        (fun n => (((a n + b n : ℝ) : ℝ) : ℂ))
        (((1 + alpha + epsilon : ℝ) : ℂ)) := by
      simpa only [Pi.add_apply, ofReal_add] using! hab
    exact LSeriesSummable_of_nonneg_of_le
      (xiRectangularWeilTailNegativePart_nonneg L N)
      (fun n => add_nonneg (hcover n).1 (hcover n).2.1)
      (fun n => (hcover n).2.2)
      hsum

end

end RHTower
