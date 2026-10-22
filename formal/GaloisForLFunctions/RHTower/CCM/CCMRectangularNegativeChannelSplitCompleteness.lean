import GaloisForLFunctions.RHTower.CCM.CCMRectangularSparseExceptionCompleteness

/-!
# Exact positive-channel completeness for one fixed rectangular Weil window

An exceptional set is only an indicator-valued way to allocate the actual negative Weil mass.
The intrinsic statement allows every pointwise nonnegative split

`q^-(n) = a(n) + b(n)`.

For every such split, RH is equivalent to finite Dirichlet energy of `a` on every line strictly
to the right of one together with a subpower envelope for `b`.  Under false RH every positive
allocation fails in at least one of these two channels.  Fractional selectors `omega(n) in [0,1]`
are obtained by taking `a = omega q^-` and `b = (1 - omega) q^-`.
-/

open Complex Filter Function Set LSeries

namespace RHTower

noncomputable section

/-- A positive two-channel allocation of the actual negative mass of a rectangular Weil tail. -/
def XiRectangularNegativeChannelSplit
    (L : ℝ) (N : ℕ) (a b : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    0 ≤ a n ∧ 0 ≤ b n ∧
      xiRectangularWeilTailNegativePart L N n = a n + b n

/-- Dirichlet energy of one nonnegative carrier channel on every real abscissa `1 + epsilon`. -/
def XiRectangularNegativeChannelEnergy (a : ℕ → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable (fun n => ((a n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ))

/-- A nonnegative residual channel is subpower when it has a pointwise `n^delta` envelope for
every positive `delta`. -/
def XiRectangularSubpowerChannel (b : ℕ → ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      b n ≤ C * powerCorrectionCoefficient delta n

private def xiRectangularChannelMajorant
    (a : ℕ → ℝ) (C delta : ℝ) (n : ℕ) : ℝ :=
  a n + C * powerCorrectionCoefficient delta n

private theorem xiRectangularChannelMajorant_nonneg
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {C delta : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ xiRectangularChannelMajorant a C delta n := by
  exact add_nonneg (ha n)
    (mul_nonneg hC (powerCorrectionCoefficient_nonneg delta n))

private theorem xiRectangularChannelMajorant_LSeriesSummable
    {a : ℕ → ℝ} (ha : XiRectangularNegativeChannelEnergy a)
    {epsilon C delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 1 + delta < 1 + epsilon) :
    LSeriesSummable
      (fun n => ((xiRectangularChannelMajorant a C delta n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) := by
  have hpower := powerCorrectionCoefficient_LSeriesSummable
    (alpha := delta) (s := (((1 + epsilon : ℝ) : ℂ))) (by
      simpa only [ofReal_re] using hdelta)
  have hadd := (ha epsilon hepsilon).add (hpower.smul (C : ℂ))
  change Summable (LSeries.term
    (fun n => ((xiRectangularChannelMajorant a C delta n : ℝ) : ℂ))
    (((1 + epsilon : ℝ) : ℂ)))
  change Summable (LSeries.term _ (((1 + epsilon : ℝ) : ℂ))) at hadd
  exact hadd.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        xiRectangularChannelMajorant, ofReal_add, ofReal_mul]

private theorem xiRectangularWeilTailNegativePart_le_channelMajorant
    {L : ℝ} {N : ℕ} {a b : ℕ → ℝ}
    (hsplit : XiRectangularNegativeChannelSplit L N a b)
    {C delta : ℝ}
    (hb : ∀ n, b n ≤ C * powerCorrectionCoefficient delta n) :
    ∀ n, xiRectangularWeilTailNegativePart L N n ≤
      xiRectangularChannelMajorant a C delta n := by
  intro n
  rw [(hsplit n).2.2]
  simpa only [xiRectangularChannelMajorant, add_comm] using
    add_le_add_left (hb n) (a n)

/-- **Exact positive-channel carrier theorem.**  For every nonnegative pointwise split of the
actual negative rectangular Weil mass, RH is equivalent to finite Dirichlet energy in the first
channel and a subpower envelope in the second. -/
theorem riemannHypothesis_iff_negativeChannelEnergy_and_subpowerChannel
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {a b : ℕ → ℝ}
    (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    RiemannHypothesis ↔
      XiRectangularNegativeChannelEnergy a ∧
        XiRectangularSubpowerChannel b := by
  constructor
  · intro hRH
    have hzero : ∀ n, xiRectangularWeilTailNegativePart L N n = 0 :=
      xiRectangularWeilTailNegativePart_eq_zero_of_riemannHypothesis hL hRH N
    have haZero : a = 0 := by
      funext n
      have hs := hsplit n
      have hz := hzero n
      simp only [Pi.zero_apply]
      linarith
    have hbZero : b = 0 := by
      funext n
      have hs := hsplit n
      have hz := hzero n
      simp only [Pi.zero_apply]
      linarith
    constructor
    · rw [haZero]
      intro epsilon hepsilon
      exact LSeriesSummable_zero
    · rw [hbZero]
      intro delta hdelta
      refine ⟨0, le_rfl, fun n => ?_⟩
      simp only [Pi.zero_apply, zero_mul]
      exact le_rfl
  · rintro ⟨haEnergy, hbSubpower⟩
    apply riemannHypothesis_of_xiRectangularWeilTailNegativePartEnergy hL hN
    intro epsilon hepsilon
    let delta := epsilon / 2
    have hdelta : 0 < delta := by dsimp only [delta]; linarith
    obtain ⟨C, hC, hb⟩ := hbSubpower delta hdelta
    apply LSeriesSummable_of_nonneg_of_le
      (xiRectangularWeilTailNegativePart_nonneg L N)
      (xiRectangularChannelMajorant_nonneg (fun n => (hsplit n).1) hC)
      (xiRectangularWeilTailNegativePart_le_channelMajorant hsplit hb)
    apply xiRectangularChannelMajorant_LSeriesSummable haEnergy hepsilon
    dsimp only [delta]
    linarith

/-- **Universal positive-channel dichotomy under false RH.**  Every nonnegative allocation of
the negative Weil mass exposes either a non-subpower residual channel or divergent Dirichlet
energy in the complementary channel. -/
theorem negativeChannelDichotomy_of_not_riemannHypothesis
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis)
    {a b : ℕ → ℝ}
    (hsplit : XiRectangularNegativeChannelSplit L N a b) :
    ¬ XiRectangularSubpowerChannel b ∨
      ∃ epsilon : ℝ, 0 < epsilon ∧
        ¬ LSeriesSummable (fun n => ((a n : ℝ) : ℂ))
          (((1 + epsilon : ℝ) : ℂ)) := by
  by_cases hb : XiRectangularSubpowerChannel b
  · right
    by_contra hdiv
    push Not at hdiv
    have ha : XiRectangularNegativeChannelEnergy a := by
      intro epsilon hepsilon
      exact hdiv epsilon hepsilon
    exact hnot
      ((riemannHypothesis_iff_negativeChannelEnergy_and_subpowerChannel
        hL hN hsplit).mpr ⟨ha, hb⟩)
  · exact Or.inl hb

/-! ## Fractional allocations -/

/-- The fraction of the negative Weil mass assigned to a selector `omega`. -/
def xiRectangularWeightedNegativeChannel
    (L : ℝ) (N : ℕ) (omega : ℕ → ℝ) (n : ℕ) : ℝ :=
  omega n * xiRectangularWeilTailNegativePart L N n

/-- The complementary fraction of the negative Weil mass. -/
def xiRectangularComplementaryNegativeChannel
    (L : ℝ) (N : ℕ) (omega : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 - omega n) * xiRectangularWeilTailNegativePart L N n

theorem xiRectangular_fractional_negativeChannelSplit
    (L : ℝ) (N : ℕ) (omega : ℕ → ℝ)
    (homega : ∀ n, 0 ≤ omega n ∧ omega n ≤ 1) :
    XiRectangularNegativeChannelSplit L N
      (xiRectangularWeightedNegativeChannel L N omega)
      (xiRectangularComplementaryNegativeChannel L N omega) := by
  intro n
  have hq := xiRectangularWeilTailNegativePart_nonneg L N n
  have hw := homega n
  constructor
  · exact mul_nonneg hw.1 hq
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hw.2) hq
  · dsimp only [xiRectangularWeightedNegativeChannel,
      xiRectangularComplementaryNegativeChannel]
    ring

/-- **Exact fractional-carrier theorem.**  Every selector with values in `[0,1]` gives an exact
continuous allocation of the negative Weil mass.  RH is equivalent to weighted negative energy
in that allocation and subpower growth of its complement. -/
theorem riemannHypothesis_iff_fractionalNegativeEnergy_and_complementarySubpower
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (omega : ℕ → ℝ) (homega : ∀ n, 0 ≤ omega n ∧ omega n ≤ 1) :
    RiemannHypothesis ↔
      XiRectangularNegativeChannelEnergy
        (xiRectangularWeightedNegativeChannel L N omega) ∧
      XiRectangularSubpowerChannel
        (xiRectangularComplementaryNegativeChannel L N omega) :=
  riemannHypothesis_iff_negativeChannelEnergy_and_subpowerChannel
    hL hN (xiRectangular_fractional_negativeChannelSplit L N omega homega)

end

end RHTower
