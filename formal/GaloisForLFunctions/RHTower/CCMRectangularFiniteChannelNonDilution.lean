import GaloisForLFunctions.RHTower.CCMRectangularNegativeDirichletAbscissa

/-!
# Finite positive-channel non-dilution for the rectangular Weil carrier

The negative fixed-window Weil mass cannot lose its Dirichlet abscissa inside a finite positive
source architecture.  Every finite nonnegative cover has a channel whose abscissa is at least the
abscissa of the covered mass.  For an exact split, one channel has exactly the total abscissa.

Applied to the formalized rectangular carrier, false RH forces one channel to pay the full shifted
transverse-divisor abscissa `1 + xiRightTransverseSup`.  This is a positive carrier theorem: a
successful finite-channel construction must expose the full horizontal exponent in one of its
channels; it cannot dilute that exponent among finitely many positive pieces.
-/

open Complex Filter Function Set LSeries

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000

/-- A finite family of nonnegative channels whose sum dominates the actual rectangular negative
mass pointwise. -/
def XiRectangularFiniteNegativeChannelCover
    {ι : Type*} [DecidableEq ι]
    (L : ℝ) (N : ℕ) (s : Finset ι) (a : ι → ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    (∀ i ∈ s, 0 ≤ a i n) ∧
      xiRectangularWeilTailNegativePart L N n ≤ ∑ i ∈ s, a i n

/-- A finite pointwise nonnegative exact decomposition of the actual rectangular negative mass. -/
def XiRectangularFiniteNegativeChannelSplit
    {ι : Type*} [DecidableEq ι]
    (L : ℝ) (N : ℕ) (s : Finset ι) (a : ι → ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    (∀ i ∈ s, 0 ≤ a i n) ∧
      xiRectangularWeilTailNegativePart L N n = ∑ i ∈ s, a i n

/-- Real source-channel coefficients viewed as complex L-series coefficients. -/
def rectangularNegativeChannelCoefficient (f : ℕ → ℝ) : ℕ → ℂ :=
  fun n => ((f n : ℝ) : ℂ)

/-- Pointwise domination of nonnegative real coefficients orders their absolute-convergence
abscissae. -/
theorem abscissaOfAbsConv_le_of_nonnegative_domination
    {f g : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (hfg : ∀ n, f n ≤ g n) :
    LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient f) ≤
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient g) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
  intro sigma hsigma
  have hsumg : LSeriesSummable (rectangularNegativeChannelCoefficient g) (sigma : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa only [ofReal_re] using hsigma)
  exact LSeriesSummable_of_nonneg_of_le hf hg hfg hsumg

/-- A finite sum has abscissa at most any common upper bound for its channel abscissae. -/
private theorem abscissaOfAbsConv_finsetSum_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : ι → ℕ → ℂ) {x : EReal}
    (hF : ∀ i ∈ s, LSeries.abscissaOfAbsConv (F i) ≤ x) :
    LSeries.abscissaOfAbsConv (fun n => ∑ i ∈ s, F i n) ≤ x := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
  intro sigma hsigma
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using (LSeriesSummable_zero (s := (sigma : ℂ)))
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      apply LSeriesSummable.add
      · apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
        simpa only [ofReal_re] using
          (hF i (Finset.mem_insert_self i s)).trans_lt hsigma
      · exact ih fun j hj => hF j (Finset.mem_insert_of_mem hj)

/-- **Finite-cover non-dilution.**  Every nonempty finite positive cover of the actual negative
carrier has one channel whose absolute-convergence abscissa is at least that of the carrier. -/
theorem finiteNegativeChannelCover_forces_full_abscissa
    {ι : Type*} [DecidableEq ι]
    {L : ℝ} {N : ℕ} {s : Finset ι} {a : ι → ℕ → ℝ}
    (hs : s.Nonempty)
    (hcover : XiRectangularFiniteNegativeChannelCover L N s a) :
    ∃ i ∈ s,
      LSeries.abscissaOfAbsConv
          (xiRectangularWeilTailNegativeDirichletCoefficient L N) ≤
        LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient (a i)) := by
  obtain ⟨i, hi, himax⟩ := s.exists_max_image
    (fun j => LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient (a j))) hs
  refine ⟨i, hi, ?_⟩
  let total : ℕ → ℝ := fun n => ∑ j ∈ s, a j n
  have htotal_nonneg : ∀ n, 0 ≤ total n := by
    intro n
    exact Finset.sum_nonneg fun j hj => (hcover n).1 j hj
  have hcarrier_le_total :
      LSeries.abscissaOfAbsConv
          (xiRectangularWeilTailNegativeDirichletCoefficient L N) ≤
        LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient total) := by
    apply abscissaOfAbsConv_le_of_nonnegative_domination
    · exact xiRectangularWeilTailNegativePart_nonneg L N
    · exact htotal_nonneg
    · exact fun n => (hcover n).2
  have htotal_le_channel :
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient total) ≤
        LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient (a i)) := by
    have hcoeff : rectangularNegativeChannelCoefficient total =
        fun n => ∑ j ∈ s, rectangularNegativeChannelCoefficient (a j) n := by
      funext n
      simp only [rectangularNegativeChannelCoefficient, total, ofReal_sum]
    rw [hcoeff]
    apply abscissaOfAbsConv_finsetSum_le
    exact himax
  exact hcarrier_le_total.trans htotal_le_channel

/-- Under false RH, every finite positive cover pays the full shifted transverse-divisor
abscissa in at least one channel.  The cover may overestimate the negative mass. -/
theorem finiteNegativeChannelCover_forces_transverseSup_of_not_rh
    {ι : Type*} [DecidableEq ι]
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis)
    {s : Finset ι} {a : ι → ℕ → ℝ}
    (hs : s.Nonempty)
    (hcover : XiRectangularFiniteNegativeChannelCover L N s a) :
    ∃ i ∈ s,
      ((1 + xiRightTransverseSup : ℝ) : EReal) ≤
        LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient (a i)) := by
  obtain ⟨i, hi, hpay⟩ :=
    finiteNegativeChannelCover_forces_full_abscissa hs hcover
  refine ⟨i, hi, ?_⟩
  rw [← xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh
    hL hN hnot]
  exact hpay

/-- **Finite-cover zero-free-region theorem.**  If every channel in one finite positive cover has
absolute-convergence abscissa at most `1 + alpha`, then every Xi zero has transverse displacement
at most `alpha`.  This is the source-consumable positive form of finite-channel non-dilution. -/
theorem xiRightTransverseSup_le_of_finiteNegativeChannelCover_abscissa
    {ι : Type*} [DecidableEq ι]
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {s : Finset ι} {a : ι → ℕ → ℝ}
    (hs : s.Nonempty)
    (hcover : XiRectangularFiniteNegativeChannelCover L N s a)
    (hchannel : ∀ i ∈ s,
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient (a i)) ≤
        ((1 + alpha : ℝ) : EReal)) :
    xiRightTransverseSup ≤ alpha := by
  obtain ⟨i, hi, hcarrier_le⟩ :=
    finiteNegativeChannelCover_forces_full_abscissa hs hcover
  have habscissa :
      LSeries.abscissaOfAbsConv
          (xiRectangularWeilTailNegativeDirichletCoefficient L N) ≤
        ((1 + alpha : ℝ) : EReal) :=
    hcarrier_le.trans (hchannel i hi)
  apply (xiRightTransverseSup_le_iff_negativePartEnergyAbove
    hL halpha hN).mpr
  intro epsilon hepsilon
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  have hstrict :
      ((1 + alpha : ℝ) : EReal) <
        ((1 + alpha + epsilon : ℝ) : EReal) := by
    exact_mod_cast (by linarith : 1 + alpha < 1 + alpha + epsilon)
  simpa only [ofReal_re] using habscissa.trans_lt hstrict

/-- **Finite-cover RH theorem.**  A finite nonnegative cover of the actual rectangular negative
mass whose every channel has absolute-convergence abscissa at most one proves RH. -/
theorem riemannHypothesis_of_finiteNegativeChannelCover_abscissa_le_one
    {ι : Type*} [DecidableEq ι]
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {s : Finset ι} {a : ι → ℕ → ℝ}
    (hs : s.Nonempty)
    (hcover : XiRectangularFiniteNegativeChannelCover L N s a)
    (hchannel : ∀ i ∈ s,
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient (a i)) ≤
        ((1 : ℝ) : EReal)) :
    RiemannHypothesis := by
  have hsup : xiRightTransverseSup ≤ 0 :=
    xiRightTransverseSup_le_of_finiteNegativeChannelCover_abscissa
      hL (show (0 : ℝ) ≤ 0 by rfl) hN hs hcover (by
        simpa only [add_zero] using hchannel)
  by_contra hnot
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot
  exact (not_lt_of_ge hsup) (xiRightTransverseSup_pos hne)

/-- **Finite exact-split conservation.**  In every nonempty finite positive exact split, one
channel has exactly the absolute-convergence abscissa of the total negative carrier. -/
theorem finiteNegativeChannelSplit_attains_full_abscissa
    {ι : Type*} [DecidableEq ι]
    {L : ℝ} {N : ℕ} {s : Finset ι} {a : ι → ℕ → ℝ}
    (hs : s.Nonempty)
    (hsplit : XiRectangularFiniteNegativeChannelSplit L N s a) :
    ∃ i ∈ s,
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient (a i)) =
        LSeries.abscissaOfAbsConv
          (xiRectangularWeilTailNegativeDirichletCoefficient L N) := by
  have hcover : XiRectangularFiniteNegativeChannelCover L N s a := by
    intro n
    exact ⟨(hsplit n).1, (hsplit n).2.le⟩
  obtain ⟨i, hi, htotal_le⟩ :=
    finiteNegativeChannelCover_forces_full_abscissa hs hcover
  refine ⟨i, hi, le_antisymm ?_ htotal_le⟩
  apply abscissaOfAbsConv_le_of_nonnegative_domination
  · exact fun n => (hsplit n).1 i hi
  · exact xiRectangularWeilTailNegativePart_nonneg L N
  · intro n
    rw [(hsplit n).2]
    exact Finset.single_le_sum (fun j hj => (hsplit n).1 j hj) hi

/-- Under false RH, an exact finite positive split has a channel whose abscissa is exactly the
full shifted transverse-divisor abscissa. -/
theorem finiteNegativeChannelSplit_attains_transverseSup_of_not_rh
    {ι : Type*} [DecidableEq ι]
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis)
    {s : Finset ι} {a : ι → ℕ → ℝ}
    (hs : s.Nonempty)
    (hsplit : XiRectangularFiniteNegativeChannelSplit L N s a) :
    ∃ i ∈ s,
      LSeries.abscissaOfAbsConv (rectangularNegativeChannelCoefficient (a i)) =
        ((1 + xiRightTransverseSup : ℝ) : EReal) := by
  obtain ⟨i, hi, hattain⟩ :=
    finiteNegativeChannelSplit_attains_full_abscissa hs hsplit
  refine ⟨i, hi, ?_⟩
  rw [hattain,
    xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh hL hN hnot]

end

end RHTower
