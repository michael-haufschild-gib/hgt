import GaloisForLFunctions.RHTower.SmoothAFEZetaRightReflectedPrimalMass
import GaloisForLFunctions.RHTower.SteinhausComplexFourthMomentBound

/-!
# Positive-mass conditional energy for the literal reflected AFE block

The literal reflected-primal coefficients are inserted into the exact largest-prime channels.
Padding each cofactor polynomial to `Fin N` permits one common complex fourth-moment estimate.
The previously proved terminal coefficient mass and Paley--Zygmund then give an
arbitrary-small-power lower bound for the set of small-prime phases on which total conditional
energy stays bounded below.
-/

noncomputable section

namespace RHTower

open Complex Finset Nat MeasureTheory
open SteinhausModel

/-- The reflected-primal AFE coefficient attached to a positive arithmetic index. -/
def smoothAFEZetaRightReflectedPrimalPositiveCoefficient
    (d tau r : ℝ) (N n : ℕ) : ℂ :=
  smoothAFEZetaRightReflectedPrimalCoefficient d tau ((N : ℝ) / r) (n - 1)

/-- A largest-prime cofactor channel, padded by zero to the common range `Fin N`. -/
def smoothAFEZetaRightReflectedPrimalChannelFinCoeff
    (d tau r : ℝ) (N p : ℕ) (j : Fin N) : ℂ :=
  if (j : ℕ) + 1 ≤ N / p then
    smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N (p * ((j : ℕ) + 1))
  else 0

/-- The padded finite carrier is exactly the largest-prime channel of the literal AFE block. -/
theorem steinhausFinCarrier_reflectedPrimalChannel_eq
    (d tau r : ℝ) (N p : ℕ) (omega : Omega) :
    steinhausFinCarrier N
        (smoothAFEZetaRightReflectedPrimalChannelFinCoeff d tau r N p) omega =
      steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N) N p omega := by
  classical
  have hfilter :
      (Finset.Icc 1 N).filter (fun m => m ≤ N / p) = Finset.Icc 1 (N / p) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hm1, hmN⟩, hmdiv⟩
      exact ⟨hm1, hmdiv⟩
    · rintro ⟨hm1, hmdiv⟩
      exact ⟨⟨hm1, hmdiv.trans (Nat.div_le_self N p)⟩, hmdiv⟩
  unfold steinhausFinCarrier smoothAFEZetaRightReflectedPrimalChannelFinCoeff
    steinhausLargePrimeChannel
  calc
    (∑ j : Fin N,
        (if (j : ℕ) + 1 ≤ N / p then
          smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N
            (p * ((j : ℕ) + 1)) else 0) * X ((j : ℕ) + 1) omega) =
      ∑ m ∈ Finset.Icc 1 N,
        (if m ≤ N / p then
          smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N (p * m) else 0) *
            X m omega :=
      sum_fin_succ_eq_sum_Icc N (fun m =>
        (if m ≤ N / p then
          smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N (p * m) else 0) *
            X m omega)
    _ = ∑ m ∈ Finset.Icc 1 (N / p),
        smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N (p * m) * X m omega := by
      rw [← hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmp : m ≤ N / p
      · simp [hmp]
      · simp [hmp]

/-- Squared norm of a positive reflected-primal coefficient is the literal actual weight. -/
theorem norm_sq_smoothAFEZetaRightReflectedPrimalPositiveCoefficient_eq_actual
    {d tau r : ℝ} (hr : 0 < r) {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    ‖smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N n‖ ^ 2 =
      terminalReflectedActualSquareWeight d tau r N n := by
  exact norm_sq_smoothAFEZetaRightReflectedPrimalCoefficient_eq_actual hr hN hn

/-- Exact coefficient variance of one padded largest-prime channel. -/
theorem sum_normSq_reflectedPrimalChannelFinCoeff_eq_actual
    {d tau r : ℝ} (hr : 0 < r) {N p : ℕ} (hN : 0 < N) (hp : 0 < p) :
    (∑ j : Fin N,
        ‖smoothAFEZetaRightReflectedPrimalChannelFinCoeff d tau r N p j‖ ^ 2) =
      ∑ m ∈ Finset.Icc 1 (N / p),
        terminalReflectedActualSquareWeight d tau r N (p * m) := by
  classical
  have hfilter :
      (Finset.Icc 1 N).filter (fun m => m ≤ N / p) = Finset.Icc 1 (N / p) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hm1, hmN⟩, hmdiv⟩
      exact ⟨hm1, hmdiv⟩
    · rintro ⟨hm1, hmdiv⟩
      exact ⟨⟨hm1, hmdiv.trans (Nat.div_le_self N p)⟩, hmdiv⟩
  unfold smoothAFEZetaRightReflectedPrimalChannelFinCoeff
  calc
    (∑ j : Fin N,
        ‖if (j : ℕ) + 1 ≤ N / p then
          smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N
            (p * ((j : ℕ) + 1)) else 0‖ ^ 2) =
      ∑ m ∈ Finset.Icc 1 N,
        ‖if m ≤ N / p then
          smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N (p * m) else 0‖ ^ 2 :=
      sum_fin_succ_eq_sum_Icc N (fun m =>
        ‖if m ≤ N / p then
          smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N (p * m) else 0‖ ^ 2)
    _ = ∑ m ∈ Finset.Icc 1 (N / p),
        terminalReflectedActualSquareWeight d tau r N (p * m) := by
      rw [← hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmp : m ≤ N / p
      · simp only [hmp, ↓reduceIte]
        have hmpos : 0 < m := by
          have hm1 := (Finset.mem_Icc.mp hm).1
          omega
        exact norm_sq_smoothAFEZetaRightReflectedPrimalPositiveCoefficient_eq_actual
          hr hN (Nat.mul_pos hp hmpos)
      · simp [hmp]

/-- Exact total padded coefficient variance over any positive prime family. -/
theorem reflectedPrimal_totalVariance_eq_actual
    {d tau r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 0 < N) {P : Finset ℕ}
    (hP : ∀ p ∈ P, 0 < p) :
    steinhausFinTotalVariance P N
        (fun p => smoothAFEZetaRightReflectedPrimalChannelFinCoeff d tau r N p) =
      ∑ p ∈ P, ∑ m ∈ Finset.Icc 1 (N / p),
        terminalReflectedActualSquareWeight d tau r N (p * m) := by
  unfold steinhausFinTotalVariance
  exact Finset.sum_congr rfl fun p hp =>
    sum_normSq_reflectedPrimalChannelFinCoeff_eq_actual hr hN (hP p hp)

/-- The total padded energy is exactly the sum of literal largest-prime channel energies. -/
theorem reflectedPrimal_finEnergy_eq_actualChannels
    (d tau r : ℝ) (N : ℕ) (P : Finset ℕ) (omega : Omega) :
    steinhausFinEnergy P N
        (fun p => smoothAFEZetaRightReflectedPrimalChannelFinCoeff d tau r N p) omega =
      ∑ p ∈ P,
        ‖steinhausLargePrimeChannel
          (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N) N p omega‖ ^ 2 := by
  unfold steinhausFinEnergy
  exact Finset.sum_congr rfl fun p hp => by
    rw [steinhausFinCarrier_reflectedPrimalChannel_eq]

/-- Dyadic terminal cofactor mass is contained in the full padded channel variance. -/
theorem reflectedPrimal_dyadicMass_le_totalVariance
    {d tau r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 0 < N) {P : Finset ℕ}
    (hP : ∀ p ∈ P, 0 < p) :
    (∑ p ∈ P, ∑ m ∈ dyadicCofactorBlock N p,
        terminalReflectedActualSquareWeight d tau r N (p * m)) ≤
      steinhausFinTotalVariance P N
        (fun p => smoothAFEZetaRightReflectedPrimalChannelFinCoeff d tau r N p) := by
  rw [reflectedPrimal_totalVariance_eq_actual hr hN hP]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    unfold dyadicCofactorBlock at hm
    exact Finset.mem_Icc.mpr ⟨by
      have hmlo := (Finset.mem_Icc.mp hm).1
      exact (Nat.succ_le_succ (Nat.zero_le (N / p / 2))).trans hmlo,
      (Finset.mem_Icc.mp hm).2⟩
  · intro m hm hmdyadic
    unfold terminalReflectedActualSquareWeight
    positivity

/-- Fixed positive terminal mass supplied by the reflected-primal AFE coefficients. -/
def reflectedActualTerminalMassFloor (d c : ℝ) : ℝ :=
  c ^ 2 *
    ((1 / 4 : ℝ) *
      (((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) *
        ((-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ))) / 2)))

theorem reflectedActualTerminalMassFloor_pos {d c : ℝ} (hc : 0 < c) :
    0 < reflectedActualTerminalMassFloor d c := by
  have hlog := terminalPrimePowerWindowMass_limit_pos
  unfold reflectedActualTerminalMassFloor
  positivity

/-- **Literal reflected-AFE conditional energy has a subpower positive-mass base event.**
Uniformly on every sufficiently high dyadic height window, the total largest-prime conditional
energy exceeds half a fixed positive constant on a set of small-prime phases of measure
`at least 1 / (4 C N^(2 epsilon))`. -/
theorem exists_eventually_measure_reflectedPrimalChannelEnergy_gt_ge_rpow
    {d epsilon : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (hepsilon : 0 < epsilon) :
    ∃ c r C : ℝ, 0 < c ∧ 0 < r ∧ 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ tau ∈ Set.Icc (N : ℝ) (2 * N : ℝ),
        1 / (4 * (C * ((N * N : ℕ) : ℝ) ^ epsilon)) ≤
          (steinhausMeasure {omega |
            (1 / 2 : ℝ) * reflectedActualTerminalMassFloor d c <
              ∑ p ∈ terminalPrimePowerWindow N,
                ‖steinhausLargePrimeChannel
                  (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N)
                  N p omega‖ ^ 2}).toReal := by
  obtain ⟨c, r, hc, hr, hmass⟩ :=
    exists_eventually_reflected_actual_terminal_channels_lower hd hdhalf
  obtain ⟨C, hC, hevent⟩ :=
    exists_measure_steinhausFinEnergy_gt_half_ge_rpow_of_totalVariance_pos hepsilon
  refine ⟨c, r, C, hc, hr, hC, ?_⟩
  filter_upwards [hmass, Filter.eventually_ge_atTop 1] with N hmassN hN
  intro tau htau
  let P : Finset ℕ := terminalPrimePowerWindow N
  let a : ℕ → Fin N → ℂ := fun p =>
    smoothAFEZetaRightReflectedPrimalChannelFinCoeff d tau r N p
  have hPpos : ∀ p ∈ P, 0 < p := by
    intro p hp
    exact (mem_terminalPrimePowerWindow.mp (by simpa [P] using hp)).1.pos
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hfloor : reflectedActualTerminalMassFloor d c ≤
      steinhausFinTotalVariance P N a := by
    calc
      reflectedActualTerminalMassFloor d c ≤
          ∑ p ∈ terminalPrimePowerWindow N,
            ∑ m ∈ dyadicCofactorBlock N p,
              terminalReflectedActualSquareWeight d tau r N (p * m) := by
        simpa [reflectedActualTerminalMassFloor] using hmassN tau htau
      _ ≤ steinhausFinTotalVariance P N a := by
        exact reflectedPrimal_dyadicMass_le_totalVariance hr hNpos hPpos
  have htotal : 0 < steinhausFinTotalVariance P N a :=
    (reflectedActualTerminalMassFloor_pos hc).trans_le hfloor
  have hbase := hevent P N a htotal
  refine hbase.trans ?_
  apply ENNReal.toReal_mono (measure_ne_top steinhausMeasure _)
  apply measure_mono
  intro omega homega
  simp only [Set.mem_setOf_eq] at homega ⊢
  have hhalf :
      (1 / 2 : ℝ) * reflectedActualTerminalMassFloor d c ≤
        (1 / 2 : ℝ) * steinhausFinTotalVariance P N a :=
    mul_le_mul_of_nonneg_left hfloor (by norm_num)
  have henergy :
      steinhausFinEnergy P N a omega =
        ∑ p ∈ terminalPrimePowerWindow N,
          ‖steinhausLargePrimeChannel
            (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N)
            N p omega‖ ^ 2 := by
    exact reflectedPrimal_finEnergy_eq_actualChannels d tau r N P omega
  rw [henergy] at homega
  exact hhalf.trans_lt homega

end RHTower

end
