import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityUpper

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- A support-certified local circuit approximates the connected static-chain evolution
in operator norm at error `ε`. -/
def OperatorApproximates {L : ℕ} (t ε : ℝ)
    (c : List (LocalGate (PairQubit L))) : Prop :=
  ‖circuitMatrix c - inverseSquareChainEvolution L t‖ ≤ ε

/-- There is an approximating circuit using at most `G` counted two-qubit gates. -/
def HasTwoGateCostAtMost (L G : ℕ) (t ε : ℝ) : Prop :=
  ∃ c : List (LocalGate (PairQubit L)),
    OperatorApproximates t ε c ∧ twoGateCount c ≤ G

theorem inverseSquareChain_integer_window_growth {L Klo Khi : ℕ} {t ε : ℝ}
    (hKlo : 8 ≤ Klo) (hKloL : 8 * Klo ≤ L)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htlo : 128 * Real.pi * ε * Klo ≤ t)
    (hthi : t < 128 * Real.pi * ε * (Klo + 1))
    (hKhi : 1 ≤ Khi) (hKhiL : Khi ≤ L)
    (hKhiScale : 2 * t / ε ≤ Khi)
    (htLab : t ≤ ε * L / 2) :
    (∀ c : List (LocalGate (PairQubit L)),
        OperatorApproximates t ε c → Klo ≤ twoGateCount c) ∧
      ∃ c : List (LocalGate (PairQubit L)),
        twoGateCount c = Khi ∧
          ‖circuitMatrix c - inverseSquareChainEvolution L t‖ < ε := by
  have hL : 2 ≤ L := by omega
  have ht0 : 0 ≤ t := by
    have hbase : 0 ≤ 128 * Real.pi * ε * (Klo : ℝ) := by positivity
    exact hbase.trans htlo
  constructor
  · intro c hc
    exact inverseSquareChain_twoGateCount_ge c hKlo hKloL hε hεmax htlo hthi htLab hc
  · exact inverseSquareChain_upper_approximation hKhi hKhiL hL hε ht0
      hKhiScale htLab

set_option maxHeartbeats 800000 in
theorem inverseSquareChain_floor_ceil_growth {L : ℕ} {t ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t)
    (htLab : t ≤ ε * L / 2) :
    (∀ c : List (LocalGate (PairQubit L)),
        OperatorApproximates t ε c →
          ⌊t / (128 * Real.pi * ε)⌋₊ ≤ twoGateCount c) ∧
      ∃ c : List (LocalGate (PairQubit L)),
        twoGateCount c = ⌈2 * t / ε⌉₊ ∧
          ‖circuitMatrix c - inverseSquareChainEvolution L t‖ < ε := by
  let d : ℝ := 128 * Real.pi * ε
  let Klo : ℕ := ⌊t / d⌋₊
  let Khi : ℕ := ⌈2 * t / ε⌉₊
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) htMin
  have hrho0 : 0 ≤ t / d := le_of_lt (div_pos htpos hd)
  have hKloFloor : (Klo : ℝ) ≤ t / d := by
    exact Nat.floor_le hrho0
  have hKloRaw : (Klo : ℝ) * d ≤ t := by
    exact (le_div_iff₀ hd).mp hKloFloor
  have hKloTime : 128 * Real.pi * ε * Klo ≤ t := by
    dsimp [d] at hKloRaw
    simpa [mul_assoc, mul_left_comm, mul_comm] using hKloRaw
  have hKloNext : t < 128 * Real.pi * ε * (Klo + 1) := by
    have hnext : t / d < (Klo : ℝ) + 1 := Nat.lt_floor_add_one (t / d)
    have hnext' : t < ((Klo : ℝ) + 1) * d := (div_lt_iff₀ hd).mp hnext
    dsimp [d] at hnext'
    nlinarith
  have hKloEight : 8 ≤ Klo := by
    rw [Nat.le_floor_iff' (by norm_num)]
    change (8 : ℝ) ≤ t / d
    rw [le_div_iff₀ hd]
    dsimp [d]
    nlinarith
  have hKloL : 8 * Klo ≤ L := by
    have hraw : ε * (128 * Real.pi * (Klo : ℝ)) ≤ ε * ((L : ℝ) / 2) := by
      calc
        ε * (128 * Real.pi * (Klo : ℝ)) =
            128 * Real.pi * ε * Klo := by ring
        _ ≤ t := hKloTime
        _ ≤ ε * L / 2 := htLab
        _ = ε * ((L : ℝ) / 2) := by ring
    have hcancel : 128 * Real.pi * (Klo : ℝ) ≤ (L : ℝ) / 2 :=
      le_of_mul_le_mul_left hraw hε
    have hpi := Real.pi_gt_three
    have hcast : (8 * Klo : ℕ) ≤ L := by
      exact_mod_cast (show (8 : ℝ) * Klo ≤ L by
        calc
          (8 : ℝ) * Klo ≤ 128 * Real.pi * Klo := by
            have hKlo0 : (0 : ℝ) ≤ Klo := by positivity
            nlinarith
          _ ≤ (L : ℝ) / 2 := hcancel
          _ ≤ L := by
            have hL0 : (0 : ℝ) ≤ L := by positivity
            linarith)
    exact hcast
  have hKhiOne : 1 ≤ Khi := by
    rw [Nat.one_le_ceil_iff]
    exact div_pos (mul_pos (by norm_num) htpos) hε
  have hKhiScale : 2 * t / ε ≤ (Khi : ℝ) := by
    exact Nat.le_ceil (2 * t / ε)
  have hKhiL : Khi ≤ L := by
    rw [Nat.ceil_le]
    rw [div_le_iff₀ hε]
    nlinarith
  simpa [d, Klo, Khi] using inverseSquareChain_integer_window_growth
    hKloEight hKloL hε hεmax hKloTime hKloNext hKhiOne hKhiL hKhiScale htLab

theorem inverseSquareChain_no_shorter_approximation {L : ℕ} {t ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t)
    (htLab : t ≤ ε * L / 2) :
    ¬ HasTwoGateCostAtMost L (⌊t / (128 * Real.pi * ε)⌋₊ - 1) t ε := by
  intro hshort
  rcases hshort with ⟨c, hc, hcost⟩
  have hlower := (inverseSquareChain_floor_ceil_growth hε hεmax htMin htLab).1 c hc
  have hd : 0 < 128 * Real.pi * ε := by positivity
  have hfloor : 1 ≤ ⌊t / (128 * Real.pi * ε)⌋₊ := by
    rw [Nat.one_le_floor_iff]
    rw [le_div_iff₀ hd]
    nlinarith
  omega

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
