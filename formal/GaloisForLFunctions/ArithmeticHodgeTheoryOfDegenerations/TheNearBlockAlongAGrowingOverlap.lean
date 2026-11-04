import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheShellMassOfTheNearPairs
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheFarCrossErrorAtGrowingOverlap
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheLogarithmicWeightOfTheNearPairs
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheGrowingGammaPairMeanIsPolar
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheActualNearCenterHasItsSignedFinitePart
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixDecomposesAtEveryOverlap

/-!
# The near block along a growing overlap

On two Ramanujan packets `u = c_{e'}`, `v = c_e`, the overlap matrix `Ov` (literal archimedean
pairing of the near atoms, center kernel added back) and the non-ratio prime matrix `NR` combine
exactly (`nearBlock_eq`) into

`Z(⟨Ov R_e, R_{e'}⟩ − ⟨NR R_e, R_{e'}⟩) = Γ − log(1/w) S/∫φ² + (α/N) C − 2 P_log − w P_ℓ + P_J + P_J' − X`,

`Z = √(φ(e)φ(e'))`, `w = c/N`: the near Gamma remainder `Γ` (`nearArchimedeanRemainder`), the shell
mass `S` (`shellMass`), the near center `C` (`nearCenterPair`), the near pairs weighted by
`log(w min(n, j))`, by the scaled gap `ℓ = |log(j/n)|/w`, and by the divisor jets `J_e`, `J_{e'}`,
and the exterior products `X`. The logarithm `log(nj)` of the downward prime products is split as
`2 log(w min(n, j)) + 2 log(1/w) + |log(j/n)|`: one `log(1/w)` cancels the archimedean shell
coefficient, the other is the shell mass.

Divided by `c` along `c → ∞`, `c² log² N/N → 0` (`tendsto_nearBlock_div_overlap`):

`(Z(⟨Ov⟩ − ⟨NR⟩) + log(1/w) S/∫φ²)/c + [e = e' = 1] κ(log c − 2)
  → [e = e' = 1](2/∫φ²)∫_0^2 nearKernel + κ[e = e'](log 2 + γ − 1 or −Λ(e)) + κ([e' = 1]Λ(e) + [e = 1]Λ(e'))`,

`κ = (∫φ)²/∫φ²`. The logarithms `κ log c` of the near center and `−2κ log c` of the weighted pairs
are left for the shell correction, which carries `κ c log c`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis BezoutValuationIncidence

/-! ### Window sums -/

/-- A sum over the near pairs `0 < |log(j/n)| ≤ 2w` of the horizon. -/
def nearWindowSum (w : ℝ) (N : ℕ) (F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
    if 0 * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ 2 * w then F n j else 0

theorem nearWindowSum_add (w : ℝ) (N : ℕ) (F G : ℕ → ℕ → ℝ) :
    nearWindowSum w N (fun n j => F n j + G n j) = nearWindowSum w N F + nearWindowSum w N G := by
  simp only [nearWindowSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => by split_ifs <;> ring

theorem nearWindowSum_smul (w : ℝ) (N : ℕ) (a : ℝ) (F : ℕ → ℕ → ℝ) :
    nearWindowSum w N (fun n j => a * F n j) = a * nearWindowSum w N F := by
  simp only [nearWindowSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => by split_ifs <;> ring

theorem nearWindowSum_congr {w : ℝ} {N : ℕ} {F G : ℕ → ℕ → ℝ}
    (h : ∀ n ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N, n ≠ j →
      |Real.log j - Real.log n| ≤ 2 * w → F n j = G n j) :
    nearWindowSum w N F = nearWindowSum w N G := by
  refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun j hj => ?_
  split_ifs with hw
  · refine h n hn j hj ?_ hw.2
    rintro rfl; rw [sub_self, abs_zero, zero_mul] at hw; exact lt_irrefl _ hw.1
  · rfl

/-- On the horizon, `n ≠ j` exactly when the log-distance is positive. -/
theorem abs_log_sub_pos_iff {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    0 < |Real.log j - Real.log n| ↔ n ≠ j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  rw [abs_pos, sub_ne_zero, ne_comm]
  constructor
  · intro h hnj; exact h (by rw [hnj])
  · intro h hlog
    exact h (by exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr hn0) (Set.mem_Ioi.mpr hj0) hlog)

/-- The autocorrelation kernel of the non-ratio rows is supported on the near window. -/
theorem sum_shellAutocorr_mul_eq_nearWindowSum {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ} (hw : 0 < w) (N : ℕ) (X : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        (if j = n then 0 else shellAutocorr φ ((Real.log j - Real.log n) / w)) * X n j =
      nearWindowSum w N (fun n j => shellAutocorr φ (|Real.log j - Real.log n| / w) * X n j) := by
  refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun j hj => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hj1 := (Finset.mem_Icc.mp hj).1
  have heven : shellAutocorr φ ((Real.log j - Real.log n) / w) =
      shellAutocorr φ (|Real.log j - Real.log n| / w) := by
    rcases le_total 0 (Real.log j - Real.log n) with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, neg_div, shellAutocorr_neg]
  by_cases hjn : j = n
  · subst hjn
    simp
  · rw [if_neg hjn, heven]
    have hpos : 0 * w < |Real.log j - Real.log n| := by
      rw [zero_mul]; exact (abs_log_sub_pos_iff hn1 hj1).mpr (Ne.symm hjn)
    by_cases h2 : |Real.log j - Real.log n| ≤ 2 * w
    · rw [if_pos ⟨hpos, h2⟩]
    · rw [if_neg (fun h => h2 h.2), shellAutocorr_eq_zero_of_one_le hφ hsupp, zero_mul]
      rw [le_div_iff₀ hw]; push Not at h2; linarith

/-- A gap matrix pair on the near window. -/
theorem gapMatrixPair_eq_nearWindowSum (A : ℕ → ℕ → ℝ) (w : ℝ) (N : ℕ) (u v : ℕ → ℝ) :
    gapMatrixPair A 0 2 w N u v =
      nearWindowSum w N (fun n j => u n * v j * A n j / (Real.sqrt n * Real.sqrt j)) := rfl

/-! ### The near block -/

section NearBlock

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
  (hM : 0 < ∫ u, φ u ^ 2)
include hφ hsupp hM

omit hφ hsupp hM in
/-- The overlap pairing: near Gamma part plus the near center. -/
theorem overlapPairing_eq (c : ℝ) (N : ℕ) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Real.sqrt e.totient * Real.sqrt e'.totient *
        ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ =
      gapMatrixPair (fun n j => atomArchPair (atomDilate φ (c / N)) n j /
          (∫ u, atomDilate φ (c / N) u ^ 2)) 0 2 (c / N) N
        (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) +
        completeWeilPoleShift φ c / N *
          nearCenterPair c N (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) := by
  have hZ : 0 < Real.sqrt e.totient * Real.sqrt e'.totient := by
    have h1 : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.mpr he
    have h2 : (0 : ℝ) < e'.totient := by exact_mod_cast Nat.totient_pos.mpr he'
    positivity
  rw [inner_matrix_ramanujanHorizonVector_eq (overlapMatrix φ c N) (fun n j : ℕ =>
    if n ≠ j ∧ |Real.log j - Real.log n| ≤ 2 * (c / N) then
      atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) +
        (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j else 0)
    (fun n j => by simp only [overlapMatrix, ne_eq]) he he',
    mul_div_cancel₀ _ hZ.ne']
  simp only [gapMatrixPair, nearCenterPair, nearRowIndices, Finset.sum_filter, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun j hj => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hiff := abs_log_sub_pos_iff hn1 hj1
  have e2 : 2 * c / N = 2 * (c / N) := by ring
  rw [e2, zero_mul]
  by_cases h : n ≠ j ∧ |Real.log j - Real.log n| ≤ 2 * (c / N)
  · rw [if_pos h, if_pos ⟨hiff.mpr h.1, h.2⟩, if_pos ⟨Ne.symm h.1, h.2⟩]; ring
  · rw [if_neg h, if_neg (fun h' => h ⟨hiff.mp h'.1, h'.2⟩),
      if_neg (fun h' => h ⟨Ne.symm h'.1, h'.2⟩)]; ring

omit hM in
/-- The shell mass as a window sum. -/
theorem shellMass_eq_nearWindowSum {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (a b : ℕ) :
    shellMass φ c N a b = nearWindowSum (c / N) N (fun n j =>
      shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) *
        (ramanujanLagCoefficient b n * ramanujanLagCoefficient a j / (Real.sqrt n * Real.sqrt j))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← sum_shellAutocorr_mul_eq_nearWindowSum hφ hsupp (div_pos hc hN0)]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit hM in
/-- The near Gamma pairing splits into its remainder and `log(1/w)` times the shell mass. -/
theorem gapMatrixPair_atomArchPair_eq {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (e e' : ℕ) :
    gapMatrixPair (fun n j => atomArchPair (atomDilate φ (c / N)) n j /
        (∫ u, atomDilate φ (c / N) u ^ 2)) 0 2 (c / N) N
        (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) =
      gapMatrixPair (nearArchimedeanRemainder φ (c / N)) 0 2 (c / N) N
        (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) +
      Real.log (1 / (c / N)) * (shellMass φ c N e e' / ∫ u, φ u ^ 2) := by
  rw [shellMass_eq_nearWindowSum hφ hsupp hc hN]
  have hlog : Real.log (1 / (c / N)) * (nearWindowSum (c / N) N (fun n j =>
      shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) *
        (ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j /
          (Real.sqrt n * Real.sqrt j))) / ∫ u, φ u ^ 2) =
      nearWindowSum (c / N) N (fun n j => Real.log (1 / (c / N)) / (∫ u, φ u ^ 2) *
        (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) *
          (ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j /
            (Real.sqrt n * Real.sqrt j)))) := by
    rw [nearWindowSum_smul]; ring
  rw [hlog, gapMatrixPair_eq_nearWindowSum, gapMatrixPair_eq_nearWindowSum, ← nearWindowSum_add]
  refine nearWindowSum_congr fun n _ j _ _ _ => ?_
  simp only [nearArchimedeanRemainder]
  ring

/-- The two interior non-ratio sums as one window sum. -/
theorem nrInterior_add_eq {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (e e' : ℕ) :
    nrInterior φ c N e e' + nrInterior φ c N e' e = nearWindowSum (c / N) N (fun n j =>
      shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) *
        ((ramanujanLagCoefficient e' n * (Real.log j * ramanujanLagCoefficient e j -
            ramanujanLogDivisorJet e j) +
          ramanujanLagCoefficient e j * (Real.log n * ramanujanLagCoefficient e' n -
            ramanujanLogDivisorJet e' n)) /
          ((∫ u, φ u ^ 2) * (Real.sqrt n * Real.sqrt j)))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have h1 : nrInterior φ c N e e' = ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
      (if j = n then 0 else shellAutocorr φ ((Real.log j - Real.log n) / (c / N))) *
        (ramanujanLagCoefficient e' n * (Real.log j * ramanujanLagCoefficient e j -
          ramanujanLogDivisorJet e j) / ((∫ u, φ u ^ 2) * (Real.sqrt n * Real.sqrt j))) := by
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => ?_
    have hM' := hM.ne'
    by_cases hjn : j = n
    · simp [hjn]
    · rw [if_neg hjn]; field_simp
  have h2 : nrInterior φ c N e' e = ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
      (if j = n then 0 else shellAutocorr φ ((Real.log j - Real.log n) / (c / N))) *
        (ramanujanLagCoefficient e j * (Real.log n * ramanujanLagCoefficient e' n -
          ramanujanLogDivisorJet e' n) / ((∫ u, φ u ^ 2) * (Real.sqrt n * Real.sqrt j))) := by
    rw [nrInterior, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => ?_
    have hM' := hM.ne'
    by_cases hjn : j = n
    · subst hjn; simp
    · rw [if_neg (Ne.symm hjn), if_neg hjn]
      have heven : shellAutocorr φ ((Real.log n - Real.log j) / (c / N)) =
          shellAutocorr φ ((Real.log j - Real.log n) / (c / N)) := by
        rw [← shellAutocorr_neg, ← neg_div, neg_sub]
      rw [heven]
      field_simp
  rw [h1, h2, sum_shellAutocorr_mul_eq_nearWindowSum hφ hsupp hw,
    sum_shellAutocorr_mul_eq_nearWindowSum hφ hsupp hw, ← nearWindowSum_add]
  refine nearWindowSum_congr fun n _ j _ _ _ => ?_
  ring

omit hφ hsupp hM in
/-- `log n + log j = 2 log min(n, j) + |log j − log n|`. -/
theorem log_add_log_eq_min {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    Real.log n + Real.log j = 2 * Real.log (min n j : ℕ) + |Real.log j - Real.log n| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases le_total n j with h | h
  · have hlog : Real.log n ≤ Real.log j := Real.log_le_log hn0 (by exact_mod_cast h)
    rw [Nat.min_eq_left h, abs_of_nonneg (by linarith)]; ring
  · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hlog : Real.log j ≤ Real.log n := Real.log_le_log hj0 (by exact_mod_cast h)
    rw [Nat.min_eq_right h, abs_of_nonpos (by linarith)]; ring

omit hφ hsupp hM in
/-- The pointwise cancellation of the near window: the logarithm `log(nj)` of the downward
products against twice the shell coefficient `log(1/w)`. -/
theorem nearWindow_identity {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (e e' : ℕ) :
    2 * nearWindowSum (c / N) N (fun n j => Real.log (1 / (c / N)) / (∫ u, φ u ^ 2) *
        (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) *
          (ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j /
            (Real.sqrt n * Real.sqrt j)))) -
      nearWindowSum (c / N) N (fun n j =>
        shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) *
          ((ramanujanLagCoefficient e' n * (Real.log j * ramanujanLagCoefficient e j -
              ramanujanLogDivisorJet e j) +
            ramanujanLagCoefficient e j * (Real.log n * ramanujanLagCoefficient e' n -
              ramanujanLogDivisorJet e' n)) /
            ((∫ u, φ u ^ 2) * (Real.sqrt n * Real.sqrt j)))) =
      -nearWindowSum (c / N) N (fun n j => 2 * Real.log (c / N * (min n j : ℕ)) *
          ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j *
            (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2) /
              (Real.sqrt n * Real.sqrt j)) -
        nearWindowSum (c / N) N (fun n j => c / N * (1 * ramanujanLagCoefficient e' n *
          ramanujanLagCoefficient e j * (|Real.log j - Real.log n| / (c / N) *
            shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2) /
              (Real.sqrt n * Real.sqrt j))) +
        nearWindowSum (c / N) N (fun n j => 1 * ramanujanLagCoefficient e' n *
          ramanujanLogDivisorJet e j *
            (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2) /
              (Real.sqrt n * Real.sqrt j)) +
        nearWindowSum (c / N) N (fun n j => 1 * ramanujanLogDivisorJet e' n *
          ramanujanLagCoefficient e j *
            (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2) /
              (Real.sqrt n * Real.sqrt j)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  rw [← nearWindowSum_smul, ← sub_eq_zero]
  simp only [nearWindowSum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_eq_zero fun n hn => Finset.sum_eq_zero fun j hj => ?_
  split_ifs with hwin
  · have hn1 := (Finset.mem_Icc.mp hn).1
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hkey := log_add_log_eq_min hn1 hj1
    have hm0 : (0 : ℝ) < (min n j : ℕ) := by
      have : 1 ≤ min n j := le_min hn1 hj1
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hl1 : Real.log (1 / (c / N)) = -Real.log (c / N) := by rw [one_div, Real.log_inv]
    have hl2 : Real.log (c / N * (min n j : ℕ)) = Real.log (c / N) + Real.log (min n j : ℕ) :=
      Real.log_mul hw.ne' hm0.ne'
    have hsw : c / N * (|Real.log j - Real.log n| / (c / N)) = |Real.log j - Real.log n| :=
      mul_div_cancel₀ _ hw.ne'
    set P := ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j *
      (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) /
        ((∫ u, φ u ^ 2) * (Real.sqrt n * Real.sqrt j)))
    linear_combination (2 * P) * hl1 + (2 * P) * hl2 + (-P) * hkey + P * hsw
  · simp

/-- **The near block on conductor packets.** -/
theorem nearBlock_eq {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) {e e' : ℕ} (he : 0 < e)
    (he' : 0 < e') :
    Real.sqrt e.totient * Real.sqrt e'.totient *
        (⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (ramanujanHorizonVector e N),
            ramanujanHorizonVector e' N⟫ -
          ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) (ramanujanHorizonVector e N),
            ramanujanHorizonVector e' N⟫) +
        Real.log (1 / (c / N)) * (shellMass φ c N e e' / ∫ u, φ u ^ 2) =
      gapMatrixPair (nearArchimedeanRemainder φ (c / N)) 0 2 (c / N) N
          (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) +
        completeWeilPoleShift φ c / N *
          nearCenterPair c N (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) -
        nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c / N) N
          (ramanujanLagCoefficient e') (ramanujanLagCoefficient e)
          (fun m => 2 * Real.log (c / N * m)) -
        c / N * nearPairSum (fun ℓ => ℓ * shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c / N) N
          (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) (fun _ => 1) +
        nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c / N) N
          (ramanujanLagCoefficient e') (ramanujanLogDivisorJet e) (fun _ => 1) +
        nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c / N) N
          (ramanujanLogDivisorJet e') (ramanujanLagCoefficient e) (fun _ => 1) -
        (nrExterior φ c N e e' + nrExterior φ c N e' e) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hZ : 0 < Real.sqrt e.totient * Real.sqrt e'.totient := by
    have h1 : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.mpr he
    have h2 : (0 : ℝ) < e'.totient := by exact_mod_cast Nat.totient_pos.mpr he'
    positivity
  have hOv := overlapPairing_eq (φ := φ) c N he he'
  rw [gapMatrixPair_atomArchPair_eq hφ hsupp hc hN] at hOv
  have hNR : Real.sqrt e.totient * Real.sqrt e'.totient *
      ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) (ramanujanHorizonVector e N),
        ramanujanHorizonVector e' N⟫ =
      nrInterior φ c N e e' + nrInterior φ c N e' e +
        (nrExterior φ c N e e' + nrExterior φ c N e' e) := by
    rw [inner_nonRatio_ramanujan_eq hφ hsupp hM hc hN he he', mul_div_cancel₀ _ hZ.ne',
      nrSum_eq_interior_add_exterior φ hc hN, nrSum_eq_interior_add_exterior φ hc hN]
    ring
  rw [mul_sub, hOv, hNR, nrInterior_add_eq hφ hsupp hM hc hN,
    shellMass_eq_nearWindowSum hφ hsupp hc hN]
  -- everything is a window sum
  have hlog : Real.log (1 / (c / N)) * (nearWindowSum (c / N) N (fun n j =>
      shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) *
        (ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j /
          (Real.sqrt n * Real.sqrt j))) / ∫ u, φ u ^ 2) =
      nearWindowSum (c / N) N (fun n j => Real.log (1 / (c / N)) / (∫ u, φ u ^ 2) *
        (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) *
          (ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j /
            (Real.sqrt n * Real.sqrt j)))) := by
    rw [nearWindowSum_smul]; ring
  rw [hlog]
  have hP1 : nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c / N) N
      (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) (fun m => 2 * Real.log (c / N * m)) =
      nearWindowSum (c / N) N (fun n j => 2 * Real.log (c / N * (min n j : ℕ)) *
        ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j *
          (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2) /
            (Real.sqrt n * Real.sqrt j)) := rfl
  have hP2 : c / N * nearPairSum (fun ℓ => ℓ * shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c / N) N
      (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) (fun _ => 1) =
      nearWindowSum (c / N) N (fun n j => c / N * (1 * ramanujanLagCoefficient e' n *
        ramanujanLagCoefficient e j * (|Real.log j - Real.log n| / (c / N) *
          shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2) /
            (Real.sqrt n * Real.sqrt j))) := by
    rw [nearWindowSum_smul]; rfl
  have hP3 : nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c / N) N
      (ramanujanLagCoefficient e') (ramanujanLogDivisorJet e) (fun _ => 1) =
      nearWindowSum (c / N) N (fun n j => 1 * ramanujanLagCoefficient e' n *
        ramanujanLogDivisorJet e j *
          (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2) /
            (Real.sqrt n * Real.sqrt j)) := rfl
  have hP4 : nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c / N) N
      (ramanujanLogDivisorJet e') (ramanujanLagCoefficient e) (fun _ => 1) =
      nearWindowSum (c / N) N (fun n j => 1 * ramanujanLogDivisorJet e' n *
        ramanujanLagCoefficient e j *
          (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / ∫ u, φ u ^ 2) /
            (Real.sqrt n * Real.sqrt j)) := rfl
  rw [hP1, hP2, hP3, hP4]
  linear_combination nearWindow_identity (φ := φ) hc hN e e'

end NearBlock

/-! ### The limit -/

theorem ramanujanLogDivisorJet_add_mul (m n k : ℕ) :
    ramanujanLogDivisorJet m (n + m * k) = ramanujanLogDivisorJet m n := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, ramanujanLogDivisorJet_add, ih]

theorem sum_range_mul_of_periodic {p : ℕ → ℝ} {q : ℕ} (hp : ∀ n, p (n + q) = p n) (k : ℕ) :
    ∑ r ∈ range (k * q), p r = k * ∑ r ∈ range q, p r := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, sum_range_shift_of_periodic hp]
    push_cast; ring

/-- The divisor jet `J_m` has mean `Λ(m)` over every multiple of its period. -/
theorem periodicMean_ramanujanLogDivisorJet {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    periodicMean (ramanujanLogDivisorJet m) (k * m) = ArithmeticFunction.vonMangoldt m := by
  unfold periodicMean
  rw [sum_range_mul_of_periodic (fun n => ramanujanLogDivisorJet_add m n) k,
    sum_range_ramanujanLogDivisorJet hm]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The rates of a growing overlap with `c² log² N/N → 0`. -/
theorem growingOverlap_rates {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => c N * (1 + Real.log (c N) + Real.log N) / N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (1 + Real.log (c N)) ^ 2 / c N) atTop (𝓝 0) := by
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N := by
    filter_upwards [eventually_ge_atTop 3] with N hN
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith [(show (3 : ℝ) ≤ N by exact_mod_cast hN)]
  have hbase : ∀ᶠ N : ℕ in atTop, c N * (1 + Real.log (c N) + Real.log N) / N ≤
      3 * (c N ^ 2 * Real.log N ^ 2 / N) := by
    filter_upwards [hev, eventually_ge_atTop 1] with N hlN hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hc := hc1 N
    have hlc : Real.log (c N) ≤ c N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hlc0 : 0 ≤ Real.log (c N) := Real.log_nonneg hc
    rw [div_le_iff₀ hN0, mul_div_assoc', div_mul_cancel₀ _ hN0.ne']
    have hl2 : 1 ≤ Real.log N ^ 2 := one_le_pow₀ hlN
    have hcc : c N ≤ c N ^ 2 := by nlinarith
    have hc2 : c N ^ 2 ≤ c N ^ 2 * Real.log N ^ 2 :=
      le_mul_of_one_le_right (sq_nonneg _) hl2
    have h1 : c N ≤ c N ^ 2 * Real.log N ^ 2 := hcc.trans hc2
    have h2 : c N * Real.log (c N) ≤ c N ^ 2 * Real.log N ^ 2 := by
      have := mul_le_mul_of_nonneg_left hlc (by linarith : (0 : ℝ) ≤ c N)
      linarith [show c N * c N = c N ^ 2 by ring]
    have hx : 1 ≤ c N * Real.log N := one_le_mul_of_one_le_of_one_le hc hlN
    have h3 : c N * Real.log N ≤ c N ^ 2 * Real.log N ^ 2 := by
      have := mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ c N * Real.log N)
      linarith [show c N * Real.log N * (c N * Real.log N) = c N ^ 2 * Real.log N ^ 2 by ring]
    linarith
  have h2 : Tendsto (fun N : ℕ => c N * (1 + Real.log (c N) + Real.log N) / N) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => ?_) hbase (by simpa using hcN.const_mul 3)
    have hc := hc1 N
    have : 0 ≤ Real.log (c N) := Real.log_nonneg hc
    have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    positivity
  have h1 : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => ?_) (Eventually.of_forall fun N => ?_) h2
    · have := hc1 N; positivity
    · have hc := hc1 N
      have : 0 ≤ Real.log (c N) := Real.log_nonneg hc
      have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
      exact div_le_div_of_nonneg_right (le_mul_of_one_le_right (by linarith) (by linarith))
        (Nat.cast_nonneg N)
  have h3 : Tendsto (fun N : ℕ => (1 + Real.log (c N)) ^ 2 / c N) atTop (𝓝 0) := by
    have hl : Tendsto (fun x : ℝ => Real.log x ^ 2 / (1 * x + 0)) atTop (𝓝 0) :=
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    have hl' : Tendsto (fun x : ℝ => 2 / x + 2 * (Real.log x ^ 2 / (1 * x + 0))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.div_atTop tendsto_id).add (hl.const_mul 2)
    refine squeeze_zero' (Eventually.of_forall fun N => ?_) (Eventually.of_forall fun N => ?_)
      (hl'.comp hcinf)
    · have := hc1 N; positivity
    · have hc := hc1 N
      have hc0 : 0 < c N := by linarith
      simp only [Function.comp_apply, one_mul, add_zero]
      rw [div_le_iff₀ hc0]
      have e : (2 / c N + 2 * (Real.log (c N) ^ 2 / c N)) * c N = 2 + 2 * Real.log (c N) ^ 2 := by
        field_simp
      rw [e]
      nlinarith [sq_nonneg (Real.log (c N) - 1)]
  exact ⟨h1, h2, h3⟩


theorem nearPairSum_const_mul_weight (K : ℝ → ℝ) (α β w : ℝ) (N : ℕ) (u v ρ : ℕ → ℝ) (a : ℝ) :
    nearPairSum K α β w N u v (fun m => a * ρ m) = a * nearPairSum K α β w N u v ρ := by
  simp only [nearPairSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => by split_ifs <;> ring

section Limits

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
  (hM : 0 < ∫ u, φ u ^ 2)
include hφ hsupp hM

/-- The kernel `G/∫φ²` is bounded by one and Lipschitz. -/
theorem exists_shellKernel_bounds : ∃ L : ℝ, 0 ≤ L ∧
    (∀ ℓ ∈ Set.Icc (0 : ℝ) 2, |shellAutocorr φ ℓ / ∫ u, φ u ^ 2| ≤ 1) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
      |shellAutocorr φ x / (∫ u, φ u ^ 2) - shellAutocorr φ y / ∫ u, φ u ^ 2| ≤ L * |x - y|) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hM0 := hM.le
  refine ⟨K / ∫ u, φ u ^ 2, by positivity, fun ℓ _ => ?_, fun x _ y _ => ?_⟩
  · rw [abs_div, abs_of_pos hM, div_le_one hM]; exact abs_shellAutocorr_le' hφ hsupp ℓ
  · have hLip : |shellAutocorr φ x - shellAutocorr φ y| ≤ K * |x - y| := by
      simpa [Real.dist_eq] using hK.dist_le_mul x y
    rw [← sub_div, abs_div, abs_of_pos hM, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hM]
    exact hLip

/-- The kernel `ℓ G(ℓ)/∫φ²` is bounded by two and Lipschitz on `[0, 2]`. -/
theorem exists_slopeKernel_bounds : ∃ L : ℝ, 0 ≤ L ∧
    (∀ ℓ ∈ Set.Icc (0 : ℝ) 2, |ℓ * shellAutocorr φ ℓ / ∫ u, φ u ^ 2| ≤ 2) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 2,
      |x * shellAutocorr φ x / (∫ u, φ u ^ 2) - y * shellAutocorr φ y / ∫ u, φ u ^ 2| ≤
        L * |x - y|) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hM0 := hM.le
  refine ⟨(2 * K + ∫ u, φ u ^ 2) / ∫ u, φ u ^ 2, by positivity, fun ℓ hℓ => ?_,
    fun x hx y _ => ?_⟩
  · have hG := abs_shellAutocorr_le' hφ hsupp ℓ
    rw [abs_div, abs_of_pos hM, abs_mul, abs_of_nonneg hℓ.1, div_le_iff₀ hM]
    have := mul_le_mul hℓ.2 hG (abs_nonneg _) (by norm_num)
    linarith
  · have hGy := abs_shellAutocorr_le' hφ hsupp y
    have hLip : |shellAutocorr φ x - shellAutocorr φ y| ≤ K * |x - y| := by
      simpa [Real.dist_eq] using hK.dist_le_mul x y
    rw [← sub_div, abs_div, abs_of_pos hM, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hM]
    have e : x * shellAutocorr φ x - y * shellAutocorr φ y =
        x * (shellAutocorr φ x - shellAutocorr φ y) + (x - y) * shellAutocorr φ y := by ring
    rw [e]
    have hx2 : |x| ≤ 2 := by rw [abs_of_nonneg hx.1]; exact hx.2
    calc _ ≤ |x * (shellAutocorr φ x - shellAutocorr φ y)| + |(x - y) * shellAutocorr φ y| :=
          abs_add_le _ _
      _ = |x| * |shellAutocorr φ x - shellAutocorr φ y| + |x - y| * |shellAutocorr φ y| := by
          rw [abs_mul, abs_mul]
      _ ≤ 2 * (K * |x - y|) + |x - y| * ∫ u, φ u ^ 2 :=
          add_le_add (mul_le_mul hx2 hLip (abs_nonneg _) (by norm_num))
            (mul_le_mul_of_nonneg_left hGy (abs_nonneg _))
      _ = (2 * K + ∫ u, φ u ^ 2) * |x - y| := by ring

theorem integral_shellKernel :
    ∫ ℓ in (0 : ℝ)..2, shellAutocorr φ ℓ / ∫ u, φ u ^ 2 =
      (∫ u, φ u) ^ 2 / (2 * ∫ u, φ u ^ 2) := by
  rw [intervalIntegral.integral_div, integral_zero_two_shellAutocorr hφ hsupp]
  field_simp

/-- The weighted near pairs: `P_log/c − [e = e' = 1] κ (log c − 1) → 0`. -/
theorem tendsto_logNearPair_div {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c N / N) N
        (ramanujanLagCoefficient e') (ramanujanLagCoefficient e)
        (fun m => Real.log (c N / N * m)) / c N -
      (if e = 1 ∧ e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0) * (Real.log (c N) - 1))
      atTop (𝓝 0) := by
  obtain ⟨hr1, hr2, hr3⟩ := growingOverlap_rates hc1 hcinf hcN
  obtain ⟨L, hL0, hA, hL⟩ := exists_shellKernel_bounds hφ hsupp hM
  have hq : 0 < e' * e := Nat.mul_pos he' he
  set B : ℝ := (∑ d ∈ e.divisors, (d : ℝ)) + ∑ d ∈ e'.divisors, (d : ℝ)
  have hu : ∀ n, ramanujanLagCoefficient e' (n + e' * e) = ramanujanLagCoefficient e' n :=
    fun n => ramanujanLagCoefficient_add_mul e' n e
  have hv : ∀ n, ramanujanLagCoefficient e (n + e' * e) = ramanujanLagCoefficient e n :=
    fun n => by rw [mul_comm]; exact ramanujanLagCoefficient_add_mul e n e'
  have huB : ∀ n, |ramanujanLagCoefficient e' n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le e' n).trans (le_add_of_nonneg_left (by positivity))
  have hvB : ∀ n, |ramanujanLagCoefficient e n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le e n).trans (le_add_of_nonneg_right (by positivity))
  have hubar := periodicMean_ramanujan_of_dvd he' hq (dvd_mul_right e' e)
  have hvbar := periodicMean_ramanujan_of_dvd he hq (dvd_mul_left e e')
  have hubar1 : |periodicMean (ramanujanLagCoefficient e') (e' * e)| ≤ 1 := by
    rw [hubar]; split_ifs <;> norm_num
  have hvbar1 : |periodicMean (ramanujanLagCoefficient e) (e' * e)| ≤ 1 := by
    rw [hvbar]; split_ifs <;> norm_num
  have hcoef : 2 * (periodicMean (ramanujanLagCoefficient e') (e' * e) *
      periodicMean (ramanujanLagCoefficient e) (e' * e)) *
        (∫ ℓ in (0 : ℝ)..2, shellAutocorr φ ℓ / ∫ u, φ u ^ 2) =
      if e = 1 ∧ e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0 := by
    rw [hubar, hvbar, integral_shellKernel hφ hsupp hM]
    have hM' := hM.ne'
    by_cases h1 : e = 1 <;> by_cases h2 : e' = 1 <;> simp [h1, h2]
    field_simp
  set C₀ := logNearConstant 1 L (e' * e) B
  have hlim : Tendsto (fun N : ℕ => C₀ * ((1 + Real.log (c N)) ^ 2 / c N +
      c N * (1 + Real.log (c N) + Real.log N) / N)) atTop (𝓝 0) := by
    simpa using (hr3.add hr2).const_mul C₀
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hr1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    eventually_ge_atTop 1] with N hN8 hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc := hc1 N
  have hc0 : 0 < c N := by linarith
  have h8 : 8 * c N ≤ N := by
    rw [div_lt_iff₀ hN0] at hN8; linarith
  have hb := abs_logNearPairSum_sub_le hA hL hL0 hq hu hv huB hvB hubar1 hvbar1 hc h8
  rw [Real.norm_eq_abs, ← hcoef]
  have e1 : nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c N / N) N
        (ramanujanLagCoefficient e') (ramanujanLagCoefficient e)
        (fun m => Real.log (c N / N * m)) / c N -
      2 * (periodicMean (ramanujanLagCoefficient e') (e' * e) *
        periodicMean (ramanujanLagCoefficient e) (e' * e)) *
        (∫ ℓ in (0 : ℝ)..2, shellAutocorr φ ℓ / ∫ u, φ u ^ 2) * (Real.log (c N) - 1) =
      (nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c N / N) N
        (ramanujanLagCoefficient e') (ramanujanLagCoefficient e)
        (fun m => Real.log (c N / N * m)) -
      2 * (periodicMean (ramanujanLagCoefficient e') (e' * e) *
        periodicMean (ramanujanLagCoefficient e) (e' * e)) *
        (∫ ℓ in (0 : ℝ)..2, shellAutocorr φ ℓ / ∫ u, φ u ^ 2) * (c N * (Real.log (c N) - 1))) /
        c N := by field_simp
  rw [e1, abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
  calc _ ≤ C₀ * ((1 + Real.log (c N)) ^ 2 + c N ^ 2 * (1 + Real.log (c N) + Real.log N) / N) := hb
    _ = _ := by field_simp

/-- The slope pairs vanish: `w P_ℓ/c → 0`. -/
theorem tendsto_slopeNearPair_div {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N / N * nearPairSum (fun ℓ => ℓ * shellAutocorr φ ℓ / ∫ u, φ u ^ 2)
        0 2 (c N / N) N (ramanujanLagCoefficient e') (ramanujanLagCoefficient e) (fun _ => 1) /
          c N) atTop (𝓝 0) := by
  obtain ⟨L, hL0, hA, hL⟩ := exists_slopeKernel_bounds hφ hsupp hM
  have hq : 0 < e' * e := Nat.mul_pos he' he
  set B : ℝ := (∑ d ∈ e.divisors, (d : ℝ)) + ∑ d ∈ e'.divisors, (d : ℝ)
  have hu : ∀ n, ramanujanLagCoefficient e' (n + e' * e) = ramanujanLagCoefficient e' n :=
    fun n => ramanujanLagCoefficient_add_mul e' n e
  have hv : ∀ n, ramanujanLagCoefficient e (n + e' * e) = ramanujanLagCoefficient e n :=
    fun n => by rw [mul_comm]; exact ramanujanLagCoefficient_add_mul e n e'
  have huB : ∀ n, |ramanujanLagCoefficient e' n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le e' n).trans (le_add_of_nonneg_left (by positivity))
  have hvB : ∀ n, |ramanujanLagCoefficient e n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le e n).trans (le_add_of_nonneg_right (by positivity))
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have h := tendsto_nearPairSum_div_overlap (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2)
    two_pos hA hL hL0 hq hu hv huB hvB hc0 hcinf hcN
  have := hcN.mul h
  rw [zero_mul] at this
  refine this.congr fun N => ?_
  ring

/-- The divisor-jet pairs: `P_J/c → κ [e' = 1] Λ(e)`. -/
theorem tendsto_jetNearPair_div {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c N / N) N
        (ramanujanLagCoefficient e') (ramanujanLogDivisorJet e) (fun _ => 1) / c N) atTop
      (𝓝 (if e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) *
        ArithmeticFunction.vonMangoldt e else 0)) := by
  obtain ⟨L, hL0, hA, hL⟩ := exists_shellKernel_bounds hφ hsupp hM
  have hq : 0 < e' * e := Nat.mul_pos he' he
  set B : ℝ := (∑ d ∈ e'.divisors, (d : ℝ)) + ramanujanJetBound e
  have hJ0 : 0 ≤ ramanujanJetBound e := (abs_nonneg _).trans (abs_ramanujanLogDivisorJet_le e 0)
  have hu : ∀ n, ramanujanLagCoefficient e' (n + e' * e) = ramanujanLagCoefficient e' n :=
    fun n => ramanujanLagCoefficient_add_mul e' n e
  have hv : ∀ n, ramanujanLogDivisorJet e (n + e' * e) = ramanujanLogDivisorJet e n :=
    fun n => by rw [mul_comm]; exact ramanujanLogDivisorJet_add_mul e n e'
  have huB : ∀ n, |ramanujanLagCoefficient e' n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le e' n).trans (le_add_of_nonneg_right hJ0)
  have hvB : ∀ n, |ramanujanLogDivisorJet e n| ≤ B := fun n =>
    (abs_ramanujanLogDivisorJet_le e n).trans (le_add_of_nonneg_left (by positivity))
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have h := tendsto_nearPairSum_div_overlap (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2)
    two_pos hA hL hL0 hq hu hv huB hvB hc0 hcinf hcN
  rw [periodicMean_ramanujan_of_dvd he' hq (dvd_mul_right e' e),
    periodicMean_ramanujanLogDivisorJet he he', integral_shellKernel hφ hsupp hM] at h
  convert h using 2
  have hM' := hM.ne'
  by_cases h1 : e' = 1
  · simp only [h1, if_true]; field_simp
  · simp [h1]

/-- The divisor-jet pairs of the row conductor: `P_J'/c → κ [e = 1] Λ(e')`. -/
theorem tendsto_jetNearPair_div' {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nearPairSum (fun ℓ => shellAutocorr φ ℓ / ∫ u, φ u ^ 2) 0 2 (c N / N) N
        (ramanujanLogDivisorJet e') (ramanujanLagCoefficient e) (fun _ => 1) / c N) atTop
      (𝓝 (if e = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) *
        ArithmeticFunction.vonMangoldt e' else 0)) := by
  obtain ⟨L, hL0, hA, hL⟩ := exists_shellKernel_bounds hφ hsupp hM
  have hq : 0 < e * e' := Nat.mul_pos he he'
  set B : ℝ := (∑ d ∈ e.divisors, (d : ℝ)) + ramanujanJetBound e'
  have hJ0 : 0 ≤ ramanujanJetBound e' := (abs_nonneg _).trans (abs_ramanujanLogDivisorJet_le e' 0)
  have hu : ∀ n, ramanujanLogDivisorJet e' (n + e * e') = ramanujanLogDivisorJet e' n :=
    fun n => by rw [mul_comm]; exact ramanujanLogDivisorJet_add_mul e' n e
  have hv : ∀ n, ramanujanLagCoefficient e (n + e * e') = ramanujanLagCoefficient e n :=
    fun n => ramanujanLagCoefficient_add_mul e n e'
  have huB : ∀ n, |ramanujanLogDivisorJet e' n| ≤ B := fun n =>
    (abs_ramanujanLogDivisorJet_le e' n).trans (le_add_of_nonneg_left (by positivity))
  have hvB : ∀ n, |ramanujanLagCoefficient e n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le e n).trans (le_add_of_nonneg_right hJ0)
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have h := tendsto_nearPairSum_div_overlap (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2)
    two_pos hA hL hL0 hq hu hv huB hvB hc0 hcinf hcN
  rw [periodicMean_ramanujanLogDivisorJet he' he, periodicMean_ramanujan_of_dvd he hq
    (dvd_mul_right e e'), integral_shellKernel hφ hsupp hM] at h
  convert h using 2
  have hM' := hM.ne'
  by_cases h1 : e = 1
  · simp only [h1, if_true]; field_simp
  · simp [h1]

/-- The exterior products vanish: `X/c → 0`. -/
theorem tendsto_nrExterior_div (e e' : ℕ) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (nrExterior φ (c N) N e e' + nrExterior φ (c N) N e' e) / c N) atTop
      (𝓝 0) := by
  obtain ⟨hr1, hr2, -⟩ := growingOverlap_rates hc1 hcinf hcN
  set K : ℝ := 12 * ((∑ t ∈ e'.divisors, (t : ℝ)) * e.totient +
    (∑ t ∈ e.divisors, (t : ℝ)) * e'.totient)
  have hlim : Tendsto (fun N : ℕ => K * (2 * (c N * (1 + Real.log (c N) + Real.log N) / N)))
      atTop (𝓝 0) := by simpa using (hr2.const_mul 2).const_mul K
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hr1.eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop 1] with N hN1' hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc := hc1 N
  have hc0 : 0 < c N := by linarith
  have hcN' : c N ≤ N := by rw [div_lt_one hN0] at hN1'; linarith
  have h1 := abs_nrExterior_le hφ hsupp hM hc0 hN1 hcN' e e'
  have h2 := abs_nrExterior_le hφ hsupp hM hc0 hN1 hcN' e' e
  have hlog : Real.log (4 * N) ≤ 2 * (1 + Real.log (c N) + Real.log N) := by
    rw [Real.log_mul (by norm_num) hN0.ne']
    have : Real.log 4 ≤ 2 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9; linarith
    have := Real.log_nonneg hc
    have := Real.log_natCast_nonneg N
    linarith
  have hσ : 0 ≤ (∑ t ∈ e'.divisors, (t : ℝ)) * e.totient +
      (∑ t ∈ e.divisors, (t : ℝ)) * e'.totient := by positivity
  have hlog0 : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
  have hpoly : (2 * c N + 1) * (c N + 1) ≤ 6 * c N ^ 2 := by nlinarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
  calc |nrExterior φ (c N) N e e' + nrExterior φ (c N) N e' e|
      ≤ |nrExterior φ (c N) N e e'| + |nrExterior φ (c N) N e' e| := abs_add_le _ _
    _ ≤ 2 * (2 * c N + 1) * (c N + 1) * (∑ t ∈ e'.divisors, (t : ℝ)) * e.totient *
          Real.log (4 * N) / N + 2 * (2 * c N + 1) * (c N + 1) * (∑ t ∈ e.divisors, (t : ℝ)) *
          e'.totient * Real.log (4 * N) / N := add_le_add h1 h2
    _ = 2 * ((2 * c N + 1) * (c N + 1)) * ((∑ t ∈ e'.divisors, (t : ℝ)) * e.totient +
          (∑ t ∈ e.divisors, (t : ℝ)) * e'.totient) * Real.log (4 * N) / N := by ring
    _ ≤ 2 * (6 * c N ^ 2) * ((∑ t ∈ e'.divisors, (t : ℝ)) * e.totient +
          (∑ t ∈ e.divisors, (t : ℝ)) * e'.totient) * (2 * (1 + Real.log (c N) + Real.log N)) / N := by
        gcongr
    _ = K * (2 * (c N * (1 + Real.log (c N) + Real.log N) / N)) * c N := by
        simp only [K]; field_simp; ring


/-- **The near block along a growing overlap.** Along `c → ∞`, `c² log² N/N → 0`:
`(Z(⟨Ov R_e, R_{e'}⟩ − ⟨NR R_e, R_{e'}⟩) + log(1/w) S/∫φ²)/c + [e = e' = 1] κ(log c − 2)`
converges to the near Gamma, near center and divisor-jet constants. -/
theorem tendsto_nearBlock_div_overlap {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (Real.sqrt e.totient * Real.sqrt e'.totient *
          (⟪Matrix.toEuclideanLin (overlapMatrix φ (c N) N) (ramanujanHorizonVector e N),
              ramanujanHorizonVector e' N⟫ -
            ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ (c N) N) (ramanujanHorizonVector e N),
              ramanujanHorizonVector e' N⟫) +
          Real.log (1 / (c N / N)) * (shellMass φ (c N) N e e' / ∫ u, φ u ^ 2)) / c N +
        (if e = 1 ∧ e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * (Real.log (c N) - 2) else 0))
      atTop (𝓝 ((if e' = 1 ∧ e = 1 then 2 / (∫ u, φ u ^ 2) * ∫ s in (0 : ℝ)..2, nearKernel φ s
          else 0) +
        (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * (if e = e' then (if e = 1 then
          Real.log 2 + Real.eulerMascheroniConstant - 1 else -ArithmeticFunction.vonMangoldt e)
          else 0) +
        ((if e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * ArithmeticFunction.vonMangoldt e
            else 0) +
          (if e = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * ArithmeticFunction.vonMangoldt e'
            else 0)))) := by
  obtain ⟨hr1, -, -⟩ := growingOverlap_rates hc1 hcinf hcN
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hL1 := tendsto_nearArchimedeanRemainderPair_div_overlap hφ hsupp hM he' he hc0 hcinf hr1
  have hL2 := tendsto_nearCenterPair_finite_part he he' hc0 hcinf hr1
  have hL3 := tendsto_logNearPair_div hφ hsupp hM he he' hc1 hcinf hcN
  have hL4 := tendsto_slopeNearPair_div hφ hsupp hM he he' hc1 hcinf hr1
  have hL5 := tendsto_jetNearPair_div hφ hsupp hM he he' hc1 hcinf hr1
  have hL6 := tendsto_jetNearPair_div' hφ hsupp hM he he' hc1 hcinf hr1
  have hL7 := tendsto_nrExterior_div hφ hsupp hM e e' hc1 hcinf hcN
  have hsum := ((((((hL1.add (hL2.const_mul ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)))).sub
    (hL3.const_mul 2)).sub hL4).add hL5).add hL6).sub hL7)
  convert hsum.congr' ?hev using 2
  case hev =>
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNB := nearBlock_eq hφ hsupp hM (hc0 N) hN he he'
    rw [hNB, nearPairSum_const_mul_weight]
    simp only [completeWeilPoleShift]
    have hcN0 := (hc0 N).ne'
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hM0 := hM.ne'
    split_ifs <;> field_simp <;> ring
  ring


end Limits


end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
