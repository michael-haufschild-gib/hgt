import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSectorGrams
import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDephasingLimit

/-!
# Trace-preserving dephasing of the actual Weil probe matrix

Cauchy dephasing preserves each positive reflection-sector Gram, hence the
two-sided Hilbert bound on the indefinite Weil matrix. Every finite iterate
has exactly the original diagonal and trace. Its limit retains precisely
the blocks whose chosen logarithmic rates coincide.
-/

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open HilbertMetric.CauchyDephasing

/-- Repeated normalized Cauchy smoothing of the actual Weil Gram. -/
def dephasedProbeGram {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) : Matrix (Fin n) (Fin n) ℂ :=
  channelPower k r (probeGram (fun i => (p i).val))

private theorem channelPower_add_matrix {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    channelPower k r (A + B) = channelPower k r A + channelPower k r B := by
  ext i j
  exact mul_add _ _ _

private theorem channelPower_sub_matrix {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    channelPower k r (A - B) = channelPower k r A - channelPower k r B := by
  ext i j
  exact mul_sub _ _ _

/-- Both reflection-sector Grams remain positive at every iteration. -/
theorem dephased_sectorGrams_posSemidef {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    (channelPower k r (positiveProbeGram p)).PosSemidef ∧
      (channelPower k r (negativeProbeGram p)).PosSemidef := by
  induction k with
  | zero =>
    simpa only [channelPower_zero] using
      And.intro (positiveProbeGram_posSemidef p) (negativeProbeGram_posSemidef p)
  | succ k ih =>
    simp only [channelPower_succ, channel_eq_hadamard]
    exact ⟨ih.1.hadamard (symbol_posSemidef r), ih.2.hadamard (symbol_posSemidef r)⟩

/-- Dephasing retains the exact signed-sector decomposition of the Weil form. -/
theorem dephasedProbeGram_sector_difference {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    dephasedProbeGram k r p = channelPower k r (positiveProbeGram p) -
      channelPower k r (negativeProbeGram p) := by
  rw [dephasedProbeGram, probeGram_eq_sector_difference, channelPower_sub_matrix]

/-- The Hilbert matrix bounds the signed Weil matrix throughout dephasing. -/
theorem dephasedProbeGram_hilbert_sandwich {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    (channelPower k r (hilbertProbeGram p) + dephasedProbeGram k r p).PosSemidef ∧
      (channelPower k r (hilbertProbeGram p) - dephasedProbeGram k r p).PosSemidef := by
  unfold dephasedProbeGram
  rw [← channelPower_add_matrix, ← channelPower_sub_matrix]
  induction k with
  | zero =>
    simpa only [channelPower_zero] using
      And.intro (hilbertProbeGram_add_probeGram_posSemidef p)
        (hilbertProbeGram_sub_probeGram_posSemidef p)
  | succ k ih =>
    simp only [channelPower_succ, channel_eq_hadamard]
    exact ⟨ih.1.hadamard (symbol_posSemidef r), ih.2.hadamard (symbol_posSemidef r)⟩

/-- Every arithmetic diagonal entry survives every dephasing step. -/
theorem dephasedProbeGram_diagonal {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) (i : Fin n) :
    dephasedProbeGram k r p i i = probeGram (fun j => (p j).val) i i := by
  simp only [dephasedProbeGram, channelPower, coherence_self,
    Complex.ofReal_one, one_pow, one_mul]

/-- The total signed Weil trace is invariant under normalized smoothing. -/
theorem trace_dephasedProbeGram {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    trace (dephasedProbeGram k r p) = trace (probeGram (fun i => (p i).val)) :=
  trace_channelPower k r _

/-- The arithmetic matrix converges to its equal-rate block projection. -/
theorem dephasedProbeGram_tendsto {n : ℕ} (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    Tendsto (fun k => dephasedProbeGram k r p) atTop
      (𝓝 (pinching r (probeGram (fun i => (p i).val)))) :=
  channelPower_tendsto_pinching r _

#print axioms dephased_sectorGrams_posSemidef
#print axioms dephasedProbeGram_sector_difference
#print axioms dephasedProbeGram_hilbert_sandwich
#print axioms trace_dephasedProbeGram
#print axioms dephasedProbeGram_tendsto

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
