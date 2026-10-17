import GaloisForLFunctions.BiScaleUncertainty.DyadicTriangularOptimality
import GaloisForLFunctions.BiScaleUncertainty.SignedGramCapacity

/-!
# Sharp logarithmic degeneration of actual signed dyadic Gram energy

One fixed smooth compact source realizes a positive anchored Gram minimum
`1 / (m + 1)` on the signed nodes with cutoff `N = 2^m`. Its full signed Gram
matrix is retained. Explicit positive triangular weights attain the minimum;
an exact squared-distance remainder classifies every equality case.

These are anchored packet coefficients, not physical collar partitions. This
conditioning law does not assert a sharp error for the physical allocation supremum.
-/

open MeasureTheory Filter Topology
open scoped BigOperators CompactlySupported ContDiff

namespace GaloisForLFunctions.BiScaleUncertainty.DyadicDifference
open RHTower.ArchimedeanAnomaly
noncomputable section

/-- The concrete source realizes the entire signed nearest-neighbor lattice kernel. -/
theorem source_dyadic_correlation (z : ℤ) :
    autocorr source ((z : ℝ) * step) = autocorr seed 0 *
      (2 * (if z = 0 then 1 else 0) - (if z = 1 then 1 else 0) -
        (if z = -1 then 1 else 0)) := by
  have h0 : translationFeature source 0 = atom 0 - atom 1 := by
    simpa only [Int.cast_zero, zero_mul, zero_add] using source_feature 0
  have hi := translationFeature_inner source 0 ((z : ℝ) * step)
  rw [h0, source_feature, inner_sub_left, inner_sub_right, inner_sub_right] at hi
  simp only [atom_inner, sub_zero] at hi
  have hh : (autocorr source ((z : ℝ) * step) : ℂ) =
      (autocorr seed 0 * (2 * (if z = 0 then 1 else 0) -
        (if z = 1 then 1 else 0) - (if z = -1 then 1 else 0)) : ℝ) := by
    rw [← hi]
    by_cases hz : z = 0
    · subst z
      norm_num
      ring
    by_cases h1 : z = 1
    · subst z
      norm_num
    by_cases hn : z = -1
    · subst z
      norm_num
    have h00 : (0 : ℤ) ≠ z := Ne.symm hz
    have h01 : (0 : ℤ) ≠ z + 1 := by omega
    have h10 : (1 : ℤ) ≠ z := Ne.symm h1
    have h11 : (1 : ℤ) ≠ z + 1 := by omega
    simp [hz, h1, hn, h00, h01, h10, h11]
  exact_mod_cast hh

def signedNodes (m : ℕ) : Finset (ℕ ⊕ ℕ) :=
  (Finset.range m).disjSum (Finset.range m)

def nodeIndex : ℕ ⊕ ℕ → ℕ := Sum.elim (fun k => 2 ^ (k + 1)) (fun k => 2 ^ (k + 1))

def signedShift : ℕ ⊕ ℕ → ℝ :=
  Sum.elim (fun k => -Real.log ((2 : ℝ) ^ (k + 1)))
    (fun k => Real.log ((2 : ℝ) ^ (k + 1)))

def signedWeight (a b : ℕ → ℝ) : ℕ ⊕ ℕ → ℝ := Sum.elim a b

/-- The full measured Gram form of the actual source, including its origin anchor. -/
def fullGram (m : ℕ) (a b : ℕ → ℝ) : ℝ :=
  AnchoredGram.gram source (signedNodes m) (signedWeight a b) signedShift 1

def normalizedGram (m : ℕ) (a b : ℕ → ℝ) : ℝ :=
  fullGram m a b / autocorr source 0

theorem signedShift_inl (k : ℕ) :
    signedShift (Sum.inl k) = ((-((k : ℤ) + 1) : ℤ) : ℝ) * step := by
  simp [signedShift, Real.log_pow, step, neg_mul]

theorem signedShift_inr (k : ℕ) :
    signedShift (Sum.inr k) = (((k : ℤ) + 1 : ℤ) : ℝ) * step := by
  simp [signedShift, Real.log_pow, step]

theorem signedNode_cutoff (m : ℕ) (p : ℕ ⊕ ℕ) (hp : p ∈ signedNodes m) :
    2 ≤ nodeIndex p ∧ nodeIndex p ≤ 2 ^ m := by
  cases p with
  | inl k =>
    have hk : k < m := by simpa [signedNodes] using hp
    change 2 ≤ 2 ^ (k + 1) ∧ 2 ^ (k + 1) ≤ 2 ^ m
    constructor
    · calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := by gcongr; omega
    · gcongr
      omega
  | inr k =>
    have hk : k < m := by simpa [signedNodes] using hp
    change 2 ≤ 2 ^ (k + 1) ∧ 2 ^ (k + 1) ≤ 2 ^ m
    constructor
    · calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := by gcongr; omega
    · gcongr
      omega

theorem gramPacket_eq_anchoredPacket (m : ℕ) (a b : ℕ → ℝ) :
    AnchoredGram.packet source (signedNodes m) (signedWeight a b) signedShift 1 =
      anchoredPacket m a b := by
  rw [AnchoredGram.packet, signedNodes, Finset.sum_disjSum]
  simp only [signedWeight, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_one, one_smul]
  rw [← Finset.sum_add_distrib]
  have h0 : translationFeature source 0 = edge 0 := by simp [edge]
  rw [h0]
  unfold anchoredPacket
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [signedShift_inl, signedShift_inr]
  rfl

theorem fullGram_eq_norm_sq (m : ℕ) (a b : ℕ → ℝ) :
    fullGram m a b = ‖anchoredPacket m a b‖ ^ 2 := by
  rw [fullGram, ← AnchoredGram.packet_norm_sq, gramPacket_eq_anchoredPacket]

/-- Exact sharp minimum plus actual-source remainder for the full signed Gram data. -/
theorem fullGram_exact_error (m : ℕ) (a b : ℕ → ℝ) :
    fullGram m a b = autocorr source 0 / ((m : ℝ) + 1) +
      ‖anchoredPacket m a b - producer m‖ ^ 2 := by
  rw [fullGram_eq_norm_sq, anchoredPacket_exact_error]

theorem normalizedGram_exact_error (m : ℕ) (a b : ℕ → ℝ) :
    normalizedGram m a b = 1 / ((m : ℝ) + 1) +
      ‖anchoredPacket m a b - producer m‖ ^ 2 / autocorr source 0 := by
  rw [normalizedGram, fullGram_exact_error, add_div]
  congr 1
  field_simp [source_energy_pos.ne']

theorem normalizedGram_minimum (m : ℕ) (a b : ℕ → ℝ) :
    1 / ((m : ℝ) + 1) ≤ normalizedGram m a b := by
  rw [normalizedGram_exact_error]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) source_energy_pos.le)

theorem fullGram_strictly_positive (m : ℕ) (a b : ℕ → ℝ) : 0 < fullGram m a b := by
  rw [fullGram_eq_norm_sq]
  exact anchoredPacket_strictly_positive m a b

theorem triangle_normalizedGram (m : ℕ) :
    normalizedGram m (triangle m) (triangle m) = 1 / ((m : ℝ) + 1) := by
  rw [normalizedGram_exact_error, triangle_attains]
  simp

theorem fullGram_minimum_iff_triangle (m : ℕ) (a b : ℕ → ℝ) :
    fullGram m a b = autocorr source 0 / ((m : ℝ) + 1) ↔
      ∀ k < m, a k = triangle m k ∧ b k = triangle m k := by
  rw [fullGram_eq_norm_sq, anchoredPacket_minimum_iff_triangle]

/-- The exact cutoff law is logarithmic in the actual largest integer node `2^m`. -/
theorem triangle_logarithmic_cutoff_law (m : ℕ) :
    normalizedGram m (triangle m) (triangle m) =
      Real.log 2 / (Real.log ((2 : ℝ) ^ m) + Real.log 2) := by
  rw [triangle_normalizedGram, Real.log_pow]
  have hd : Real.log 2 ≠ 0 := step_pos.ne'
  rw [show (m : ℝ) * Real.log 2 + Real.log 2 = ((m : ℝ) + 1) * Real.log 2 by ring]
  field_simp [hd]

theorem triangle_error_antitone :
    Antitone (fun m => normalizedGram m (triangle m) (triangle m)) := by
  intro m n h
  rw [triangle_normalizedGram, triangle_normalizedGram]
  have hn : (m : ℝ) ≤ n := by exact_mod_cast h
  gcongr

theorem triangle_error_tendsto_zero :
    Tendsto (fun m => normalizedGram m (triangle m) (triangle m)) atTop (𝓝 0) := by
  simp only [triangle_normalizedGram]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Even nonnegative anchored coefficients admit no positive cutoff-uniform bound. -/
theorem no_uniform_positive_anchored_bound :
    ¬∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (a b : ℕ → ℝ),
      (∀ k < m, 0 ≤ a k ∧ 0 ≤ b k) → c ≤ normalizedGram m a b := by
  rintro ⟨c, hc, hb⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / c)
  have hl := hb m (triangle m) (triangle m) (fun k hk =>
    ⟨(triangle_pos m k hk).le, (triangle_pos m k hk).le⟩)
  rw [triangle_normalizedGram] at hl
  have hm' : 1 < (m : ℝ) * c := (div_lt_iff₀ hc).mp hm
  have hu : 1 / ((m : ℝ) + 1) < c := by
    apply (div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mpr
    nlinarith only [hm', hc]
  exact (not_lt_of_ge hl) hu

end
end GaloisForLFunctions.BiScaleUncertainty.DyadicDifference
