import GaloisForLFunctions.HTGeometry.NewtonIrrationalLevelVertex

/-!
# A leading vertex beats every other shift by a uniform margin

The weighted level of a shift polynomial is bounded above by `m − s μ`, so only finitely many shifts
can come within a fixed distance of the leading one.  On that finite set the strict inequalities
supplied by an irrational level have a positive minimum, and beyond it the crude bound already gives
a gap of one.

A uniform gap is exactly what a coefficient recursion needs: the comparison of one shift with all the
others is a sum over `μ ≤ n`, and a gap that degenerated as `μ` grew would leave the sum
uncontrolled.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The leading vertex has a uniform positive advantage over every other shift.** -/
theorem exists_uniform_weightedLevel_gap {m : ℕ} {Φ : ℕ → Polynomial ℂ} {s : ℝ} (hs : 0 < s)
    (hdeg : ∀ μ, (Φ μ).natDegree ≤ m) {ν : ℕ}
    (hmax : ∀ μ, Φ μ ≠ 0 → μ ≠ ν → weightedLevel s Φ μ < weightedLevel s Φ ν) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ μ : ℕ, Φ μ ≠ 0 → μ ≠ ν →
      weightedLevel s Φ μ + γ ≤ weightedLevel s Φ ν := by
  classical
  set L : ℝ := weightedLevel s Φ ν with hL
  set N₀ : ℕ := ⌈((m : ℝ) - L + 1) / s⌉₊ with hN₀
  have hfar : ∀ μ : ℕ, N₀ < μ → weightedLevel s Φ μ + 1 ≤ L := by
    intro μ hμ
    have h1 : ((m : ℝ) - L + 1) / s ≤ (N₀ : ℝ) := Nat.le_ceil _
    have h2 : (N₀ : ℝ) ≤ (μ : ℝ) := by exact_mod_cast le_of_lt hμ
    have h3 : ((m : ℝ) - L + 1) / s ≤ (μ : ℝ) := le_trans h1 h2
    have h4 : (m : ℝ) - L + 1 ≤ s * (μ : ℝ) := by
      rw [div_le_iff₀ hs] at h3
      linarith
    have h5 : (((Φ μ).natDegree : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (hdeg μ)
    rw [weightedLevel]
    linarith
  set T : Finset ℕ :=
    (Finset.range (N₀ + 1)).filter (fun μ => Φ μ ≠ 0 ∧ μ ≠ ν) with hT
  have hmemT : ∀ μ : ℕ, μ ≤ N₀ → Φ μ ≠ 0 → μ ≠ ν → μ ∈ T := by
    intro μ hμ h1 h2
    rw [hT, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by omega), h1, h2⟩
  by_cases hTne : T.Nonempty
  · obtain ⟨a, haT, hamin⟩ := T.exists_min_image (fun μ => L - weightedLevel s Φ μ) hTne
    have haprops : Φ a ≠ 0 ∧ a ≠ ν := by
      rw [hT, Finset.mem_filter] at haT
      exact haT.2
    have hapos : 0 < L - weightedLevel s Φ a := by
      have h := hmax a haprops.1 haprops.2
      linarith
    refine ⟨min 1 (L - weightedLevel s Φ a), lt_min zero_lt_one hapos, fun μ hμ hμν => ?_⟩
    by_cases hcase : μ ≤ N₀
    · have hmin := hamin μ (hmemT μ hcase hμ hμν)
      have hle : min 1 (L - weightedLevel s Φ a) ≤ L - weightedLevel s Φ μ :=
        le_trans (min_le_right _ _) hmin
      linarith
    · have hf := hfar μ (by omega)
      have hle : min 1 (L - weightedLevel s Φ a) ≤ 1 := min_le_left _ _
      linarith
  · refine ⟨1, zero_lt_one, fun μ hμ hμν => ?_⟩
    by_cases hcase : μ ≤ N₀
    · exact absurd ⟨μ, hmemT μ hcase hμ hμν⟩ hTne
    · exact hfar μ (by omega)

end GaloisForLFunctions.HTGeometry
