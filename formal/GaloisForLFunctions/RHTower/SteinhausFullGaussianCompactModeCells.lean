import GaloisForLFunctions.RHTower.SteinhausFullGaussianCompactPackets

open Filter Topology Finset Complex Metric
noncomputable section
namespace RHTower

/-- All prescribed modes persist on one fixed finite-character cell with whole-disc
accuracy, separated scale blocks, and their actual mean-weighted budgets. -/
theorem exists_fullGaussianCofactor_compact_mode_cell_blocks
    (S : Finset ℕ) (ω : SteinhausModel.Omega) (B0 : ℕ) (K ε : ℝ) (hε : 0 < ε)
    {c : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hrρ : r < ρ)
    (hc0 : 0 < c.re - ρ) (hc1 : c.re + ρ < 1)
    {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ) :
    ∃ ω' : SteinhausModel.Omega, (∀ p ∈ S, ω' p = ω p) ∧
      ∃ M : Fin k → ℕ, ∃ A : Fin k → ℂ, ∃ B : ℕ, ∃ δ : ℝ,
        B0 ≤ B ∧ 0 < δ ∧ (∀ i j, i < j → 2 * M i < M j) ∧
        ∀ i, B0 ≤ M i ∧ 1 ≤ M i ∧ A i ≠ 0 ∧ K ≤ (M i : ℝ) * ‖A i‖ ^ 2 ∧
          2 * M i ≤ B ∧ ∀ η : SteinhausModel.Omega,
            (∀ n ∈ Icc 1 B, ‖SteinhausModel.X n η - SteinhausModel.X n ω'‖ < δ) →
            ∀ R : ℝ, (M i : ℝ) ≤ R → R ≤ 2 * (M i : ℝ) → ∀ s ∈ closedBall c r,
              ‖relativeFullGaussianCofactorScalarMode s (t i) (A i) R η -
                smoothAFEGaussianKernel (s + (t i : ℂ) * I)‖ < ε := by
  classical
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hdisc (s : ℂ) (hs : s ∈ closedBall c r) : 0 ≤ s.re ∧ s.re ≤ c.re + ρ := by
    have habs : |s.re - c.re| ≤ dist s c := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
    have hd : dist s c ≤ r := hs
    have hl := (abs_le.mp habs).1
    have hu := (abs_le.mp habs).2
    constructor <;> linarith
  obtain ⟨ω', hp, M, A, hsep, hblocks⟩ :=
    exists_prescribed_fullGaussianCofactor_compact_mode_blocks S ω B0 K (ε / 2)
      (by positivity) hρ hrρ hc0 hc1 k t
  choose B' _hB' δ hδ htolerance using fun i : Fin k =>
    exists_relativeFullGaussianCofactor_compact_character_tolerance (c.re + ρ)
      (2 * (M i : ℝ)) (t i) (A i) (show 0 < ε / 2 by positivity)
  obtain ⟨i0, _, hmin⟩ := exists_min_image univ δ univ_nonempty
  let B := B0 + ∑ i, (2 * M i + B' i)
  have hB : ∀ i, 2 * M i + B' i ≤ B := by
    intro i
    have h := single_le_sum (f := fun j => 2 * M j + B' j)
      (fun j _ => Nat.zero_le (2 * M j + B' j)) (mem_univ i)
    omega
  refine ⟨ω', hp, M, A, B, δ i0, by omega, hδ i0, hsep, ?_⟩
  intro i
  obtain ⟨hB0, hMi, hAi, hbudget, hmode⟩ := hblocks i
  refine ⟨hB0, hMi, hAi, hbudget, by have := hB i; omega, ?_⟩
  intro η hcell R hlo hhi s hs
  have hR1 : 1 ≤ R := le_trans (by exact_mod_cast hMi) hlo
  have hpert := htolerance i s (hdisc s hs).1 (hdisc s hs).2 R hR1 hhi ω' η
    (fun n hn => (hcell n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
      (mem_Icc.mp hn).2.trans (by have := hB i; omega)⟩)).trans_le (hmin i (mem_univ i)))
  have hbase := hmode R hlo hhi s hs
  calc
    _ ≤ ‖relativeFullGaussianCofactorScalarMode s (t i) (A i) R η -
          relativeFullGaussianCofactorScalarMode s (t i) (A i) R ω'‖ +
        ‖relativeFullGaussianCofactorScalarMode s (t i) (A i) R ω' -
          smoothAFEGaussianKernel (s + (t i : ℂ) * I)‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (relativeFullGaussianCofactorScalarMode s (t i) (A i) R η)
        (relativeFullGaussianCofactorScalarMode s (t i) (A i) R ω')
        (smoothAFEGaussianKernel (s + (t i : ℂ) * I))
    _ < ε / 2 + ε / 2 := add_lt_add hpert hbase
    _ = ε := by ring

end RHTower
