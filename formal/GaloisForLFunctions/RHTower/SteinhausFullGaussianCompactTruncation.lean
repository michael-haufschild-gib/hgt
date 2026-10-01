import GaloisForLFunctions.RHTower.SteinhausFullGaussianCompactModeCells

open Filter Topology Finset Complex Metric
noncomputable section
namespace RHTower

/-- Exact coherent normalization of the literal truncated Gaussian cofactor. -/
def relativeTruncatedFullGaussianCofactorScalarMode (s : ℂ) (t : ℝ) (A : ℂ)
    (R : ℝ) (L : ℕ) (ω : SteinhausModel.Omega) : ℂ :=
  A⁻¹ * (truncatedFullGaussianCofactor s R L ω * (R : ℂ) ^ (-(s + (t : ℂ) * I)))

/-- One cutoff controls the normalized literal truncation across the whole abscissa
band, every phase, and every bounded scale interval starting at one. -/
theorem eventually_relativeTruncatedFullGaussianCofactor_compact_error
    (b U t : ℝ) {A : ℂ} (hA : A ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b →
      ∀ R : ℝ, 1 ≤ R → R ≤ U → ∀ ω : SteinhausModel.Omega,
        ‖relativeTruncatedFullGaussianCofactorScalarMode s t A R L ω -
          relativeFullGaussianCofactorScalarMode s t A R ω‖ < ε := by
  have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
  obtain ⟨B, _, htail⟩ := exists_fullGaussianCofactor_uniform_abscissa_tail b U
    (mul_pos hε hAnorm)
  filter_upwards [eventually_ge_atTop B] with L hL
  intro s hs0 hsb R hR hRU ω
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have h := htail L hL s hsb R hR0 hRU ω
  rw [norm_sub_rev] at h
  have hp : ‖(R : ℂ) ^ (-(s + (t : ℂ) * I))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hR0]
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hR (neg_nonpos.mpr hs0)
  have heq : relativeTruncatedFullGaussianCofactorScalarMode s t A R L ω -
      relativeFullGaussianCofactorScalarMode s t A R ω =
      (A⁻¹ * (truncatedFullGaussianCofactor s R L ω - steinhausFullGaussianCofactor s R ω)) *
        (R : ℂ) ^ (-(s + (t : ℂ) * I)) := by
    unfold relativeTruncatedFullGaussianCofactorScalarMode relativeFullGaussianCofactorScalarMode
    ring
  rw [heq, norm_mul, norm_mul, norm_inv]
  calc
    _ ≤ (‖A‖⁻¹ * ‖truncatedFullGaussianCofactor s R L ω -
        steinhausFullGaussianCofactor s R ω‖) * 1 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ < ‖A‖⁻¹ * (ε * ‖A‖) := by
      rw [mul_one]
      exact mul_lt_mul_of_pos_left h (inv_pos.mpr hAnorm)
    _ = ε := by field_simp [hAnorm.ne']

/-- The same fixed character cell realizes every compact Gaussian mode through literal
finite cofactors, uniformly above a single cutoff and throughout every scale block. -/
theorem exists_truncatedGaussianCofactor_compact_mode_cell_blocks
    (S : Finset ℕ) (ω : SteinhausModel.Omega) (B0 : ℕ) (K ε : ℝ) (hε : 0 < ε)
    {c : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hrρ : r < ρ)
    (hc0 : 0 < c.re - ρ) (hc1 : c.re + ρ < 1)
    {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ) :
    ∃ ω' : SteinhausModel.Omega, (∀ p ∈ S, ω' p = ω p) ∧
      ∃ M : Fin k → ℕ, ∃ A : Fin k → ℂ, ∃ B D : ℕ, ∃ δ : ℝ,
        B0 ≤ B ∧ 0 < δ ∧ (∀ i j, i < j → 2 * M i < M j) ∧
        ∀ i, B0 ≤ M i ∧ 1 ≤ M i ∧ A i ≠ 0 ∧ K ≤ (M i : ℝ) * ‖A i‖ ^ 2 ∧
          2 * M i ≤ B ∧ ∀ η : SteinhausModel.Omega,
            (∀ n ∈ Icc 1 B, ‖SteinhausModel.X n η - SteinhausModel.X n ω'‖ < δ) →
            ∀ R : ℝ, (M i : ℝ) ≤ R → R ≤ 2 * (M i : ℝ) → ∀ L : ℕ, D ≤ L →
              ∀ s ∈ closedBall c r,
                ‖relativeTruncatedFullGaussianCofactorScalarMode s (t i) (A i) R L η -
                  smoothAFEGaussianKernel (s + (t i : ℂ) * I)‖ < ε := by
  classical
  obtain ⟨ω', hp, M, A, B, δ, hB, hδ, hsep, hblocks⟩ :=
    exists_fullGaussianCofactor_compact_mode_cell_blocks S ω B0 K (ε / 2)
      (by positivity) hρ hrρ hc0 hc1 hk t
  have herrors : ∀ᶠ L : ℕ in atTop, ∀ i : Fin k, ∀ s : ℂ,
      0 ≤ s.re → s.re ≤ c.re + ρ → ∀ R : ℝ, 1 ≤ R → R ≤ 2 * (M i : ℝ) →
      ∀ η : SteinhausModel.Omega,
        ‖relativeTruncatedFullGaussianCofactorScalarMode s (t i) (A i) R L η -
          relativeFullGaussianCofactorScalarMode s (t i) (A i) R η‖ < ε / 2 :=
    Filter.eventually_all.mpr (fun i =>
      eventually_relativeTruncatedFullGaussianCofactor_compact_error (c.re + ρ)
        (2 * (M i : ℝ)) (t i) (hblocks i).2.2.1 (show 0 < ε / 2 by positivity))
  obtain ⟨D, hD⟩ := Filter.eventually_atTop.mp herrors
  refine ⟨ω', hp, M, A, B, D, δ, hB, hδ, hsep, ?_⟩
  intro i
  obtain ⟨hB0, hMi, hAi, hbudget, hMB, hmode⟩ := hblocks i
  refine ⟨hB0, hMi, hAi, hbudget, hMB, ?_⟩
  intro η hcell R hlo hhi L hL s hs
  have hR1 : 1 ≤ R := le_trans (by exact_mod_cast hMi) hlo
  have habs : |s.re - c.re| ≤ dist s c := by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
  have hd : dist s c ≤ r := hs
  have hl := (abs_le.mp habs).1
  have hu := (abs_le.mp habs).2
  have hpert := hD L hL i s (by linarith) (by linarith) R hR1 hhi η
  have hbase := hmode η hcell R hlo hhi s hs
  calc
    _ ≤ ‖relativeTruncatedFullGaussianCofactorScalarMode s (t i) (A i) R L η -
          relativeFullGaussianCofactorScalarMode s (t i) (A i) R η‖ +
        ‖relativeFullGaussianCofactorScalarMode s (t i) (A i) R η -
          smoothAFEGaussianKernel (s + (t i : ℂ) * I)‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (relativeTruncatedFullGaussianCofactorScalarMode s (t i) (A i) R L η)
        (relativeFullGaussianCofactorScalarMode s (t i) (A i) R η)
        (smoothAFEGaussianKernel (s + (t i : ℂ) * I))
    _ < ε / 2 + ε / 2 := add_lt_add hpert hbase
    _ = ε := by ring

end RHTower
