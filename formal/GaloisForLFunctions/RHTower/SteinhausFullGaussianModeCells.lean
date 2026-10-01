import GaloisForLFunctions.RHTower.SteinhausFullGaussianModePackets
import GaloisForLFunctions.RHTower.SteinhausFullGaussianCharacterStability


open Filter Topology Finset
noncomputable section
namespace RHTower

/-- A positive finite-character tolerance preserves all normalized full Gaussian node responses
uniformly on a bounded scale interval away from zero. -/
theorem exists_relativeFullGaussianCofactorMode_character_tolerance
    {J : ℕ} (hJ : 0 < J) (s : Fin J → ℂ) (hs : ∀ j, 0 ≤ (s j).re)
    (t : ℝ) {A : ℂ} (hA : A ≠ 0) (U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R → R ≤ U →
      ∀ ω η : SteinhausModel.Omega,
        (∀ n ∈ Icc 1 B, ‖SteinhausModel.X n η - SteinhausModel.X n ω‖ < δ) →
        ‖relativeFullGaussianCofactorMode s t A R η -
          relativeFullGaussianCofactorMode s t A R ω‖ < ε := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
  choose B _hB δ hδ htolerance using fun j =>
    exists_fullGaussianCofactor_character_tolerance (s j) U (mul_pos hε hAnorm)
  obtain ⟨j₀, _, hmin⟩ := exists_min_image univ δ univ_nonempty
  refine ⟨univ.sup B, δ j₀, hδ j₀, fun R hR hRU ω η hcell => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have htwist : ‖(R : ℂ) ^ (-((t : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hR0]
    simp
  apply (pi_norm_lt_iff hε).mpr
  intro j
  have hd := htolerance j R hR0 hRU ω η
    (fun n hn => (hcell n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
      (mem_Icc.mp hn).2.trans (le_sup (mem_univ j))⟩)).trans_le (hmin j (mem_univ j)))
  have heq : relativeFullGaussianCofactorMode s t A R η j -
      relativeFullGaussianCofactorMode s t A R ω j =
      A⁻¹ * ((R : ℂ) ^ (-((t : ℂ) * Complex.I)) *
        ((steinhausFullGaussianCofactor (s j) R η - steinhausFullGaussianCofactor (s j) R ω) *
          (R : ℂ) ^ (-s j))) := by
    simp only [relativeFullGaussianCofactorMode, fullGaussianCofactorNodeVector,
      Pi.smul_apply, smul_eq_mul]
    ring
  change ‖relativeFullGaussianCofactorMode s t A R η j -
    relativeFullGaussianCofactorMode s t A R ω j‖ < ε
  rw [heq, norm_mul, norm_mul, norm_mul, norm_inv, htwist, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hR0, Complex.neg_re]
  calc
    _ ≤ ‖A‖⁻¹ * ‖steinhausFullGaussianCofactor (s j) R η -
        steinhausFullGaussianCofactor (s j) R ω‖ :=
      mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hR
          (neg_nonpos.mpr (hs j)))) (inv_nonneg.mpr hAnorm.le)
    _ < ‖A‖⁻¹ * (ε * ‖A‖) := mul_lt_mul_of_pos_left hd (inv_pos.mpr hAnorm)
    _ = ε := by field_simp [hAnorm.ne']

/-- All prescribed full Gaussian mode blocks persist on one fixed positive-radius character
cell, retaining the original finite phase prescription. -/
theorem exists_fullGaussianCofactor_mode_cell_blocks
    {J : ℕ} (hJ : 0 < J) (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (ω : SteinhausModel.Omega) (B₀ : ℕ) (K ε : ℝ) (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ) :
    ∃ ω' : SteinhausModel.Omega, (∀ p ∈ S, ω' p = ω p) ∧
      ∃ M : Fin k → ℕ, ∃ A : Fin k → ℂ, ∃ B : ℕ, ∃ δ : ℝ,
        B₀ ≤ B ∧ 0 < δ ∧ (∀ i j, i < j → 2 * M i < M j) ∧
        ∀ i, B₀ ≤ M i ∧ 1 ≤ M i ∧ A i ≠ 0 ∧ K ≤ (M i : ℝ) * ‖A i‖ ^ 2 ∧
          2 * M i ≤ B ∧ ∀ η : SteinhausModel.Omega,
            (∀ n ∈ Icc 1 B, ‖SteinhausModel.X n η - SteinhausModel.X n ω'‖ < δ) →
            ∀ R : ℝ, (M i : ℝ) ≤ R → R ≤ 2 * (M i : ℝ) →
              ‖relativeFullGaussianCofactorMode s (t i) (A i) R η -
                (fun j => smoothAFEGaussianKernel (s j + (t i : ℂ) * Complex.I))‖ < ε := by
  classical
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨ω', hp, M, A, hsep, hblocks⟩ :=
    exists_prescribed_fullGaussianCofactor_mode_blocks s hs hs1 S ω B₀ K (ε / 2)
      (by positivity) k t
  choose B' δ hδ htolerance using fun i : Fin k =>
    exists_relativeFullGaussianCofactorMode_character_tolerance hJ s (fun j => (hs j).le)
      (t i) ((hblocks i).2.2.1) (2 * (M i : ℝ)) (show 0 < ε / 2 by positivity)
  obtain ⟨i₀, _, hmin⟩ := exists_min_image univ δ univ_nonempty
  let B := B₀ + ∑ i, (2 * M i + B' i)
  have hB : ∀ i, 2 * M i + B' i ≤ B := by
    intro i
    have h := single_le_sum (fun j _ => Nat.zero_le (2 * M j + B' j)) (mem_univ i)
    omega
  refine ⟨ω', hp, M, A, B, δ i₀, by omega, hδ i₀, hsep, ?_⟩
  intro i
  obtain ⟨hB₀, hMi, hAi, hbudget, hmode⟩ := hblocks i
  refine ⟨hB₀, hMi, hAi, hbudget, by have := hB i; omega, ?_⟩
  intro η hcell R hlo hhi
  have hR1 : 1 ≤ R := le_trans (by exact_mod_cast hMi) hlo
  have hpert := htolerance i R hR1 hhi ω' η
    (fun n hn => (hcell n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
      (mem_Icc.mp hn).2.trans (by have := hB i; omega)⟩)).trans_le (hmin i (mem_univ i)))
  have hbase := hmode R hlo hhi
  calc
    _ ≤ ‖relativeFullGaussianCofactorMode s (t i) (A i) R η -
          relativeFullGaussianCofactorMode s (t i) (A i) R ω'‖ +
        ‖relativeFullGaussianCofactorMode s (t i) (A i) R ω' -
          (fun j => smoothAFEGaussianKernel (s j + (t i : ℂ) * Complex.I))‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (relativeFullGaussianCofactorMode s (t i) (A i) R η)
        (relativeFullGaussianCofactorMode s (t i) (A i) R ω')
        (fun j => smoothAFEGaussianKernel (s j + (t i : ℂ) * Complex.I))
    _ < ε / 2 + ε / 2 := add_lt_add hpert hbase
    _ = ε := by ring

end RHTower
