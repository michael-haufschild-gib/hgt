import GaloisForLFunctions.RHTower.SmoothAFECorrectedCofactorModes
import GaloisForLFunctions.RHTower.HighBlockCutoffMonotone

/-!
# Fixed phase cells for literal corrected cofactor modes

For bounded cofactor lengths, character perturbations control every corrected row uniformly
in the actual prime-channel floor ratio and every positive Gaussian smoothing scale. The cutoff
has norm at most one; the floor factor has norm at most two at nodes with positive real part.
The remaining finite sum gives an explicit finite perturbation constant.

Applying this estimate with half the mode tolerance preserves all prescribed coherent blocks
on one fixed positive-radius finite-character cell. This supplies uniform stability, separately
from the cell's measure, the conditional centre, and deterministic recurrence.
-/

noncomputable section
open Filter Topology Finset Complex
namespace RHTower

private theorem norm_cutoff_le_one {r : ℝ} (hr : 0 < r) : ‖smoothAFECutoff r‖ ≤ 1 := by
  have heq : smoothAFECutoff r = ((smoothAFECutoff r).re : ℂ) := by
    apply Complex.ext <;> simp [smoothAFECutoff_im_eq_zero hr]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (smoothAFECutoff_re_nonneg hr)]
  exact smoothAFECutoff_re_le_one hr

private theorem norm_floor_cpow_le_two {s : ℂ} (hs : 0 < s.re)
    {N p : ℕ} (hN : 0 < N) (hp : 0 < p) (hL : 0 < N / p) :
    ‖(primeCofactorFloorRatio N p : ℂ) ^ (s - 1)‖ ≤ 2 := by
  obtain ⟨hq, hq1, hqL⟩ := primeCofactorFloorRatio_bounds hN hp hL
  have hLR : (1 : ℝ) ≤ (N / p : ℕ) := by exact_mod_cast hL
  have hhalf : 1 / 2 ≤ primeCofactorFloorRatio N p := by
    have h : (1 / 2 : ℝ) ≤ ((N / p : ℕ) : ℝ) / ((N / p : ℕ) + 1) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    exact h.trans hqL.le
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
  calc
    _ ≤ (primeCofactorFloorRatio N p) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hq hq1 (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    _ ≤ (1 / 2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hhalf (by norm_num)
    _ = 2 := by rw [Real.rpow_neg_one]; norm_num

private theorem smoothCofactorNodeVector_sub_le {J : ℕ} (s : Fin J → ℂ)
    {L : ℕ} (hL : 0 < L) {r δ : ℝ} (hr : 0 < r)
    (omega eta : SteinhausModel.Omega)
    (hcell : ∀ n ∈ Icc 1 L, ‖SteinhausModel.X n eta - SteinhausModel.X n omega‖ ≤ δ)
    (j : Fin J) :
    ‖smoothCofactorNodeVector s r L eta j - smoothCofactorNodeVector s r L omega j‖ ≤
      ((∑ n ∈ Icc 1 L, ‖(n : ℂ) ^ (s j - 1)‖) * ‖(L : ℂ) ^ (-s j)‖) * δ := by
  have hdiff : smoothCofactorNodeVector s r L eta j - smoothCofactorNodeVector s r L omega j =
      (∑ n ∈ Icc 1 L, smoothAFECutoff (r * ((n : ℝ) / L)) *
        (SteinhausModel.X n eta - SteinhausModel.X n omega) * (n : ℂ) ^ (s j - 1)) *
        (L : ℂ) ^ (-s j) := by
    simp only [smoothCofactorNodeVector, ← sub_mul, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hdiff, norm_mul]
  have hsum : ‖∑ n ∈ Icc 1 L, smoothAFECutoff (r * ((n : ℝ) / L)) *
        (SteinhausModel.X n eta - SteinhausModel.X n omega) * (n : ℂ) ^ (s j - 1)‖ ≤
      (∑ n ∈ Icc 1 L, ‖(n : ℂ) ^ (s j - 1)‖) * δ := by
    calc
      _ ≤ ∑ n ∈ Icc 1 L, ‖smoothAFECutoff (r * ((n : ℝ) / L)) *
        (SteinhausModel.X n eta - SteinhausModel.X n omega) * (n : ℂ) ^ (s j - 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Icc 1 L, ‖(n : ℂ) ^ (s j - 1)‖ * δ := by
        apply Finset.sum_le_sum
        intro n hn
        have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hLR : (0 : ℝ) < L := by exact_mod_cast hL
        have hW := norm_cutoff_le_one (mul_pos hr (div_pos hnR hLR))
        simp only [norm_mul]
        calc
          _ ≤ 1 * δ * ‖(n : ℂ) ^ (s j - 1)‖ := by gcongr; exact hcell n hn
          _ = _ := by ring
      _ = _ := (Finset.sum_mul ..).symm
  calc
    _ ≤ ((∑ n ∈ Icc 1 L, ‖(n : ℂ) ^ (s j - 1)‖) * δ) *
        ‖(L : ℂ) ^ (-s j)‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    _ = _ := by ring

/-- Bounded cofactor lengths make the exact corrected rows uniformly stable under
finite-character perturbations, for every positive smoothing scale and actual floor ratio. -/
theorem exists_correctedCofactorMode_character_tolerance {J : ℕ} (s : Fin J → ℂ)
    (hs : ∀ j, 0 < (s j).re) (t : ℝ) (A : ℂ) (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N p : ℕ, 0 < N → 0 < p → 0 < N / p → N / p ≤ B →
      ∀ r : ℝ, 0 < r → ∀ omega eta : SteinhausModel.Omega,
        (∀ n ∈ Icc 1 B, ‖SteinhausModel.X n eta - SteinhausModel.X n omega‖ < δ) →
        ‖correctedCofactorMode s t A r N p eta - correctedCofactorMode s t A r N p omega‖ < ε := by
  classical
  let C : ℕ → Fin J → ℝ := fun L j => 2 * ‖A⁻¹‖ *
    ((∑ n ∈ Icc 1 L, ‖(n : ℂ) ^ (s j - 1)‖) * ‖(L : ℂ) ^ (-s j)‖)
  let D : ℝ := 1 + ∑ L ∈ Icc 1 B, ∑ j, C L j
  have hC : ∀ L j, 0 ≤ C L j := by intros; dsimp only [C]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hCD : ∀ L ∈ Icc 1 B, ∀ j, C L j ≤ D := by
    intro L hLB j
    have h1 := Finset.single_le_sum (fun k _ => hC L k) (mem_univ j)
    have h2 := Finset.single_le_sum (f := fun k => ∑ l, C k l)
      (fun k _ => Finset.sum_nonneg (fun l _ => hC k l)) hLB
    dsimp only [D]
    linarith
  refine ⟨ε / (2 * D), by positivity, ?_⟩
  intro N p hN hp hL hLB r hr omega eta hcell
  rw [pi_norm_lt_iff hε]
  intro j
  have hq := (primeCofactorFloorRatio_bounds hN hp hL).1
  have hvec := smoothCofactorNodeVector_sub_le s hL (mul_pos hr hq)
    omega eta
    (fun n hn => (hcell n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hLB⟩)).le) j
  have hpow : ‖((N / p : ℕ) : ℂ) ^ (-((t : ℂ) * I))‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hL]
    simp
  have hQ := norm_floor_cpow_le_two (hs j) hN hp hL
  have hbound : ‖correctedCofactorMode s t A r N p eta j -
      correctedCofactorMode s t A r N p omega j‖ ≤ C (N / p) j * (ε / (2 * D)) := by
    simp only [correctedCofactorMode, relativeSmoothCofactorMode, Pi.smul_apply, smul_eq_mul,
      ← mul_sub, norm_mul, hpow, one_mul]
    calc
      _ ≤ 2 * (‖A⁻¹‖ *
          (((∑ n ∈ Icc 1 (N / p), ‖(n : ℂ) ^ (s j - 1)‖) *
            ‖((N / p : ℕ) : ℂ) ^ (-s j)‖) * (ε / (2 * D)))) := by gcongr
      _ = _ := by dsimp only [C]; ring
  calc
    _ ≤ C (N / p) j * (ε / (2 * D)) := hbound
    _ ≤ D * (ε / (2 * D)) := by gcongr; exact hCD _ (mem_Icc.mpr ⟨hL, hLB⟩) j
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- The prescribed cofactor blocks hold throughout one fixed finite-character cell. -/
theorem exists_corrected_cofactor_mode_cell_blocks
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (omega : SteinhausModel.Omega) (B₀ : ℕ) (K ε : ℝ) (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ M : Fin k → ℕ, ∃ A : Fin k → ℂ, ∃ r₀ : ℝ, ∃ B : ℕ, ∃ δ : ℝ,
        0 < r₀ ∧ 0 < δ ∧ (∀ i j, i < j → 2 * M i < M j) ∧
        ∀ i, B₀ ≤ M i ∧ 0 < M i ∧ A i ≠ 0 ∧ K ≤ (M i : ℝ) * ‖A i‖ ^ 2 ∧
          2 * M i ≤ B ∧
          ∀ eta : SteinhausModel.Omega,
            (∀ n ∈ Icc 1 B, ‖SteinhausModel.X n eta - SteinhausModel.X n omega'‖ < δ) →
            ∀ N p : ℕ, 0 < N → 0 < p → M i ≤ N / p → N / p ≤ 2 * M i →
              ∀ r : ℝ, 0 < r → r ≤ r₀ →
                ‖correctedCofactorMode s (t i) (A i) r N p eta - cofactorCauchyMode s (t i)‖ < ε := by
  classical
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨omega', hp, M, A, r₀, hr₀, hsep, hblocks⟩ :=
    exists_corrected_cofactor_mode_blocks s hs hs1 S omega B₀ K (ε / 2) (by positivity) k t
  choose δ hδ htolerance using fun i : Fin k =>
    exists_correctedCofactorMode_character_tolerance s hs (t i) (A i) (2 * M i)
      (show 0 < ε / 2 by positivity)
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image univ δ univ_nonempty
  let B := ∑ i, 2 * M i
  have hB : ∀ i, 2 * M i ≤ B := by
    intro i
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (2 * M j)) (mem_univ i)
  refine ⟨omega', hp, M, A, r₀, B, δ i₀, hr₀, hδ i₀, hsep, ?_⟩
  intro i
  obtain ⟨hB₀, hMi, hAi, hbudget, hmode⟩ := hblocks i
  refine ⟨hB₀, hMi, hAi, hbudget, hB i, ?_⟩
  intro eta hcell N p hN hpp hlo hhi r hr hrle
  have hpert := htolerance i N p hN hpp (hMi.trans_le hlo) hhi r hr omega' eta
    (fun n hn => (hcell n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans (hB i)⟩)).trans_le
      (hmin i (mem_univ i)))
  have hbase := hmode N p hN hpp hlo hhi r hr hrle
  calc
    _ ≤ ‖correctedCofactorMode s (t i) (A i) r N p eta -
        correctedCofactorMode s (t i) (A i) r N p omega'‖ +
        ‖correctedCofactorMode s (t i) (A i) r N p omega' - cofactorCauchyMode s (t i)‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (correctedCofactorMode s (t i) (A i) r N p eta)
        (correctedCofactorMode s (t i) (A i) r N p omega') (cofactorCauchyMode s (t i))
    _ < ε / 2 + ε / 2 := add_lt_add hpert hbase
    _ = ε := by ring

/-- The positive Gaussian smoothing cutoff has norm at most one at every scale. -/
theorem norm_smoothAFECutoff_le_one {r : ℝ} (hr : 0 < r) : ‖smoothAFECutoff r‖ ≤ 1 :=
  norm_cutoff_le_one hr

end RHTower
