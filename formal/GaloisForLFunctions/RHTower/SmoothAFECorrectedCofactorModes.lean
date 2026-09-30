import GaloisForLFunctions.RHTower.SmoothAFEReflectedCofactorTransfer

/-!
# Uniformly corrected cofactor modes for actual prime channels

Construct the cofactor blocks only after choosing an initial cutoff that controls the exact
floor factor at every fixed node. The Gaussian mode approximation survives multiplication
by that factor, uniformly for all actual channels whose integer cofactor cutoff lies in a
constructed block and for every sufficiently small common positive smoothing parameter.

This retains arbitrary mean-weighted length budgets and any prescribed finite phase prefix.
The resulting rows are the ones in the literal channel factorization; a conditional Gram
bound and the simultaneous target law still require further assembly.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower

/-- A cofactor mode including the exact fixed-node floor factor of a literal prime channel. -/
def correctedCofactorMode {J : ℕ} (s : Fin J → ℂ) (t : ℝ) (A : ℂ)
    (r : ℝ) (N p : ℕ) (omega : SteinhausModel.Omega) : Fin J → ℂ := fun j =>
  (primeCofactorFloorRatio N p : ℂ) ^ (s j - 1) *
    relativeSmoothCofactorMode s t A (r * primeCofactorFloorRatio N p) (N / p) omega j

/-- The prescribed-mode construction controls the exact floor-corrected rows, uniformly
for every channel whose cofactor cutoff belongs to one of the separated blocks. -/
theorem exists_corrected_cofactor_mode_blocks
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (omega : SteinhausModel.Omega) (B : ℕ) (K ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (t : Fin k → ℝ) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ M : Fin k → ℕ, ∃ A : Fin k → ℂ, ∃ r₀ : ℝ, 0 < r₀ ∧
        (∀ i j, i < j → 2 * M i < M j) ∧
        ∀ i, B ≤ M i ∧ 0 < M i ∧ A i ≠ 0 ∧ K ≤ (M i : ℝ) * ‖A i‖ ^ 2 ∧
          ∀ N p : ℕ, 0 < N → 0 < p → M i ≤ N / p → N / p ≤ 2 * M i →
            ∀ r : ℝ, 0 < r → r ≤ r₀ →
              ‖correctedCofactorMode s (t i) (A i) r N p omega' - cofactorCauchyMode s (t i)‖ < ε := by
  classical
  let H : ℝ := 1 + ∑ i, ‖cofactorCauchyMode s (t i)‖
  have hH : 0 < H := by dsimp only [H]; positivity
  have hCH : ∀ i j, ‖cofactorCauchyMode s (t i) j‖ ≤ H := by
    intro i j
    have hi : ‖cofactorCauchyMode s (t i)‖ ≤ ∑ l, ‖cofactorCauchyMode s (t l)‖ :=
      Finset.single_le_sum (fun l _ => norm_nonneg (cofactorCauchyMode s (t l))) (mem_univ i)
    exact (norm_le_pi_norm _ j).trans (by dsimp only [H]; linarith)
  let δ := min 1 (ε / (4 * H))
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδH : δ * H ≤ ε / 4 := by
    have h := min_le_right (1 : ℝ) (ε / (4 * H))
    have h' := mul_le_mul_of_nonneg_right h hH.le
    have heq : (ε / (4 * H)) * H = ε / 4 := by field_simp
    simpa only [heq] using h'
  choose Bj hBj hfloor using fun j => exists_primeCofactorFloorRatio_cpow_close (s j - 1) hδ
  let B' := B + (∑ j, Bj j) + 1
  have hBjB : ∀ j, Bj j ≤ B' := by
    intro j
    have h := Finset.single_le_sum (fun l _ => Nat.zero_le (Bj l)) (mem_univ j)
    dsimp only [B']
    omega
  obtain ⟨omega', hp, M, A, r₀, hr₀, hsep, hblocks⟩ :=
    exists_prescribed_smooth_cofactor_mode_blocks s hs hs1 S omega B' K (ε / 4)
      (by positivity) k t
  refine ⟨omega', hp, M, A, r₀, hr₀, hsep, ?_⟩
  intro i
  have hMi : B' ≤ M i := (hblocks i).1
  refine ⟨by dsimp only [B'] at hMi; omega, by dsimp only [B'] at hMi; omega,
    (hblocks i).2.1, (hblocks i).2.2.1, ?_⟩
  intro N p hN hpp hlo hhi r hr hrle
  have hL : 0 < N / p := by dsimp only [B'] at hMi; omega
  obtain ⟨hqpos, hqle, _⟩ := primeCofactorFloorRatio_bounds hN hpp hL
  have hrq : 0 < r * primeCofactorFloorRatio N p := mul_pos hr hqpos
  have hrqle : r * primeCofactorFloorRatio N p ≤ r₀ :=
    (mul_le_of_le_one_right hr.le hqle).trans hrle
  have hV := (hblocks i).2.2.2 (r * primeCofactorFloorRatio N p) hrq hrqle (N / p) hlo hhi
  rw [pi_norm_lt_iff hε]
  intro j
  let Q : ℂ := (primeCofactorFloorRatio N p : ℂ) ^ (s j - 1)
  let V := relativeSmoothCofactorMode s (t i) (A i) (r * primeCofactorFloorRatio N p) (N / p) omega' j
  let C := cofactorCauchyMode s (t i) j
  have hQ : ‖Q - 1‖ < δ := hfloor j N p hN hpp ((hBjB j).trans (hMi.trans hlo))
  have hQ2 : ‖Q‖ ≤ 2 := by
    have h' : ‖Q‖ ≤ ‖Q - 1‖ + 1 := by
      have hh := norm_add_le (Q - 1) (1 : ℂ)
      simpa only [sub_add_cancel, norm_one] using hh
    linarith
  have hVC : ‖V - C‖ ≤ ε / 4 :=
    (norm_le_pi_norm _ j).trans hV.le
  have hC : ‖C‖ ≤ H := hCH i j
  change ‖Q * V - C‖ < ε
  have hdecomp : Q * V - C = Q * (V - C) + (Q - 1) * C := by ring
  rw [hdecomp]
  calc
    _ ≤ ‖Q * (V - C)‖ + ‖(Q - 1) * C‖ := norm_add_le _ _
    _ = ‖Q‖ * ‖V - C‖ + ‖Q - 1‖ * ‖C‖ := by rw [norm_mul, norm_mul]
    _ ≤ 2 * (ε / 4) + δ * H := add_le_add
      (mul_le_mul hQ2 hVC (norm_nonneg _) (by norm_num))
      (mul_le_mul hQ.le hC (norm_nonneg _) hδ.le)
    _ < ε := by linarith

end RHTower
