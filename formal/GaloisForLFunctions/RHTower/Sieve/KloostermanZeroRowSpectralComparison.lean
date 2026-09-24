import GaloisForLFunctions.RHTower.Sieve.KloostermanAnalyticFrontier

/-!
# Zero-row versus complete-column Kloosterman energy

The Ramanujan quadratic in the Qi--Qiao/Luo spectral-sieve cancellation is built from
`S(n,0;c) S(k,0;c) / c²`. At one modulus it is the square of the zero row of the complete
Kloosterman column transform. The corpus's equal-modulus physical Gram instead sums the square
over *every* output residue. This file gives their exact finite comparison, retaining the
nonnegative transverse-row energy. It does not assert a bound for that energy.
-/

open scoped BigOperators
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- One finite-modulus term of the Ramanujan square in the spectral-sieve main, extended to complex
source coefficients by a Hermitian square. The stored modulus is `q + 1`. -/
def kloostermanZeroRowPaperMain
    (M q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  (M : ℝ) / (q + 1 : ℝ) ^ 2 *
    ‖kloostermanCompleteColumnTransform (q + 1) B b 0‖ ^ 2

/-- The complete-column main energy remaining after removing its zero output row. -/
def kloostermanTransverseMain
    (M q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  (M : ℝ) / (q + 1 : ℝ) *
    ∑ m ∈ (Finset.univ : Finset (ZMod (q + 1))).erase 0,
      ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2

/-- The zero Kloosterman output row is exactly the source's Ramanujan amplitude. -/
theorem kloostermanZeroRow_eq_ramanujanAmplitude
    (q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanCompleteColumnTransform (q + 1) B b 0 =
      ∑ n ∈ B, b n *
        RHTower.cglRamanujanAdditiveSum ⟨q + 1, Nat.succ_pos q⟩
          (n : ZMod (q + 1)) := by
  unfold kloostermanCompleteColumnTransform
  apply Finset.sum_congr rfl
  intro n hn
  rw [← stadlmannReciprocalPhaseSum_eq_kloosterman,
    stadlmannReciprocalPhaseSum_eq_cglRamanujan]

/-- The paper-normalized term is the squared finite Ramanujan amplitude. -/
theorem kloostermanZeroRowPaperMain_eq_ramanujanSquare
    (M q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanZeroRowPaperMain M q B b =
      (M : ℝ) / (q + 1 : ℝ) ^ 2 *
        ‖∑ n ∈ B, b n *
          RHTower.cglRamanujanAdditiveSum ⟨q + 1, Nat.succ_pos q⟩
            (n : ZMod (q + 1))‖ ^ 2 := by
  unfold kloostermanZeroRowPaperMain
  rw [kloostermanZeroRow_eq_ramanujanAmplitude]

/-- Exact per-modulus comparison: complete-column energy is `q + 1` times the paper's zero-row
term plus a nonnegative transverse remainder. -/
theorem kloostermanCompleteMain_eq_zeroRow_add_transverse
    (M q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    (M : ℝ) / (q + 1 : ℝ) *
      ∑ m : ZMod (q + 1),
        ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2 =
      (q + 1 : ℝ) * kloostermanZeroRowPaperMain M q B b +
        kloostermanTransverseMain M q B b := by
  have hsplit := Finset.sum_erase_add
    (Finset.univ : Finset (ZMod (q + 1)))
    (fun m => ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2)
    (Finset.mem_univ (0 : ZMod (q + 1)))
  unfold kloostermanZeroRowPaperMain kloostermanTransverseMain
  rw [← hsplit]
  have hq : (q + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem kloostermanTransverseMain_nonneg
    (M q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    0 ≤ kloostermanTransverseMain M q B b := by
  unfold kloostermanTransverseMain
  positivity

/-- The weighted complete-column main energy retains transverse rows at every modulus. -/
theorem kloostermanRamanujanMainEnergy_eq_zeroRow_add_transverse
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanRamanujanMainEnergy M Q w B b =
      (∑ q ∈ Q, (q + 1 : ℝ) * ‖w q‖ ^ 2 *
        kloostermanZeroRowPaperMain M q B b) +
      ∑ q ∈ Q, ‖w q‖ ^ 2 * kloostermanTransverseMain M q B b := by
  unfold kloostermanRamanujanMainEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ = ‖w q‖ ^ 2 * ((M : ℝ) / (q + 1 : ℝ) *
          ∑ m : ZMod (q + 1),
            ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2) := by ring
    _ = ‖w q‖ ^ 2 * ((q + 1 : ℝ) *
          kloostermanZeroRowPaperMain M q B b +
          kloostermanTransverseMain M q B b) := by
      rw [kloostermanCompleteMain_eq_zeroRow_add_transverse]
    _ = _ := by ring

/-- A spectral zero-row estimate controls only a lower bound for this physical main energy. -/
theorem kloostermanRamanujanMainEnergy_zeroRow_le
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ q ∈ Q, (q + 1 : ℝ) * ‖w q‖ ^ 2 *
      kloostermanZeroRowPaperMain M q B b) ≤
      kloostermanRamanujanMainEnergy M Q w B b := by
  rw [kloostermanRamanujanMainEnergy_eq_zeroRow_add_transverse]
  have h : 0 ≤ ∑ q ∈ Q, ‖w q‖ ^ 2 *
      kloostermanTransverseMain M q B b := by
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (sq_nonneg _) (kloostermanTransverseMain_nonneg M q B b)
  linarith

end
end RHTower.Sieve
