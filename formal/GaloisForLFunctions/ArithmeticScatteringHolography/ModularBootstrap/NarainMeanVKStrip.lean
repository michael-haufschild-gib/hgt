import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanVerticalBounds
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanHalfPlane
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovInvZeta

/-!
# Arithmetic rectangles for the averaged Narain transform

The uniform reciprocal-zeta estimate gives holomorphy on a shrinking rectangle
and an exponential high-ordinate envelope for the actual mean.
-/

open Complex RHTower Set
open RHTower.Sieve
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The arithmetic zero-free width after changing from `s` to `u=(s-1)/2`. -/
def narainVKWidth (δ T : ℝ) : ℝ :=
  min (min δ 1) (vkHadamardWidth (2 * T + 1)) / 8

/-- The uniform reciprocal-zeta cost of a finite-height contour. -/
def narainVKCost (T : ℝ) : ℝ :=
  Real.log (2 * T + 1) ^ 7 * (1 + 2 / vkHadamardWidth (2 * T + 1)) ^ 7

/-- The actual averaged transform is analytic across a shrinking Vinogradov–Korobov strip,
and its high-ordinate envelope retains exponential decay. -/
theorem exists_narainMellinMean_vk_strip (Y Z : Height) :
    ∃ δ T₀ C : ℝ, ∃ N : ℕ, 0 < δ ∧ 3 ≤ T₀ ∧ 0 ≤ C ∧
      ∀ T : ℝ, T₀ ≤ T →
        0 < narainVKWidth δ T ∧ narainVKWidth δ T ≤ 1 / 8 ∧
        ∀ u : ℂ, -narainVKWidth δ T ≤ u.re → u.re ≤ 0 → |u.im| ≤ T →
          AnalyticAt ℂ (narainMellinMean Y Z) u ∧
          (1 ≤ |u.im| → ‖narainMellinMean Y Z u‖ ≤
            C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) * narainVKCost T) := by
  obtain ⟨Cζ, δ, T₀, hCζ, hδ, hT₀, hTexp, hzero, hinv⟩ := exists_bound_invZeta_vk_uniform
  obtain ⟨CM, N, hCM, hM⟩ := exists_narainMellinMean_strip_bound Y Z (B := 1) (by norm_num)
  refine ⟨δ, T₀, CM * Cζ, N, hδ, hT₀, mul_nonneg hCM hCζ.le, ?_⟩
  intro T hT
  have hT3 : 3 ≤ T := hT₀.trans hT
  have hK : T₀ ≤ 2 * T := by linarith only [hT, hT3]
  have hw : 0 < vkHadamardWidth (2 * T + 1) := by
    apply vkHadamardWidth_pos
    have hexp : Real.exp (Real.exp 1) ≤ Real.exp (Real.exp 30) :=
      Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))
    linarith only [hexp, hTexp, hT, hT3]
  have hd : 0 < narainVKWidth δ T := div_pos (lt_min (lt_min hδ zero_lt_one) hw) (by norm_num)
  have hd8 : narainVKWidth δ T ≤ 1 / 8 := by
    unfold narainVKWidth
    exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right δ 1)) (by norm_num)
  have hdmin : 2 * narainVKWidth δ T ≤ min δ (vkHadamardWidth (2 * T + 1)) / 4 := by
    have hmin : min (min δ 1) (vkHadamardWidth (2 * T + 1)) ≤
        min δ (vkHadamardWidth (2 * T + 1)) :=
      min_le_min (min_le_left _ _) le_rfl
    unfold narainVKWidth
    linarith only [hmin]
  refine ⟨hd, hd8, ?_⟩
  intro u hlo hhi him
  have hre : (1 + 2 * u).re = 1 + 2 * u.re := by simp
  have him' : |(1 + 2 * u).im| ≤ 2 * T := by
    have he : (1 + 2 * u).im = 2 * u.im := by simp
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [him]
  have hlo' : 1 - min δ (vkHadamardWidth (2 * T + 1)) / 4 ≤ (1 + 2 * u).re := by
    rw [hre]
    linarith only [hlo, hdmin]
  have hre0 : 0 < (1 + 2 * u).re := by rw [hre]; linarith only [hlo, hd8]
  have hD : xi (1 + 2 * u) ≠ 0 := by
    by_cases hne : 1 + 2 * u = 1
    · rw [hne, xi_one]; norm_num
    · exact fun hz => hzero (1 + 2 * u) (2 * T) hK him' hlo' hne
        ((xi_eq_zero_iff hre0 hne).mp hz)
  have hlin : 1 + 2 * u ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hre0
    exact lt_irrefl 0 hre0
  have hmain : u ≠ 1 / 2 := by
    intro hz
    norm_num [hz] at hhi
  refine ⟨analyticAt_narainMellinMean_of_regular Y Z (mul_ne_zero hlin hD) hmain, ?_⟩
  intro ht
  have hne : 1 + 2 * u ≠ 1 := by
    intro hz
    have hv := congrArg Complex.im hz
    simp at hv
    have huim : u.im = 0 := by linarith only [hv]
    rw [huim, abs_zero] at ht
    linarith only [ht]
  have hζ := hinv (1 + 2 * u) (2 * T) hK him' hlo' (by rw [hre]; linarith only [hhi])
  rw [invZeta_eq_inv hne] at hζ
  have huB : |u.re| ≤ 1 := abs_le.mpr ⟨by linarith only [hlo, hd8], by linarith only [hhi]⟩
  calc
    _ ≤ CM * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) *
        ‖(riemannZeta (1 + 2 * u))⁻¹‖ := hM u huB ht
    _ ≤ CM * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) *
        (Cζ * Real.log (2 * T + 1) ^ 7 * (1 + 2 / vkHadamardWidth (2 * T + 1)) ^ 7) :=
      mul_le_mul_of_nonneg_left hζ (by positivity)
    _ = _ := by unfold narainVKCost; ring

#print axioms exists_narainMellinMean_vk_strip
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
