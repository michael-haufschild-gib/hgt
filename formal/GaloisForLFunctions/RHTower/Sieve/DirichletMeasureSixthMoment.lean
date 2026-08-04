import GaloisForLFunctions.RHTower.Sieve.DirichletMeasureLargeValues
import GaloisForLFunctions.RHTower.Sieve.DirichletSixthMomentDivisor

/-!
# The measure of a level set, sixth-power form

`volume_largeValues_le` bounds the measure of `{|F| ≥ V}` by `V^{-2}` times the mean value.  Running
the same argument on the cube replaces `V^{-2}` by `V^{-6}`:

    V⁶ · |{t ∈ (0,T] : |F(t)| ≥ V}| ≤ (T + 4N³(1+log N³)) · C N^ε · (∑_n |a_n|²)³ .

The level set is unchanged because `‖F³‖ = ‖F‖³`, so the two statements are about the same set and
differ only in the moment used to estimate it.  The sixth power is what makes the bound survive when
`V` is close to the trivial size of `F`.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The level sets of `F` and of `F³` coincide at the cubed threshold. -/
theorem largeValues_cube_setOf (N : ℕ) (a : Fin N → ℂ) (S : Set ℝ) {V : ℝ} (hV : 0 ≤ V) :
    {t ∈ S | V ^ 3 ≤ ‖dirPoly (N ^ 3) (convCube N a) t‖}
      = {t ∈ S | V ≤ ‖dirPoly N a t‖} := by
  ext t
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro _
  rw [dirPoly_convCube, norm_pow]
  constructor
  · intro h
    exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) h
  · intro h
    exact pow_le_pow_left₀ hV h 3

/-- **The measure of a level set, sixth-power form.** -/
theorem volume_largeValues_sixth_le (N : ℕ) (a : Fin N → ℂ) {T V D : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hD : ∀ j : Fin (N ^ 3), ((cubeFibre N j).card : ℝ) ≤ D) :
    V ^ 6 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ (T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)))
          * (D * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3) := by
  have hV3 : (0 : ℝ) ≤ V ^ 3 := by positivity
  have hbase := volume_largeValues_le (N ^ 3) (convCube N a) hT hV3
  rw [largeValues_cube_setOf N a _ hV] at hbase
  have hpow : (V ^ 3) ^ 2 = V ^ 6 := by ring
  rw [hpow] at hbase
  refine le_trans hbase ?_
  have hlogN3 : (0 : ℝ) ≤ Real.log ((N ^ 3 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N ^ 3) with h | h
    · simp [h]
    · have h1 : 1 ≤ N ^ 3 := h
      exact Real.log_nonneg (by exact_mod_cast h1)
  have hcast : (0 : ℝ) ≤ ((N ^ 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfactor : (0 : ℝ)
      ≤ T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)) := by nlinarith
  exact mul_le_mul_of_nonneg_left (sum_normSq_convCube_le N a hD) hfactor

/-- **The measure of a level set, sixth-power form, with no hypothesis on the fibres.** -/
theorem exists_volume_largeValues_sixth_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : Fin N → ℂ) (T V : ℝ),
      1 ≤ N → 0 ≤ T → 0 ≤ V →
      V ^ 6 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
        ≤ (T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)))
            * (C * (N : ℝ) ^ ε * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3) := by
  obtain ⟨C, hC, hfib⟩ := exists_cubeFibre_card_le_rpow hε
  refine ⟨C, hC, ?_⟩
  intro N a T V hN hT hV
  exact volume_largeValues_sixth_le N a hT hV (fun j => hfib N hN j)

end RHTower.Sieve
