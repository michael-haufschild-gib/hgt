import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropEightOne
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSevenTwo

set_option autoImplicit false

/-!
# Guth–Maynard Proposition 8.1: `S₃ ⪅ T² |W|^{1/2} E(W)^{1/2}`

Guth–Maynard (arXiv 2405.20552) Proposition 8.1: for a real CGL bump `w`, `0 < ε ≤ 1`,
`2 ≤ T`, `T^ε ≤ N ≤ T` and every nonempty `1`-separated `W ⊂ [0, T]`,

`|S₃| = |Σ_{m ∈ ℤ³, m₁m₂m₃ ≠ 0} I_m| ≤ C T^{4ε} · T² |W|^{1/2} E(W)^{1/2}`.

Proof: Proposition 7.2 (`prop72`) expands `S₃` into the dyadic block sum of the smoothed cubic terms
`Ĩ_m` with the bumps `innerBump (2T^{ε/2})`, `outerBump` and `M ≤ T^{1+ε}/N`; the assembly
`guthMaynard_prop81_innerBump_outerBump` (Hölder `(2, 4, 4)` with Lemmas 8.2 and 8.3) bounds that
sum. Since `ε` is arbitrary, this is `S₃ ⪅ T² |W|^{1/2} E(W)^{1/2}`.
-/

open Set

namespace RHTower.GuthMaynard

noncomputable section

/-- **Guth–Maynard Proposition 8.1 (`S₃` controlled by the additive energy).** For a real CGL
bump `w` and `0 < ε ≤ 1` there is `C ≥ 0` such that for `2 ≤ T`, `1 ≤ N ≤ T`, `T^ε ≤ N` and every
nonempty `1`-separated `W ⊂ [0, T]`:
`‖S₃‖ ≤ C T^{4ε} · T² |W|^{1/2} E(W)^{1/2}`. -/
theorem prop81 (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ), 2 ≤ T → 1 ≤ N → N ≤ T → T ^ ε ≤ N →
      (∀ t ∈ W, t ∈ Icc 0 T) → IsSeparated 1 W → W.Nonempty →
      ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖
        ≤ C * T ^ (4 * ε) * (T ^ 2 * Real.sqrt W.card * Real.sqrt (additiveEnergy W)) := by
  obtain ⟨C, hC0, h72⟩ := prop72 w hε hε1
  obtain ⟨K, hK0, h81⟩ := guthMaynard_prop81_innerBump_outerBump
  refine ⟨K * (8 * max C 1) ^ 4 + 8 * max C 1, by positivity,
    fun T N W hT hN hNT hTεN hW hsep hne => ?_⟩
  obtain ⟨M₁, M, hM₁, hM₁M, hMT, hS⟩ := h72 T N W hT hN hNT hTεN hW hsep
  have hN0 : 0 < N := by linarith
  have hC₇ : C ≤ max C 1 := le_max_left _ _
  have hNM : N * (M : ℝ) ≤ T ^ (1 + ε) := by
    rw [le_div_iff₀ hN0] at hMT
    linarith
  have hbox : ∀ m ∈ dyadicFrequencyBlock M₁ M,
      (M₁ : ℝ) ≤ |(m.1 : ℝ)| ∧ |(m.1 : ℝ)| ≤ 2 * M₁ ∧ (M : ℝ) ≤ |(m.2.1 : ℝ)| ∧
        |(m.2.1 : ℝ)| ≤ 9 * M ∧ (M : ℝ) ≤ |(m.2.2 : ℝ)| ∧ |(m.2.2 : ℝ)| ≤ 9 * M := by
    intro m hm
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_dyadicFrequencyBlock.mp hm
    have e1 : (M₁ : ℝ) ≤ |(m.1 : ℝ)| := by exact_mod_cast h1
    have e2 : |(m.1 : ℝ)| < 2 * M₁ := by exact_mod_cast h2
    have e3 : (M : ℝ) ≤ |(m.2.1 : ℝ)| := by exact_mod_cast h3
    have e4 : |(m.2.1 : ℝ)| < 2 * M := by exact_mod_cast h4
    have e5 : (M : ℝ) ≤ |(m.2.2 : ℝ)| := by exact_mod_cast h5
    have e6 : |(m.2.2 : ℝ)| < 9 * M := by exact_mod_cast h6
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    exact ⟨e1, e2.le, e3, by linarith, e5, e6.le⟩
  have hsum : 0 ≤ (N ^ 2 / M) * ∑ m ∈ dyadicFrequencyBlock M₁ M,
      smoothedCubicTerm (innerBump (2 * T ^ (ε / 2))) outerBump N M W m.1 m.2.1 m.2.2 :=
    mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun m _ => smoothedCubicTerm_nonneg _ _ _ _ _ _ _ _)
  have hS' : ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖
      ≤ max C 1 * T ^ ε * (N ^ 2 / M) * ∑ m ∈ dyadicFrequencyBlock M₁ M,
          smoothedCubicTerm (innerBump (2 * T ^ (ε / 2))) outerBump N M W m.1 m.2.1 m.2.2
        + max C 1 * T ^ (-100 : ℝ) := by
    have hTε : 0 ≤ T ^ ε := by positivity
    have hT100 : 0 ≤ T ^ (-100 : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₇ hTε) hsum
    have h2 := mul_le_mul_of_nonneg_right hC₇ hT100
    simp only [mul_assoc] at hS h1 ⊢
    linarith
  exact h81 ε T N M M₁ (max C 1) _ W (dyadicFrequencyBlock M₁ M) hε hT (le_max_right _ _) hN0
    (by exact_mod_cast hM₁) (by exact_mod_cast hM₁M) hNM hne hsep hbox hS'

end

end RHTower.GuthMaynard
