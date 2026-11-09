import GaloisForLFunctions.HTGeometry.PowerSumTuranWeightedLowerBound
import GaloisForLFunctions.InfiniteRankWeilTheory.TheExceptionalRankDecidesTheWindow

/-!
# Turán's second main theorem on thick sets of levels

A tower at a base `b` has level sums `S(ν) = Σ_{i∈s} b_i z_i^ν + E(ν)`: a finite top part and a
remainder with `‖E(ν)‖ ≤ B r^ν`. For the zeros of `ζ`, `z_ρ = b^{ρ−½}`, and the reciprocity of
returns (`TheReciprocityOfReturns`) writes `S(ν)` as an orbit polynomial at scale `b^ν`.

* **Windows** (`exists_window_ge`). If the top part reaches radius `R` and every top group
  `{i : τR ≤ |z_i|}`, `τ ∈ [½, 1]`, has weight sum of modulus `≥ β`, then every window
  `[M + 1, M + n]`, `n = |s|`, contains a level with
  `‖S(ν)‖ ≥ βR^ν/λ(M, n) − Br^ν`, `λ(M, n) = 2en(6(n+1)(M+2n+2))^n`: separation-free, with a loss
  polynomial in the position `M`.
* **Thick sets** (`exists_mem_thick_ge`). A thick set of levels contains such windows arbitrarily far
  out, so a thick set sees the top part.

The loss is polynomial in `M`, the gain `(R/r)^ν` exponential, so a crude bound `Cρ^ν`, `ρ < R`, on a
thick set fails once the remainder is strictly inside (`InfiniteRankWeilTheory.not_forall_mem_thick_norm_levelSum_le`):
this is how a thick crude count eliminates an isolated top (AAL). The window length is the rank `n`
of the top part, and a remainder at the same radius as the top is not controlled: a tower with
infinitely many modes near the top radius (no ZAL) is outside the theorem, and the Wolff towers of
`InfiniteRankWeilTheory` show that no power-sum argument on levels repairs this. Turán's method
decides the finite-rank part above the well-founded radius; it cannot produce ZAL.
-/

open Real Finset

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

/-- The Turán loss `λ(M, n) = 2en(6(n+1)(M+2n+2))^n`. -/
def turanLoss (M n : ℕ) : ℝ := 2 * (Real.exp 1 * n * (6 * (n + 1) * ((M : ℝ) + 2 * n + 2)) ^ n)

theorem turanLoss_pos {M n : ℕ} (hn : 1 ≤ n) : 0 < turanLoss M n := by
  unfold turanLoss
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

variable {ι : Type*}

/-- **Turán's second main theorem with a remainder, at radius `R`.** -/
theorem exists_window_ge (s : Finset ι) (z b : ι → ℂ) {R : ℝ} (hR : 0 < R)
    (htop : ∃ i ∈ s, R ≤ ‖z i‖) (M : ℕ) {β : ℝ} (hβ0 : 0 < β)
    (hβ : ∀ τ : ℝ, 1 / 2 ≤ τ → τ ≤ 1 → β ≤ ‖∑ i ∈ s.filter (fun i => τ * R ≤ ‖z i‖), b i‖)
    (E : ℕ → ℂ) {B r : ℝ} (hE : ∀ ν, ‖E ν‖ ≤ B * r ^ ν) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + s.card ∧
      β * R ^ ν / turanLoss M s.card - B * r ^ ν ≤ ‖∑ i ∈ s, b i * z i ^ ν + E ν‖ := by
  set z' : ι → ℂ := fun i => z i / R
  have hnorm : ∀ i, ‖z' i‖ = ‖z i‖ / R := fun i => by
    simp [z', Real.norm_eq_abs, abs_of_pos hR]
  have htop' : ∃ i ∈ s, 1 ≤ ‖z' i‖ := by
    obtain ⟨i, hi, h⟩ := htop
    exact ⟨i, hi, by rw [hnorm, le_div_iff₀ hR, one_mul]; exact h⟩
  have hhalf : (1 : ℝ) / 2 ≤ 1 - 1 / ((M : ℝ) + 2 * s.card + 2) := by
    have : (2 : ℝ) ≤ (M : ℝ) + 2 * s.card + 2 := by
      have h0 : (0 : ℝ) ≤ (M : ℝ) + 2 * s.card := by positivity
      linarith
    have : 1 / ((M : ℝ) + 2 * s.card + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hβ' : ∀ τ : ℝ, 1 - 1 / ((M : ℝ) + 2 * s.card + 2) ≤ τ → τ ≤ 1 →
      β ≤ ‖∑ i ∈ s.filter (fun i => τ ≤ ‖z' i‖), b i‖ := fun τ h1 h2 => by
    have hf : s.filter (fun i => τ ≤ ‖z' i‖) = s.filter (fun i => τ * R ≤ ‖z i‖) := by
      refine Finset.filter_congr fun i _ => ?_
      rw [hnorm, le_div_iff₀ hR]
    rw [hf]
    exact hβ τ (hhalf.trans h1) h2
  obtain ⟨ν, hν1, hν2, hlow⟩ := HTGeometry.exists_norm_weightedPowerSum_ge s z' b htop' M hβ0 hβ'
  refine ⟨ν, hν1, hν2, ?_⟩
  have hscale : ∑ i ∈ s, b i * z i ^ ν = (R : ℂ) ^ ν * ∑ i ∈ s, b i * z' i ^ ν := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    simp only [z', div_pow]
    field_simp
  have hmain : β * R ^ ν / turanLoss M s.card ≤ ‖∑ i ∈ s, b i * z i ^ ν‖ := by
    rw [hscale, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have h := mul_le_mul_of_nonneg_left hlow (pow_nonneg hR.le ν)
    unfold turanLoss
    calc β * R ^ ν / (2 * (Real.exp 1 * s.card * (6 * (s.card + 1) *
          ((M : ℝ) + 2 * s.card + 2)) ^ s.card))
        = R ^ ν * (β / (2 * (Real.exp 1 * s.card * (6 * (s.card + 1) *
          ((M : ℝ) + 2 * s.card + 2)) ^ s.card))) := by ring
      _ ≤ _ := h
  have htri := norm_sub_norm_le (∑ i ∈ s, b i * z i ^ ν) (-E ν)
  rw [norm_neg, sub_neg_eq_add] at htri
  linarith [hE ν]

/-- **A thick set sees the top part.** Every thick set of levels contains, beyond every `M₀`, a level
`ν` with `‖S(ν)‖ ≥ βR^ν/λ(M, n) − Br^ν` for some window position `M ≥ M₀`. -/
theorem exists_mem_thick_ge (s : Finset ι) (z b : ι → ℂ) {R : ℝ} (hR : 0 < R)
    (htop : ∃ i ∈ s, R ≤ ‖z i‖) {β : ℝ} (hβ0 : 0 < β)
    (hβ : ∀ τ : ℝ, 1 / 2 ≤ τ → τ ≤ 1 → β ≤ ‖∑ i ∈ s.filter (fun i => τ * R ≤ ‖z i‖), b i‖)
    (E : ℕ → ℂ) {B r : ℝ} (hE : ∀ ν, ‖E ν‖ ≤ B * r ^ ν) {G : Set ℕ}
    (hG : InfiniteRankWeilTheory.Thick G) (M₀ : ℕ) :
    ∃ ν ∈ G, M₀ < ν ∧ ∃ M : ℕ, M₀ ≤ M ∧
      β * R ^ ν / turanLoss M s.card - B * r ^ ν ≤ ‖∑ i ∈ s, b i * z i ^ ν + E ν‖ := by
  obtain ⟨M, hM, hwin⟩ := hG s.card M₀
  obtain ⟨ν, hν1, hν2, hbound⟩ := exists_window_ge s z b hR htop M hβ0 hβ E hE
  exact ⟨ν, hwin ν hν1 hν2, by omega, M, hM, hbound⟩

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
