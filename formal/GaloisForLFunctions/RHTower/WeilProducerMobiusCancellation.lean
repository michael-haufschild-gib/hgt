import GaloisForLFunctions.RHTower.WeilProducerReciprocalZeta
import GaloisForLFunctions.RHTower.Sieve.PerronSummable
import GaloisForLFunctions.HTGeometry.SmoothWeightShift
import GaloisForLFunctions.HTGeometry.SmoothWeightSharpMellin

/-!
# Half-power Möbius cancellation for every Weil-positive system

Let `lam` (with `lam(1) = 0`) be Weil-positive in Herglotz form for a datum of logarithmic growth,
and let `μ_lam` (`producerMobius`) be the Dirichlet coefficients of the reciprocal
`1/F = exp(−Σ lam(n) n^{−s}/log n)` of its zeta function.

**Theorem** (`exists_smoothed_producerMobius_le`).  For every `ε > 0` there is `C` with

`|Σ_n μ_lam(n) w_N(n)| ≤ C N^{1/2 + ε}`  for all `N ≥ 1`,

where `w_N` is the smooth cutoff equal to `1` on `[0, N]` and `0` on `[2N, ∞)`.  For a full-cone
producer for `ζ`'s datum (`exists_smoothed_producerMobius_le_of_weilPositiveFull`) this is
Littlewood's half-power Möbius bound for the system's own Möbius function; for `lam = Λ`, which is
a producer exactly under RH, it is the smoothed form of `M(x) = O(x^{1/2+ε})`.

**Proof.**  Mellin inversion on `Re s = 2` writes the smoothed sum as
`(1/2π)∫ G(2+iy) w̃_N(2+iy) dy`, where `G` is the continuation of `1/F` to `Re s > 1/2`
(`exists_reciprocalZeta_continuation`).  The strip bound `‖G(s)‖ ≤ K(2+|Im s|)^{1/8}`
(`exists_reciprocalZeta_strip_bound`, from producer Lindelöf) moves the contour to
`Re s = 1/2 + δ`, where the fractional Mellin bound of the cutoff gives `O(N^{1/2+δ})`.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem producerMobius_zero (lam : ℕ → ℝ) : producerMobius lam 0 = 0 :=
  GaloisForLFunctions.HTGeometry.dirichletExp_zero

theorem summable_norm_producerMobius_mul_rpow {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    Summable fun n : ℕ => ‖producerMobius lam n‖ * (n : ℝ) ^ (-(2 : ℝ)) := by
  have h := (LSeries_producerMobius hsum (s := 2) (by norm_num)).1
  refine h.norm.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    rw [producerMobius_zero, norm_zero, zero_mul]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv]
    norm_num

theorem tsum_producerMobius_mul_cpow_eq {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 1 < s.re) :
    ∑' n : ℕ, producerMobius lam n * (n : ℂ) ^ (-s) =
      cexp (-LSeries (logZetaCoeff lam) s) := by
  rw [← (LSeries_producerMobius hsum hs).2, LSeries]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def]
  split_ifs with hn
  · subst hn
    rw [producerMobius_zero, zero_mul]
  · rw [Complex.cpow_neg, div_eq_mul_inv]

/-- **Half-power cancellation of a producer's Möbius function.** -/
theorem exists_smoothed_producerMobius_le {lam : ℕ → ℝ} {A : ℂ → ℂ}
    (hW : HerglotzWeilPositive lam A) (h1 : lam 1 = 0) {K : ℝ} (hK : 0 ≤ K)
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N →
      ‖∑' n : ℕ, producerMobius lam n * ((smoothWeight N N (n : ℝ) : ℝ) : ℂ)‖ ≤
        C * N ^ (1 / 2 + ε) := by
  have hsum := hW.summable
  obtain ⟨δ, hδ, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ δ ≤ ε :=
    ⟨min (ε / 2) (1 / 4), by positivity, by
      have := min_le_right (ε / 2) (1 / 4); linarith, by
      have := min_le_left (ε / 2) (1 / 4); linarith⟩
  obtain ⟨G, hGd, hGL⟩ := exists_reciprocalZeta_continuation hW h1 hA
  set a : ℝ := 1 / 8 with ha
  set q : ℝ := 1 / 4 with hq
  obtain ⟨Kb, hKb, hbd⟩ := exists_reciprocalZeta_strip_bound hW h1 hK hA hAK hδ hδ1
    (ε := a) (by norm_num) hGd hGL
  obtain ⟨C₀, C₁, hC₀, hC₁, hfrac⟩ := exists_integral_norm_mul_mellin_smoothWeight_fractional_bound
  set c : ℝ := 1 / 2 + δ with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc2 : c ≤ 2 := by rw [hc]; linarith
  set P : ℝ := C₀ ^ (1 - q) * C₁ ^ q with hP
  set B : ℝ := 2 * (Kb * 3 ^ a * (2 ^ c / c)) +
    2 * (Kb * 3 ^ a * (P * 2 ^ q * 2 ^ c)) * (1 / (q - a)) with hB
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hB0 : 0 ≤ B := by
    rw [hB]
    have : 0 < q - a := by rw [hq, ha]; norm_num
    positivity
  have hpi : 0 < 2 * Real.pi := by positivity
  refine ⟨B / (2 * Real.pi), div_nonneg hB0 hpi.le, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hstrip : verticalStrip c 2 ⊆ {s : ℂ | 1 / 2 < s.re} := fun s hs => by
    show 1 / 2 < s.re
    have := hs.1
    linarith
  -- Mellin inversion on `Re s = 2`
  have hperron := Sieve.tsum_mul_smoothWeight_eq_integral_summable (producerMobius_zero lam)
    hN0 hN0 (σ := 2) (by norm_num) (summable_norm_producerMobius_mul_rpow hsum)
  have hint2 : (fun y : ℝ => (∑' n : ℕ, producerMobius lam n *
      (n : ℂ) ^ (-(((2 : ℝ) : ℂ) + (y : ℝ) * I))) *
        mellin (fun x : ℝ => ((smoothWeight N N x : ℝ) : ℂ)) (((2 : ℝ) : ℂ) + (y : ℝ) * I)) =
      fun y : ℝ => G (((2 : ℝ) : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((smoothWeight N N x : ℝ) : ℂ)) (((2 : ℝ) : ℂ) + (y : ℝ) * I) := by
    funext y
    have hre : 1 < (((2 : ℝ) : ℂ) + (y : ℝ) * I).re := by simp
    rw [tsum_producerMobius_mul_cpow_eq hsum hre, hGL _ hre]
  rw [hint2] at hperron
  -- shift to `Re s = c`
  have hshift := integral_mul_mellin_smoothWeight_shift hN0 hN0 hc0 hc2 (hGd.mono hstrip) hKb
    (by norm_num : (0 : ℝ) ≤ a) hbd
  rw [hshift] at hperron
  -- bound on the line `Re s = c`
  have hline : ∀ y : ℝ, ‖G ((c : ℂ) + (y : ℝ) * I)‖ ≤ Kb * (2 + |y|) ^ a := by
    intro y
    have := hbd ((c : ℂ) + (y : ℝ) * I) ⟨by simp, by simp; linarith⟩
    simpa using this
  have hint := integrable_mul_mellin_smoothWeight_line hN0 hN0 hc0
    (hGd.mono hstrip).continuousOn hKb (by norm_num : (0 : ℝ) ≤ a) hbd le_rfl hc2
  have hbound := hfrac N N c a q Kb hN0 hN0 hc0 (by norm_num) (by rw [ha, hq]; norm_num)
    (by rw [hq]; norm_num) hKb G hline hint
  have hNN : (N + N) / N = 2 := by field_simp; ring
  have h2N : (N + N) ^ c = 2 ^ c * N ^ c := by
    rw [show N + N = 2 * N by ring, Real.mul_rpow (by norm_num) hN0.le]
  rw [hNN, h2N] at hbound
  have hBN : 2 * (Kb * 3 ^ a * (2 ^ c * N ^ c / c)) +
      2 * (Kb * 3 ^ a * (P * 2 ^ q * (2 ^ c * N ^ c))) * (1 / (q - a)) = B * N ^ c := by
    rw [hB]; ring
  rw [hBN] at hbound
  have hnorm : ‖(2 * Real.pi : ℝ) • ∑' n : ℕ, producerMobius lam n *
      ((smoothWeight N N (n : ℝ) : ℝ) : ℂ)‖ ≤ B * N ^ c := by
    rw [hperron]
    exact (norm_integral_le_integral_norm _).trans hbound
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpi] at hnorm
  have hNc : N ^ c ≤ N ^ (1 / 2 + ε) := Real.rpow_le_rpow_of_exponent_le hN (by rw [hc]; linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
  calc ‖∑' n : ℕ, producerMobius lam n * ((smoothWeight N N (n : ℝ) : ℝ) : ℂ)‖ * (2 * Real.pi)
      = 2 * Real.pi * ‖∑' n : ℕ, producerMobius lam n *
          ((smoothWeight N N (n : ℝ) : ℝ) : ℂ)‖ := by ring
    _ ≤ B * N ^ c := hnorm
    _ ≤ B * N ^ (1 / 2 + ε) := mul_le_mul_of_nonneg_left hNc hB0

/-- **Half-power Möbius cancellation for every full-cone producer.**  If `lam` is full-cone
Weil-positive, the Möbius function of `exp(Σ_{n≥2} lam(n) n^{−s}/log n)` satisfies
`|Σ μ_lam(n) w_N(n)| ≤ C N^{1/2+ε}` for all `N ≥ 1`. -/
theorem exists_smoothed_producerMobius_le_of_weilPositiveFull {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N →
      ‖∑' n : ℕ, producerMobius (fun n => if 2 ≤ n then lam n else 0) n *
        ((smoothWeight N N (n : ℝ) : ℝ) : ℂ)‖ ≤ C * N ^ (1 / 2 + ε) := by
  obtain ⟨K, hK, hAK⟩ := exists_log_bound_zetaArchimedeanDatum
  exact exists_smoothed_producerMobius_le
    (WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW) (by simp) hK
    (differentiableOn_zetaArchimedeanDatum.mono fun s (hs : 1 / 2 < s.re) =>
      show 0 < s.re by linarith) hAK hε

end RHTower

end
