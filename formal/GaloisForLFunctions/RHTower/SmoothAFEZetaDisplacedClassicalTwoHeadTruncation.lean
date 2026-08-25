import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualHeadMainApproximation
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedTwoHeadTruncation

/-!
# Classical finite two-head AFE on displaced lines

The exact displaced dual weight is removed from the finite reflected head.
Its replacement by the classical reflected Dirichlet polynomial costs the
uniform conductor-small correction proved in the preceding module.
-/

noncomputable section

namespace RHTower

open Complex

theorem exists_riemannZeta_displaced_sub_two_smoothAFE_classical_heads_le
    {d₀ η : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    {d x : ℝ} (hd : 0 < d) (hdd₀ : d ≤ d₀)
    (hx : 0 < x) (τ : ℝ) :
    ∃ C K E : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ 0 ≤ E ∧ ∀ Ld Lu : ℕ,
      1 ≤ Ld → 1 ≤ Lu →
      ‖riemannZeta (displacedLinePt d τ) -
          ((∑ n ∈ Finset.range Ld,
              (((n + 1 : ℕ) : ℂ)) ^ (-displacedLinePt d τ) *
                smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)) +
            (∑ n ∈ Finset.range Lu,
              zetaChi (displacedLinePt d τ) *
                (((n + 1 : ℕ) : ℂ)) ^ (displacedLinePt d τ - 1)) -
            smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x)‖ ≤
        C * x *
            (((Ld : ℝ)) ^ (-(1 / 2 - d)) / (1 / 2 - d)) +
          K * (((Lu : ℝ)) ^ (-(1 / 2 + d)) / (1 / 2 + d)) +
          E * x ^ (d + η) / (max 1 |τ|) ^ η *
            (1 + (Lu : ℝ) ^ (1 / 2 + η) / (1 / 2 + η)) := by
  have hdhalf : d < 1 / 2 := hdd₀.trans_lt hd₀half
  obtain ⟨C, K, hC, hK, hbase⟩ :=
    exists_riemannZeta_displaced_sub_two_smoothAFE_weight_heads_le
      hd hdhalf hx τ
  obtain ⟨E, hE, herror⟩ :=
    exists_norm_sum_smoothAFEZetaDualCoefficientGeneral_displaced_add_main_le
      hd₀0 hd₀half hη hηhalf
  refine ⟨C, K, E, hC, hK, hE, fun Ld Lu hLd hLu => ?_⟩
  let D : ℂ := ∑ n ∈ Finset.range Ld,
    (((n + 1 : ℕ) : ℂ)) ^ (-displacedLinePt d τ) *
      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)
  let W : ℂ := ∑ n ∈ Finset.range Lu,
    (zetaChi (displacedLinePt d τ) *
      (((n + 1 : ℕ) : ℂ)) ^ (displacedLinePt d τ - 1)) *
      smoothAFEZetaDisplacedDualWeight d τ (((n + 1 : ℕ) : ℝ) * x)
  let M : ℂ := ∑ n ∈ Finset.range Lu,
    zetaChi (displacedLinePt d τ) *
      (((n + 1 : ℕ) : ℂ)) ^ (displacedLinePt d τ - 1)
  let R : ℂ := smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x
  have hbase' :
      ‖riemannZeta (displacedLinePt d τ) - (D + W - R)‖ ≤
        C * x * (((Ld : ℝ)) ^ (-(1 / 2 - d)) / (1 / 2 - d)) +
          K * (((Lu : ℝ)) ^ (-(1 / 2 + d)) / (1 / 2 + d)) := by
    simpa only [D, W, R] using hbase Ld Lu hLd hLu
  have herr :
      ‖∑ n ∈ Finset.range Lu,
          (smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n +
            zetaChi (displacedLinePt d τ) *
              (n + 1 : ℂ) ^ (displacedLinePt d τ - 1))‖ ≤
        E * x ^ (d + η) / (max 1 |τ|) ^ η *
          (1 + (Lu : ℝ) ^ (1 / 2 + η) / (1 / 2 + η)) :=
    herror d hd hdd₀ τ hx Lu
  have hWM :
      W - M = -(∑ n ∈ Finset.range Lu,
        (smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n +
          zetaChi (displacedLinePt d τ) *
            (n + 1 : ℂ) ^ (displacedLinePt d τ - 1))) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [smoothAFEZetaDualCoefficientGeneral_displaced_eq_neg_weight hx d τ n]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hdecomp :
      riemannZeta (displacedLinePt d τ) - (D + M - R) =
        (riemannZeta (displacedLinePt d τ) - (D + W - R)) + (W - M) := by
    ring
  rw [hdecomp]
  calc
    ‖riemannZeta (displacedLinePt d τ) - (D + W - R) + (W - M)‖
        ≤ ‖riemannZeta (displacedLinePt d τ) - (D + W - R)‖ + ‖W - M‖ :=
          norm_add_le _ _
    _ ≤
        (C * x * (((Ld : ℝ)) ^ (-(1 / 2 - d)) / (1 / 2 - d)) +
          K * (((Lu : ℝ)) ^ (-(1 / 2 + d)) / (1 / 2 + d))) +
          E * x ^ (d + η) / (max 1 |τ|) ^ η *
            (1 + (Lu : ℝ) ^ (1 / 2 + η) / (1 / 2 + η)) := by
      gcongr
      rw [hWM, norm_neg]
      exact herr
    _ = C * x * (((Ld : ℝ)) ^ (-(1 / 2 - d)) / (1 / 2 - d)) +
          K * (((Lu : ℝ)) ^ (-(1 / 2 + d)) / (1 / 2 + d)) +
          E * x ^ (d + η) / (max 1 |τ|) ^ η *
            (1 + (Lu : ℝ) ^ (1 / 2 + η) / (1 / 2 + η)) := by
      ring

end RHTower
