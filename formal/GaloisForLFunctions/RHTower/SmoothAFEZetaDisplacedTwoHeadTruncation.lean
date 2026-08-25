import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualReflection
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralTwoHeadTruncation

/-!
# Finite conductor-oriented AFE on displaced lines

Both Gaussian Dirichlet series are truncated after rewriting the reflected
head through the exact displaced dual weight.
-/

noncomputable section

namespace RHTower

open Complex

theorem exists_riemannZeta_displaced_sub_two_smoothAFE_weight_heads_le
    {d x : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hx : 0 < x) (τ : ℝ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ Ld Lu : ℕ,
      1 ≤ Ld → 1 ≤ Lu →
      ‖riemannZeta (displacedLinePt d τ) -
          ((∑ n ∈ Finset.range Ld,
              (((n + 1 : ℕ) : ℂ)) ^ (-displacedLinePt d τ) *
                smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)) +
            (∑ n ∈ Finset.range Lu,
              (zetaChi (displacedLinePt d τ) *
                (((n + 1 : ℕ) : ℂ)) ^ (displacedLinePt d τ - 1)) *
                smoothAFEZetaDisplacedDualWeight d τ
                  (((n + 1 : ℕ) : ℝ) * x)) -
            smoothAFEZetaShiftedPoleResidue (displacedLinePt d τ) x)‖ ≤
        C * x *
            (((Ld : ℝ)) ^ (-(1 / 2 - d)) / (1 / 2 - d)) +
          K * (((Lu : ℝ)) ^ (-(1 / 2 + d)) / (1 / 2 + d)) := by
  have hs : displacedLinePt d τ ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    rw [displacedLinePt_re] at hre
    norm_num at hre
    linarith
  obtain ⟨C, K, hC, hK, hbase⟩ :=
    exists_riemannZeta_sub_two_smoothAFE_heads_le
      (A := (1 : ℝ)) (by norm_num)
      (s := displacedLinePt d τ) (x := x) hx hs
      (displacedLinePt_mem_openStrip hd hdhalf τ).1
      (displacedLinePt_mem_openStrip hd hdhalf τ).2
      (by rw [displacedLinePt_re]; linarith)
  refine ⟨C, K, hC, hK, fun Ld Lu hLd hLu => ?_⟩
  have h := hbase Ld Lu hLd hLu
  have hdual :
      (∑ n ∈ Finset.range Lu,
        smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n) =
        -(∑ n ∈ Finset.range Lu,
          (zetaChi (displacedLinePt d τ) *
            (((n + 1 : ℕ) : ℂ)) ^ (displacedLinePt d τ - 1)) *
            smoothAFEZetaDisplacedDualWeight d τ
              (((n + 1 : ℕ) : ℝ) * x)) := by
    calc
      (∑ n ∈ Finset.range Lu,
          smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n) =
          ∑ n ∈ Finset.range Lu,
            -((zetaChi (displacedLinePt d τ) *
              (((n + 1 : ℕ) : ℂ)) ^ (displacedLinePt d τ - 1)) *
              smoothAFEZetaDisplacedDualWeight d τ
                (((n + 1 : ℕ) : ℝ) * x)) := by
        apply Finset.sum_congr rfl
        intro n hn
        simpa only [Nat.cast_add, Nat.cast_one] using
          smoothAFEZetaDualCoefficientGeneral_displaced_eq_neg_weight
            hx d τ n
      _ = -(∑ n ∈ Finset.range Lu,
          (zetaChi (displacedLinePt d τ) *
            (((n + 1 : ℕ) : ℂ)) ^ (displacedLinePt d τ - 1)) *
            smoothAFEZetaDisplacedDualWeight d τ
              (((n + 1 : ℕ) : ℝ) * x)) := by
        rw [Finset.sum_neg_distrib]
  rw [hdual] at h
  rw [displacedLinePt_re] at h
  simp only [sub_neg_eq_add, Nat.cast_add, Nat.cast_one] at h ⊢
  convert h using 1
  rw [Real.rpow_one]
  ring_nf

end RHTower
