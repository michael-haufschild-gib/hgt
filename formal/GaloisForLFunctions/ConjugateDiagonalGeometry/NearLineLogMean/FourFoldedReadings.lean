import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheFoldedReadoutOfAMoebiusWindow
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PhaseRetrievalFromWideWindowSlopes

/-!
# Detecting squarefreeness from four folded Möbius measurements

On each prefix the width slope of the integer square readout of Shi, Chen,
Huang and Wang (arXiv:2611.23979, §3.1) is the squared Mertens sum.
The next step changes this integer by an odd amount precisely at a
squarefree site. Bounded errors in the four observations preserve this test.
-/
noncomputable section
open Finset Complex MeasureTheory
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.FoldedWindow

private def mers (N : ℕ) : ℤ := ∑ n ∈ Icc 1 N, ArithmeticFunction.moebius n

/-- Integral of the folded square at capacity 2^L. -/
def foldedMertensReading (L N : ℕ) (d : ℝ) :=
  ∫ u : ℝ, foldedSquare L |(mobiusWindow (Icc 1 N) d u:ℝ)|

private theorem folded_equals_energy {L N : ℕ} (hcap : N ≤ 2^L) (d : ℝ) :
    foldedMertensReading L N d=energy (fun n => (ArithmeticFunction.moebius n:ℂ)) N d := by
  have hc : (Icc 1 N).card ≤ 2^L := by simpa [Nat.card_Icc] using hcap
  rw [foldedMertensReading,mobius_window_energy_exact L _ hc,energy,RHTower.Sieve.integral_normSq_logWindowSum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp [← Int.cast_mul]

private theorem norm_mertens (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, (ArithmeticFunction.moebius n:ℂ)‖^2 = (mers N:ℝ)^2 := by
  change ‖∑ n ∈ Icc 1 N, ((ArithmeticFunction.moebius n:ℤ):ℂ)‖^2 = _
  rw [←Int.cast_sum,←Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rfl

private theorem mers_succ (N : ℕ) : mers (N+1)=mers N+ArithmeticFunction.moebius (N+1) := by
  have he : Icc 1 (N+1) = insert (N+1) (Icc 1 N) := by
    ext i; simp only [mem_Icc,mem_insert]; omega
  rw [mers,he,sum_insert (by simp),add_comm]
  rfl

/-- Difference of the two consecutive Mertens squares. -/
def squareJump (N : ℕ) : ℤ :=
  (ArithmeticFunction.moebius (N+1):ℤ)*(2*mers N+ArithmeticFunction.moebius (N+1))

/-- Rectangular four-reading difference across a cutoff and a bandwidth step. -/
def readingDifference (Y : ℕ → ℝ → ℝ) (N : ℕ) (d h : ℝ) :=
  (Y (N+1) (d+h)-Y (N+1) d)-(Y N (d+h)-Y N d)

theorem folded_mertens_square_jump {N L : ℕ} (hcap : N+1 ≤ 2^L)
    {d h : ℝ} (hd : Real.log (N+1:ℕ) ≤ d) (hh : 0 ≤ h) :
    readingDifference (foldedMertensReading L) N d h = h*(squareJump N:ℝ) := by
  have hcap' := (Nat.le_succ N).trans hcap
  have hd' : Real.log N ≤ d := by
    rcases Nat.eq_zero_or_pos N with rfl|hN
    · simpa using hd
    exact (Real.log_le_log (Nat.cast_pos.mpr hN) (Nat.cast_le.mpr (Nat.le_succ N))).trans hd
  unfold readingDifference
  rw [folded_equals_energy hcap,folded_equals_energy hcap,folded_equals_energy hcap',folded_equals_energy hcap',
    wide_window_step _ _ hd hh,wide_window_step _ _ hd' hh,norm_mertens,norm_mertens,mers_succ,squareJump]
  push_cast
  ring

/-- No cancellation can conceal a nonzero unit step of the integer walk:
the observed jump is odd exactly on the squarefree support. -/
theorem square_jump_odd_iff (N : ℕ) : Odd (squareJump N) ↔ Squarefree (N+1) := by
  rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree]
  rcases ArithmeticFunction.moebius_eq_or (N+1) with h|h|h <;>
    simp only [squareJump,h] <;> constructor
  all_goals first | (intro hbad; simp_all) | (intro hμ; unfold Odd; use mers N; ring) |
    (intro hμ; unfold Odd; use -(mers N); ring) | (intro hμ; norm_num)

private theorem square_jump_gap (N : ℕ) :
    (Squarefree (N+1) → 1 ≤ |(squareJump N:ℝ)|) ∧
      (¬ Squarefree (N+1) → squareJump N=0) := by
  constructor
  · intro hs
    obtain ⟨k,hk⟩ := (square_jump_odd_iff N).mpr hs
    have h₁ : (1:ℤ) ≤ |squareJump N| := by rw [hk]; rw [le_abs]; omega
    exact_mod_cast h₁
  · intro hs
    have hzero : ArithmeticFunction.moebius (N+1)=0 := not_ne_iff.mp
      (fun hn => hs (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hn))
    simp [squareJump,hzero]

/-- Four noisy integrals still decide squarefreeness whenever the
bandwidth step exceeds eight times the error of each reading. -/
theorem noisy_folded_readings_detect_squarefree {N L : ℕ} (hcap : N+1 ≤ 2^L)
    {d h δ : ℝ} (hd : Real.log (N+1:ℕ) ≤ d) (hδ : 0 ≤ δ) (hh : 8*δ < h)
    (Y : ℕ → ℝ → ℝ) (he : ∀ k ∈ ({N,N+1} : Finset ℕ), ∀ w ∈ ({d,d+h} : Finset ℝ),
      |Y k w-foldedMertensReading L k w| ≤ δ) :
    Squarefree (N+1) ↔ h/2 < |readingDifference Y N d h| := by
  have hp : 0 < h := by linarith
  have h₁ := abs_le.mp (he N (by simp) d (by simp))
  have h₂ := abs_le.mp (he N (by simp) (d+h) (by simp))
  have h₃ := abs_le.mp (he (N+1) (by simp) d (by simp))
  have h₄ := abs_le.mp (he (N+1) (by simp) (d+h) (by simp))
  have hD : |readingDifference Y N d h-h*(squareJump N:ℝ)| ≤ 4*δ := by
    rw [←folded_mertens_square_jump hcap hd hp.le,abs_le]
    dsimp only [readingDifference]
    constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2,h₄.1,h₄.2]
  obtain ⟨hbig,hzero⟩ := square_jump_gap N
  constructor
  · intro hs
    have ht := abs_sub_abs_le_abs_sub (h*(squareJump N:ℝ)) (readingDifference Y N d h)
    rw [abs_sub_comm (h*(squareJump N:ℝ)),abs_mul,abs_of_pos hp] at ht
    linarith only [hD,ht,mul_le_mul_of_nonneg_left (hbig hs) hp.le,hh]
  · contrapose!
    intro hn
    rw [hzero hn,Int.cast_zero,mul_zero,sub_zero] at hD
    linarith

end GaloisForLFunctions.ConjugateDiagonalGeometry.FoldedWindow
