import GaloisForLFunctions.RHTower.XiSpectralFamilyDecay
import GaloisForLFunctions.RHTower.XiPoissonVerticalSplit

/-!
# The bottom shell of an admissible family

Shell structure over the interface: the copies at the least height form a finite set on which the
height factors out of the trace exactly, everything above it is separated by a spectral gap, and the
trace splits accordingly on a vertical line.

These are the last Xi-specific facts of the chain, restated so that they hold for any admissible
family.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

namespace SpectralFamily

noncomputable section

variable (F : SpectralFamily)

/-- The copies at the family's least height. -/
def bottomShell : Finset XiZeroCopy := (F.shell_finite F.bottomHeight).toFinset

theorem mem_bottomShell {q : XiZeroCopy} :
    q ∈ F.bottomShell ↔ (F.pt q).re = F.bottomHeight := by
  rw [bottomShell, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun h => le_antisymm h (F.bottomHeight_le q), fun h => le_of_eq h⟩

theorem mem_bottomShell_lineConj {q : XiZeroCopy} (hq : q ∈ F.bottomShell) :
    xiZeroCopyLineConjEquiv q ∈ F.bottomShell := by
  rw [mem_bottomShell, F.conj_stable, Complex.conj_re]
  exact F.mem_bottomShell.mp hq

/-- The copies strictly above the least height. -/
def aboveBottom : Set XiZeroCopy := ((F.bottomShell : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ

theorem mem_aboveBottom {q : XiZeroCopy} :
    q ∈ F.aboveBottom ↔ F.bottomHeight < (F.pt q).re := by
  rw [aboveBottom, Set.mem_compl_iff, Finset.mem_coe, F.mem_bottomShell]
  constructor
  · intro h
    exact lt_of_le_of_ne (F.bottomHeight_le q) (fun heq => h heq.symm)
  · intro h heq
    exact absurd heq (ne_of_gt h)

theorem exists_secondHeight (hne : F.aboveBottom.Nonempty) :
    ∃ g₂ : ℝ, F.bottomHeight < g₂ ∧ ∀ q ∈ F.aboveBottom, g₂ ≤ (F.pt q).re := by
  obtain ⟨q₀, hq₀, hmin⟩ := F.exists_min_re_of_nonempty hne
  exact ⟨(F.pt q₀).re, F.mem_aboveBottom.mp hq₀, hmin⟩

/-- The bottom-shell sum on a vertical line. -/
def bottomShellSum (σ u : ℝ) : ℂ :=
  ∑ q ∈ F.bottomShell, F.term ((σ : ℂ) + (u : ℂ) * I) q

/-- The above-bottom part of the trace on a vertical line. -/
def aboveBottomSum (s u : ℝ) : ℂ :=
  ∑' q : F.aboveBottom, F.term ((s : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)

/-- On the bottom shell the height factors out, leaving only a phase. -/
theorem bottomShellSum_eq (σ u : ℝ) :
    F.bottomShellSum σ u =
      Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * (F.bottomHeight : ℂ)) *
        ∑ q ∈ F.bottomShell,
          Complex.exp (-(σ : ℂ) * I * ((F.pt q).im : ℂ)) *
            ((Real.exp (u * (F.pt q).im) : ℝ) : ℂ) := by
  rw [bottomShellSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hsplit : F.pt q = ((F.bottomHeight : ℝ) : ℂ) + ((F.pt q).im : ℂ) * I := by
    rw [← F.mem_bottomShell.mp hq]
    exact (Complex.re_add_im _).symm
  rw [term]
  conv_lhs => rw [hsplit]
  exact xiPoisson_line_factor σ u F.bottomHeight (F.pt q).im

/-- The trace on a vertical line is its bottom shell plus everything above. -/
theorem traceC_vertical_split {s : ℝ} (hs : 0 < s) (u : ℝ) :
    F.traceC ((s : ℂ) + (u : ℂ) * I) = F.bottomShellSum s u + F.aboveBottomSum s u := by
  have hre : 0 < ((s : ℂ) + (u : ℂ) * I).re := by rw [re_vertical]; exact hs
  have hsum : Summable (fun q : XiZeroCopy => F.term ((s : ℂ) + (u : ℂ) * I) q) :=
    (F.summable_norm_term hre).of_norm
  exact (hsum.sum_add_tsum_compl).symm

/-- **The weighted tail bound.** -/
theorem exp_bottomHeight_mul_norm_aboveBottomSum_le {σ : ℝ} (hσ : 0 < σ)
    {g₂ : ℝ} (hg₂ : ∀ q ∈ F.aboveBottom, g₂ ≤ (F.pt q).re)
    {v : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    Real.exp (F.bottomHeight * v) * ‖F.aboveBottomSum (σ + v) u‖ ≤
      Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
        ∑' q : F.aboveBottom, F.weight σ (q : XiZeroCopy) := by
  have hsv : 0 < σ + v := by linarith
  have hre : 0 < (((σ + v : ℝ) : ℂ) + (u : ℂ) * I).re := by rw [re_vertical]; exact hsv
  have hsumnorm := F.summable_norm_term hre
  have hsumσ : Summable (fun q : F.aboveBottom => F.weight σ (q : XiZeroCopy)) :=
    (F.summable_weight hσ).subtype _
  have hterm : ∀ q : F.aboveBottom,
      Real.exp (F.bottomHeight * v) * ‖F.term (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)‖ ≤
        Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
          F.weight σ (q : XiZeroCopy) := by
    intro q
    have hR : g₂ ≤ (F.pt (q : XiZeroCopy)).re := hg₂ _ q.2
    have hJ : |(F.pt (q : XiZeroCopy)).im| < 1 / 2 := F.abs_im_lt _
    rw [norm_term, re_vertical, im_vertical, weight, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have huJ : u * (F.pt (q : XiZeroCopy)).im ≤ |u| / 2 := by
      calc u * (F.pt (q : XiZeroCopy)).im ≤ |u * (F.pt (q : XiZeroCopy)).im| := le_abs_self _
        _ = |u| * |(F.pt (q : XiZeroCopy)).im| := abs_mul _ _
        _ ≤ |u| * (1 / 2) := mul_le_mul_of_nonneg_left hJ.le (abs_nonneg _)
        _ = |u| / 2 := by ring
    nlinarith [hR, hv, huJ]
  calc Real.exp (F.bottomHeight * v) * ‖F.aboveBottomSum (σ + v) u‖
      ≤ Real.exp (F.bottomHeight * v) *
          ∑' q : F.aboveBottom,
            ‖F.term (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact norm_tsum_le_tsum_norm (hsumnorm.subtype _)
    _ = ∑' q : F.aboveBottom,
          Real.exp (F.bottomHeight * v) *
            ‖F.term (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)‖ := (tsum_mul_left).symm
    _ ≤ ∑' q : F.aboveBottom,
          Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
            F.weight σ (q : XiZeroCopy) :=
        Summable.tsum_le_tsum hterm ((hsumnorm.subtype _).mul_left _) (hsumσ.mul_left _)
    _ = Real.exp (|u| / 2) * Real.exp (-((g₂ - F.bottomHeight) * v)) *
          ∑' q : F.aboveBottom, F.weight σ (q : XiZeroCopy) := tsum_mul_left

end

end SpectralFamily

end RHTower
