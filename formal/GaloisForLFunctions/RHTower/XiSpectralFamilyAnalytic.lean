import GaloisForLFunctions.RHTower.XiSpectralFamily
import GaloisForLFunctions.RHTower.XiPoissonTraceAnalytic

/-!
# Analyticity and shell structure of an admissible family

Continuing the transfer of the vertical-line argument to `SpectralFamily`.  On a box of the open
right half-plane the multipliers are dominated by a summable function, so Weierstrass gives
analyticity; and finite shells give least heights on every nonempty set of copies, hence a bottom
shell and a spectral gap above it.

Both proofs are the ones already run for the Poisson coordinate, with the structure fields in place
of the named lemmas.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

namespace SpectralFamily

noncomputable section

variable (F : SpectralFamily)

theorem differentiable_term (q : XiZeroCopy) :
    Differentiable ℂ (fun τ : ℂ => F.term τ q) := by
  unfold term
  fun_prop

theorem norm_term_le_on_box {σ₀ M : ℝ} (q : XiZeroCopy) {t : ℂ}
    (ht : t ∈ xiPoissonBox σ₀ M) :
    ‖F.term t q‖ ≤ Real.exp (M / 2) * F.weight σ₀ q := by
  obtain ⟨hre, him⟩ := ht
  rw [norm_term, weight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hR : 0 ≤ (F.pt q).re := F.re_nonneg q
  have hJ : |(F.pt q).im| < 1 / 2 := F.abs_im_lt q
  have h1 : σ₀ * (F.pt q).re ≤ t.re * (F.pt q).re :=
    mul_le_mul_of_nonneg_right hre.le hR
  have h2 : t.im * (F.pt q).im ≤ M / 2 := by
    calc t.im * (F.pt q).im ≤ |t.im * (F.pt q).im| := le_abs_self _
      _ = |t.im| * |(F.pt q).im| := abs_mul _ _
      _ ≤ M * (1 / 2) := by
          refine mul_le_mul him.le hJ.le (abs_nonneg _) ?_
          exact le_trans (abs_nonneg _) him.le
      _ = M / 2 := by ring
  linarith

theorem differentiableOn_traceC_box {σ₀ M : ℝ} (hσ₀ : 0 < σ₀) :
    DifferentiableOn ℂ F.traceC (xiPoissonBox σ₀ M) :=
  Complex.differentiableOn_tsum_of_summable_norm
    (u := fun q : XiZeroCopy => Real.exp (M / 2) * F.weight σ₀ q)
    ((F.summable_weight hσ₀).mul_left _)
    (fun q => (F.differentiable_term q).differentiableOn)
    (isOpen_xiPoissonBox σ₀ M)
    (fun q _ ht => F.norm_term_le_on_box q ht)

theorem differentiableAt_traceC {t : ℂ} (ht : 0 < t.re) :
    DifferentiableAt ℂ F.traceC t := by
  have hmem : t ∈ xiPoissonBox (t.re / 2) (|t.im| + 1) := ⟨by linarith, by linarith⟩
  refine (F.differentiableOn_traceC_box (M := |t.im| + 1)
    (by linarith : (0 : ℝ) < t.re / 2)).differentiableAt ?_
  exact (isOpen_xiPoissonBox _ _).mem_nhds hmem

/-- **The trace of an admissible family is analytic on the open right half-plane.** -/
theorem analyticOnNhd_traceC : AnalyticOnNhd ℂ F.traceC {t : ℂ | 0 < t.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  intro t ht
  exact (F.differentiableAt_traceC ht).differentiableWithinAt

/-- Any nonempty set of copies attains a least height. -/
theorem exists_min_re_of_nonempty {s : Set XiZeroCopy} (hs : s.Nonempty) :
    ∃ q₀ ∈ s, ∀ q ∈ s, (F.pt q₀).re ≤ (F.pt q).re := by
  classical
  obtain ⟨q₁, hq₁⟩ := hs
  have hfin : (s ∩ {q : XiZeroCopy | (F.pt q).re ≤ (F.pt q₁).re}).Finite :=
    (F.shell_finite (F.pt q₁).re).subset Set.inter_subset_right
  have hmem : q₁ ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨hq₁, le_refl _⟩
  obtain ⟨q₀, hq₀mem, hq₀min⟩ :=
    Finset.exists_min_image hfin.toFinset (fun q => (F.pt q).re) ⟨q₁, hmem⟩
  have hq₀ : q₀ ∈ s ∧ (F.pt q₀).re ≤ (F.pt q₁).re := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq] using hq₀mem
  refine ⟨q₀, hq₀.1, fun q hq => ?_⟩
  by_cases hcase : (F.pt q).re ≤ (F.pt q₁).re
  · refine hq₀min q ?_
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨hq, hcase⟩
  · linarith [not_le.mp hcase, hq₀.2]

/-- The copies at or above a height cut. -/
def cut (g : ℝ) : Set XiZeroCopy := {q : XiZeroCopy | g ≤ (F.pt q).re}

theorem mem_cut {g : ℝ} {q : XiZeroCopy} : q ∈ F.cut g ↔ g ≤ (F.pt q).re := Iff.rfl

theorem cut_lineConj {g : ℝ} {q : XiZeroCopy} (hq : q ∈ F.cut g) :
    xiZeroCopyLineConjEquiv q ∈ F.cut g := by
  rw [mem_cut, F.conj_stable, Complex.conj_re]
  exact hq

theorem finite_cut_shell (g R : ℝ) :
    {q : XiZeroCopy | q ∈ F.cut g ∧ (F.pt q).re ≤ R}.Finite :=
  (F.shell_finite R).subset fun _ hq => hq.2

end

end SpectralFamily

end RHTower
