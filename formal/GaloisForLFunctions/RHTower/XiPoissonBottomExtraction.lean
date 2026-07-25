import GaloisForLFunctions.RHTower.XiPoissonBottomShellRigidity

/-!
# Extracting the bottom Poisson shell

Above the bottom shell there is a strictly higher lowest height `g₂`, because shells are finite and
the heights of the copies outside the bottom shell are bounded below by their own minimum.  The
whole above-bottom part of the trace therefore decays, along the real time axis, strictly faster
than the bottom shell does:

`exp (g₁ v) * sum_{q above} exp (-(sigma + v) R q)  <=  exp (-(g₂ - g₁) v) * (constant)  ->  0`.

This is the estimate that isolates the bottom shell inside the trace: multiplying by `exp (g₁ v)`
holds the bottom shell fixed and kills everything above it.
-/

open Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Any nonempty set of copies attains a least height, because shells are finite. -/
theorem exists_min_xiPoissonPoint_re_of_nonempty {s : Set XiZeroCopy} (hs : s.Nonempty) :
    ∃ q₀ ∈ s, ∀ q ∈ s, (xiPoissonPoint q₀).re ≤ (xiPoissonPoint q).re := by
  classical
  obtain ⟨q₁, hq₁⟩ := hs
  have hfin : (s ∩ {q : XiZeroCopy | (xiPoissonPoint q).re ≤ (xiPoissonPoint q₁).re}).Finite :=
    (finite_xiPoissonShell (xiPoissonPoint q₁).re).subset Set.inter_subset_right
  have hmem : q₁ ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨hq₁, le_refl _⟩
  obtain ⟨q₀, hq₀mem, hq₀min⟩ :=
    Finset.exists_min_image hfin.toFinset (fun q => (xiPoissonPoint q).re) ⟨q₁, hmem⟩
  have hq₀ : q₀ ∈ s ∧ (xiPoissonPoint q₀).re ≤ (xiPoissonPoint q₁).re := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq] using hq₀mem
  refine ⟨q₀, hq₀.1, fun q hq => ?_⟩
  by_cases hcase : (xiPoissonPoint q).re ≤ (xiPoissonPoint q₁).re
  · refine hq₀min q ?_
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨hq, hcase⟩
  · linarith [not_le.mp hcase, hq₀.2]

/-- The copies strictly above the bottom shell, i.e. the complement of the bottom shell. -/
def xiPoissonAboveBottom : Set XiZeroCopy :=
  ((xiPoissonBottomShell : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ

theorem mem_xiPoissonAboveBottom {q : XiZeroCopy} :
    q ∈ xiPoissonAboveBottom ↔ xiPoissonBottomHeight < (xiPoissonPoint q).re := by
  rw [xiPoissonAboveBottom, Set.mem_compl_iff, Finset.mem_coe, mem_xiPoissonBottomShell]
  constructor
  · intro h
    exact lt_of_le_of_ne (xiPoissonBottomCopy_min q) (fun heq => h heq.symm)
  · intro h heq
    exact absurd heq (ne_of_gt h)

/-- There is a spectral gap above the bottom shell. -/
theorem exists_xiPoissonSecondHeight (hne : xiPoissonAboveBottom.Nonempty) :
    ∃ g₂ : ℝ, xiPoissonBottomHeight < g₂ ∧
      ∀ q ∈ xiPoissonAboveBottom, g₂ ≤ (xiPoissonPoint q).re := by
  obtain ⟨q₀, hq₀, hmin⟩ := exists_min_xiPoissonPoint_re_of_nonempty hne
  exact ⟨(xiPoissonPoint q₀).re, mem_xiPoissonAboveBottom.mp hq₀, hmin⟩

/-- **The extraction estimate.**  Weighting by the bottom height, the above-bottom part of the
Poisson trace vanishes as the real time grows.  This is what leaves the bottom shell alone in the
limit. -/
theorem tendsto_exp_bottomHeight_mul_aboveBottom_tail {σ : ℝ} (hσ : 0 < σ)
    (hne : xiPoissonAboveBottom.Nonempty) :
    Tendsto
      (fun v : ℝ => Real.exp (xiPoissonBottomHeight * v) *
        ∑' q : xiPoissonAboveBottom, xiPoissonWeight (σ + v) (q : XiZeroCopy))
      atTop (nhds 0) := by
  classical
  obtain ⟨g₂, hgap, hg₂⟩ := exists_xiPoissonSecondHeight hne
  set C : ℝ := ∑' q : xiPoissonAboveBottom, xiPoissonWeight σ (q : XiZeroCopy) with hC
  have hsumσ : Summable (fun q : xiPoissonAboveBottom => xiPoissonWeight σ (q : XiZeroCopy)) :=
    (summable_xiPoissonWeight hσ).subtype _
  refine squeeze_zero'
    (g := fun v : ℝ => Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) * C) ?_ ?_ ?_
  · filter_upwards with v
    exact mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun q => (xiPoissonWeight_pos _ _).le)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    have hsumv : Summable
        (fun q : xiPoissonAboveBottom => xiPoissonWeight (σ + v) (q : XiZeroCopy)) :=
      (summable_xiPoissonWeight (by linarith)).subtype _
    have hterm : ∀ q : xiPoissonAboveBottom,
        Real.exp (xiPoissonBottomHeight * v) * xiPoissonWeight (σ + v) (q : XiZeroCopy) ≤
          Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) * xiPoissonWeight σ (q : XiZeroCopy) := by
      intro q
      have hR : g₂ ≤ (xiPoissonPoint (q : XiZeroCopy)).re := hg₂ _ q.2
      rw [xiPoissonWeight, xiPoissonWeight, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hR, hv, hgap]
    calc Real.exp (xiPoissonBottomHeight * v) *
          ∑' q : xiPoissonAboveBottom, xiPoissonWeight (σ + v) (q : XiZeroCopy)
        = ∑' q : xiPoissonAboveBottom,
            Real.exp (xiPoissonBottomHeight * v) * xiPoissonWeight (σ + v) (q : XiZeroCopy) :=
          (tsum_mul_left).symm
      _ ≤ ∑' q : xiPoissonAboveBottom,
            Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) *
              xiPoissonWeight σ (q : XiZeroCopy) :=
          Summable.tsum_le_tsum hterm (hsumv.mul_left _) (hsumσ.mul_left _)
      _ = Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) * C := tsum_mul_left
  · have hneg : -(g₂ - xiPoissonBottomHeight) < 0 := by linarith
    have h1 : Tendsto (fun v : ℝ => v * -(g₂ - xiPoissonBottomHeight)) atTop atBot :=
      Filter.Tendsto.atTop_mul_const_of_neg hneg Filter.tendsto_id
    have h2 : Tendsto (fun v : ℝ => Real.exp (-((g₂ - xiPoissonBottomHeight) * v)))
        atTop (nhds 0) := by
      have := Real.tendsto_exp_atBot.comp h1
      refine this.congr fun v => ?_
      simp only [Function.comp_apply]
      congr 1
      ring
    simpa using h2.mul_const C

/-- **The extraction, performed.**  Along the real time axis the bottom-height-weighted Poisson
trace converges to the bottom shell's own mass; everything above the bottom shell disappears.  The
limit records the multiplicity of the lowest shell. -/
theorem tendsto_exp_bottomHeight_mul_xiPoissonTraceReal {σ : ℝ} (hσ : 0 < σ)
    (hne : xiPoissonAboveBottom.Nonempty) :
    Tendsto (fun v : ℝ => Real.exp (xiPoissonBottomHeight * v) * xiPoissonTraceReal (σ + v))
      atTop
      (nhds ((xiPoissonBottomShell.card : ℝ) * Real.exp (-(σ * xiPoissonBottomHeight)))) := by
  have hsplit : ∀ v : ℝ, 0 ≤ v →
      Real.exp (xiPoissonBottomHeight * v) * xiPoissonTraceReal (σ + v) =
        (xiPoissonBottomShell.card : ℝ) * Real.exp (-(σ * xiPoissonBottomHeight)) +
          Real.exp (xiPoissonBottomHeight * v) *
            ∑' q : xiPoissonAboveBottom, xiPoissonWeight (σ + v) (q : XiZeroCopy) := by
    intro v hv
    have hsum : Summable (fun q : XiZeroCopy => xiPoissonWeight (σ + v) q) :=
      summable_xiPoissonWeight (by linarith)
    have hcompl : (∑ q ∈ xiPoissonBottomShell, xiPoissonWeight (σ + v) q) +
        ∑' q : xiPoissonAboveBottom, xiPoissonWeight (σ + v) (q : XiZeroCopy) =
          xiPoissonTraceReal (σ + v) := hsum.sum_add_tsum_compl
    have hbot : Real.exp (xiPoissonBottomHeight * v) *
        (∑ q ∈ xiPoissonBottomShell, xiPoissonWeight (σ + v) q) =
          (xiPoissonBottomShell.card : ℝ) * Real.exp (-(σ * xiPoissonBottomHeight)) := by
      have hconst : ∀ q ∈ xiPoissonBottomShell,
          xiPoissonWeight (σ + v) q = Real.exp (-((σ + v) * xiPoissonBottomHeight)) := by
        intro q hq
        rw [xiPoissonWeight, mem_xiPoissonBottomShell.mp hq]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
        mul_comm (Real.exp (xiPoissonBottomHeight * v)), mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [← hcompl, mul_add, hbot]
  have hmain : Tendsto
      (fun v : ℝ => (xiPoissonBottomShell.card : ℝ) * Real.exp (-(σ * xiPoissonBottomHeight)) +
        Real.exp (xiPoissonBottomHeight * v) *
          ∑' q : xiPoissonAboveBottom, xiPoissonWeight (σ + v) (q : XiZeroCopy))
      atTop (nhds ((xiPoissonBottomShell.card : ℝ) * Real.exp (-(σ * xiPoissonBottomHeight)))) := by
    simpa using (tendsto_exp_bottomHeight_mul_aboveBottom_tail hσ hne).const_add _
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
  exact (hsplit v hv).symm

/-- **The imaginary-ray bound.**  Weighting by the bottom height never increases the real-time trace,
because every height is at least the bottom height.  This is the boundary bound on the negative
imaginary ray needed to run Phragmén--Lindelöf on the lower quadrants. -/
theorem exp_bottomHeight_mul_xiPoissonTraceReal_le {σ : ℝ} (hσ : 0 < σ) {v : ℝ} (hv : 0 ≤ v) :
    Real.exp (xiPoissonBottomHeight * v) * xiPoissonTraceReal (σ + v) ≤ xiPoissonTraceReal σ := by
  have hsumv : Summable (fun q : XiZeroCopy => xiPoissonWeight (σ + v) q) :=
    summable_xiPoissonWeight (by linarith)
  have hterm : ∀ q : XiZeroCopy,
      Real.exp (xiPoissonBottomHeight * v) * xiPoissonWeight (σ + v) q ≤ xiPoissonWeight σ q := by
    intro q
    have hR : xiPoissonBottomHeight ≤ (xiPoissonPoint q).re := xiPoissonBottomCopy_min q
    rw [xiPoissonWeight, xiPoissonWeight, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hR, hv]
  calc Real.exp (xiPoissonBottomHeight * v) * xiPoissonTraceReal (σ + v)
      = ∑' q : XiZeroCopy, Real.exp (xiPoissonBottomHeight * v) * xiPoissonWeight (σ + v) q := by
        rw [xiPoissonTraceReal, tsum_mul_left]
    _ ≤ ∑' q : XiZeroCopy, xiPoissonWeight σ q :=
        Summable.tsum_le_tsum hterm (hsumv.mul_left _) (summable_xiPoissonWeight hσ)
    _ = xiPoissonTraceReal σ := rfl

end

end RHTower
