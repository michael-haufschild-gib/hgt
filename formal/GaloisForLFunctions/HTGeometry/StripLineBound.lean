import Mathlib

/-!
# From a large-height line bound to a full line bound

Phragmén--Lindelöf asks for a bound on the *whole* boundary line, while the analytic estimates that
feed it are only available above a fixed height.  For a continuous function the gap is closed by
compactness of the remaining segment.

## Main results

* `isCompact_verticalSegment`
* `exists_line_bound_of_high`
-/

noncomputable section

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem continuous_verticalLinePoint (σ : ℝ) :
    Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) := by
  fun_prop

theorem isCompact_verticalSegment (σ T : ℝ) :
    IsCompact ((fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) '' (Icc (-T) T)) :=
  isCompact_Icc.image (continuous_verticalLinePoint σ)

/-- **A continuous function bounded above a fixed height on a vertical line is bounded on the whole
line.** -/
theorem exists_line_bound_of_high {F : ℂ → ℂ} (hF : Continuous F) {σ C T : ℝ} (hC : 0 ≤ C)
    (hT : 0 ≤ T) (h : ∀ t : ℝ, T ≤ |t| → ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ z : ℂ, z.re = σ → ‖F z‖ ≤ C' := by
  classical
  set K : Set ℂ := (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) '' (Icc (-T) T) with hK
  have hKc : IsCompact K := isCompact_verticalSegment σ T
  have hKne : K.Nonempty := ⟨(σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I, ⟨0, ⟨by linarith, hT⟩, rfl⟩⟩
  obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hKne (hF.norm.continuousOn)
  refine ⟨max C ‖F z₀‖, le_trans hC (le_max_left _ _), ?_⟩
  intro z hz
  have hzeq : z = (σ : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hz]
  rcases le_or_gt T |z.im| with hge | hlt
  · refine le_trans ?_ (le_max_left _ _)
    rw [hzeq]
    exact h z.im hge
  · refine le_trans ?_ (le_max_right _ _)
    refine hmax ?_
    refine ⟨z.im, ⟨?_, ?_⟩, hzeq.symm⟩
    · have := abs_le.1 (le_of_lt hlt)
      linarith [this.1]
    · have := abs_le.1 (le_of_lt hlt)
      linarith [this.2]

/-- A weighted version: a large-height weighted bound extends to the whole line as soon as the
weight is at least one there. -/
theorem exists_line_bound_weighted {F : ℂ → ℂ} (hF : Continuous F) {σ c₀ ν C T : ℝ}
    (hν : 0 ≤ ν) (hσc : 1 ≤ σ - c₀) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (h : ∀ t : ℝ, T ≤ |t| →
      ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * ‖((σ : ℂ) + (t : ℂ) * Complex.I) - (c₀ : ℂ)‖ ^ ν) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ z : ℂ, z.re = σ → ‖F z‖ ≤ C' * ‖z - (c₀ : ℂ)‖ ^ ν := by
  classical
  set K : Set ℂ := (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) '' (Icc (-T) T) with hK
  have hKc : IsCompact K := isCompact_verticalSegment σ T
  have hKne : K.Nonempty := ⟨(σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I, ⟨0, ⟨by linarith, hT⟩, rfl⟩⟩
  obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hKne (hF.norm.continuousOn)
  refine ⟨max C ‖F z₀‖, le_trans hC (le_max_left _ _), ?_⟩
  intro z hz
  have hweight : 1 ≤ ‖z - (c₀ : ℂ)‖ := by
    calc (1 : ℝ) ≤ σ - c₀ := hσc
      _ = (z - (c₀ : ℂ)).re := by rw [Complex.sub_re, Complex.ofReal_re, hz]
      _ ≤ |(z - (c₀ : ℂ)).re| := le_abs_self _
      _ ≤ ‖z - (c₀ : ℂ)‖ := Complex.abs_re_le_norm _
  have hpow : (1 : ℝ) ≤ ‖z - (c₀ : ℂ)‖ ^ ν := Real.one_le_rpow hweight hν
  have hzeq : z = (σ : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hz]
  rcases le_or_gt T |z.im| with hge | hlt
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left C ‖F z₀‖)
      (Real.rpow_nonneg (norm_nonneg _) ν))
    rw [hzeq]
    exact h z.im hge
  · have hb : ‖F z‖ ≤ ‖F z₀‖ := by
      refine hmax ?_
      refine ⟨z.im, ⟨?_, ?_⟩, hzeq.symm⟩
      · have := abs_le.1 (le_of_lt hlt)
        linarith [this.1]
      · have := abs_le.1 (le_of_lt hlt)
        linarith [this.2]
    calc ‖F z‖ ≤ ‖F z₀‖ := hb
      _ ≤ max C ‖F z₀‖ := le_max_right _ _
      _ ≤ max C ‖F z₀‖ * ‖z - (c₀ : ℂ)‖ ^ ν := by
          nlinarith [le_trans hC (le_max_left C ‖F z₀‖)]

theorem isCompact_stripSegment (A B T : ℝ) :
    IsCompact {z : ℂ | A ≤ z.re ∧ z.re ≤ B ∧ |z.im| ≤ T} := by
  have himg : {z : ℂ | A ≤ z.re ∧ z.re ≤ B ∧ |z.im| ≤ T}
      = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) '' (Icc A B ×ˢ Icc (-T) T) := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · exact ⟨by linarith [(abs_le.1 h3).1], (abs_le.1 h3).2⟩
      · apply Complex.ext <;> simp
    · rintro ⟨⟨x, y⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
      refine ⟨by simpa using h1, by simpa using h2, ?_⟩
      have : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
      rw [this, abs_le]
      exact ⟨h3, h4⟩
  rw [himg]
  refine (isCompact_Icc.prod isCompact_Icc).image ?_
  fun_prop

/-- A large-height polynomial bound on a strip extends to the whole strip. -/
theorem exists_strip_bound_of_high {F : ℂ → ℂ} (hF : Continuous F) {A B C N T : ℝ}
    (hN : 0 ≤ N) (hC : 0 ≤ C) (hT : 0 ≤ T) (hAB : A ≤ B)
    (h : ∀ z : ℂ, A ≤ z.re → z.re ≤ B → T ≤ |z.im| → ‖F z‖ ≤ C * (1 + |z.im|) ^ N) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ z : ℂ, A ≤ z.re → z.re ≤ B → ‖F z‖ ≤ C' * (1 + |z.im|) ^ N := by
  classical
  set K : Set ℂ := {z : ℂ | A ≤ z.re ∧ z.re ≤ B ∧ |z.im| ≤ T} with hK
  have hKc : IsCompact K := isCompact_stripSegment A B T
  have hKne : K.Nonempty := ⟨(A : ℂ), ⟨by simp, by simpa using hAB, by simp [hT]⟩⟩
  obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hKne (hF.norm.continuousOn)
  refine ⟨max C ‖F z₀‖, le_trans hC (le_max_left _ _), ?_⟩
  intro z h1 h2
  have hpow : (1 : ℝ) ≤ (1 + |z.im|) ^ N :=
    Real.one_le_rpow (by linarith [abs_nonneg z.im]) hN
  rcases le_or_gt T |z.im| with hge | hlt
  · refine le_trans (h z h1 h2 hge) ?_
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    positivity
  · have hb : ‖F z‖ ≤ ‖F z₀‖ := hmax ⟨h1, h2, le_of_lt hlt⟩
    calc ‖F z‖ ≤ ‖F z₀‖ := hb
      _ ≤ max C ‖F z₀‖ := le_max_right _ _
      _ ≤ max C ‖F z₀‖ * (1 + |z.im|) ^ N := by
          nlinarith [le_trans hC (le_max_left C ‖F z₀‖)]

end GaloisForLFunctions.HTGeometry

end
