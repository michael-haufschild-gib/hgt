import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonAnnulus

/-!
# No ultraviolet cascade

In a weak real frequency-diagonal potential the clock's energy above a cutoff is trapped: it is the
energy of an independent sub-clock, and the trapping law bounds it by a fixed multiple of its own
initial value, at every instant of time. The initial value tends to zero as the cutoff grows, because
the low-pass projections converge strongly to the identity.

So for every `ε` there is a cutoff above which the clock carries less than `ε` of energy — *for all
time*, not merely on a finite window. Such a background cannot drive energy up the spectrum: what
starts below a frequency stays below it, up to an error that is fixed once and for all.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The high-frequency part of a datum vanishes as the cutoff grows. -/
theorem tendsto_norm_sub_kgLowPassOp (x : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun R : ℝ => ‖x - kgLowPassOp R x‖) atTop (𝓝 0) := by
  have h := (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply x)
  simpa [norm_sub_rev] using h

section NoCascade

variable {φ : E → ℂ} {b : ℝ}

/-- The energy of a clock splits into its low- and high-frequency parts, in the autonomous
register. -/
theorem kgFieldEnergy_band_split_static (hφ : Measurable φ) (hb0 : 0 ≤ b)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (R : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad (fourierMulCLM hφ hb0 hC) g h t‖ ^ (2 : ℕ)
        + ‖kgFieldVel (fourierMulCLM hφ hb0 hC) g h t‖ ^ (2 : ℕ)
      = (‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (kgLowPassOp R g) (kgLowPassOp R h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (kgLowPassOp R g) (kgLowPassOp R h) t‖ ^ (2 : ℕ))
        + (‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)) := by
  have hsplit := kgFieldEnergyT_band_split (w := fun _ : ℝ => φ) (fun _ => hφ) hb0
    (fun _ => hC) (fun _ => continuous_const) R g h t
  simp only [kgFieldGradT_const, kgFieldVelT_const] at hsplit
  exact hsplit

/-- **The high-frequency energy is bounded by a fixed multiple of its own initial value**, at every
instant of time. -/
theorem kgFieldEnergy_high_le (hφ : Measurable φ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ)
    (R : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
          (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)
        + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
          (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)
      ≤ (1 + b) / (1 - b)
          * (‖g - kgLowPassOp R g‖ ^ (2 : ℕ) + ‖h - kgLowPassOp R h‖ ^ (2 : ℕ)) :=
  (kgFieldEnergy_trapped_diagonal hφ hb0 hb1 hC hreal (g - kgLowPassOp R g)
    (h - kgLowPassOp R h) t).2

/-- **No ultraviolet cascade.** For every `ε` there is a cutoff above which the clock carries less
than `ε` of energy, at every instant of time. -/
theorem exists_cutoff_high_energy_small (hφ : Measurable φ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ)
    (g h : Lp ℂ 2 (volume : Measure E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ t : ℝ,
      ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
            (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
            (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ) ≤ ε := by
  have hK : (0 : ℝ) < (1 + b) / (1 - b) := div_pos (by linarith) (by linarith)
  have hquot : (0 : ℝ) < ε / ((1 + b) / (1 - b)) := div_pos hε hK
  have hg := tendsto_norm_sub_kgLowPassOp g
  have hh := tendsto_norm_sub_kgLowPassOp h
  have hsum : Tendsto (fun R : ℝ =>
      ‖g - kgLowPassOp R g‖ ^ (2 : ℕ) + ‖h - kgLowPassOp R h‖ ^ (2 : ℕ)) atTop (𝓝 0) := by
    have hpow := (hg.pow 2).add (hh.pow 2)
    simpa using hpow
  have hev : ∀ᶠ R : ℝ in atTop,
      ‖g - kgLowPassOp R g‖ ^ (2 : ℕ) + ‖h - kgLowPassOp R h‖ ^ (2 : ℕ)
        < ε / ((1 + b) / (1 - b)) := hsum.eventually_lt_const hquot
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hev
  refine ⟨R₀, fun R hR t => ?_⟩
  have hbound := kgFieldEnergy_high_le hφ hb0 hb1 hC hreal R g h t
  have hlt := hR₀ R hR
  have hchain : (1 + b) / (1 - b)
      * (‖g - kgLowPassOp R g‖ ^ (2 : ℕ) + ‖h - kgLowPassOp R h‖ ^ (2 : ℕ))
      ≤ (1 + b) / (1 - b) * (ε / ((1 + b) / (1 - b))) :=
    mul_le_mul_of_nonneg_left hlt.le hK.le
  have hcancel : (1 + b) / (1 - b) * (ε / ((1 + b) / (1 - b))) = ε := by
    rw [mul_comm, div_mul_cancel₀ _ hK.ne']
  linarith

/-- **All but `ε` of a clock's energy stays below a fixed frequency, forever.** -/
theorem kgFieldEnergy_no_uv_cascade (hφ : Measurable φ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ)
    (g h : Lp ℂ 2 (volume : Measure E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ t : ℝ,
      ‖kgFieldGrad (fourierMulCLM hφ hb0 hC) g h t‖ ^ (2 : ℕ)
            + ‖kgFieldVel (fourierMulCLM hφ hb0 hC) g h t‖ ^ (2 : ℕ)
          = (‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
                (kgLowPassOp R g) (kgLowPassOp R h) t‖ ^ (2 : ℕ)
              + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
                (kgLowPassOp R g) (kgLowPassOp R h) t‖ ^ (2 : ℕ))
            + (‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
                (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)
              + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
                (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ))
        ∧ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC)
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ)
            + ‖kgFieldVel (fourierMulCLM hφ hb0 hC)
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t‖ ^ (2 : ℕ) ≤ ε := by
  obtain ⟨R₀, hR₀⟩ := exists_cutoff_high_energy_small hφ hb0 hb1 hC hreal g h hε
  exact ⟨R₀, fun R hR t =>
    ⟨kgFieldEnergy_band_split_static hφ hb0 hC R g h t, hR₀ R hR t⟩⟩

end NoCascade

end GaloisForLFunctions.HTGeometry
