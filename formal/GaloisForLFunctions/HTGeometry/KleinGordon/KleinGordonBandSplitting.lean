import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandExact

/-!
# The flow decouples across a projection

A symmetry that is a projection splits the Cauchy datum into two pieces, and the flow keeps them
apart: the projected piece stays in the range of the projection for all time, the complementary piece
stays in its kernel, and the trajectory is at every instant the sum of the two.

For a frequency-diagonal background the low-pass operators are such projections, so a clock's
dynamics decouples across every frequency band exactly — the low-frequency part of the solution is the
solution of the low-frequency part of the datum, and nothing crosses between them at any time.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Splitting

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **The state is additive in the Cauchy datum.** -/
theorem kgFieldStateT_add (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT W (g₁ + g₂) (h₁ + h₂) t
      = kgFieldStateT W g₁ h₁ t + kgFieldStateT W g₂ h₂ t := by
  rw [kgFieldStateT_eq_kgStateMildT hb0 hWb hWs, kgFieldStateT_eq_kgStateMildT hb0 hWb hWs,
    kgFieldStateT_eq_kgStateMildT hb0 hWb hWs]
  have hlin := kgStateMildT_linear hb0 hWb hWs 1 1 g₁ h₁ g₂ h₂ t
  simpa using hlin

/-- The zero datum generates the zero state. -/
theorem kgFieldStateT_zero_datum (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (t : ℝ) :
    kgFieldStateT W (0 : Lp ℂ 2 (volume : Measure E)) 0 t = 0 := by
  have hsmul := kgFieldStateT_smul hb0 hWb hWs (0 : ℂ)
    (0 : Lp ℂ 2 (volume : Measure E)) 0 t
  simpa using hsmul

variable {Λ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}

/-- **The trajectory splits across a projection**, and the two pieces stay apart for all time. -/
theorem kgFieldStateT_decouple (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hcos : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgCosOp t x) = kgCosOp t (Λ x))
    (hsin : ∀ (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (kgSinOp t x) = kgSinOp t (Λ x))
    (hinv : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (kgFreqInvOp x) = kgFreqInvOp (Λ x))
    (hW : ∀ (r : ℝ) (x : Lp ℂ 2 (volume : Measure E)), Λ (W r x) = W r (Λ x))
    (hidem : ∀ x : Lp ℂ 2 (volume : Measure E), Λ (Λ x) = Λ x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT W g h t
        = kgFieldStateT W (Λ g) (Λ h) t + kgFieldStateT W (g - Λ g) (h - Λ h) t
      ∧ kgDiagOp Λ (kgFieldStateT W (Λ g) (Λ h) t) = kgFieldStateT W (Λ g) (Λ h) t
      ∧ kgDiagOp Λ (kgFieldStateT W (g - Λ g) (h - Λ h) t) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have hsum := kgFieldStateT_add hb0 hWb hWs (Λ g) (Λ h) (g - Λ g) (h - Λ h) t
    have hg : Λ g + (g - Λ g) = g := by abel
    have hh : Λ h + (h - Λ h) = h := by abel
    rw [hg, hh] at hsum
    exact hsum
  · exact kgFieldStateT_fixed hb0 hWb hWs hcos hsin hinv hW (hidem g) (hidem h) t
  · have hzg : Λ (g - Λ g) = 0 := by
      rw [map_sub, hidem, sub_self]
    have hzh : Λ (h - Λ h) = 0 := by
      rw [map_sub, hidem, sub_self]
    have hstate := kgFieldStateT_diag hb0 hWb hWs hcos hsin hinv hW (g - Λ g) (h - Λ h) t
    rw [hzg, hzh, kgFieldStateT_zero_datum hb0 hWb hWs] at hstate
    exact hstate.symm

end Splitting

/-! ## The low-pass projection -/

section LowPass

variable {b : ℝ} {w : ℝ → E → ℂ}

/-- **A clock in a frequency-diagonal background decouples across every frequency band.** The
low-frequency part of the solution is the solution of the low-frequency part of the datum, the
complementary part stays complementary, and nothing crosses between them at any time. -/
theorem kgFieldStateT_band_decouple (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (R : ℝ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t
        = kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (kgLowPassOp R g) (kgLowPassOp R h) t
          + kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
            (g - kgLowPassOp R g) (h - kgLowPassOp R h) t
      ∧ kgDiagOp (kgLowPassOp R)
            (kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (kgLowPassOp R g) (kgLowPassOp R h) t)
          = kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (kgLowPassOp R g) (kgLowPassOp R h) t
      ∧ kgDiagOp (kgLowPassOp R)
            (kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
              (g - kgLowPassOp R g) (h - kgLowPassOp R h) t) = 0 :=
  kgFieldStateT_decouple hb0 (fun _ => norm_fourierMulCLM_le _ _ _) hWs
    (fourierMulCLM_kgCosOp_comm (measurable_kgLowPass (E := E) R) zero_le_one
      (norm_kgLowPass_le R))
    (fourierMulCLM_kgSinOp_comm (measurable_kgLowPass (E := E) R) zero_le_one
      (norm_kgLowPass_le R))
    (fourierMulCLM_kgFreqInvOp_comm (measurable_kgLowPass (E := E) R) zero_le_one
      (norm_kgLowPass_le R))
    (fun r x => fourierMulCLM_comm (measurable_kgLowPass (E := E) R) (hw r) zero_le_one
      (norm_kgLowPass_le R) hb0 (hwb r) x)
    (kgLowPassOp_idem R) g h t

end LowPass

end GaloisForLFunctions.HTGeometry
