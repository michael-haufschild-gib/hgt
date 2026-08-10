import GaloisForLFunctions.HTGeometry.KleinGordonBandSplitting

/-!
# Real symbols give self-adjoint potentials

The small-potential theory — the two-sided monodromy bound, the trapped energy, the eigen-clock, the
flat envelope — is stated for a self-adjoint potential, with self-adjointness carried as a hypothesis.
For a Fourier multiplier that hypothesis is a property of the symbol alone: multiplication by a
real-valued bounded symbol is self-adjoint on `L²`, because the `L²` inner product is an integral of
`conj f · g` and a real factor may be moved across it; and the Fourier transform is unitary, so the
multiplier it conjugates inherits the property.

The hypothesis is therefore discharged for every real bounded symbol, and the trapping law becomes a
statement with no hypotheses beyond the size of the symbol: a clock in a real frequency-diagonal
potential of sup-norm `b < 1` has its energy confined to the band `[(1−b)/(1+b), (1+b)/(1−b)]` times
its initial value, at every instant of time.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section SelfAdjoint

variable {φ : E → ℂ} {C : ℝ}

/-- **Multiplication by a real-valued bounded symbol is self-adjoint on `L²`.** -/
theorem lpBoundedMulCLM_inner (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C)
    (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ) (f g : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC f) g : ℂ)
      = inner ℂ f (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hφ hC0 hC g) :=
  MeasureTheory.lpBoundedMulCLM_inner_real hφ hC0 hC hreal f g

set_option maxHeartbeats 1000000 in
/-- **A Fourier multiplier with a real symbol is self-adjoint on `L²`.** -/
theorem fourierMulCLM_inner (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C)
    (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ) (f g : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (fourierMulCLM hφ hC0 hC f) g : ℂ)
      = inner ℂ f (fourierMulCLM hφ hC0 hC g) := by
  have hU1 : ∀ u v : Lp ℂ 2 (volume : Measure E),
      (inner ℂ (fourierL2inv E u) v : ℂ) = inner ℂ u (fourierL2 E v) := by
    intro u v
    have h := (Lp.fourierTransformₗᵢ E ℂ).inner_map_map
      ((Lp.fourierTransformₗᵢ E ℂ).symm u) v
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  have hU2 : ∀ u v : Lp ℂ 2 (volume : Measure E),
      (inner ℂ u (fourierL2inv E v) : ℂ) = inner ℂ (fourierL2 E u) v := by
    intro u v
    have h := (Lp.fourierTransformₗᵢ E ℂ).inner_map_map u
      ((Lp.fourierTransformₗᵢ E ℂ).symm v)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  rw [fourierMulCLM_apply, fourierMulCLM_apply, hU1, hU2]
  exact lpBoundedMulCLM_inner hφ hC0 hC hreal (fourierL2 E f) (fourierL2 E g)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The low-pass symbol is real. -/
theorem starRingEnd_kgLowPass (R : ℝ) (ξ : E) :
    (starRingEnd ℂ) (kgLowPass R ξ) = kgLowPass R ξ := by
  simp only [kgLowPass]
  split <;> simp

/-- **The low-pass projection is self-adjoint**, hence an orthogonal projection. -/
theorem kgLowPassOp_inner (R : ℝ) (f g : Lp ℂ 2 (volume : Measure E)) :
    (inner ℂ (kgLowPassOp R f) g : ℂ) = inner ℂ f (kgLowPassOp R g) :=
  fourierMulCLM_inner (measurable_kgLowPass (E := E) R) zero_le_one (norm_kgLowPass_le R)
    (starRingEnd_kgLowPass R) f g

end SelfAdjoint

section DiagonalTrap

variable {φ : E → ℂ} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **A clock in a weak real frequency-diagonal potential has its energy trapped in a band, at every
instant of time.** No hypothesis beyond the size of the symbol is needed: self-adjointness is a
consequence of the symbol being real. -/
theorem kgFieldEnergy_trapped_diagonal (hφ : Measurable φ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    (‖g‖ ^ 2 + ‖h‖ ^ 2) / ((1 + b) / (1 - b))
        ≤ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC) g h t‖ ^ 2
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC) g h t‖ ^ 2
      ∧ ‖kgFieldGrad (fourierMulCLM hφ hb0 hC) g h t‖ ^ 2
          + ‖kgFieldVel (fourierMulCLM hφ hb0 hC) g h t‖ ^ 2
        ≤ (1 + b) / (1 - b) * (‖g‖ ^ 2 + ‖h‖ ^ 2) :=
  kgFieldEnergy_trapped_all_time hb0 hb1 (norm_fourierMulCLM_le hφ hb0 hC)
    (fourierMulCLM_inner hφ hb0 hC hreal) g h t

set_option maxHeartbeats 1000000 in
/-- **The state of such a clock is bounded above and below at every instant**, by the same constant. -/
theorem norm_kgFieldState_trapped_diagonal (hφ : Measurable φ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hC : ∀ ξ : E, ‖φ ξ‖ ≤ b) (hreal : ∀ ξ : E, (starRingEnd ℂ) (φ ξ) = φ ξ)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgPair E (g, h)‖ / Real.sqrt ((1 + b) / (1 - b))
        ≤ ‖kgFieldState (fourierMulCLM hφ hb0 hC) g h t‖
      ∧ ‖kgFieldState (fourierMulCLM hφ hb0 hC) g h t‖
        ≤ Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖ := by
  have hW := norm_fourierMulCLM_le hφ hb0 hC
  have hsa := fourierMulCLM_inner hφ hb0 hC hreal
  have hWb : ∀ r : ℝ, ‖(fun _ : ℝ => fourierMulCLM hφ hb0 hC) r‖ ≤ b := fun _ => hW
  have hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => fourierMulCLM hφ hb0 hC) r x := fun _ =>
    continuous_const
  refine ⟨?_, norm_kgFieldState_le_uniform hb0 hb1 hW hsa g h t⟩
  have hge := norm_kgFieldStateT_ge_all_time hb0 hb1 hW hsa hWb hWs g h t
  rwa [kgFieldStateT_const] at hge

end DiagonalTrap

end GaloisForLFunctions.HTGeometry
