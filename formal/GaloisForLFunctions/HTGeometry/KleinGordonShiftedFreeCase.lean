import GaloisForLFunctions.HTGeometry.KleinGordonShiftedIdentification

/-!
# The shifted calculus at zero potential, and exact conservation

At zero potential the shifted frequency is the free frequency, and every operator of the shifted
calculus is its free counterpart. The identification of the mild solution therefore contains the free
propagator as the special case `p = 0`.

The same layer discharges the self-adjointness hypothesis of the exact conservation law: a real
diagonal potential is self-adjoint, so the modified energy `E(t) − ⟨p·u, u⟩` is exactly conserved for
every such potential, with no smallness assumption at all.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Two symbols agreeing almost everywhere give the same Fourier multiplier, whatever bounds are
used to build it. -/
theorem fourierMulCLM_congr {φ ψ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    {C D : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D) (hD : ∀ ξ, ‖ψ ξ‖ ≤ D)
    (hae : φ =ᵐ[(volume : Measure E)] ψ) :
    fourierMulCLM hφ hC0 hC = fourierMulCLM hψ hD0 hD := by
  rw [fourierMulCLM, fourierMulCLM,
    lpBoundedMulCLM_congr (p := 2) (μ := (volume : Measure E)) hφ hψ hC0 hC hD0 hD hae]

section FreeCase

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **At zero potential the shifted frequency is the free frequency.** -/
theorem kgShiftedFreq_zero (ξ : E) : kgShiftedFreq (fun _ : E => (0 : ℝ)) ξ = kgFreq ξ := by
  rw [kgShiftedFreq, add_zero, Real.sqrt_sq (le_trans zero_le_one (one_le_kgFreq ξ))]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem kgShiftedCos_zero_pot (t : ℝ) (ξ : E) :
    kgShiftedCos (fun _ : E => (0 : ℝ)) t ξ = kgCosSymbol t ξ := by
  rw [kgShiftedCos, kgCosSymbol, kgShiftedFreq_zero]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem kgShiftedSinOverFreq_zero_pot (t : ℝ) (ξ : E) :
    kgShiftedSinOverFreq (fun _ : E => (0 : ℝ)) t ξ = kgSinOverFreq t ξ := by
  rw [kgShiftedSinOverFreq, kgSinOverFreq, kgShiftedFreq_zero]

set_option maxHeartbeats 1000000 in
/-- **At zero potential the shifted cosine propagator is the free one.** -/
theorem kgShiftedCosOp_zero_pot (t : ℝ) :
    kgShiftedCosOp (E := E) (measurable_const (a := (0 : ℝ))) t = kgCosOp t := by
  rw [kgShiftedCosOp, kgCosOp]
  exact fourierMulCLM_congr _ _ _ _ _ _
    (Eventually.of_forall (kgShiftedCos_zero_pot (E := E) t))

set_option maxHeartbeats 1000000 in
/-- **At zero potential the shifted sine propagator is the free one.** -/
theorem kgShiftedSinFreqOp_zero_pot (t : ℝ) :
    kgShiftedSinFreqOp (E := E) (measurable_const (a := (0 : ℝ))) t = kgSinFreqOp t := by
  rw [kgShiftedSinFreqOp, kgSinFreqOp]
  exact fourierMulCLM_congr _ _ _ _ _ _
    (Eventually.of_forall (kgShiftedSinOverFreq_zero_pot (E := E) t))

end FreeCase

section DiagonalConservation

variable {p : E → ℝ} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The modified energy of a real diagonal potential is exactly conserved**, with no smallness
assumption: self-adjointness is a property of the symbol. -/
theorem kgFieldEnergy_conserved_diagonal (hp : Measurable p) (hb0 : 0 ≤ b)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad (fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
          (norm_kgRealPotSymbol_le hpb)) g h t‖ ^ (2 : ℕ)
        + ‖kgFieldVel (fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
          (norm_kgRealPotSymbol_le hpb)) g h t‖ ^ (2 : ℕ)
        - RCLike.re (inner ℂ (fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
            (norm_kgRealPotSymbol_le hpb)
              (kgFieldMild (fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
                (norm_kgRealPotSymbol_le hpb)) (kgFreqInvOp g) h t))
            (kgFieldMild (fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
              (norm_kgRealPotSymbol_le hpb)) (kgFreqInvOp g) h t))
      = ‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ)
        - RCLike.re (inner ℂ (fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
            (norm_kgRealPotSymbol_le hpb) (kgFreqInvOp g)) (kgFreqInvOp g)) :=
  kgFieldEnergy_conserved hb0 (norm_fourierMulCLM_le _ _ _)
    (fourierMulCLM_inner _ _ _ (starRingEnd_kgRealPotSymbol p)) g h t

end DiagonalConservation

end GaloisForLFunctions.HTGeometry
