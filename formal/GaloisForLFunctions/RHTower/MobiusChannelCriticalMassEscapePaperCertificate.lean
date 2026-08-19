import GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscape
import GaloisForLFunctions.RHTower.ShiftedEulerMobiusSynthesis

/-!
# Paper certificate: the normalized Möbius channel is contractive and loses every finite coordinate

Formal certificate for
`docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius/`
`mobius-channel-critical-mass-escape-law.md`.

The paper writes `σ = 1 + 2ω`.  With that substitution the certified statements are

```text
(4)  ‖C_ω f‖² = ζ(2+4ω)⁻¹ ‖f‖² ,
(5)  ‖C_ω‖   = ζ(2+4ω)^(-1/2) < 1 ,
(8)  ‖1_F C_ω f‖ → 0                (ω ↓ 0, F finite),
(9)  ‖C_ω f‖² → ζ(2)⁻¹ ‖f‖² ,
(11) ‖(1-1_F) C_ω f‖² → ζ(2)⁻¹ ‖f‖² ,
     C_ω f ⇀ 0 weakly, but not strongly for `f ≠ 0`,
(12) K C_ω f → 0 strongly for every fixed compact `K`,
(14)/(15) the signed Möbius superposition of the translated packet atoms is the shifted-Euler
     atomic source with coefficient `c_ω(n) = ∑_{dm=n} μ(d) d^(-ω) m^ω`.
```

The channel-probability identity `(3)` of the companion boundary-layer card is certified here as
well: for every nonzero input the squared divisor-coordinate norms of `C_ω f`, normalized by the
total squared norm, are exactly the squarefree probabilities `P_ω{d}`.

Every statement is unconditional; no RH-bearing gate of the card is asserted.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace RHTower

section Card

variable {sigma : ℝ}

/-- **Card `(4)`.**  Exact squared-norm law of the paper-normalized Möbius analysis channel. -/
theorem mobiusChannelPaper_norm_sq
    (hsigma : 1 < sigma) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mobiusCriticalShiftChannel sigma f‖ ^ 2 = (zetaTwoShiftTotal sigma)⁻¹ * ‖f‖ ^ 2 := by
  rw [mobiusCriticalShiftChannel_eq hsigma, norm_mobiusCriticalShiftChannelValue_sq]

/-- **Card `(4)`, zeta form.**  The normalization constant is the value `ζ(2σ)`. -/
theorem mobiusChannelPaper_ofReal_norm_sq
    (hsigma : 1 < sigma) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ((‖mobiusCriticalShiftChannel sigma f‖ ^ 2 : ℝ) : ℂ) =
      (riemannZeta (2 * (sigma : ℂ)))⁻¹ * ((‖f‖ ^ 2 : ℝ) : ℂ) := by
  rw [mobiusChannelPaper_norm_sq hsigma]
  push_cast
  rw [ofReal_zetaTwoShiftTotal_eq_riemannZeta hsigma]

/-- **Card `(5)`.**  The channel is a strict contraction: its exact gain is `ζ(2σ)^(-1/2) < 1`. -/
theorem mobiusChannelPaper_gain
    (hsigma : 1 < sigma) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mobiusCriticalShiftChannel sigma f‖ = mobiusCriticalContractionScale sigma * ‖f‖ := by
  rw [mobiusCriticalShiftChannel_eq hsigma, mobiusCriticalShiftChannelValue, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mobiusCriticalContractionScale_nonneg sigma),
    norm_infiniteMobiusShiftAnalysisValue]

/-- **Card `(5)`.**  The gain is strictly below one. -/
theorem mobiusChannelPaper_strict_contraction
    (hsigma : 1 < sigma) {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) :
    ‖mobiusCriticalShiftChannel sigma f‖ < ‖f‖ := by
  rw [mobiusChannelPaper_gain hsigma]
  exact (mul_lt_iff_lt_one_left (norm_pos_iff.mpr hf)).mpr
    (mobiusCriticalContractionScale_lt_one hsigma)

/-- **Companion card `(3)`.**  The squared divisor-coordinate norms of the channel, normalized by
the total squared norm, are exactly the squarefree channel probabilities.  In particular the law
does not depend on the input vector. -/
theorem mobiusChannelPaper_coordinate_probability
    (hsigma : 1 < sigma) {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) (n : ℕ) :
    ‖mobiusCriticalShiftChannel sigma f n‖ ^ 2 / ‖mobiusCriticalShiftChannel sigma f‖ ^ 2 =
      squarefreeMobiusProbability sigma n := by
  have hz0 : zetaTwoShiftTotal sigma ≠ 0 := ne_of_gt (zetaTwoShiftTotal_pos hsigma)
  have hfpos : (0 : ℝ) < ‖f‖ ^ 2 := by positivity
  rw [norm_mobiusCriticalShiftChannel_apply_sq hsigma, mobiusChannelPaper_norm_sq hsigma]
  field_simp

/-- **Card `(8)`.**  Every fixed finite divisor window loses all its norm at criticality. -/
theorem mobiusChannelPaper_finite_window_escape
    (F : Finset ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto
      (fun sigma : ℝ =>
        ‖mobiusCriticalShiftChannelFiniteRestriction F (mobiusCriticalShiftChannel sigma f)‖)
      (𝓝[>] (1 : ℝ)) (𝓝 0) :=
  tendsto_norm_mobiusCriticalShiftChannelFiniteRestriction F f

/-- **Card `(9)`.**  The total squared norm has the positive critical limit `ζ(2)⁻¹ ‖f‖²`. -/
theorem mobiusChannelPaper_total_energy (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun sigma : ℝ => ‖mobiusCriticalShiftChannel sigma f‖ ^ 2)
      (𝓝[>] (1 : ℝ)) (𝓝 (((riemannZeta (2 : ℂ)).re)⁻¹ * ‖f‖ ^ 2)) :=
  tendsto_norm_mobiusCriticalShiftChannel_sq f

/-- **Card `(11)`.**  The complement of every fixed finite window carries the whole limit energy. -/
theorem mobiusChannelPaper_tail_energy
    (F : Finset ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto
      (fun sigma : ℝ => ‖mobiusCriticalShiftChannel sigma f‖ ^ 2 -
        ‖mobiusCriticalShiftChannelFiniteRestriction F (mobiusCriticalShiftChannel sigma f)‖ ^ 2)
      (𝓝[>] (1 : ℝ)) (𝓝 (((riemannZeta (2 : ℂ)).re)⁻¹ * ‖f‖ ^ 2)) :=
  tendsto_mobiusCriticalShiftChannel_tail_energy F f

/-- **Card §3.**  The critical channel is weakly null. -/
theorem mobiusChannelPaper_weakly_null
    (f : Lp ℂ 2 (volume : Measure ℝ)) (ell : InfiniteMobiusShiftChannel →L[ℂ] ℂ) :
    Tendsto (fun sigma : ℝ => ell (mobiusCriticalShiftChannel sigma f))
      (𝓝[>] (1 : ℝ)) (𝓝 0) :=
  mobiusCriticalShiftChannel_weakly_tendsto_zero f ell

/-- **Card §3.**  It is not strongly null on any nonzero input. -/
theorem mobiusChannelPaper_not_strongly_null
    {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) :
    ¬ Tendsto (fun sigma : ℝ => mobiusCriticalShiftChannel sigma f) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
  mobiusCriticalShiftChannel_not_strongly_tendsto_zero hf

/-- **Card `(12)`.**  A fixed compact synthesis annihilates the critical channel mass. -/
theorem mobiusChannelPaper_compact_synthesis_kills
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : InfiniteMobiusShiftChannel →L[ℂ] H) (hK : IsCompactOperator K)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun sigma : ℝ => ‖K (mobiusCriticalShiftChannel sigma f)‖)
      (𝓝[>] (1 : ℝ)) (𝓝 0) :=
  IsCompactOperator.tendsto_norm_apply_mobiusCriticalShiftChannel_zero K hK f

/-- **Card `(15)`.**  The shifted-Euler coefficient is the Möbius divisor switch. -/
theorem mobiusChannelPaper_shiftedEuler_coefficient (ω : ℝ) (n : ℕ) :
    shiftedEulerCoefficient ω n =
      ∑ p ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius p.1 : ℝ) * (p.1 : ℝ) ^ (-ω) * (p.2 : ℝ) ^ ω :=
  rfl

/-- **Card `(14)`.**  Exact locally finite factorization of the coupled source: the signed Möbius
superposition of the translated packet atoms is the shifted-Euler atomic source. -/
theorem mobiusChannelPaper_suzuki_factorization
    (ω δ : ℝ) (hω : 0 < ω) (hδ : 0 < δ) {f : ℝ → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    (∑' d : ℕ+, ∑' m : ℕ+,
        (ArithmeticFunction.moebius (d : ℕ) : ℝ) * ((d : ℕ) : ℝ) ^ (-1 - 2 * ω)
          * (((d : ℕ) : ℝ) ^ (-δ) * ((m : ℕ) : ℝ) ^ (-1 - δ))
          * f (Real.log ((d : ℕ) * (m : ℕ))))
      = ∑' n : ℕ+, shiftedEulerCoefficient ω (n : ℕ) * ((n : ℕ) : ℝ) ^ (-1 - ω - δ)
          * f (Real.log (n : ℕ)) :=
  mobiusSynthesis_atoms ω δ hω hδ hf

end Card

end RHTower
