import GaloisForLFunctions.HTGeometry.SineVerticalDecay
import GaloisForLFunctions.HTGeometry.RealTaylorCoefficients

/-!
# FZZ integer-genus replica-tangent interpolation no-go

Mori--Sakai--Shigemori's unresolved replica contribution requires analytic continuation of the
sine--Liouville amplitude from integer worldsheet genus to a nonintegral genus approaching zero.
This file proves that the complete integer-genus amplitude sequence, even with entireness and
Schwarz reality, cannot determine the required genus-zero tangent.

For an entire baseline `F` and target tangent `v`, the deformation

`F_v(g) = F(g) + (v - F'(0)) sin(π g) / π`

has exactly the same value at every nonnegative integer genus and derivative `v` at zero.  If `F`
is Schwarz-real, every real target gives another Schwarz-real continuation.  Therefore the
integer-genus restriction map has a tangent-surjective fibre, not merely two distinct elements.

This kills the sample-only branch

`integer-genus FZZ amplitudes + entireness/Schwarz reality`
`  -> canonical genus-zero replica tangent -> divisor-mode passivity -> RH`.

The sharp positive survivor is a source-derived condition excluding the type-`π` sine null
direction: a strict sampling-growth law, off-lattice moduli data, or a genus recursion/localization
law.  None is a consequence of bare analytic continuation.

**[ROUTE KILL] [PAPER-PROVED] [LEAN-PROVED]**

**[NOVELTY AUDIT]** Integer-lattice null functions and Carlson-type uniqueness are classical.
The new content is the exact tangent-surjectivity obstruction for the FZZ worldsheet-genus replica
producer, its persistence under Schwarz reality, and the resulting RH-route classification.
-/

open Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Two genus continuations carry exactly the same amplitudes at every physical integer genus. -/
def SameIntegerGenusAmplitudeSamples (F G : ℂ → ℂ) : Prop :=
  ∀ n : ℕ, G (n : ℂ) = F (n : ℂ)

/-- The sine-null deformation that keeps all integer-genus amplitudes and prescribes the tangent
at genus zero. -/
def fzzIntegerGenusReplicaTangentDeformation (F : ℂ → ℂ) (v z : ℂ) : ℂ :=
  (F + fun w => ((v - deriv F 0) / (Real.pi : ℂ)) *
    Complex.sin ((Real.pi : ℂ) * w)) z

theorem differentiable_fzzIntegerGenusReplicaTangentDeformation
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (v : ℂ) :
    Differentiable ℂ (fzzIntegerGenusReplicaTangentDeformation F v) := by
  unfold fzzIntegerGenusReplicaTangentDeformation
  exact hF.add ((differentiable_const _).mul
    (Complex.differentiable_sin.comp (by fun_prop)))

/-- The deformation is invisible at every nonnegative integer genus, including genus zero. -/
theorem fzzIntegerGenusReplicaTangentDeformation_sameIntegerSamples
    {F : ℂ → ℂ} (v : ℂ) :
    SameIntegerGenusAmplitudeSamples F
      (fzzIntegerGenusReplicaTangentDeformation F v) := by
  intro n
  change F (n : ℂ) + ((v - deriv F 0) / (Real.pi : ℂ)) *
      Complex.sin ((Real.pi : ℂ) * (n : ℂ)) = F (n : ℂ)
  rw [show (Real.pi : ℂ) * (n : ℂ) = (n : ℂ) * (Real.pi : ℂ) by ring,
    Complex.sin_nat_mul_pi, mul_zero, add_zero]

/-- The sine-null coefficient gives the prescribed derivative at genus zero. -/
theorem hasDerivAt_fzzIntegerGenusReplicaTangentDeformation
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (v : ℂ) :
    HasDerivAt (fzzIntegerGenusReplicaTangentDeformation F v) v 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hbase : HasDerivAt F (deriv F 0) 0 := hF.differentiableAt.hasDerivAt
  have hsine := GaloisForLFunctions.HTGeometry.hasDerivAt_sin_pi_mul_zero.const_mul
    ((v - deriv F 0) / (Real.pi : ℂ))
  have hsum := hbase.add hsine
  have hvalue : deriv F 0 + (v - deriv F 0) / (Real.pi : ℂ) *
      (Real.pi : ℂ) = v := by
    rw [div_mul_cancel₀ _ hpi]
    ring
  rw [hvalue] at hsum
  exact hsum

/-- **Tangent-surjective interpolation fibre.** Every entire genus continuation has another
entire continuation with the same complete integer-genus sequence and any prescribed complex
genus-zero tangent. -/
theorem exists_entire_sameIntegerGenusSamples_deriv_eq
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (v : ℂ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      SameIntegerGenusAmplitudeSamples F G ∧ deriv G 0 = v := by
  refine ⟨fzzIntegerGenusReplicaTangentDeformation F v,
    differentiable_fzzIntegerGenusReplicaTangentDeformation hF v,
    fzzIntegerGenusReplicaTangentDeformation_sameIntegerSamples v, ?_⟩
  exact (hasDerivAt_fzzIntegerGenusReplicaTangentDeformation hF v).deriv

/-- A real target preserves Schwarz reality. -/
theorem fzzIntegerGenusReplicaTangentDeformation_schwarzReal
    {F : ℂ → ℂ}
    (hs : ∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z)) (v : ℝ) :
    ∀ z, fzzIntegerGenusReplicaTangentDeformation F (v : ℂ) ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (fzzIntegerGenusReplicaTangentDeformation F (v : ℂ) z) := by
  have hderiv : deriv F 0 =
      ((GaloisForLFunctions.HTGeometry.realTaylorCoeff F 1 : ℝ) : ℂ) := by
    symm
    simpa using GaloisForLFunctions.HTGeometry.ofReal_realTaylorCoeff_deriv hs 1
  intro z
  have hcoef :
      (starRingEnd ℂ) (((v : ℂ) - deriv F 0) / (Real.pi : ℂ)) =
        ((v : ℂ) - deriv F 0) / (Real.pi : ℂ) := by
    rw [hderiv]
    simp
  have hsin :
      Complex.sin ((Real.pi : ℂ) * ((starRingEnd ℂ) z)) =
        (starRingEnd ℂ) (Complex.sin ((Real.pi : ℂ) * z)) := by
    rw [← Complex.sin_conj]
    congr 1
    simp
  change F ((starRingEnd ℂ) z) +
      (((v : ℂ) - deriv F 0) / (Real.pi : ℂ)) *
        Complex.sin ((Real.pi : ℂ) * ((starRingEnd ℂ) z)) =
    (starRingEnd ℂ) (F z +
      (((v : ℂ) - deriv F 0) / (Real.pi : ℂ)) *
        Complex.sin ((Real.pi : ℂ) * z))
  rw [hs, hsin, map_add, map_mul, hcoef]

/-- Schwarz reality still leaves the genus-zero tangent completely arbitrary on the real axis. -/
theorem exists_schwarzReal_entire_sameIntegerGenusSamples_deriv_eq
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hs : ∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z)) (v : ℝ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      SameIntegerGenusAmplitudeSamples F G ∧
      (∀ z, G ((starRingEnd ℂ) z) = (starRingEnd ℂ) (G z)) ∧
      deriv G 0 = (v : ℂ) := by
  refine ⟨fzzIntegerGenusReplicaTangentDeformation F (v : ℂ),
    differentiable_fzzIntegerGenusReplicaTangentDeformation hF _,
    fzzIntegerGenusReplicaTangentDeformation_sameIntegerSamples _,
    fzzIntegerGenusReplicaTangentDeformation_schwarzReal hs v, ?_⟩
  exact (hasDerivAt_fzzIntegerGenusReplicaTangentDeformation hF (v : ℂ)).deriv

/-- The sample-only uniqueness premise that the FZZ replica route would need. -/
def FZZIntegerGenusReplicaTangentIdentifiable : Prop :=
  ∀ F G : ℂ → ℂ, Differentiable ℂ F → Differentiable ℂ G →
    SameIntegerGenusAmplitudeSamples F G → deriv F 0 = deriv G 0

theorem not_FZZIntegerGenusReplicaTangentIdentifiable :
    ¬ FZZIntegerGenusReplicaTangentIdentifiable := by
  intro h
  let F : ℂ → ℂ := fun _ => 0
  have hF : Differentiable ℂ F := differentiable_const 0
  obtain ⟨G, hG, hsamples, hderiv⟩ :=
    exists_entire_sameIntegerGenusSamples_deriv_eq hF (1 : ℂ)
  have heq := h F G hF hG hsamples
  rw [hderiv] at heq
  simp [F] at heq

/-- Closed certificate: every entire integer-genus interpolation fibre is tangent-surjective,
this persists on all real tangents under Schwarz reality, and the sample-only tangent
identifiability premise is false. -/
def FZZIntegerGenusReplicaTangentInterpolationNoGo : Prop :=
  (∀ (F : ℂ → ℂ), Differentiable ℂ F → ∀ v : ℂ,
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      SameIntegerGenusAmplitudeSamples F G ∧ deriv G 0 = v) ∧
  (∀ (F : ℂ → ℂ), Differentiable ℂ F →
    (∀ z, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z)) → ∀ v : ℝ,
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      SameIntegerGenusAmplitudeSamples F G ∧
      (∀ z, G ((starRingEnd ℂ) z) = (starRingEnd ℂ) (G z)) ∧
      deriv G 0 = (v : ℂ)) ∧
  ¬ FZZIntegerGenusReplicaTangentIdentifiable

/-- **Closed FZZ integer-genus replica-tangent route kill.** -/
theorem fzzCigarParity_integerGenusReplicaTangentInterpolation_noGo :
    FZZIntegerGenusReplicaTangentInterpolationNoGo := by
  exact ⟨fun _ hF v => exists_entire_sameIntegerGenusSamples_deriv_eq hF v,
    fun _ hF hs v => exists_schwarzReal_entire_sameIntegerGenusSamples_deriv_eq hF hs v,
    not_FZZIntegerGenusReplicaTangentIdentifiable⟩

end RHTower
