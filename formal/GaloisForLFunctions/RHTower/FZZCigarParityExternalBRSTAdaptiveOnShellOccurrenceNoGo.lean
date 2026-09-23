import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles
import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBranchChargeNoGo
import GaloisForLFunctions.RHTower.FZZCigarParityLinearReplicaAreaHolonomySelector

/-!
# FZZ external-BRST adaptive on-shell occurrence no-go

Halder--Jafferis' continuum external vertices have radial label

`j = -1/2 - i sqrt(k-2) P`.

For every `k > 2` and nonzero continuum momentum `P`, both external-leg Gamma normalization
factors are nonzero.  At zero target momentum the left and right cigar weights coincide, so a
single spectator dressing makes both chiral weights exactly one.  The external-BRST even
log-modulus also remains nonzero and hence sees `P`.  Nevertheless the literal linear
replica-area response is nonpassive, by the exact passivity classification already proved in the
FZZ tower.

Thus neither BRST `(1,1)` occurrence, external-leg Gamma normalization, nor radial visibility can
be the missing producer in

`external-BRST occurrence -> replica-area passivity -> Mellin completeness -> RH`.

The positive survivor starts at a fixed-source integrated amplitude or a Ward identity coupling
the external-BRST modulus to the marked replica-area response.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- Halder--Jafferis continuum label, equation (4.3). -/
def fzzHJPhysicalRadialLabel (k P : ℝ) : ℂ :=
  -(1 : ℂ) / 2 - (((Real.sqrt (k - 2) * P : ℝ) : ℂ) * I)

/-- Holomorphic cigar weight of an external vertex. -/
def fzzCigarExternalHolomorphicWeight
    (k : ℝ) (j : ℂ) (p nu : ℤ) : ℂ :=
  -(j * (j + 1)) / ((k - 2 : ℝ) : ℂ) +
    fzzCigarExternalVertexMomentum k p nu ^ (2 : ℕ) / (k : ℂ)

/-- Antiholomorphic cigar weight of an external vertex. -/
def fzzCigarExternalAntiholomorphicWeight
    (k : ℝ) (j : ℂ) (p nu : ℤ) : ℂ :=
  -(j * (j + 1)) / ((k - 2 : ℝ) : ℂ) +
    fzzCigarExternalVertexBarMomentum k p nu ^ (2 : ℕ) / (k : ℂ)

/-- Target-adaptive spectator weight needed to make the holomorphic weight one. -/
def fzzHJExternalSpectatorWeight (k P : ℝ) (nu : ℤ) : ℂ :=
  1 - fzzCigarExternalHolomorphicWeight k
    (fzzHJPhysicalRadialLabel k P) 0 nu

/-- Both chiral weights can be dressed to `(1,1)` by the same spectator weight. -/
def FZZHJExternalBRSTAdaptiveOnShell (k P : ℝ) (nu : ℤ) : Prop :=
  fzzCigarExternalHolomorphicWeight k (fzzHJPhysicalRadialLabel k P) 0 nu +
        fzzHJExternalSpectatorWeight k P nu = 1 ∧
    fzzCigarExternalAntiholomorphicWeight k (fzzHJPhysicalRadialLabel k P) 0 nu +
        fzzHJExternalSpectatorWeight k P nu = 1

theorem fzzHJExternalBRSTAdaptiveOnShell_all
    (k P : ℝ) (nu : ℤ) :
    FZZHJExternalBRSTAdaptiveOnShell k P nu := by
  have hm : fzzCigarExternalVertexMomentum k 0 nu =
      fzzCigarExternalVertexBarMomentum k 0 nu := by
    rw [fzzCigarExternalVertexMomentum,
      fzzCigarExternalVertexBarMomentum]
    push_cast
    ring
  unfold FZZHJExternalBRSTAdaptiveOnShell
  constructor
  · simp [fzzHJExternalSpectatorWeight]
  · rw [fzzHJExternalSpectatorWeight]
    rw [fzzCigarExternalHolomorphicWeight,
      fzzCigarExternalAntiholomorphicWeight, hm]
    ring

def fzzHJExternalGammaPlusNumeratorArgument (k P : ℝ) : ℂ :=
  (k : ℂ) / 2 - fzzHJPhysicalRadialLabel k P

def fzzHJExternalGammaPlusDenominatorArgument (k P : ℝ) : ℂ :=
  1 - (k : ℂ) / 2 + fzzHJPhysicalRadialLabel k P

def fzzHJExternalGammaMinusNumeratorArgument (k P : ℝ) : ℂ :=
  -(k : ℂ) / 2 - fzzHJPhysicalRadialLabel k P

def fzzHJExternalGammaMinusDenominatorArgument (k P : ℝ) : ℂ :=
  1 + (k : ℂ) / 2 + fzzHJPhysicalRadialLabel k P

@[simp] theorem fzzHJExternalGammaPlusNumeratorArgument_im (k P : ℝ) :
    (fzzHJExternalGammaPlusNumeratorArgument k P).im =
      Real.sqrt (k - 2) * P := by
  simp [fzzHJExternalGammaPlusNumeratorArgument, fzzHJPhysicalRadialLabel]

@[simp] theorem fzzHJExternalGammaPlusDenominatorArgument_im (k P : ℝ) :
    (fzzHJExternalGammaPlusDenominatorArgument k P).im =
      -(Real.sqrt (k - 2) * P) := by
  simp [fzzHJExternalGammaPlusDenominatorArgument, fzzHJPhysicalRadialLabel]

@[simp] theorem fzzHJExternalGammaMinusNumeratorArgument_im (k P : ℝ) :
    (fzzHJExternalGammaMinusNumeratorArgument k P).im =
      Real.sqrt (k - 2) * P := by
  simp [fzzHJExternalGammaMinusNumeratorArgument, fzzHJPhysicalRadialLabel]

@[simp] theorem fzzHJExternalGammaMinusDenominatorArgument_im (k P : ℝ) :
    (fzzHJExternalGammaMinusDenominatorArgument k P).im =
      -(Real.sqrt (k - 2) * P) := by
  simp [fzzHJExternalGammaMinusDenominatorArgument, fzzHJPhysicalRadialLabel]

private theorem ne_neg_natCast_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n h
  apply hz
  have him := congrArg Complex.im h
  simpa using him

/-- Halder--Jafferis `W+` external-leg Gamma normalization. -/
def fzzHJExternalGammaPlusNormalization (k P : ℝ) : ℂ :=
  Complex.Gamma (fzzHJExternalGammaPlusNumeratorArgument k P) /
    Complex.Gamma (fzzHJExternalGammaPlusDenominatorArgument k P)

/-- Halder--Jafferis `W-` external-leg Gamma normalization. -/
def fzzHJExternalGammaMinusNormalization (k P : ℝ) : ℂ :=
  Complex.Gamma (fzzHJExternalGammaMinusNumeratorArgument k P) /
    Complex.Gamma (fzzHJExternalGammaMinusDenominatorArgument k P)

/-- Both external-leg normalizations are nonzero at every nonzero continuum momentum. -/
theorem fzzHJExternalGammaNormalizations_ne_zero
    {k P : ℝ} (hk : 2 < k) (hP : P ≠ 0) :
    fzzHJExternalGammaPlusNormalization k P ≠ 0 ∧
      fzzHJExternalGammaMinusNormalization k P ≠ 0 := by
  have hsqrt : Real.sqrt (k - 2) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have him : Real.sqrt (k - 2) * P ≠ 0 := mul_ne_zero hsqrt hP
  have hpn := Complex.Gamma_ne_zero
    (ne_neg_natCast_of_im_ne_zero
      (by simpa using him :
        (fzzHJExternalGammaPlusNumeratorArgument k P).im ≠ 0))
  have hpd := Complex.Gamma_ne_zero
    (ne_neg_natCast_of_im_ne_zero
      (by simpa using neg_ne_zero.mpr him :
        (fzzHJExternalGammaPlusDenominatorArgument k P).im ≠ 0))
  have hmn := Complex.Gamma_ne_zero
    (ne_neg_natCast_of_im_ne_zero
      (by simpa using him :
        (fzzHJExternalGammaMinusNumeratorArgument k P).im ≠ 0))
  have hmd := Complex.Gamma_ne_zero
    (ne_neg_natCast_of_im_ne_zero
      (by simpa using neg_ne_zero.mpr him :
        (fzzHJExternalGammaMinusDenominatorArgument k P).im ≠ 0))
  exact ⟨div_ne_zero hpn hpd, div_ne_zero hmn hmd⟩

/-- The external-BRST even modulus sees every nonzero HJ continuum momentum. -/
theorem fzzHJExternalBRSTEvenLogModulusMean_im_ne_zero
    {k P : ℝ} (hk : 2 < k) (hP : P ≠ 0) :
    (fzzCigarExternalBRSTEvenLogModulusMean k
      (fzzHJPhysicalRadialLabel k P) 0 1).im ≠ 0 := by
  intro hzero
  have hrec := fzzCigarExternalBRSTEvenLogModulusMean_reconstructs_radialLabel
    hk (fzzHJPhysicalRadialLabel k P) 0 1
  have him := congrArg Complex.im hrec
  rw [mul_im] at him
  have hzero' :
      (fzzCigarExternalBRSTEvenLogModulusMean k
        (-1 / 2 - (Real.sqrt (k - 2) : ℂ) * (P : ℂ) * Complex.I) 0 1).im = 0 := by
    simpa [fzzHJPhysicalRadialLabel] using hzero
  simp [fzzCigarReplicaRadialDenominator,
    fzzHJPhysicalRadialLabel] at him
  rw [hzero', mul_zero] at him
  have hsqrt : Real.sqrt (k - 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hprod : Real.sqrt (k - 2) * P = 0 := by linarith
  exact hP ((mul_eq_zero.mp hprod).resolve_left hsqrt)

/-- Literal linear replica-area passivity fails at every nonzero radial coordinate. -/
theorem not_fzzLinearReplicaAreaNormalizedResponse_passive_of_ne_zero
    {P : ℝ} (hP : P ≠ 0) :
    ¬ fzzLinearReplicaAreaNormalizedResponse 1 P ≤ 1 := by
  intro hpassive
  exact hP ((fzzLinearReplicaAreaNormalizedResponse_le_one_iff
    (n := 1) (by norm_num) P).mp hpassive)

/-- Closed route class: normalized adaptive on-shell occurrence does not force passivity. -/
def FZZHJExternalBRSTAdaptiveOnShellOccurrenceRouteKilled : Prop :=
  ∀ (k : ℝ), 2 < k → ∀ P : ℝ, P ≠ 0 →
    (∀ nu : ℤ, nu = 1 ∨ nu = -1 →
      FZZHJExternalBRSTAdaptiveOnShell k P nu) ∧
    fzzHJExternalGammaPlusNormalization k P ≠ 0 ∧
    fzzHJExternalGammaMinusNormalization k P ≠ 0 ∧
    (fzzCigarExternalBRSTEvenLogModulusMean k
      (fzzHJPhysicalRadialLabel k P) 0 1).im ≠ 0 ∧
    ¬ fzzLinearReplicaAreaNormalizedResponse 1 P ≤ 1

/-- Premise-free certificate killing adaptive on-shell/normalization occurrence as FZZ passivity
producer. -/
theorem fzzHJExternalBRSTAdaptiveOnShellOccurrenceRouteKilled :
    FZZHJExternalBRSTAdaptiveOnShellOccurrenceRouteKilled := by
  intro k hk P hP
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro nu _
    exact fzzHJExternalBRSTAdaptiveOnShell_all k P nu
  · exact (fzzHJExternalGammaNormalizations_ne_zero hk hP).1
  · exact (fzzHJExternalGammaNormalizations_ne_zero hk hP).2
  · exact fzzHJExternalBRSTEvenLogModulusMean_im_ne_zero hk hP
  · exact not_fzzLinearReplicaAreaNormalizedResponse_passive_of_ne_zero hP

end

end RHTower
