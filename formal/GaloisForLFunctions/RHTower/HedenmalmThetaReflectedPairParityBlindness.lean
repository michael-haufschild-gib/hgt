import GaloisForLFunctions.RHTower.HedenmalmThetaSourceFunctionalEquationRootCurrentTransport

/-!
# Reflected-pair parity blindness for the fixed theta carrier

Functional-equation reflection exchanges the distinct nonzero root blocks at `mu` and `-mu`.
On their direct sum it gives the standard quarter-turn whose square is `-1`; the paired space has
even dimension for every local multiplicity.  This is therefore inter-block doubling, not Kramers
degeneracy inside the `mu`-block.  It cannot force the Xi multiplicity at `mu` to be even.
-/

open Complex Module

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Functional-equation reflection never fixes a nonzero theta spectral point. -/
theorem thetaSpectrumNeg_ne (mu : ThetaNonzeroSpectrum) :
    thetaSpectrumNeg mu ≠ mu := by
  intro h
  have hval : -(mu : ℂ) = (mu : ℂ) := congrArg Subtype.val h
  apply mu.2.2
  have htwo : (2 : ℂ) * (mu : ℂ) = 0 := by
    calc
      (2 : ℂ) * (mu : ℂ) = (mu : ℂ) + (mu : ℂ) := two_mul _
      _ = -(mu : ℂ) + (mu : ℂ) := by rw [hval]
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The two complete root blocks exchanged by functional-equation reflection. -/
abbrev ThetaReflectedRootPair (mu : ThetaNonzeroSpectrum) :=
  ThetaRootBlock mu × ThetaRootBlock (thetaSpectrumNeg mu)

/-- Canonical quarter-turn on the reflected pair.  It exists without any parity condition on the
dimension of either individual root block. -/
def thetaReflectedRootPairQuarterTurn (mu : ThetaNonzeroSpectrum) :
    Module.End ℂ (ThetaReflectedRootPair mu) where
  toFun p :=
    (-(thetaRootBlockReflectionLIE mu).symm p.2,
      thetaRootBlockReflectionLIE mu p.1)
  map_add' p q := by
    apply Prod.ext
    · change -(thetaRootBlockReflectionLIE mu).symm (p.2 + q.2) =
        -(thetaRootBlockReflectionLIE mu).symm p.2 +
          -(thetaRootBlockReflectionLIE mu).symm q.2
      rw [map_add, neg_add]
    · exact map_add (thetaRootBlockReflectionLIE mu) p.1 q.1
  map_smul' c p := by
    apply Prod.ext
    · change -(thetaRootBlockReflectionLIE mu).symm (c • p.2) =
        c • (-(thetaRootBlockReflectionLIE mu).symm p.2)
      rw [map_smul, smul_neg]
    · exact map_smul (thetaRootBlockReflectionLIE mu) c p.1

/-- The reflected-pair quarter-turn has quaternionic square `-1`, independently of local
multiplicity. -/
theorem thetaReflectedRootPairQuarterTurn_sq_apply
    (mu : ThetaNonzeroSpectrum) (p : ThetaReflectedRootPair mu) :
    thetaReflectedRootPairQuarterTurn mu
        (thetaReflectedRootPairQuarterTurn mu p) = -p := by
  apply Prod.ext
  · change -(thetaRootBlockReflectionLIE mu).symm
        (thetaRootBlockReflectionLIE mu p.1) = -p.1
    rw [(thetaRootBlockReflectionLIE mu).symm_apply_apply]
  · change thetaRootBlockReflectionLIE mu
        (-(thetaRootBlockReflectionLIE mu).symm p.2) = -p.2
    rw [map_neg, (thetaRootBlockReflectionLIE mu).apply_symm_apply]

/-- Reflection doubling makes the total dimension even tautologically: it is twice the dimension
of one block. -/
theorem finrank_thetaReflectedRootPair (mu : ThetaNonzeroSpectrum) :
    finrank ℂ (ThetaReflectedRootPair mu) =
      2 * finrank ℂ (ThetaRootBlock mu) := by
  rw [finrank_prod, finrank_thetaRootBlock_reflection]
  omega

/-- At an actual Xi divisor point, reflected-pair dimension is twice the Xi multiplicity, so its
evenness contains no information about parity of that multiplicity. -/
theorem finrank_thetaReflectedRootPair_at_XiSupport (rho : XiDivisorSupport) :
    finrank ℂ (ThetaReflectedRootPair (thetaSpectrumOfXiSupport rho)) =
      2 * xiSupportMultiplicity rho := by
  rw [finrank_thetaReflectedRootPair, finrank_thetaRootBlock_at_XiSupport]

theorem finrank_thetaReflectedRootPair_at_XiSupport_even (rho : XiDivisorSupport) :
    Even (finrank ℂ (ThetaReflectedRootPair (thetaSpectrumOfXiSupport rho))) := by
  rw [finrank_thetaReflectedRootPair_at_XiSupport]
  exact even_two_mul _

end

end RHTower.HedenmalmThetaSource
