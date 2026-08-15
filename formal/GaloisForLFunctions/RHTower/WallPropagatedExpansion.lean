import GaloisForLFunctions.RHTower.WallBlockResolventRegularity

/-!
# The propagated four-term expansion at a single position

Variation of constants places the transport in front of the whole moving-endpoint integral, and the
two-fold integration by parts produces four terms inside it.  Propagating them, the transport
*cancels* against the two boundary terms at the moving endpoint — the phase map is the inverse
transport times a unimodular phase — and survives only in front of the two boundary terms at the
threshold and the remaining integral.  So the propagated expansion reads

`e^{-ixL}C(x,L)^{-1}·i + e^{-ixL}C^{-1}(C^{-1})'(x,L) − H(x)·(threshold operator) − H(x)·(remainder)`,

with the first two terms carrying no transport at all.  That is why the first of them does not decay
and needs the Laplace representation, while the second already carries one power of the resolvent
derivative.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- The boundary operator produced at the threshold by the two-fold expansion. -/
def thresholdOperator (E : ℂ → ℂ) (T : X →L[ℂ] X) (σ L Y : ℝ) : X →L[ℂ] X :=
  (Complex.I : ℂ) • (wallPhaseMap E T σ L Y * invFamily (wallGeneratorShift T σ L) Y)
    + wallPhaseMap E T σ L Y
      * invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) Y

omit [Nontrivial X] in
/-- **The propagated expansion at a single position.**  The transport cancels at the moving endpoint
and survives only in front of the threshold terms. -/
theorem stripPropagator_expansion_apply
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (L x Y : ℝ) (R : X →L[ℂ] X) (v : X) :
    stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        ((((Complex.I : ℂ) • (wallPhaseMap E T σ L x * invFamily (wallGeneratorShift T σ L) x
            - wallPhaseMap E T σ L Y * invFamily (wallGeneratorShift T σ L) Y)
          + (wallPhaseMap E T σ L x
              * invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x
            - wallPhaseMap E T σ L Y
              * invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) Y)
          - R) v))
      = (Complex.I : ℂ) • (Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
            • (invFamily (wallGeneratorShift T σ L) x v))
        + Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
            • (invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x v)
        - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
            (thresholdOperator E T σ L Y v)
        - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (R v) := by
  set H : X →L[ℂ] X := stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) with hH
  set A : X →L[ℂ] X := invFamily (wallGeneratorShift T σ L) x with hA
  set P : X →L[ℂ] X :=
    invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x with hP
  set A' : X →L[ℂ] X := invFamily (wallGeneratorShift T σ L) Y with hA'
  set P' : X →L[ℂ] X :=
    invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) Y with hP'
  set Wx : X →L[ℂ] X := wallPhaseMap E T σ L x with hWx
  set WY : X →L[ℂ] X := wallPhaseMap E T σ L Y with hWY
  set e : ℂ := Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) with he
  have hcancelA : H * (Wx * A) = e • A := by
    rw [hH, hWx, he]
    exact stripPropagator_mul_wallPhaseMap_mul hE hσ0 hσ1 L x A
  have hcancelP : H * (Wx * P) = e • P := by
    rw [hH, hWx, he]
    exact stripPropagator_mul_wallPhaseMap_mul hE hσ0 hσ1 L x P
  have hthr : thresholdOperator E T σ L Y = (Complex.I : ℂ) • (WY * A') + WY * P' := rfl
  have happ : ∀ M N : X →L[ℂ] X, (M * N) v = M (N v) := fun M N => rfl
  have hexpand : ((((Complex.I : ℂ) • (Wx * A - WY * A')) + (Wx * P - WY * P') - R) v)
      = (Complex.I : ℂ) • ((Wx * A) v) - (Complex.I : ℂ) • ((WY * A') v)
        + ((Wx * P) v - (WY * P') v) - R v := by
    simp only [add_apply, sub_apply, smul_apply, smul_sub]
  rw [hexpand]
  rw [map_sub, map_add, map_sub, map_sub, map_smul, map_smul]
  have h1 : H ((Wx * A) v) = e • (A v) := by
    rw [← happ H (Wx * A), hcancelA]
    rfl
  have h2 : H ((Wx * P) v) = e • (P v) := by
    rw [← happ H (Wx * P), hcancelP]
    rfl
  have h3 : H (thresholdOperator E T σ L Y v)
      = (Complex.I : ℂ) • H ((WY * A') v) + H ((WY * P') v) := by
    rw [hthr]
    simp only [add_apply, smul_apply, map_add, map_smul]
  rw [h1, h2, h3]
  abel

end GaloisForLFunctions.RHTower
