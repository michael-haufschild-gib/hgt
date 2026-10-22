import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPoissonCalderonGraph

/-!
# Square-zero first-suspension cross-effect obstruction

The existing Calderón regulator is linear after fixing a rational-Witt packet.  Varying both the
Calderón quotient class and the packet exposes a bilinear cross-effect.  Its canonical
linearization lives on the tensor product of those two source factors.

This module proves that no linear map on their direct sum can realize the nonzero cross-effect.
In particular, the square-zero radial/phase direct sum may remain the underlying three-term
complex, but it cannot by itself encode Route L's source-varying Cauchy restriction.  The positive
survivor is the tensor-linearized secondary operation, which is nonzero on every nonzero finite
rational-Witt packet stage.
-/

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-- Local Meyer--Poisson Calderón quotient at an arithmetic prime. -/
abbrev DeningerMeyerPrimeCalderonQuotient (p : Nat.Primes) :=
  (ℂ × ℂ) ⧸ deningerMeyerPoissonCalderonGraph (p : ℝ)

/--
The source-varying first-suspension cross-effect.  Its first input is a Calderón quotient class;
its second input is a rational-Witt packet coefficient.
-/
def deningerMeyerCalderonPacketCrossEffect (p : Nat.Primes) :
    DeningerMeyerPrimeCalderonQuotient p →ₗ[ℂ]
      DeningerPrimePacketComplexHaarL2 p →ₗ[ℂ]
        DeningerPrimeSuspensionHaarL2 p where
  toFun q :=
    { toFun := fun packet =>
        deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ) q •
          (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
            deningerPrimeSuspensionFirstMode p packet)
      map_add' := by
        intro a b
        rw [map_add]
        module
      map_smul' := by
        intro c a
        simp [smul_smul]
        module }
  map_add' := by
    intro q r
    ext packet
    simp [add_smul]
  map_smul' := by
    intro c q
    ext packet
    simp [smul_smul]

/-- Canonical tensor linearization of the varying-packet Calderón cross-effect. -/
def deningerMeyerCalderonPacketTensorRegulator (p : Nat.Primes) :
    TensorProduct ℂ
      (DeningerMeyerPrimeCalderonQuotient p)
      (DeningerPrimePacketComplexHaarL2 p) →ₗ[ℂ]
        DeningerPrimeSuspensionHaarL2 p :=
  TensorProduct.lift (deningerMeyerCalderonPacketCrossEffect p)

@[simp]
theorem deningerMeyerCalderonPacketTensorRegulator_tmul
    (p : Nat.Primes)
    (q : DeningerMeyerPrimeCalderonQuotient p)
    (packet : DeningerPrimePacketComplexHaarL2 p) :
    deningerMeyerCalderonPacketTensorRegulator p
        (q ⊗ₜ[ℂ] packet) =
      deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ) q •
        (((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
          deningerPrimeSuspensionFirstMode p packet) :=
  rfl

/--
The tensor operation is exactly the previously constructed fixed-packet quotient regulator on
every pure tensor.
-/
@[simp]
theorem deningerMeyerCalderonPacketTensorRegulator_tmul_eq_fixedPacket
    (p : Nat.Primes)
    (q : DeningerMeyerPrimeCalderonQuotient p)
    (packet : DeningerPrimePacketComplexHaarL2 p) :
    deningerMeyerCalderonPacketTensorRegulator p
        (q ⊗ₜ[ℂ] packet) =
      deningerMeyerPoissonCalderonPacketRegulator p packet q := by
  induction q using Submodule.Quotient.induction_on with
  | _ u =>
    rw [deningerMeyerCalderonPacketTensorRegulator_tmul,
      deningerMeyerPoissonCalderonPacketRegulator_mk,
      deningerMeyerReflectedFirstModeRegulator_apply,
      deningerMeyerPoissonCalderonQuotientEquiv_mk]

/--
Any direct-sum linear map agreeing with the bilinear cross-effect must make that cross-effect
identically zero.
-/
theorem deningerMeyerCalderonDirectSumLinearization_forces_zero
    (p : Nat.Primes)
    (L :
      (DeningerMeyerPrimeCalderonQuotient p ×
        DeningerPrimePacketComplexHaarL2 p) →ₗ[ℂ]
          DeningerPrimeSuspensionHaarL2 p)
    (hL : ∀ q packet,
      L (q, packet) =
        deningerMeyerCalderonPacketTensorRegulator p
          (q ⊗ₜ[ℂ] packet))
    (q : DeningerMeyerPrimeCalderonQuotient p)
    (packet : DeningerPrimePacketComplexHaarL2 p) :
    deningerMeyerCalderonPacketTensorRegulator p
        (q ⊗ₜ[ℂ] packet) =
      0 := by
  rw [← hL]
  calc
    L (q, packet) = L ((q, 0) + (0, packet)) := by simp
    _ = L (q, 0) + L (0, packet) := map_add L _ _
    _ =
        deningerMeyerCalderonPacketTensorRegulator p
            (q ⊗ₜ[ℂ]
              (0 : DeningerPrimePacketComplexHaarL2 p)) +
          deningerMeyerCalderonPacketTensorRegulator p
            ((0 : DeningerMeyerPrimeCalderonQuotient p) ⊗ₜ[ℂ]
              packet) := by
      rw [hL, hL]
    _ = 0 := by simp

/--
The tensor survivor detects every nonzero packet on the canonical unit defect class.
-/
theorem deningerMeyerCalderonPacketTensorRegulator_unit_ne_zero
    (p : Nat.Primes)
    {packet : DeningerPrimePacketComplexHaarL2 p}
    (hpacket : packet ≠ 0) :
    deningerMeyerCalderonPacketTensorRegulator p
      (Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ)) ⊗ₜ[ℂ]
        packet) ≠ 0 := by
  rw [deningerMeyerCalderonPacketTensorRegulator_tmul]
  simp only [deningerMeyerPoissonCalderonQuotientEquiv_mk,
    deningerMeyerReflectedCollarDefect_apply, mul_zero, sub_zero,
    one_smul]
  apply smul_ne_zero
  · exact
      Complex.ofReal_ne_zero.mpr
        (deningerPrimePolarizedHalfDensity_pos p).ne'
  · intro hmode
    apply hpacket
    apply deningerPrimeSuspensionFirstMode_injective p
    rw [map_zero]
    exact hmode

/--
No ordinary linear map on the square-zero direct sum can realize the source-varying
first-suspension cross-effect when one nonzero packet is present.
-/
theorem deningerMeyerCalderon_no_directSumLinearization
    (p : Nat.Primes)
    {packet : DeningerPrimePacketComplexHaarL2 p}
    (hpacket : packet ≠ 0) :
    ¬ ∃ L :
      (DeningerMeyerPrimeCalderonQuotient p ×
        DeningerPrimePacketComplexHaarL2 p) →ₗ[ℂ]
          DeningerPrimeSuspensionHaarL2 p,
      ∀ q a,
        L (q, a) =
          deningerMeyerCalderonPacketTensorRegulator p
            (q ⊗ₜ[ℂ] a) := by
  rintro ⟨L, hL⟩
  exact
    deningerMeyerCalderonPacketTensorRegulator_unit_ne_zero p
      hpacket
      (deningerMeyerCalderonDirectSumLinearization_forces_zero
        p L hL
        (Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ)))
        packet)

/-- Every nonzero finite rational-Witt packet produces a nonzero tensor cross-effect. -/
theorem deningerFiniteRationalWittCalderonTensorRegulator_ne_zero
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    {F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ}
    (hF : F ≠ 0) :
    deningerMeyerCalderonPacketTensorRegulator p
      (Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ)) ⊗ₜ[ℂ]
        deningerPrimeFiniteStageComplexHaarL2 p s F) ≠ 0 := by
  rw [deningerMeyerCalderonPacketTensorRegulator_tmul]
  simp only [deningerMeyerPoissonCalderonQuotientEquiv_mk,
    deningerMeyerReflectedCollarDefect_apply, mul_zero, sub_zero,
    one_smul]
  exact
    smul_ne_zero
      (Complex.ofReal_ne_zero.mpr
        (deningerPrimePolarizedHalfDensity_pos p).ne')
      (deningerPrimeFiniteStageFirstSuspensionMode_ne_zero p s hF)

/--
Concrete Route L no-go: every nonzero finite rational-Witt stage rules out a direct-sum linear
realization of the varying-packet first-suspension regulator.
-/
theorem deningerFiniteRationalWitt_no_squareZeroLinearFirstSuspension
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    {F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ}
    (hF : F ≠ 0) :
    ¬ ∃ L :
      (DeningerMeyerPrimeCalderonQuotient p ×
        DeningerPrimePacketComplexHaarL2 p) →ₗ[ℂ]
          DeningerPrimeSuspensionHaarL2 p,
      ∀ q packet,
        L (q, packet) =
          deningerMeyerCalderonPacketTensorRegulator p
            (q ⊗ₜ[ℂ] packet) := by
  rintro ⟨L, hL⟩
  exact
    deningerFiniteRationalWittCalderonTensorRegulator_ne_zero
      p s hF
      (deningerMeyerCalderonDirectSumLinearization_forces_zero
        p L hL
        (Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ)))
        (deningerPrimeFiniteStageComplexHaarL2 p s F))

/--
Actual rational-Witt capstone: the arithmetic-Frobenius-fixed witness, its nonzero tensor
cross-effect, and the direct-sum no-go hold simultaneously.
-/
theorem deningerPrimeComplexifiedRationalWitt_exists_crossEffect_no_directSum
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ)
    (hF : F ≠ 0) :
    ∃ w : DeningerFiniteCyclotomicWittAlgebra s.modulus,
      deningerPrimeComplexifiedRationalWittFrobenius p
          (deningerPrimeFiniteCyclotomicWittInclusion p s w) =
        deningerPrimeFiniteCyclotomicWittInclusion p s w ∧
      (∀ u : (ZMod s.modulus)ˣ,
        deningerFiniteCyclotomicWittEvaluation s.modulus u w =
          F (QuotientGroup.mk u)) ∧
      deningerMeyerCalderonPacketTensorRegulator p
        (Submodule.Quotient.mk ((1 : ℂ), (0 : ℂ)) ⊗ₜ[ℂ]
          deningerPrimeFiniteStageComplexHaarL2 p s F) ≠ 0 ∧
      ¬ ∃ L :
        (DeningerMeyerPrimeCalderonQuotient p ×
          DeningerPrimePacketComplexHaarL2 p) →ₗ[ℂ]
            DeningerPrimeSuspensionHaarL2 p,
        ∀ q packet,
          L (q, packet) =
            deningerMeyerCalderonPacketTensorRegulator p
              (q ⊗ₜ[ℂ] packet) := by
  obtain ⟨w, hw, heval, -, -⟩ :=
    deningerPrimeComplexifiedRationalWitt_exists_nonzero_firstSuspensionMode
      p s F hF
  exact
    ⟨w, hw, heval,
      deningerFiniteRationalWittCalderonTensorRegulator_ne_zero
        p s hF,
      deningerFiniteRationalWitt_no_squareZeroLinearFirstSuspension
        p s hF⟩

end

end RHTower
