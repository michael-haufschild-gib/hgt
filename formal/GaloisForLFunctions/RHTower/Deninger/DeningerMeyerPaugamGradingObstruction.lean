import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerEndpointGlobalPoissonComplex
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReciprocalPaugamPolarization

/-!
# Grading obstruction for local reciprocal Paugam defects

The reciprocal Calderón quotient has a valid positive odd Paugam
polarization, but the quotient records failure of the Poisson graph.  Every
genuine endpoint-global degree-one cycle lies on that graph at every positive
radius.  Therefore its local quotient class, reciprocal double, and positive
cup--Hodge defect energy are all zero.

Consequently the local reciprocal polarization belongs to transverse
regulator/degree-two data.  It cannot itself be the nondegenerate Hodge form on
middle cohomology.  A Route L middle pairing must instead be constructed on
the one-collar global-cycle quotient by Meyer boundaries.
-/

namespace RHTower

noncomputable section

/-- Two-collar trace at an arbitrary positive or nonpositive real radius. -/
def deningerMeyerLocalRadialTraceLM (x : ℝ) :
    DeningerMeyerRadialCochainPair →ₗ[ℂ] ℂ × ℂ :=
  LinearMap.prod
    ((LinearMap.proj x).comp
      (LinearMap.fst ℂ (ℝ → ℂ) (ℝ → ℂ)))
    ((LinearMap.proj x⁻¹).comp
      (LinearMap.snd ℂ (ℝ → ℂ) (ℝ → ℂ)))

@[simp]
theorem deningerMeyerLocalRadialTraceLM_apply
    (x : ℝ) (h : DeningerMeyerRadialCochainPair) :
    deningerMeyerLocalRadialTraceLM x h =
      (h.1 x, h.2 x⁻¹) :=
  rfl

/-- Local Calderón quotient class of an arbitrary radial cochain pair. -/
def deningerMeyerLocalPoissonQuotientLM (x : ℝ) :
    DeningerMeyerRadialCochainPair →ₗ[ℂ]
      DeningerMeyerPoissonCollarQuotient x :=
  (deningerMeyerPoissonCalderonGraph x).mkQ.comp
    (deningerMeyerLocalRadialTraceLM x)

@[simp]
theorem deningerMeyerLocalPoissonQuotientLM_apply
    (x : ℝ) (h : DeningerMeyerRadialCochainPair) :
    deningerMeyerLocalPoissonQuotientLM x h =
      Submodule.Quotient.mk (h.1 x, h.2 x⁻¹) :=
  rfl

/-- Reciprocal pair of local quotient defects at `x` and `x⁻¹`. -/
def deningerMeyerReciprocalPoissonQuotientLM (x : ℝ) :
    DeningerMeyerRadialCochainPair →ₗ[ℂ]
      DeningerMeyerPoissonCollarQuotient x ×
        DeningerMeyerPoissonCollarQuotient x⁻¹ :=
  LinearMap.prod
    (deningerMeyerLocalPoissonQuotientLM x)
    (deningerMeyerLocalPoissonQuotientLM x⁻¹)

variable (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p)

/-- Forget cycle, endpoint, parity, and Bessel certificates down to the collar pair. -/
def deningerMeyerEndpointGlobalCyclesToPairLM :
    (deningerMeyerEndpointGlobalPoissonThreeTermComplex packet).cycles1 →ₗ[ℂ]
      DeningerMeyerRadialCochainPair :=
  (DeningerMeyerEvenSecondaryBesselDomain packet).subtype.comp
    ((DeningerMeyerEndpointEvenBesselDomain packet).subtype.comp
      (deningerMeyerEndpointGlobalPoissonThreeTermComplex
        packet).cycles1.subtype)

/-- Reciprocal local defect quotient evaluated on endpoint-global cycles. -/
def deningerMeyerEndpointCycleReciprocalQuotientLM (x : ℝ) :
    (deningerMeyerEndpointGlobalPoissonThreeTermComplex packet).cycles1 →ₗ[ℂ]
      DeningerMeyerPoissonCollarQuotient x ×
        DeningerMeyerPoissonCollarQuotient x⁻¹ :=
  (deningerMeyerReciprocalPoissonQuotientLM x).comp
    (deningerMeyerEndpointGlobalCyclesToPairLM packet)

/--
**Grading obstruction.**  Every reciprocal local Calderón quotient class of
every genuine global degree-one cycle is zero.
-/
theorem deningerMeyerEndpointCycleReciprocalQuotient_eq_zero
    (x : ℝ) (hx : 0 < x)
    (h :
      (deningerMeyerEndpointGlobalPoissonThreeTermComplex packet).cycles1) :
    deningerMeyerEndpointCycleReciprocalQuotientLM packet x h =
      0 := by
  have hgraph :=
    (deningerMeyerEndpointGlobalPoisson_cycles1_iff
      packet h).mp h.property
  apply Prod.ext
  · change Submodule.Quotient.mk
      ((h : DeningerMeyerRadialCochainPair).1 x,
        (h : DeningerMeyerRadialCochainPair).2 x⁻¹) = 0
    rw [Submodule.Quotient.mk_eq_zero,
      deningerMeyerPoissonCalderonGraph_mem_iff]
    convert hgraph ⟨x, hx⟩ using 1
    norm_cast
  · change Submodule.Quotient.mk
      ((h : DeningerMeyerRadialCochainPair).1 x⁻¹,
        (h : DeningerMeyerRadialCochainPair).2 (x⁻¹)⁻¹) = 0
    rw [Submodule.Quotient.mk_eq_zero,
      deningerMeyerPoissonCalderonGraph_mem_iff]
    convert hgraph ⟨x⁻¹, inv_pos.mpr hx⟩ using 1
    norm_cast

/--
The positive reciprocal defect cup--Hodge diagonal pulls back identically to
zero on endpoint-global middle cycles.
-/
theorem deningerMeyerEndpointCycleReciprocal_cupSigma_self_zero
    (x : ℝ) (hx : 0 < x)
    (h :
      (deningerMeyerEndpointGlobalPoissonThreeTermComplex packet).cycles1) :
    PaugamSpectralExchange.splitPairing
        (deningerMeyerPoissonReciprocalCrossPairing x)
        (deningerMeyerEndpointCycleReciprocalQuotientLM packet x h)
        ((deningerMeyerPoissonReciprocalPaugamExchange x).signConjugationSigma
          (deningerMeyerEndpointCycleReciprocalQuotientLM packet x h)) =
      0 := by
  rw [deningerMeyerEndpointCycleReciprocalQuotient_eq_zero
    packet x hx h]
  simp

end

end RHTower
