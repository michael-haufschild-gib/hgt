import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPrimeSamplingCohomologyObstruction

/-!
# Endpoint-zero global Meyer--Poisson complex

The all-radius Poisson relation does not see radius zero.  Meyer's source has
two additional forced endpoint conditions, so this file intersects the even
Bessel middle term with vanishing of both collar zero modes and then uses the
global Calderón defect as second differential.

The resulting cycles satisfy the full Poisson graph and are determined
injectively by their physical collar.  This is the algebraic shape of Meyer's
single-collar quotient, but no nuclear-topological or arithmetic-sheaf
identification is asserted.
-/

namespace RHTower

open scoped FourierTransform SchwartzMap

noncomputable section

variable (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p)

/-- Joint physical/Fourier zero-mode trace on the even Bessel middle term. -/
def deningerMeyerEvenEndpointTraceLM :
    DeningerMeyerEvenSecondaryBesselDomain packet →ₗ[ℂ] ℂ × ℂ :=
  (LinearMap.prod
    ((LinearMap.proj 0).comp
      (LinearMap.fst ℂ (ℝ → ℂ) (ℝ → ℂ)))
    ((LinearMap.proj 0).comp
      (LinearMap.snd ℂ (ℝ → ℂ) (ℝ → ℂ)))).comp
    (DeningerMeyerEvenSecondaryBesselDomain packet).subtype

@[simp]
theorem deningerMeyerEvenEndpointTraceLM_apply
    (h : DeningerMeyerEvenSecondaryBesselDomain packet) :
    deningerMeyerEvenEndpointTraceLM packet h =
      ((h : DeningerMeyerRadialCochainPair).1 0,
        (h : DeningerMeyerRadialCochainPair).2 0) :=
  rfl

/-- Every literal Meyer boundary has both zero modes equal to zero. -/
theorem deningerMeyerEvenPoissonBoundary_endpointTrace_zero
    (f : DeningerMeyerCap) :
    deningerMeyerEvenEndpointTraceLM packet
        (deningerMeyerEvenPoissonBoundaryLM packet f) =
      0 := by
  apply Prod.ext
  · change deningerMeyerSum f 0 = 0
    exact deningerMeyerSum_zero f
  · change deningerMeyerSum
      (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) 0 = 0
    exact deningerMeyerFourierSum_zero f

/--
Parity- and endpoint-corrected middle domain.  Its members have actual
secondary Bessel values and the two zero modes forced by Meyer's source.
-/
def DeningerMeyerEndpointEvenBesselDomain :
    Submodule ℂ
      (DeningerMeyerEvenSecondaryBesselDomain packet) :=
  LinearMap.ker (deningerMeyerEvenEndpointTraceLM packet)

/-- Literal Meyer boundary with parity, Bessel, and endpoint certificates. -/
def deningerMeyerEndpointEvenPoissonBoundaryLM :
    DeningerMeyerCap →ₗ[ℂ]
      DeningerMeyerEndpointEvenBesselDomain packet :=
  (deningerMeyerEvenPoissonBoundaryLM packet).codRestrict
    (DeningerMeyerEndpointEvenBesselDomain packet)
    (deningerMeyerEvenPoissonBoundary_endpointTrace_zero packet)

/-- Global Calderón defect restricted to the endpoint-corrected domain. -/
def deningerMeyerEndpointGlobalPoissonDefectLM :
    DeningerMeyerEndpointEvenBesselDomain packet →ₗ[ℂ]
      (DeningerMeyerPositiveRadius → ℂ) :=
  (deningerMeyerEvenGlobalPoissonDefectLM packet).comp
    (DeningerMeyerEndpointEvenBesselDomain packet).subtype

/--
Endpoint-zero, parity-corrected, all-radius Meyer--Poisson complex.
-/
def deningerMeyerEndpointGlobalPoissonThreeTermComplex :
    DeningerArithmeticThreeTermComplex ℂ
      DeningerMeyerCap
      (DeningerMeyerEndpointEvenBesselDomain packet)
      (DeningerMeyerPositiveRadius → ℂ) where
  d0 := deningerMeyerEndpointEvenPoissonBoundaryLM packet
  d1 := deningerMeyerEndpointGlobalPoissonDefectLM packet
  d1_comp_d0 := by
    apply LinearMap.ext
    intro f
    exact deningerMeyerGlobalPoissonDefect_boundary_zero f

/-- Its cycles are exactly the full positive-radius Poisson graphs. -/
theorem deningerMeyerEndpointGlobalPoisson_cycles1_iff
    (h : DeningerMeyerEndpointEvenBesselDomain packet) :
    h ∈
        (deningerMeyerEndpointGlobalPoissonThreeTermComplex packet).cycles1 ↔
      ∀ x : DeningerMeyerPositiveRadius,
        (h : DeningerMeyerRadialCochainPair).1 (x : ℝ) =
          ((((x : ℝ)⁻¹ : ℝ) : ℂ) *
            (h : DeningerMeyerRadialCochainPair).2
              ((x : ℝ)⁻¹)) := by
  change deningerMeyerEndpointGlobalPoissonDefectLM packet h = 0 ↔ _
  constructor
  · intro hzero x
    have heval := congrArg
      (fun u : DeningerMeyerPositiveRadius → ℂ => u x)
      hzero
    simp only [Pi.zero_apply] at heval
    change deningerMeyerGlobalPoissonDefectLM
      (h : DeningerMeyerRadialCochainPair) x = 0 at heval
    rw [deningerMeyerGlobalPoissonDefectLM_apply] at heval
    exact sub_eq_zero.mp heval
  · intro hgraph
    funext x
    change
      (h : DeningerMeyerRadialCochainPair).1 (x : ℝ) -
          ((((x : ℝ)⁻¹ : ℝ) : ℂ) *
            (h : DeningerMeyerRadialCochainPair).2
              ((x : ℝ)⁻¹)) =
        0
    exact sub_eq_zero.mpr (hgraph x)

/-- Physical-collar projection on endpoint-zero global cycles. -/
def deningerMeyerEndpointGlobalCyclesFirstLM :
    (deningerMeyerEndpointGlobalPoissonThreeTermComplex packet).cycles1 →ₗ[ℂ]
      (ℝ → ℂ) :=
  ((LinearMap.fst ℂ (ℝ → ℂ) (ℝ → ℂ)).comp
    (DeningerMeyerEvenSecondaryBesselDomain packet).subtype).comp
      ((DeningerMeyerEndpointEvenBesselDomain packet).subtype.comp
        (deningerMeyerEndpointGlobalPoissonThreeTermComplex
          packet).cycles1.subtype)

/--
One collar determines an endpoint-zero global cycle.  The second collar is
forced at nonzero radii by Poisson reflection, at negative radii by parity,
and at zero by the endpoint condition.
-/
theorem deningerMeyerEndpointGlobalCyclesFirstLM_injective :
    Function.Injective
      (deningerMeyerEndpointGlobalCyclesFirstLM packet) := by
  intro h k hfirst
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hfirst
  · have hgraph :=
      (deningerMeyerEndpointGlobalPoisson_cycles1_iff
        packet h).mp h.property
    have kgraph :=
      (deningerMeyerEndpointGlobalPoisson_cycles1_iff
        packet k).mp k.property
    have hsecond_pos :
        ∀ {x : ℝ}, 0 < x →
          (h : DeningerMeyerRadialCochainPair).2 x =
            (k : DeningerMeyerRadialCochainPair).2 x := by
      intro x hx
      have hr := hgraph ⟨x⁻¹, inv_pos.mpr hx⟩
      have kr := kgraph ⟨x⁻¹, inv_pos.mpr hx⟩
      have hfirstx := congrFun hfirst x⁻¹
      change
        (h : DeningerMeyerRadialCochainPair).1 x⁻¹ =
          (k : DeningerMeyerRadialCochainPair).1 x⁻¹ at hfirstx
      rw [hfirstx] at hr
      change
        (k : DeningerMeyerRadialCochainPair).1 x⁻¹ =
          (((x⁻¹)⁻¹ : ℝ) : ℂ) *
            (h : DeningerMeyerRadialCochainPair).2
              ((x⁻¹)⁻¹) at hr
      change
        (k : DeningerMeyerRadialCochainPair).1 x⁻¹ =
          (((x⁻¹)⁻¹ : ℝ) : ℂ) *
            (k : DeningerMeyerRadialCochainPair).2
              ((x⁻¹)⁻¹) at kr
      rw [inv_inv] at hr kr
      have hmul :
          (x : ℂ) *
              (h : DeningerMeyerRadialCochainPair).2 x =
            (x : ℂ) *
              (k : DeningerMeyerRadialCochainPair).2 x :=
        hr.symm.trans kr
      exact mul_left_cancel₀
        (by exact_mod_cast ne_of_gt hx) hmul
    funext x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have heven :=
        ((h : DeningerMeyerEndpointEvenBesselDomain packet) :
          DeningerMeyerEvenSecondaryBesselDomain packet).property.2.2 x
      have keven :=
        ((k : DeningerMeyerEndpointEvenBesselDomain packet) :
          DeningerMeyerEvenSecondaryBesselDomain packet).property.2.2 x
      change
        (h : DeningerMeyerRadialCochainPair).2 (-x) =
          (h : DeningerMeyerRadialCochainPair).2 x at heven
      change
        (k : DeningerMeyerRadialCochainPair).2 (-x) =
          (k : DeningerMeyerRadialCochainPair).2 x at keven
      rw [← heven, ← keven]
      exact hsecond_pos (neg_pos.mpr hx)
    · subst x
      have ht := congrArg (fun q : ℂ × ℂ => q.2) h.1.property
      have kt := congrArg (fun q : ℂ × ℂ => q.2) k.1.property
      change
        (h : DeningerMeyerRadialCochainPair).2 0 = 0 at ht
      change
        (k : DeningerMeyerRadialCochainPair).2 0 = 0 at kt
      exact ht.trans kt.symm
    · exact hsecond_pos hx

end

end RHTower
