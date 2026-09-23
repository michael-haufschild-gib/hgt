import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedExteriorSource
import GaloisForLFunctions.RHTower.MobiusGammaCoPoissonPrimePowerBoundary
import GaloisForLFunctions.RHTower.DeningerCalderonWittMilnorIncidence

/-!
# Primitive-promoted Gamma/co-Poisson Green transport

This module constructs the source-pointed finite-stage transport forced by
the Euler primitive promotion.  The normalized Gamma/co-Poisson interval
cell is exactly the promoted modular current on its confluent diagonal.
Before orientation trace, that coefficient acts on the rational-Witt packet
leg of Calderón--Witt degree one.  Exterior multiplication then gives a
vector-valued chain map compatible with cup, Koszul--Green section, Milnor
incidence, and Green retraction.

The resulting incidence endomorphism identifies the remaining Route J
frontier precisely: preservation of the admitted cofinal/Hodge sector.
-/

open Complex

namespace RHTower

noncomputable section

def xiGammaEulerPrimitiveGammaCoPoissonCell
    (pe : Nat.Primes × ℕ) (z w : ℂ) : ℂ :=
  -((pe.2 + 1 : ℕ) : ℂ)⁻¹ *
    gammaCoPoissonIntervalCell
      (-(((pe.2 + 1 : ℕ) : ℂ) *
        (Real.log (pe.1 : ℝ) : ℂ))) z w

theorem xiGammaEulerPrimitiveModularCurrent_explicit
    (a : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveModularCurrent a pe =
      Real.log (pe.1 : ℝ) *
        Real.exp (-(1 / 2 + a) *
          Real.log (xiGammaEulerValuationNat pe : ℝ)) := by
  rw [xiGammaEulerPrimitiveModularCurrent_eq_primitiveFibre]
  unfold primitiveFibreModularCurrent primitiveFibreCriticalCurrent
    primitiveFibreModularTilt
  have hlog :
      Real.log (xiGammaEulerValuationNat pe : ℝ) =
        (pe.2 + 1 : ℕ) * Real.log (pe.1 : ℝ) := by
    rw [xiGammaEulerValuationNat]
    norm_num [Real.log_pow]
  have hpR : (0 : ℝ) < (pe.1 : ℝ) := by
    exact_mod_cast pe.1.property.pos
  rw [hlog, criticalPrimeTowerRadius,
    Real.rpow_def_of_pos hpR, Real.log_exp, ← Real.exp_nat_mul]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  push_cast
  ring_nf

theorem xiGammaEulerPrimitiveGammaCoPoissonCell_self
    (a : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveGammaCoPoissonCell pe
        (((1 : ℝ) + a : ℝ) : ℂ) (((1 : ℝ) + a : ℝ) : ℂ) =
      (xiGammaEulerPrimitiveModularCurrent a pe : ℂ) := by
  rw [xiGammaEulerPrimitiveGammaCoPoissonCell,
    gammaCoPoissonIntervalCell_self,
    xiGammaEulerPrimitiveModularCurrent_explicit]
  have he : ((pe.2 + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero pe.2
  have hlog :
      Real.log (xiGammaEulerValuationNat pe : ℝ) =
        (pe.2 + 1 : ℕ) * Real.log (pe.1 : ℝ) := by
    rw [xiGammaEulerValuationNat]
    norm_num [Real.log_pow]
  rw [hlog]
  have harg :
    ((((1 + a : ℝ) : ℂ) - 1 / 2) *
      -(((pe.2 + 1 : ℕ) : ℂ) * (Real.log (pe.1 : ℝ) : ℂ))) =
      ((-(1 / 2 + a) *
        ((pe.2 + 1 : ℕ) * Real.log (pe.1 : ℝ)) : ℝ) : ℂ) := by
    push_cast
    ring_nf
  rw [harg, ← Complex.ofReal_exp]
  field_simp [he]
  norm_cast
  ring_nf

/-- The local promoted cell is exactly the ordinary-integer
Gamma/co-Poisson Euler jet, with its canonical interval orientation
reversed. -/
theorem xiGammaEulerPrimitiveGammaCoPoissonCell_self_eq_neg_eulerJet
    (a : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveGammaCoPoissonCell pe
        (((1 : ℝ) + a : ℝ) : ℂ) (((1 : ℝ) + a : ℝ) : ℂ) =
      -eulerGammaCoPoissonJetTerm 0
        (xiGammaEulerValuationNat pe) (((1 / 2 : ℝ) + a : ℝ) : ℂ) := by
  rw [xiGammaEulerPrimitiveGammaCoPoissonCell,
    eulerGammaCoPoissonJetTerm]
  simp only [iteratedDeriv_zero]
  have hcoeff :=
    dividedVonMangoldtCoefficient_prime_pow
      pe.1.property (Nat.succ_ne_zero pe.2)
  change
    -((pe.2 + 1 : ℕ) : ℂ)⁻¹ *
        gammaCoPoissonIntervalCell
          (-(((pe.2 + 1 : ℕ) : ℂ) *
            (Real.log (pe.1 : ℝ) : ℂ)))
          (((1 : ℝ) + a : ℝ) : ℂ) (((1 : ℝ) + a : ℝ) : ℂ) =
      -((ArithmeticFunction.vonMangoldt
          (xiGammaEulerValuationNat pe) : ℂ) /
            (Real.log (xiGammaEulerValuationNat pe : ℝ) : ℂ) *
        gammaCoPoissonIntervalCell
          (-(Real.log (xiGammaEulerValuationNat pe : ℝ) : ℂ))
          ((((1 / 2 : ℝ) + a : ℝ) : ℂ) + 1 / 2)
          ((((1 / 2 : ℝ) + a : ℝ) : ℂ) + 1 / 2))
  have hlog :
      (Real.log (xiGammaEulerValuationNat pe : ℝ) : ℂ) =
        ((pe.2 + 1 : ℕ) : ℂ) * (Real.log (pe.1 : ℝ) : ℂ) := by
    rw [xiGammaEulerValuationNat]
    norm_num [Real.log_pow]
  have hcoeff' :
      (ArithmeticFunction.vonMangoldt
          (xiGammaEulerValuationNat pe) : ℂ) /
            (Real.log (xiGammaEulerValuationNat pe : ℝ) : ℂ) =
        ((pe.2 + 1 : ℕ) : ℂ)⁻¹ := by
    simpa only [xiGammaEulerValuationNat,
      dividedVonMangoldtCoefficient] using hcoeff
  rw [hcoeff', hlog]
  push_cast
  ring_nf

/-- The complete modular exterior is the two-leg confluence of the
Gamma/co-Poisson relation before scalar fusion. -/
def xiGammaEulerPrimitiveGammaCoPoissonModularExterior
    (a : ℝ) (i j : Nat.Primes × ℕ) : ℂ :=
  xiGammaEulerPrimitiveGammaCoPoissonCell i
      (((1 : ℝ) + a : ℝ) : ℂ) (((1 : ℝ) + a : ℝ) : ℂ) *
    xiGammaEulerPrimitiveGammaCoPoissonCell j
      (((1 : ℝ) + a : ℝ) : ℂ) (((1 : ℝ) + a : ℝ) : ℂ) *
      (xiGammaEulerBoundaryHalfHeight i.1 i.2 -
        xiGammaEulerBoundaryHalfHeight j.1 j.2 : ℝ)

theorem xiGammaEulerPrimitiveGammaCoPoissonModularExterior_eq
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveGammaCoPoissonModularExterior a i j =
      (xiGammaEulerPrimitiveModularExterior a i j : ℂ) := by
  rw [xiGammaEulerPrimitiveGammaCoPoissonModularExterior,
    xiGammaEulerPrimitiveGammaCoPoissonCell_self,
    xiGammaEulerPrimitiveGammaCoPoissonCell_self]
  unfold xiGammaEulerPrimitiveModularExterior
  push_cast
  rfl

theorem spectralBoundary_mul_xiGammaEulerPrimitiveGammaCoPoissonCell
    (pe : Nat.Primes × ℕ) (z w : ℂ) :
    (z - w) * xiGammaEulerPrimitiveGammaCoPoissonCell pe z w =
      ((pe.2 + 1 : ℕ) : ℂ)⁻¹ *
        (Complex.exp ((w - 1 / 2) *
            (-(((pe.2 + 1 : ℕ) : ℂ) *
              (Real.log (pe.1 : ℝ) : ℂ)))) -
          Complex.exp ((z - 1 / 2) *
            (-(((pe.2 + 1 : ℕ) : ℂ) *
              (Real.log (pe.1 : ℝ) : ℂ))))) := by
  unfold xiGammaEulerPrimitiveGammaCoPoissonCell
  calc
    (z - w) *
        (-((pe.2 + 1 : ℕ) : ℂ)⁻¹ *
          gammaCoPoissonIntervalCell
            (-(((pe.2 + 1 : ℕ) : ℂ) *
              (Real.log (pe.1 : ℝ) : ℂ))) z w) =
      -((pe.2 + 1 : ℕ) : ℂ)⁻¹ *
        ((z - w) *
          gammaCoPoissonIntervalCell
            (-(((pe.2 + 1 : ℕ) : ℂ) *
              (Real.log (pe.1 : ℝ) : ℂ))) z w) := by ring
    _ = _ := by
      rw [spectralBoundary_mul_gammaCoPoissonIntervalCell]
      ring

theorem xiGammaEulerPrimitiveGammaCoPoissonCell_depth_add
    (p : Nat.Primes) (r s : ℕ) (z w : ℂ) :
    (((r + 1 : ℕ) : ℂ) + ((s + 1 : ℕ) : ℂ)) *
        xiGammaEulerPrimitiveGammaCoPoissonCell
          (p, r + s + 1) z w =
      ((s + 1 : ℕ) : ℂ) *
          Complex.exp ((z - 1 / 2) *
            (-(((r + 1 : ℕ) : ℂ) * (Real.log (p : ℝ) : ℂ)))) *
          xiGammaEulerPrimitiveGammaCoPoissonCell (p, s) z w +
        ((r + 1 : ℕ) : ℂ) *
          xiGammaEulerPrimitiveGammaCoPoissonCell (p, r) z w *
          Complex.exp ((w - 1 / 2) *
            (-(((s + 1 : ℕ) : ℂ) * (Real.log (p : ℝ) : ℂ)))) := by
  have hr : ((r + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero r
  have hs : ((s + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero s
  have hrs : (((r + 1 : ℕ) : ℂ) + ((s + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : r + 1 + (s + 1) ≠ 0)
  have hrs2 : (2 + (r : ℂ) + (s : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : 2 + r + s ≠ 0)
  have halg
      (E₁ E₂ C₁ C₂ : ℂ) :
      (((r + 1 : ℕ) : ℂ) + ((s + 1 : ℕ) : ℂ)) *
          (-((((r + 1 : ℕ) : ℂ) + ((s + 1 : ℕ) : ℂ))⁻¹) *
            (E₁ * C₂ + C₁ * E₂)) =
        ((s + 1 : ℕ) : ℂ) * E₁ *
            (-((s + 1 : ℕ) : ℂ)⁻¹ * C₂) +
          ((r + 1 : ℕ) : ℂ) *
            (-((r + 1 : ℕ) : ℂ)⁻¹ * C₁) * E₂ := by
    field_simp [hr, hs, hrs, hrs2]
    ring
  rw [xiGammaEulerPrimitiveGammaCoPoissonCell,
    xiGammaEulerPrimitiveGammaCoPoissonCell,
    xiGammaEulerPrimitiveGammaCoPoissonCell]
  rw [show r + s + 1 + 1 = (r + 1) + (s + 1) by omega]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show
    -((↑r + 1 + (↑s + 1)) * (Real.log (p : ℝ) : ℂ)) =
      -((↑r + 1) * (Real.log (p : ℝ) : ℂ)) +
        -((↑s + 1) * (Real.log (p : ℝ) : ℂ)) by ring,
    gammaCoPoissonIntervalCell_add]
  simpa only [Nat.cast_add, Nat.cast_one] using halg
    (Complex.exp ((z - 1 / 2) *
      (-(((r + 1 : ℕ) : ℂ) * (Real.log (p : ℝ) : ℂ)))))
    (Complex.exp ((w - 1 / 2) *
      (-(((s + 1 : ℕ) : ℂ) * (Real.log (p : ℝ) : ℂ)))))
    (gammaCoPoissonIntervalCell
      (-(((r + 1 : ℕ) : ℂ) * (Real.log (p : ℝ) : ℂ))) z w)
    (gammaCoPoissonIntervalCell
      (-(((s + 1 : ℕ) : ℂ) * (Real.log (p : ℝ) : ℂ))) z w)

/-! ## Vector-valued Calderón--Witt transport before orientation trace -/

/--
The Gamma/co-Poisson boundary coefficient acts on the labelled
rational-Witt packet leg of degree one, leaving the Calderón defect leg
fixed.  This is the operation order forced by the source object: retain
degree-one labels, transport the packet, and only then form the exterior
cup.
-/
def deningerCalderonWittPacketLegTransport
    (p : Nat.Primes) (c : ℂ) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeOne p where
  toFun x := (x.1, c • x.2)
  map_add' x y := by
    ext <;> simp
  map_smul' a x := by
    ext <;> simp [smul_smul, mul_comm]

@[simp]
theorem deningerCalderonWittPacketLegTransport_apply
    (p : Nat.Primes) (c : ℂ)
    (x : DeningerCalderonWittAlgebraicDegreeOne p) :
    deningerCalderonWittPacketLegTransport p c x =
      (x.1, c • x.2) :=
  rfl

/--
Packet-leg transport scales the vector-valued Calderón--Witt cup by exactly
one copy of its coefficient.  Both alternating terms contain exactly one
packet leg.
-/
theorem deningerCalderonWittAlgebraicCup_packetLegTransport
    (p : Nat.Primes) (c : ℂ)
    (x y : DeningerCalderonWittAlgebraicDegreeOne p) :
    deningerCalderonWittAlgebraicCup p
        (deningerCalderonWittPacketLegTransport p c x)
        (deningerCalderonWittPacketLegTransport p c y) =
      c • deningerCalderonWittAlgebraicCup p x y := by
  change
    deningerMeyerCalderonWittAlgebraicCrossEffect p x.1 (c • y.2) -
        deningerMeyerCalderonWittAlgebraicCrossEffect p y.1 (c • x.2) =
      c •
        (deningerMeyerCalderonWittAlgebraicCrossEffect p x.1 y.2 -
          deningerMeyerCalderonWittAlgebraicCrossEffect p y.1 x.2)
  rw [map_smul, map_smul]
  module

/-- Induced transport on the full vector-valued exterior source. -/
def deningerCalderonWittExteriorPacketTransport
    (p : Nat.Primes) (c : ℂ) :
    (⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p)) →ₗ[ℂ]
      (⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p)) :=
  exteriorPower.map 2 (deningerCalderonWittPacketLegTransport p c)

/-- Boundary transport on the algebraic suspension packet. -/
def deningerCalderonWittDegreeTwoBoundaryTransport
    (p : Nat.Primes) (c : ℂ) :
    DeningerCalderonWittAlgebraicDegreeTwo p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeTwo p :=
  c • LinearMap.id

/--
The packet-leg exterior transport is a chain map for the Calderón--Witt
cup: source exterior multiplication precedes scalar boundary fusion.
-/
theorem deningerCalderonWittExteriorPacketTransport_cup
    (p : Nat.Primes) (c : ℂ) :
    (deningerCalderonWittAlgebraicExteriorCup p).comp
        (deningerCalderonWittExteriorPacketTransport p c) =
      (deningerCalderonWittDegreeTwoBoundaryTransport p c).comp
        (deningerCalderonWittAlgebraicExteriorCup p) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  unfold deningerCalderonWittExteriorPacketTransport
    deningerCalderonWittDegreeTwoBoundaryTransport
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [exteriorPower.map_apply_ιMulti,
    deningerCalderonWittAlgebraicExteriorCup_ιMulti]
  simp only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [deningerCalderonWittAlgebraicExteriorCup_ιMulti]
  change
    deningerCalderonWittAlgebraicCup p
        (deningerCalderonWittPacketLegTransport p c (f 0))
        (deningerCalderonWittPacketLegTransport p c (f 1)) =
      c • deningerCalderonWittAlgebraicCup p (f 0) (f 1)
  exact deningerCalderonWittAlgebraicCup_packetLegTransport p c (f 0) (f 1)

/--
The Gamma/co-Poisson coefficient at a prime-power cell, acting before cup
and orientation trace.
-/
def deningerCalderonWittPrimitiveGammaCoPoissonExteriorTransport
    (pe : Nat.Primes × ℕ) (z w : ℂ) :
    (⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne pe.1)) →ₗ[ℂ]
      (⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne pe.1)) :=
  deningerCalderonWittExteriorPacketTransport pe.1
    (xiGammaEulerPrimitiveGammaCoPoissonCell pe z w)

/--
Cellwise Gamma/co-Poisson transport has the required vector-valued boundary:
cup after transport equals confluence coefficient times cup.
-/
theorem deningerCalderonWittPrimitiveGammaCoPoissonExteriorTransport_cup
    (pe : Nat.Primes × ℕ) (z w : ℂ) :
    (deningerCalderonWittAlgebraicExteriorCup pe.1).comp
        (deningerCalderonWittPrimitiveGammaCoPoissonExteriorTransport
          pe z w) =
      (deningerCalderonWittDegreeTwoBoundaryTransport pe.1
        (xiGammaEulerPrimitiveGammaCoPoissonCell pe z w)).comp
          (deningerCalderonWittAlgebraicExteriorCup pe.1) := by
  exact deningerCalderonWittExteriorPacketTransport_cup pe.1
    (xiGammaEulerPrimitiveGammaCoPoissonCell pe z w)

/--
The canonical center-to-packet Green leg is equivariant for packet
transport.  This is the source-level statement that the boundary
coefficient is applied before reconstructing its exterior primitive.
-/
theorem deningerCalderonWittPacketLegTransport_centerToDegreeOne
    (p : Nat.Primes) (c : ℂ)
    (z : DeningerCalderonWittAlgebraicDegreeTwo p) :
    deningerCalderonWittPacketLegTransport p c
        (deningerCalderonWittCenterToDegreeOne p z) =
      deningerCalderonWittCenterToDegreeOne p (c • z) := by
  rw [deningerCalderonWittCenterToDegreeOne_apply,
    deningerCalderonWittPacketLegTransport_apply,
    deningerCalderonWittCenterToDegreeOne_apply]
  apply Prod.ext
  · simp
  · simp only [map_smul]
    module

/--
Koszul--Green section commutes with packet-leg exterior transport.  Hence
the canonical Green primitive is transported inside the vector-valued
source, not recreated after scalar orientation trace.
-/
theorem deningerCalderonWittExteriorPacketTransport_section
    (p : Nat.Primes) (c : ℂ)
    (z : DeningerCalderonWittAlgebraicDegreeTwo p) :
    deningerCalderonWittExteriorPacketTransport p c
        (deningerCalderonWittExteriorCupSection p z) =
      deningerCalderonWittExteriorCupSection p
        (deningerCalderonWittDegreeTwoBoundaryTransport p c z) := by
  unfold deningerCalderonWittExteriorPacketTransport
    deningerCalderonWittDegreeTwoBoundaryTransport
  rw [deningerCalderonWittExteriorCupSection,
    LinearMap.comp_apply,
    deningerCalderonWittExteriorWedgeLeft_apply,
    exteriorPower.map_apply_ιMulti]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  apply congrArg
    (fun f : Fin 2 → DeningerCalderonWittAlgebraicDegreeOne p =>
      exteriorPower.ιMulti ℂ 2 f)
  funext i
  fin_cases i
  · simp [deningerCalderonWittPacketLegTransport]
  · exact
      deningerCalderonWittPacketLegTransport_centerToDegreeOne p c z

/--
Exterior packet transport preserves exact Milnor-incidence relations.
This is necessary for it to define a chain transport rather than only a
map on the cup quotient.
-/
theorem deningerCalderonWittExteriorPacketTransport_mem_milnorIncidence
    (p : Nat.Primes) (c : ℂ)
    (i : deningerCalderonWittMilnorIncidence p) :
    deningerCalderonWittExteriorPacketTransport p c i.1 ∈
      deningerCalderonWittMilnorIncidence p := by
  change
    deningerCalderonWittAlgebraicExteriorCup p
        (deningerCalderonWittExteriorPacketTransport p c i.1) = 0
  have hchain := LinearMap.congr_fun
    (deningerCalderonWittExteriorPacketTransport_cup p c) i.1
  change
    deningerCalderonWittAlgebraicExteriorCup p
        (deningerCalderonWittExteriorPacketTransport p c i.1) =
      c • deningerCalderonWittAlgebraicExteriorCup p i.1 at hchain
  rw [hchain, i.2, smul_zero]

/-- Restriction of packet transport to the exact incidence sector. -/
def deningerCalderonWittMilnorIncidencePacketTransport
    (p : Nat.Primes) (c : ℂ) :
    deningerCalderonWittMilnorIncidence p →ₗ[ℂ]
      deningerCalderonWittMilnorIncidence p where
  toFun i :=
    ⟨deningerCalderonWittExteriorPacketTransport p c i.1,
      deningerCalderonWittExteriorPacketTransport_mem_milnorIncidence p c i⟩
  map_add' i j := by
    apply Subtype.ext
    exact map_add (deningerCalderonWittExteriorPacketTransport p c) i.1 j.1
  map_smul' a i := by
    apply Subtype.ext
    exact map_smul (deningerCalderonWittExteriorPacketTransport p c) a i.1

@[simp]
theorem deningerCalderonWittMilnorIncidencePacketTransport_coe
    (p : Nat.Primes) (c : ℂ)
    (i : deningerCalderonWittMilnorIncidence p) :
    (deningerCalderonWittMilnorIncidencePacketTransport p c i :
        ⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p)) =
      deningerCalderonWittExteriorPacketTransport p c i.1 :=
  rfl

/--
Exact Green retraction is natural for packet transport.  The theorem
isolates remaining analytic problem: whether this explicit incidence
endomorphism preserves cofinal admitted sector.
-/
theorem deningerCalderonWittMilnorGreenRetraction_packetTransport
    (p : Nat.Primes) (c : ℂ)
    (w : ⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p)) :
    deningerCalderonWittMilnorGreenRetraction p
        (deningerCalderonWittExteriorPacketTransport p c w) =
      deningerCalderonWittMilnorIncidencePacketTransport p c
        (deningerCalderonWittMilnorGreenRetraction p w) := by
  apply Subtype.ext
  rw [deningerCalderonWittMilnorGreenRetraction_coe,
    deningerCalderonWittMilnorIncidencePacketTransport_coe,
    deningerCalderonWittMilnorGreenRetraction_coe, map_sub]
  have hchain := LinearMap.congr_fun
    (deningerCalderonWittExteriorPacketTransport_cup p c) w
  change
    deningerCalderonWittAlgebraicExteriorCup p
        (deningerCalderonWittExteriorPacketTransport p c w) =
      deningerCalderonWittDegreeTwoBoundaryTransport p c
        (deningerCalderonWittAlgebraicExteriorCup p w) at hchain
  rw [hchain,
    ← deningerCalderonWittExteriorPacketTransport_section]

end

end RHTower
