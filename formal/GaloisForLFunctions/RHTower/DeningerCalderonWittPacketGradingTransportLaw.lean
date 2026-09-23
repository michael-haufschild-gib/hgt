import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedGammaCoPoissonGreenTransport

/-!
# Packet-grading law for Gamma/co-Poisson Green transport

The primitive-promoted Gamma/co-Poisson map is not an isolated family of
cellwise endomorphisms.  Its scalar coefficient acts through one canonical
multiplicative grading representation on the Calderón--Witt source.

The action fixes the Calderón defect leg and scales the rational-Witt packet
leg.  Exterior transport therefore preserves cup and Milnor incidence, and
the Green retraction is equivariant.  Nonzero coefficients act bijectively:
no finite Gamma/co-Poisson cell loses source information.

This identifies the remaining cofinal question sharply.  One need not
construct another local transport.  One must prove that the singular
cofinal/Hodge admission sector is a subrepresentation of this explicit
packet-grading action.
-/

namespace RHTower

noncomputable section

/-- Packet-leg transports multiply under composition. -/
theorem deningerCalderonWittPacketLegTransport_comp
    (p : Nat.Primes)
    (c d : ℂ) :
    (deningerCalderonWittPacketLegTransport p c).comp
        (deningerCalderonWittPacketLegTransport p d) =
      deningerCalderonWittPacketLegTransport p (c * d) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · simp [deningerCalderonWittPacketLegTransport, smul_smul]

/-- Coefficient one acts identically on degree one. -/
theorem deningerCalderonWittPacketLegTransport_one
    (p : Nat.Primes) :
    deningerCalderonWittPacketLegTransport p 1 =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Prod.ext <;>
    simp [deningerCalderonWittPacketLegTransport]

/-- Exterior packet transports multiply under composition. -/
theorem deningerCalderonWittExteriorPacketTransport_comp
    (p : Nat.Primes)
    (c d : ℂ) :
    (deningerCalderonWittExteriorPacketTransport p c).comp
        (deningerCalderonWittExteriorPacketTransport p d) =
      deningerCalderonWittExteriorPacketTransport p (c * d) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [deningerCalderonWittExteriorPacketTransport,
    deningerCalderonWittExteriorPacketTransport,
    deningerCalderonWittExteriorPacketTransport,
    exteriorPower.map_apply_ιMulti,
    exteriorPower.map_apply_ιMulti,
    exteriorPower.map_apply_ιMulti]
  apply congrArg (fun g => exteriorPower.ιMulti ℂ 2 g)
  funext i
  exact LinearMap.congr_fun
    (deningerCalderonWittPacketLegTransport_comp p c d) (f i)

/-- Coefficient one acts identically on the exterior source. -/
theorem deningerCalderonWittExteriorPacketTransport_one
    (p : Nat.Primes) :
    deningerCalderonWittExteriorPacketTransport p 1 =
      LinearMap.id := by
  rw [deningerCalderonWittExteriorPacketTransport,
    deningerCalderonWittPacketLegTransport_one,
    exteriorPower.map_id]

/-- The induced Milnor-incidence transports multiply under composition. -/
theorem deningerCalderonWittMilnorIncidencePacketTransport_comp
    (p : Nat.Primes)
    (c d : ℂ) :
    (deningerCalderonWittMilnorIncidencePacketTransport p c).comp
        (deningerCalderonWittMilnorIncidencePacketTransport p d) =
      deningerCalderonWittMilnorIncidencePacketTransport p (c * d) := by
  apply LinearMap.ext
  intro i
  apply Subtype.ext
  change
    deningerCalderonWittExteriorPacketTransport p c
        (deningerCalderonWittExteriorPacketTransport p d i.1) =
      deningerCalderonWittExteriorPacketTransport p (c * d) i.1
  exact LinearMap.congr_fun
    (deningerCalderonWittExteriorPacketTransport_comp p c d) i.1

/-- Coefficient one acts identically on Milnor incidence. -/
theorem deningerCalderonWittMilnorIncidencePacketTransport_one
    (p : Nat.Primes) :
    deningerCalderonWittMilnorIncidencePacketTransport p 1 =
      LinearMap.id := by
  apply LinearMap.ext
  intro i
  apply Subtype.ext
  change deningerCalderonWittExteriorPacketTransport p 1 i.1 = i.1
  rw [deningerCalderonWittExteriorPacketTransport_one,
    LinearMap.id_apply]

/--
**Packet-grading representation.** Scalar Gamma/co-Poisson coefficients act
multiplicatively on the exact Milnor-incidence source.
-/
def deningerCalderonWittMilnorPacketGradingAction
    (p : Nat.Primes) :
    ℂ →* Module.End ℂ (deningerCalderonWittMilnorIncidence p) where
  toFun := deningerCalderonWittMilnorIncidencePacketTransport p
  map_one' := deningerCalderonWittMilnorIncidencePacketTransport_one p
  map_mul' c d :=
    (deningerCalderonWittMilnorIncidencePacketTransport_comp p c d).symm

/-- Every nonzero grading coefficient acts bijectively on exact incidence. -/
theorem deningerCalderonWittMilnorIncidencePacketTransport_bijective
    (p : Nat.Primes)
    {c : ℂ}
    (hc : c ≠ 0) :
    Function.Bijective
      (deningerCalderonWittMilnorIncidencePacketTransport p c) := by
  constructor
  · intro x y hxy
    have h := congrArg
      (deningerCalderonWittMilnorIncidencePacketTransport p c⁻¹) hxy
    have hcomp :=
      deningerCalderonWittMilnorIncidencePacketTransport_comp p c⁻¹ c
    rw [inv_mul_cancel₀ hc,
      deningerCalderonWittMilnorIncidencePacketTransport_one] at hcomp
    calc
      x = deningerCalderonWittMilnorIncidencePacketTransport p c⁻¹
          (deningerCalderonWittMilnorIncidencePacketTransport p c x) := by
        simpa [LinearMap.comp_apply] using
          (LinearMap.congr_fun hcomp x).symm
      _ = deningerCalderonWittMilnorIncidencePacketTransport p c⁻¹
          (deningerCalderonWittMilnorIncidencePacketTransport p c y) := h
      _ = y := by
        simpa [LinearMap.comp_apply] using
          LinearMap.congr_fun hcomp y
  · intro y
    refine
      ⟨deningerCalderonWittMilnorIncidencePacketTransport p c⁻¹ y, ?_⟩
    have hcomp :=
      deningerCalderonWittMilnorIncidencePacketTransport_comp p c c⁻¹
    rw [mul_inv_cancel₀ hc,
      deningerCalderonWittMilnorIncidencePacketTransport_one] at hcomp
    exact LinearMap.congr_fun hcomp y

/--
Green retraction is equivariant for the packet-grading representation.
Thus the Gamma/co-Poisson transport carries the actual canonical primitive,
not merely its scalar trace.
-/
theorem deningerCalderonWittMilnorGreenRetraction_gradingEquivariant
    (p : Nat.Primes)
    (c : ℂ)
    (w : ⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p)) :
    deningerCalderonWittMilnorGreenRetraction p
        (deningerCalderonWittExteriorPacketTransport p c w) =
      deningerCalderonWittMilnorPacketGradingAction p c
        (deningerCalderonWittMilnorGreenRetraction p w) := by
  exact deningerCalderonWittMilnorGreenRetraction_packetTransport p c w

/-- Every physical diagonal primitive Gamma/co-Poisson coefficient is
strictly positive. -/
theorem xiGammaEulerPrimitiveModularCurrent_pos
    (a : ℝ)
    (pe : Nat.Primes × ℕ) :
    0 < xiGammaEulerPrimitiveModularCurrent a pe := by
  rw [xiGammaEulerPrimitiveModularCurrent_explicit]
  exact mul_pos
    (Real.log_pos (by
      exact_mod_cast pe.1.property.two_le))
    (Real.exp_pos _)

/-- Hence every physical diagonal Gamma/co-Poisson cell is nonzero. -/
theorem xiGammaEulerPrimitiveGammaCoPoissonCell_self_ne_zero
    (a : ℝ)
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveGammaCoPoissonCell pe
        (((1 : ℝ) + a : ℝ) : ℂ)
        (((1 : ℝ) + a : ℝ) : ℂ) ≠
      0 := by
  rw [xiGammaEulerPrimitiveGammaCoPoissonCell_self]
  exact_mod_cast (xiGammaEulerPrimitiveModularCurrent_pos a pe).ne'

/--
Every physical finite Gamma/co-Poisson cell acts bijectively on the exact
Milnor-incidence source.  Finite-stage transport therefore cannot be the
location of information loss.
-/
theorem deningerCalderonWittPhysicalGammaCellTransport_bijective
    (a : ℝ)
    (pe : Nat.Primes × ℕ) :
    Function.Bijective
      (deningerCalderonWittMilnorIncidencePacketTransport pe.1
        (xiGammaEulerPrimitiveGammaCoPoissonCell pe
          (((1 : ℝ) + a : ℝ) : ℂ)
          (((1 : ℝ) + a : ℝ) : ℂ))) :=
  deningerCalderonWittMilnorIncidencePacketTransport_bijective pe.1
    (xiGammaEulerPrimitiveGammaCoPoissonCell_self_ne_zero a pe)

end

end RHTower
