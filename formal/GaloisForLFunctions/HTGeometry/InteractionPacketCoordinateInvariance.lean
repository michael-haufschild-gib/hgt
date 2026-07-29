import GaloisForLFunctions.HTGeometry.LocalSpectralObserverDirectSumLaw
import GaloisForLFunctions.HTGeometry.InteractionPacketRelabelling

/-!
# Coordinate invariance of interaction-packet sectors

Packet sectors encode independently switchable interaction channels rather
than arbitrary numerical coordinates.  This file proves that their germ
visibility is unchanged by the two harmless coordinate operations on that
control architecture:

* arbitrary relabelling of the channels;
* independent nonzero changes of units in every channel.

An arbitrary linear mixing of channels is not a coordinate change of the same
independent-control architecture: it changes which subsets can be switched
off.  No invariance under such a physical redesign is asserted.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open FiniteLocalInteractionFamily

/-- Independent coordinatewise change of units on an interaction-control
space. -/
def diagonalRescaleCoupling
    {E : Type*} (scale z : E → ℂ) : E → ℂ :=
  fun e => scale e * z e

@[simp]
theorem diagonalRescaleCoupling_zero
    {E : Type*} (scale : E → ℂ) :
    diagonalRescaleCoupling scale (0 : E → ℂ) = 0 := by
  funext e
  simp [diagonalRescaleCoupling]

/-- Coordinatewise changes of units commute with switching a packet on or
off. -/
@[simp]
theorem diagonalRescaleCoupling_restrictInteractionPacket
    {E : Type*} [DecidableEq E]
    (scale : E → ℂ) (packet : Finset E) (z : E → ℂ) :
    diagonalRescaleCoupling scale
        (restrictInteractionPacket packet z) =
      restrictInteractionPacket packet
        (diagonalRescaleCoupling scale z) := by
  funext e
  by_cases he : e ∈ packet <;>
    simp [diagonalRescaleCoupling, restrictInteractionPacket, he]

/-- Every coordinatewise change of units is analytic at zero control. -/
theorem diagonalRescaleCoupling_analyticAt
    {E : Type*} [Fintype E] [DecidableEq E]
    (scale : E → ℂ) :
    AnalyticAt ℂ
      (diagonalRescaleCoupling scale : (E → ℂ) → E → ℂ) 0 := by
  apply AnalyticAt.pi
  intro e
  simpa [diagonalRescaleCoupling] using
    (analyticAt_const.mul
      ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : E => ℂ) e).analyticAt 0))

/-- Every coordinatewise change of units preserves the zero-control
limit. -/
theorem diagonalRescaleCoupling_tendsto_zero
    {E : Type*} [Fintype E] [DecidableEq E]
    (scale : E → ℂ) :
    Tendsto
      (diagonalRescaleCoupling scale : (E → ℂ) → E → ℂ)
      (𝓝 0) (𝓝 0) := by
  have hc := (diagonalRescaleCoupling_analyticAt scale).continuousAt
  change Tendsto
    (diagonalRescaleCoupling scale : (E → ℂ) → E → ℂ)
    (𝓝 0) (𝓝 (diagonalRescaleCoupling scale 0)) at hc
  simpa only [diagonalRescaleCoupling_zero] using hc

/-- Inverse units undo a nonzero coordinatewise rescaling. -/
theorem diagonalRescaleCoupling_inv_apply
    {E : Type*} (scale : E → ℂ)
    (hscale : ∀ e, scale e ≠ 0) (z : E → ℂ) :
    diagonalRescaleCoupling (fun e => (scale e)⁻¹)
        (diagonalRescaleCoupling scale z) = z := by
  funext e
  simp [diagonalRescaleCoupling, hscale e]

/-- A nonzero coordinatewise rescaling undoes its inverse units. -/
theorem diagonalRescaleCoupling_apply_inv
    {E : Type*} (scale : E → ℂ)
    (hscale : ∀ e, scale e ≠ 0) (z : E → ℂ) :
    diagonalRescaleCoupling scale
        (diagonalRescaleCoupling (fun e => (scale e)⁻¹) z) = z := by
  funext e
  simp [diagonalRescaleCoupling, hscale e]

/-- Packet projection commutes exactly with an independent coordinatewise
change of units. -/
theorem spectralPacketResponse_diagonalRescaleCoupling
    {E : Type*} [Fintype E] [DecidableEq E]
    (branch : (E → ℂ) → ℂ) (scale : E → ℂ)
    (packet : Finset E) (z : E → ℂ) :
    spectralPacketResponse
        (fun w => branch (diagonalRescaleCoupling scale w))
        packet z =
      spectralPacketResponse branch packet
        (diagonalRescaleCoupling scale z) := by
  unfold spectralPacketResponse finsetMobiusResponse
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  apply congrArg branch
  rw [diagonalRescaleCoupling_restrictInteractionPacket]

/-- **Unit invariance of packet visibility.**  Independent nonzero changes of
units preserve and reflect whether an irreducible packet sector is the zero
germ. -/
theorem spectralPacketResponse_diagonalRescaleCoupling_germ_eq_zero_iff
    {E : Type*} [Fintype E] [DecidableEq E]
    (branch : (E → ℂ) → ℂ) (scale : E → ℂ)
    (hscale : ∀ e, scale e ≠ 0) (packet : Finset E) :
    spectralPacketResponse
        (fun w => branch (diagonalRescaleCoupling scale w))
        packet =ᶠ[𝓝 0] (fun _ : E → ℂ => 0) ↔
      spectralPacketResponse branch packet =ᶠ[𝓝 0]
        (fun _ : E → ℂ => 0) := by
  constructor
  · intro hscaled
    have hcomp := hscaled.comp_tendsto
      (diagonalRescaleCoupling_tendsto_zero
        (fun e => (scale e)⁻¹))
    filter_upwards [hcomp] with z hz
    change spectralPacketResponse
      (fun w => branch (diagonalRescaleCoupling scale w))
      packet (diagonalRescaleCoupling (fun e => (scale e)⁻¹) z) = 0 at hz
    rw [spectralPacketResponse_diagonalRescaleCoupling] at hz
    simpa [diagonalRescaleCoupling_apply_inv scale hscale z] using hz
  · intro hzero
    have hcomp := hzero.comp_tendsto
      (diagonalRescaleCoupling_tendsto_zero scale)
    filter_upwards [hcomp] with z hz
    rw [spectralPacketResponse_diagonalRescaleCoupling]
    exact hz

/-- Packet projection transports exactly under an arbitrary equivalence of
interaction labels. -/
theorem spectralPacketResponse_relabelCoupling
    {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q]
    (e : P ≃ Q) (branch : (Q → ℂ) → ℂ)
    (packet : Finset P) (z : P → ℂ) :
    spectralPacketResponse
        (fun w => branch (relabelCoupling e w)) packet z =
      spectralPacketResponse branch (e.finsetCongr packet)
        (relabelCoupling e z) := by
  unfold spectralPacketResponse
  let response : Finset P → ℂ :=
    fun active =>
      branch (relabelCoupling e
        (restrictInteractionPacket active z))
  change finsetMobiusResponse packet response = _
  rw [← finsetMobiusResponse_equiv e packet response]
  apply congrArg (finsetMobiusResponse (e.finsetCongr packet))
  funext active
  apply congrArg branch
  rw [relabelCoupling_restrictInteractionPacket]
  have hactive :
      e.finsetCongr (e.symm.finsetCongr active) = active := by
    ext q
    simp
  rw [hactive]

/-- **Label invariance of packet visibility.**  Relabelling independently
switchable channels preserves and reflects the zero-germ status of every
corresponding packet sector. -/
theorem spectralPacketResponse_relabelCoupling_germ_eq_zero_iff
    {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q]
    (e : P ≃ Q) (branch : (Q → ℂ) → ℂ)
    (packet : Finset P) :
    spectralPacketResponse
        (fun w => branch (relabelCoupling e w)) packet
          =ᶠ[𝓝 0] (fun _ : P → ℂ => 0) ↔
      spectralPacketResponse branch (e.finsetCongr packet)
          =ᶠ[𝓝 0] (fun _ : Q → ℂ => 0) := by
  constructor
  · intro hleft
    have hcomp := hleft.comp_tendsto
      (relabelCoupling_tendsto_zero e.symm)
    filter_upwards [hcomp] with z hz
    change spectralPacketResponse
      (fun w => branch (relabelCoupling e w)) packet
        (relabelCoupling e.symm z) = 0 at hz
    rw [spectralPacketResponse_relabelCoupling] at hz
    have hrelabel :
        relabelCoupling e (relabelCoupling e.symm z) = z := by
      funext q
      simp [relabelCoupling]
    rw [hrelabel] at hz
    exact hz
  · intro hright
    have hcomp := hright.comp_tendsto
      (relabelCoupling_tendsto_zero e)
    filter_upwards [hcomp] with z hz
    rw [spectralPacketResponse_relabelCoupling]
    exact hz

end GaloisForLFunctions.HTGeometry
