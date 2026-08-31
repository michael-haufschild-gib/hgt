import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVacuumRegularNonlinearSourceGaugeNoGo

/-!
# Vacuum-differentiable nonlinear HB evolution cannot repair the linear clock defect

Static vacuum-regular nonlinear source gauges have already been excluded as producers of the
missing HB source-FE clock covariance. This module treats the genuinely time-dependent
perturbative escape.

Let `Phi` be an arbitrary nonlinear finite-time packet evolution. Its coefficientwise vacuum first
variation is required only along real source amplitudes, so Hermitian and conjugate nonlinearities
are included. If that first variation is the centered Birmingham--Mokhtari QNM clock and `Phi`
is exactly covariant under literal anti-linear source-FE transport, then covariance differentiates:
the centered-QNM clock itself must be source-FE covariant.

At any source-predeclared nonzero physical time, the existing finite-clock classification makes
existence of such an evolution equivalent to RH. Thus no perturbatively regular nonlinear
Einstein--Teukolsky correction can repair an off-wall linear defect, independently of locality,
channel count, perturbative order, memory, continuum, positivity, or invertibility. A survivor
must change the linearized clock or literal source law, be singular at vacuum, or assert only an
isolated finite-amplitude coincidence rather than an amplitude-neighborhood symmetry.

`[NEW] [HB NO-GO] [TIME-DEPENDENT] [FIRST VARIATION] [LEAN-PROVED]`
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- Coefficientwise first variation of a nonlinear packet evolution at vacuum. Real source
amplitudes make this strictly weaker than complex differentiability and retain conjugate/Hermitian
nonlinear terms. -/
def HBXiPeierlsVacuumFirstVariation
    (evolution : HBXiPeierlsPacket → HBXiPeierlsPacket)
    (linearization : HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket) : Prop :=
  ∀ x : HBXiPeierlsPacket, ∀ r : XiZeroCopy,
    Tendsto
      (fun amplitude : ℝ =>
        ((amplitude : ℂ)⁻¹ * evolution ((amplitude : ℂ) • x) r))
      (𝓝[≠] 0) (𝓝 (linearization x r))

/-- Exact nonlinear source-FE covariance of one finite-time evolution step. -/
def HBXiPeierlsNonlinearEvolutionSourceFECovariant
    (evolution : HBXiPeierlsPacket → HBXiPeierlsPacket) : Prop :=
  ∀ x : HBXiPeierlsPacket,
    hbXiPeierlsUnitSourceFEPacketTransport (evolution x) =
      evolution (hbXiPeierlsUnitSourceFEPacketTransport x)

/-- Vacuum first variation of a nonlinear source-FE-covariant evolution is itself source-FE
covariant. No norm or topology on the full packet space is used: the argument is coordinatewise
on finite packets. -/
theorem hbXiPeierls_vacuumFirstVariation_sourceFECovariant
    (evolution : HBXiPeierlsPacket → HBXiPeierlsPacket)
    (linearization : HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket)
    (hlinear : HBXiPeierlsVacuumFirstVariation evolution linearization)
    (hcovariant : HBXiPeierlsNonlinearEvolutionSourceFECovariant evolution) :
    ∀ x : HBXiPeierlsPacket,
      hbXiPeierlsUnitSourceFEPacketTransport (linearization x) =
        linearization (hbXiPeierlsUnitSourceFEPacketTransport x) := by
  intro x
  ext r
  have hleft := hlinear x (xiZeroCopyReflectEquiv r)
  have hconj : Tendsto
      (fun amplitude : ℝ =>
        (starRingEnd ℂ)
          ((amplitude : ℂ)⁻¹ *
            evolution ((amplitude : ℂ) • x) (xiZeroCopyReflectEquiv r)))
      (𝓝[≠] 0)
      (𝓝 ((starRingEnd ℂ) (linearization x (xiZeroCopyReflectEquiv r)))) :=
    (Complex.continuous_conj.tendsto _).comp hleft
  have htransport : Tendsto
      (fun amplitude : ℝ =>
        ((amplitude : ℂ)⁻¹ *
          hbXiPeierlsUnitSourceFEPacketTransport
            (evolution ((amplitude : ℂ) • x)) r))
      (𝓝[≠] 0)
      (𝓝 (hbXiPeierlsUnitSourceFEPacketTransport (linearization x) r)) := by
    have hcocycle : Tendsto
        (fun _amplitude : ℝ =>
          hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv r))
        (𝓝[≠] 0)
        (𝓝 (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv r))) :=
      tendsto_const_nhds
    have hmul := hcocycle.mul hconj
    convert hmul using 1
    · funext amplitude
      simp only [hbXiPeierlsUnitSourceFEPacketTransport_apply, map_mul, map_inv₀]
      simp
      ring
    · simp only [hbXiPeierlsUnitSourceFEPacketTransport_apply]
  have hright := hlinear (hbXiPeierlsUnitSourceFEPacketTransport x) r
  have heq :
      (fun amplitude : ℝ =>
        ((amplitude : ℂ)⁻¹ *
          hbXiPeierlsUnitSourceFEPacketTransport
            (evolution ((amplitude : ℂ) • x)) r)) =
      (fun amplitude : ℝ =>
        ((amplitude : ℂ)⁻¹ *
          evolution ((amplitude : ℂ) •
            hbXiPeierlsUnitSourceFEPacketTransport x) r)) := by
    funext amplitude
    have hrealSmul :
        hbXiPeierlsUnitSourceFEPacketTransport ((amplitude : ℂ) • x) =
          (amplitude : ℂ) • hbXiPeierlsUnitSourceFEPacketTransport x := by
      ext s
      simp [hbXiPeierlsUnitSourceFEPacketTransport_apply]
      ring
    rw [hcovariant, hrealSmul]
  rw [heq] at htransport
  exact tendsto_nhds_unique htransport hright

/-- Every complex-linear packet map is its own coefficientwise vacuum first variation. -/
theorem hbXiPeierlsVacuumFirstVariation_linear
    (linearization : HBXiPeierlsPacket →ₗ[ℂ] HBXiPeierlsPacket) :
    HBXiPeierlsVacuumFirstVariation (fun x => linearization x) linearization := by
  intro x r
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with amplitude hamplitude
  have hamplitude0 : amplitude ≠ 0 := by
    simpa using hamplitude
  rw [map_smul]
  simp only [smul_eq_mul, Finsupp.smul_apply]
  have hamplitudeC : (amplitude : ℂ) ≠ 0 := by
    exact_mod_cast hamplitude0
  field_simp [hamplitudeC]

/-- Existence of a perturbatively regular nonlinear time step whose first variation is the BM
centered-QNM physical clock and which is exactly source-FE covariant. -/
def HBXiPeierlsExistsVacuumDifferentiableNonlinearEvolution
    (n : ℕ) (t : ℝ) : Prop :=
  ∃ evolution : HBXiPeierlsPacket → HBXiPeierlsPacket,
    HBXiPeierlsVacuumFirstVariation evolution
      (hbXiPeierlsCenteredQNMPhysicalClockStep n t) ∧
    HBXiPeierlsNonlinearEvolutionSourceFECovariant evolution

/-- Hard reduction: any perturbatively regular nonlinear FE-covariant evolution with prescribed
BM first variation forces the already-classified linear finite-clock covariance. -/
theorem hbXiPeierlsVacuumDifferentiableNonlinearEvolution_forces_linearClockCovariance
    (n : ℕ) (t : ℝ)
    {evolution : HBXiPeierlsPacket → HBXiPeierlsPacket}
    (hlinear : HBXiPeierlsVacuumFirstVariation evolution
      (hbXiPeierlsCenteredQNMPhysicalClockStep n t))
    (hcovariant : HBXiPeierlsNonlinearEvolutionSourceFECovariant evolution) :
    HBXiPeierlsUnitSourceFEPhysicalClockStepCovariant n t :=
  hbXiPeierls_vacuumFirstVariation_sourceFECovariant evolution
    (hbXiPeierlsCenteredQNMPhysicalClockStep n t) hlinear hcovariant

/-- Exact nonlinear classification: at one nonzero physical time, existence of a
vacuum-differentiable nonlinear evolution with BM linearization and literal source-FE covariance
is equivalent to RH. -/
theorem hbXiPeierlsExistsVacuumDifferentiableNonlinearEvolution_iff_rh
    (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HBXiPeierlsExistsVacuumDifferentiableNonlinearEvolution n t ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨evolution, hlinear, hcovariant⟩
    apply (hbXiPeierlsUnitSourceFEPhysicalClockStepCovariant_iff_rh n ht).mp
    exact hbXiPeierlsVacuumDifferentiableNonlinearEvolution_forces_linearClockCovariance
      n t hlinear hcovariant
  · intro hRH
    refine ⟨hbXiPeierlsCenteredQNMPhysicalClockStep n t,
      hbXiPeierlsVacuumFirstVariation_linear
        (hbXiPeierlsCenteredQNMPhysicalClockStep n t), ?_⟩
    exact (hbXiPeierlsUnitSourceFEPhysicalClockStepCovariant_iff_rh n ht).mpr hRH

/-- Unit-time specialization of the nonlinear existence classification. -/
theorem hbXiPeierlsExistsVacuumDifferentiableNonlinearUnitEvolution_iff_rh
    (n : ℕ) :
    HBXiPeierlsExistsVacuumDifferentiableNonlinearEvolution n 1 ↔
      RiemannHypothesis :=
  hbXiPeierlsExistsVacuumDifferentiableNonlinearEvolution_iff_rh n one_ne_zero

/-- Closed route-kill package: no perturbatively regular nonlinear Einstein--Teukolsky time step
can repair the off-wall source-FE defect while retaining literal source transport and the BM
linearized clock. -/
def D4HBVacuumDifferentiableNonlinearEvolutionRouteKilled : Prop :=
  ∀ (n : ℕ) (t : ℝ), t ≠ 0 →
    (HBXiPeierlsExistsVacuumDifferentiableNonlinearEvolution n t ↔
      RiemannHypothesis)

/-- Premise-free certificate killing perturbatively regular time-dependent nonlinear repair as
an independent HB proof route. -/
theorem d4HBVacuumDifferentiableNonlinearEvolutionRouteKilled :
    D4HBVacuumDifferentiableNonlinearEvolutionRouteKilled := by
  intro n t ht
  exact hbXiPeierlsExistsVacuumDifferentiableNonlinearEvolution_iff_rh n ht

end


end RHTower
