import GaloisForLFunctions.HTGeometry.FiniteObservableKoopmanBoundary

/-!
# Finite reporters miss a nonzero hypertranscendental jet packet

A finite panel of linear reporters maps the derivative-observable tower into a finite-dimensional
readout space.  If the tower has no nonzero constant-coefficient differential annihilator, its
first `finrank + 1` jets are linearly independent before measurement but dependent after
measurement.  The resulting relation is therefore a nonzero finite derivative packet that every
reported coordinate sends to zero.

This strengthens the finite invariant-model boundary: no derivative-invariant latent space is
assumed.  The obstruction applies to any finite linear readout, including finite-outcome quantum
tomography, Koopman/DMD sensor panels, and genetic-network reporter panels.  It is a static
observability theorem, not a claim about temporal evolution.

The hypothesis is deliberately the weaker constant-coefficient differential transcendence, so the
result applies beyond hypertranscendental functions.  In particular, meromorphic simple-pole
sources and finite spectral dressings already present in the corpus inherit the same blindness.

Physics/ML/genomics provenance: finite informational completeness is a rank condition on the
measurement map; finite Koopman representations restrict an infinite observable operator to a
finite-dimensional subspace; and genetic reporter placement maximizes a Koopman observability
Gramian.  The exact theorem below is their common finite-rank linear-algebra boundary.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

open GaloisForLFunctions Module

/-- A finite linear packet of derivative observations. -/
def finiteDerivativeReporterPacket
    {n : ℕ} (c : Fin n → ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  ∑ i, c i • iteratedDeriv (i : ℕ) f

/-- **Finite-reporter blindness.**  Every finite-dimensional linear readout of an infinitely
constant-coefficient-transcendental derivative clock misses a nonzero finite jet packet. -/
theorem exists_nonzero_finiteDerivativeReporterPacket_ker
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    ∃ c : Fin (finrank ℂ Y + 1) → ℂ,
      (∃ i, c i ≠ 0) ∧
      finiteDerivativeReporterPacket c f ≠ 0 ∧
      report (finiteDerivativeReporterPacket c f) = 0 := by
  let v : Fin (finrank ℂ Y + 1) → Y :=
    fun i ↦ report (iteratedDeriv (i : ℕ) f)
  have hv : ¬ LinearIndependent ℂ v := by
    intro hli
    have hbound := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hbound
    omega
  obtain ⟨c, hsum, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hv
  have hjets : LinearIndependent ℂ
      (fun i : Fin (finrank ℂ Y + 1) ↦ iteratedDeriv (i : ℕ) f) := by
    have hall : LinearIndependent ℂ (fun n : ℕ ↦ iteratedDeriv n f) :=
      (constantCoefficientDifferentiallyTranscendental_iff_linearIndependent_iteratedDeriv f).mp hf
    exact hall.comp (fun i : Fin (finrank ℂ Y + 1) ↦ (i : ℕ)) Fin.val_injective
  have hpacket : finiteDerivativeReporterPacket c f ≠ 0 := by
    intro hzero
    have hcoeff := Fintype.linearIndependent_iff.mp hjets c
    exact hi (hcoeff (by simpa [finiteDerivativeReporterPacket] using hzero) i)
  refine ⟨c, ⟨i, hi⟩, hpacket, ?_⟩
  rw [finiteDerivativeReporterPacket, map_sum]
  simpa only [map_smul, v] using hsum

/-- Hypertranscendence supplies the reporter-blind nonzero packet. -/
theorem exists_nonzero_finiteDerivativeReporterPacket_ker_of_hypertranscendental
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    ∃ c : Fin (finrank ℂ Y + 1) → ℂ,
      (∃ i, c i ≠ 0) ∧
      finiteDerivativeReporterPacket c f ≠ 0 ∧
      report (finiteDerivativeReporterPacket c f) = 0 :=
  exists_nonzero_finiteDerivativeReporterPacket_ker
    (hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf) report

end

end HTGeometry
