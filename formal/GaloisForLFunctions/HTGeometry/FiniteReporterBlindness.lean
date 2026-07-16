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

/-- Linear synthesis of the first `n` derivative observables from a coefficient packet. -/
def finiteDerivativeJetSynthesis
    (n : ℕ) (f : ℂ → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun c := finiteDerivativeReporterPacket c f
  map_add' c d := by
    funext z
    simp [finiteDerivativeReporterPacket, Finset.sum_add_distrib, add_smul]
  map_smul' a c := by
    funext z
    simp only [finiteDerivativeReporterPacket, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [RingHom.id_apply]
    ring

/-- The coefficient-to-readout map for the first `n` observations of one derivative clock. -/
def finiteDerivativeReporterMap
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (n : ℕ) (f : ℂ → ℂ) (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    (Fin n → ℂ) →ₗ[ℂ] Y :=
  report.comp (finiteDerivativeJetSynthesis n f)

/-- Constant-coefficient differential transcendence makes every finite jet-synthesis map
injective.  Thus coefficient nullity below counts genuine nonzero clock observables, rather than
formal coefficient aliases. -/
theorem finiteDerivativeJetSynthesis_injective
    {n : ℕ} {f : ℂ → ℂ}
    (hf : ConstantCoefficientDifferentiallyTranscendental f) :
    Function.Injective (finiteDerivativeJetSynthesis n f) := by
  have hjets : LinearIndependent ℂ
      (fun i : Fin n ↦ iteratedDeriv (i : ℕ) f) := by
    have hall : LinearIndependent ℂ (fun m : ℕ ↦ iteratedDeriv m f) :=
      (constantCoefficientDifferentiallyTranscendental_iff_linearIndependent_iteratedDeriv f).mp hf
    exact hall.comp (fun i : Fin n ↦ (i : ℕ)) Fin.val_injective
  intro c d hcd
  have hzero : finiteDerivativeJetSynthesis n f (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  have hcoeff := Fintype.linearIndependent_iff.mp hjets (c - d)
  have hcoeffZero : ∀ i, (c - d) i = 0 := by
    apply hcoeff
    simpa [finiteDerivativeJetSynthesis, finiteDerivativeReporterPacket] using hzero
  funext i
  exact sub_eq_zero.mp (hcoeffZero i)

/-- **Exact finite-reporter value relation.**  On the first `n` derivative observations, the
number of visible coefficient directions plus the number of reporter-blind directions is exactly
`n`.  This is the rank--nullity law behind finite genetic reporters, learned sensor panels, and
finite-outcome measurement channels. -/
theorem finiteDerivativeReporterMap_rank_nullity
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (n : ℕ) (f : ℂ → ℂ) (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    finrank ℂ (LinearMap.range (finiteDerivativeReporterMap n f report)) +
        finrank ℂ (LinearMap.ker (finiteDerivativeReporterMap n f report)) = n := by
  simpa using
    (LinearMap.finrank_range_add_finrank_ker (finiteDerivativeReporterMap n f report))

/-- A `d`-dimensional reporter leaves enough blind coefficient directions to cover the excess of
the jet resolution over `d`.  Unlike the earlier first-collision theorem, this quantifies the
whole unresolved packet space at every finite resolution. -/
theorem finiteDerivativeReporterMap_blind_finrank_lower
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (n : ℕ) (f : ℂ → ℂ) (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    n ≤ finrank ℂ Y +
      finrank ℂ (LinearMap.ker (finiteDerivativeReporterMap n f report)) := by
  have hrange :
      finrank ℂ (LinearMap.range (finiteDerivativeReporterMap n f report)) ≤
        finrank ℂ Y :=
    (LinearMap.range (finiteDerivativeReporterMap n f report)).finrank_le
  have hrank := finiteDerivativeReporterMap_rank_nullity n f report
  omega

/-- Every nonzero blind coefficient direction supplied by the nullity law is a genuinely nonzero
derivative observable before reporting. -/
theorem finiteDerivativeReporterMap_nonzero_packet_of_mem_ker
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {n : ℕ} {f : ℂ → ℂ}
    (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) {c : Fin n → ℂ}
    (hc : c ∈ LinearMap.ker (finiteDerivativeReporterMap n f report))
    (hc0 : c ≠ 0) :
    finiteDerivativeReporterPacket c f ≠ 0 ∧
      report (finiteDerivativeReporterPacket c f) = 0 := by
  constructor
  · intro hpacket
    apply hc0
    apply finiteDerivativeJetSynthesis_injective hf
    change finiteDerivativeReporterPacket c f =
      finiteDerivativeReporterPacket 0 f
    rw [hpacket]
    simp [finiteDerivativeReporterPacket]
  · simpa [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis] using hc

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
