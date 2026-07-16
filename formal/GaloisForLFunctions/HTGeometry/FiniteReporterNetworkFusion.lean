import GaloisForLFunctions.HTGeometry.FiniteReporterGramFisher
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite reporter-network fusion

Independent gravitational-wave detectors, quantum measurement panels, genomic reporter panels,
and learned sensor ensembles combine by an `L2` direct sum.  Their Gram/Fisher information matrices
add, while the fused blind space is exactly the intersection of the component blind spaces.

This extends the existing two-panel theorem to an arbitrary finite dependent family of Hilbert
output spaces.  It is a static value law for observation networks and assumes no temporal
propagation model.
-/

open scoped BigOperators InnerProductSpace

namespace HTGeometry

noncomputable section

open GaloisForLFunctions Module

/-- Fuse a finite family of Hilbert-valued reporters into their `L2` direct sum. -/
def finiteFamilyDerivativeReporter
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (ℂ → ℂ) →ₗ[ℂ] PiLp 2 Y :=
  (WithLp.linearEquiv 2 ℂ (∀ a, Y a)).symm.toLinearMap.comp
    (LinearMap.pi report)

@[simp] theorem finiteFamilyDerivativeReporter_apply
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) (g : ℂ → ℂ) :
    finiteFamilyDerivativeReporter report g =
      WithLp.toLp 2 (fun a => report a g) := rfl

/-- Coefficient reporting commutes with finite-family fusion. -/
theorem finiteDerivativeReporterMap_family_apply
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (n : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) (c : Fin n → ℂ) :
    finiteDerivativeReporterMap n f (finiteFamilyDerivativeReporter report) c =
      WithLp.toLp 2 (fun a => finiteDerivativeReporterMap n f (report a) c) := rfl

/-- **Finite-network Fisher addition.**  Gram/Fisher information adds over an arbitrary finite
reporter network. -/
theorem finiteDerivativeReporterGram_family_eq_sum
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (n : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    finiteDerivativeReporterGram n f (finiteFamilyDerivativeReporter report) =
      ∑ a, finiteDerivativeReporterGram n f (report a) := by
  ext i j
  simp [finiteDerivativeReporterGram, Matrix.gram_apply,
    finiteFamilyDerivativeReporter, PiLp.inner_apply, Matrix.sum_apply]

/-- The blind space of a finite reporter network is the intersection of all component blind
spaces. -/
theorem ker_finiteDerivativeReporterMap_family
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (n : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    LinearMap.ker (finiteDerivativeReporterMap n f
        (finiteFamilyDerivativeReporter report)) =
      ⨅ a, LinearMap.ker (finiteDerivativeReporterMap n f (report a)) := by
  ext c
  simp only [LinearMap.mem_ker, Submodule.mem_iInf]
  rw [finiteDerivativeReporterMap_family_apply]
  simp only [WithLp.toLp_eq_zero]
  constructor
  · intro h a
    exact congrFun h a
  · intro h
    funext a
    exact h a

/-- A finite reporter network is complete exactly when its component panels have no common blind
coefficient direction. -/
theorem finiteDerivativeReporterGram_family_det_ne_zero_iff_iInf_ker_eq_bot
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (n : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (finiteDerivativeReporterGram n f
        (finiteFamilyDerivativeReporter report)).det ≠ 0 ↔
      (⨅ a, LinearMap.ker (finiteDerivativeReporterMap n f (report a))) = ⊥ := by
  rw [finiteDerivativeReporterGram_det_ne_zero_iff_injective,
    ← LinearMap.ker_eq_bot, ker_finiteDerivativeReporterMap_family]

/-- For a genuine infinite derivative clock, fused singularity is witnessed by a nonzero packet
erased by every member of the finite network. -/
theorem finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    {n : ℕ} {f : ℂ → ℂ}
    (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (finiteDerivativeReporterGram n f
        (finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin n → ℂ,
        (∀ a, report a (finiteDerivativeReporterPacket c f) = 0) ∧
          finiteDerivativeReporterPacket c f ≠ 0 := by
  rw [finiteDerivativeReporterGram_det_eq_zero_iff_exists_blindPacket hf]
  constructor
  · rintro ⟨c, hfamily, hc⟩
    refine ⟨c, ?_, hc⟩
    intro a
    change WithLp.toLp 2
      (fun a => report a (finiteDerivativeReporterPacket c f)) = 0 at hfamily
    have hzero := (WithLp.toLp_eq_zero 2).mp hfamily
    exact congrFun hzero a
  · rintro ⟨c, hfamily, hc⟩
    refine ⟨c, ?_, hc⟩
    change WithLp.toLp 2
      (fun a => report a (finiteDerivativeReporterPacket c f)) = 0
    apply (WithLp.toLp_eq_zero 2).mpr
    funext a
    exact hfamily a

end

end HTGeometry
