import GaloisForLFunctions.HTGeometry.FiniteReporterBlindness
import GaloisForLFunctions.HTGeometry.QuantumGeometricTensorGram
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Gram/Fisher certificate for finite derivative-clock reporters

A finite genetic reporter panel, learned sensor map, or finite-outcome quantum measurement sends
the first `n` derivative observables to vectors `v_i` in an output Hilbert space.  Their Gram matrix
is the static information matrix of this finite observation problem.  Its determinant is nonzero
exactly when the coefficient-to-readout map is injective.

For a constant-coefficient-differentially-transcendental clock, synthesis of the derivative packet
is already injective.  Hence singularity of the reporter Gram matrix is equivalent to the existence
of a genuinely nonzero derivative observable erased by the panel.  This supplies a positive
finite-resolution completeness criterion together with the exact blind-packet alternative.  No
temporal evolution or learned dynamics is assumed.
-/

open scoped BigOperators InnerProductSpace

namespace HTGeometry

noncomputable section

open GaloisForLFunctions Module

/-- Gram/Fisher matrix of the first `n` derivative observables after applying a linear reporter. -/
def finiteDerivativeReporterGram
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (n : ℕ) (f : ℂ → ℂ) (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.gram ℂ (fun i : Fin n ↦ report (iteratedDeriv (i : ℕ) f))

/-- The coefficient reporter map is the linear combination of the reported derivative vectors. -/
theorem finiteDerivativeReporterMap_apply
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (n : ℕ) (f : ℂ → ℂ) (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (c : Fin n → ℂ) :
    finiteDerivativeReporterMap n f report c =
      ∑ i, c i • report (iteratedDeriv (i : ℕ) f) := by
  simp [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis,
    finiteDerivativeReporterPacket, map_sum]

/-- Independence of the reported jets is exactly injectivity of the finite coefficient reporter. -/
theorem linearIndependent_reportedDerivativeJets_iff_injective
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (n : ℕ) (f : ℂ → ℂ) (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    LinearIndependent ℂ
        (fun i : Fin n ↦ report (iteratedDeriv (i : ℕ) f)) ↔
      Function.Injective (finiteDerivativeReporterMap n f report) := by
  constructor
  · intro hli c d hcd
    have hzero : finiteDerivativeReporterMap n f report (c - d) = 0 := by
      rw [map_sub, hcd, sub_self]
    have hcoeff := Fintype.linearIndependent_iff.mp hli (c - d)
    have hcoeffZero : ∀ i, (c - d) i = 0 := by
      apply hcoeff
      rw [finiteDerivativeReporterMap_apply] at hzero
      exact hzero
    funext i
    exact sub_eq_zero.mp (hcoeffZero i)
  · intro hinj
    apply Fintype.linearIndependent_iff.mpr
    intro c hsum
    have hmap : finiteDerivativeReporterMap n f report c = 0 := by
      rw [finiteDerivativeReporterMap_apply]
      exact hsum
    have hc0 : c = 0 := by
      apply hinj
      rw [hmap, map_zero]
    intro i
    exact congrFun hc0 i

/-- **Finite reporter Gram criterion.**  The reporter Gram/Fisher matrix is nonsingular exactly
when the first `n` derivative coefficients are identifiable from the reported values. -/
theorem finiteDerivativeReporterGram_det_ne_zero_iff_injective
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (n : ℕ) (f : ℂ → ℂ) (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    (finiteDerivativeReporterGram n f report).det ≠ 0 ↔
      Function.Injective (finiteDerivativeReporterMap n f report) := by
  rw [finiteDerivativeReporterGram,
    Matrix.det_gram_ne_zero_iff_linearIndependent,
    linearIndependent_reportedDerivativeJets_iff_injective]

/-- For a genuine infinite derivative clock, Gram nonsingularity is equivalent to faithfulness of
the reporter on the entire synthesized `n`-jet packet space. -/
theorem finiteDerivativeReporterGram_det_ne_zero_iff_faithful
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    {n : ℕ} {f : ℂ → ℂ}
    (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    (finiteDerivativeReporterGram n f report).det ≠ 0 ↔
      ∀ c : Fin n → ℂ,
        report (finiteDerivativeReporterPacket c f) = 0 →
          finiteDerivativeReporterPacket c f = 0 := by
  rw [finiteDerivativeReporterGram_det_ne_zero_iff_injective]
  constructor
  · intro hinj c hreport
    have hc0 : c = 0 := by
      apply hinj
      change report (finiteDerivativeReporterPacket c f) =
        report (finiteDerivativeReporterPacket 0 f)
      rw [hreport]
      simp [finiteDerivativeReporterPacket]
    rw [hc0]
    simp [finiteDerivativeReporterPacket]
  · intro hfaithful c d hcd
    have hreport : report (finiteDerivativeReporterPacket (c - d) f) = 0 := by
      have hzero : finiteDerivativeReporterMap n f report (c - d) = 0 := by
        rw [map_sub, hcd, sub_self]
      simpa [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis] using hzero
    have hpacket := hfaithful (c - d) hreport
    have hcoeff : c - d = 0 := by
      apply finiteDerivativeJetSynthesis_injective hf
      change finiteDerivativeReporterPacket (c - d) f =
        finiteDerivativeReporterPacket 0 f
      rw [hpacket]
      simp [finiteDerivativeReporterPacket]
    exact sub_eq_zero.mp hcoeff

/-- **Exact Gram singularity alternative.**  For an infinite derivative clock, singularity of
the finite information matrix is equivalent to a genuinely nonzero derivative packet being
erased by the reporter. -/
theorem finiteDerivativeReporterGram_det_eq_zero_iff_exists_blindPacket
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    {n : ℕ} {f : ℂ → ℂ}
    (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    (finiteDerivativeReporterGram n f report).det = 0 ↔
      ∃ c : Fin n → ℂ,
        report (finiteDerivativeReporterPacket c f) = 0 ∧
          finiteDerivativeReporterPacket c f ≠ 0 := by
  have h := not_congr
    (finiteDerivativeReporterGram_det_ne_zero_iff_faithful (n := n) hf report)
  simp only [not_ne_iff] at h
  push Not at h
  exact h

/-- Output dimension below jet resolution forces singular reporter information, independently of
the source. -/
theorem finiteDerivativeReporterGram_det_eq_zero_of_finrank_lt
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [FiniteDimensional ℂ Y]
    (n : ℕ) (f : ℂ → ℂ) (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (hcapacity : finrank ℂ Y < n) :
    (finiteDerivativeReporterGram n f report).det = 0 := by
  by_contra hdet
  have hli : LinearIndependent ℂ
      (fun i : Fin n ↦ report (iteratedDeriv (i : ℕ) f)) :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mp hdet
  have hbound := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hbound
  omega

/-! ### Reporter fusion: the positive statement beyond finite-panel blindness -/

/-- Pair two reporter panels without imposing an evolution model on the observed clock. -/
def pairedFiniteDerivativeReporter
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (reportY : (ℂ → ℂ) →ₗ[ℂ] Y) (reportZ : (ℂ → ℂ) →ₗ[ℂ] Z) :
    (ℂ → ℂ) →ₗ[ℂ] WithLp 2 (Y × Z) :=
  (WithLp.linearEquiv 2 ℂ (Y × Z)).symm.toLinearMap.comp
    (reportY.prod reportZ)

/-- Coefficient reporting commutes exactly with pairing two panels into their Hilbert `L2`
product. -/
theorem finiteDerivativeReporterMap_paired_apply
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (n : ℕ) (f : ℂ → ℂ)
    (reportY : (ℂ → ℂ) →ₗ[ℂ] Y) (reportZ : (ℂ → ℂ) →ₗ[ℂ] Z) :
    ∀ c : Fin n → ℂ,
      finiteDerivativeReporterMap n f
          (pairedFiniteDerivativeReporter reportY reportZ) c =
        WithLp.toLp 2
          (finiteDerivativeReporterMap n f reportY c,
            finiteDerivativeReporterMap n f reportZ c) := by
  intro c
  rfl

/-- **Fisher/observability information adds under reporter fusion.**  The Gram matrix of the
Hilbert `L2` product panel is the entrywise sum of the two constituent information matrices. -/
theorem finiteDerivativeReporterGram_paired_eq_add
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (n : ℕ) (f : ℂ → ℂ)
    (reportY : (ℂ → ℂ) →ₗ[ℂ] Y) (reportZ : (ℂ → ℂ) →ₗ[ℂ] Z) :
    finiteDerivativeReporterGram n f
        (pairedFiniteDerivativeReporter reportY reportZ) =
      finiteDerivativeReporterGram n f reportY +
        finiteDerivativeReporterGram n f reportZ := by
  ext i j
  simp only [finiteDerivativeReporterGram, Matrix.gram_apply,
    pairedFiniteDerivativeReporter, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, WithLp.coe_symm_linearEquiv,
    WithLp.prod_inner_apply, LinearMap.prod_apply, Function.prod_apply,
    Matrix.add_apply]

/-- **Exact sensor-fusion law.**  The blind subspace of a paired genetic/learned/quantum reporter
panel is the intersection of the blind subspaces of its two constituent panels. -/
theorem ker_finiteDerivativeReporterMap_paired
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (n : ℕ) (f : ℂ → ℂ)
    (reportY : (ℂ → ℂ) →ₗ[ℂ] Y) (reportZ : (ℂ → ℂ) →ₗ[ℂ] Z) :
    LinearMap.ker (finiteDerivativeReporterMap n f
        (pairedFiniteDerivativeReporter reportY reportZ)) =
      LinearMap.ker (finiteDerivativeReporterMap n f reportY) ⊓
        LinearMap.ker (finiteDerivativeReporterMap n f reportZ) := by
  ext c
  simp only [LinearMap.mem_ker, Submodule.mem_inf]
  rw [finiteDerivativeReporterMap_paired_apply]
  simp only [WithLp.toLp_eq_zero, Prod.mk_eq_zero]

/-- A paired panel is informationally complete at jet resolution `n` exactly when the two panels
have no common blind coefficient direction.  Each panel may be singular on its own. -/
theorem finiteDerivativeReporterGram_paired_det_ne_zero_iff_commonKer_eq_bot
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (n : ℕ) (f : ℂ → ℂ)
    (reportY : (ℂ → ℂ) →ₗ[ℂ] Y) (reportZ : (ℂ → ℂ) →ₗ[ℂ] Z) :
    (finiteDerivativeReporterGram n f
        (pairedFiniteDerivativeReporter reportY reportZ)).det ≠ 0 ↔
      LinearMap.ker (finiteDerivativeReporterMap n f reportY) ⊓
          LinearMap.ker (finiteDerivativeReporterMap n f reportZ) = ⊥ := by
  rw [finiteDerivativeReporterGram_det_ne_zero_iff_injective,
    ← LinearMap.ker_eq_bot,
    ker_finiteDerivativeReporterMap_paired]

/-- For a genuine infinite derivative clock, singularity of the fused information matrix is
equivalent to a genuine nonzero derivative observable erased by both panels. -/
theorem finiteDerivativeReporterGram_paired_det_eq_zero_iff_exists_commonBlindPacket
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    {n : ℕ} {f : ℂ → ℂ}
    (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (reportY : (ℂ → ℂ) →ₗ[ℂ] Y) (reportZ : (ℂ → ℂ) →ₗ[ℂ] Z) :
    (finiteDerivativeReporterGram n f
        (pairedFiniteDerivativeReporter reportY reportZ)).det = 0 ↔
      ∃ c : Fin n → ℂ,
        reportY (finiteDerivativeReporterPacket c f) = 0 ∧
          reportZ (finiteDerivativeReporterPacket c f) = 0 ∧
          finiteDerivativeReporterPacket c f ≠ 0 := by
  rw [finiteDerivativeReporterGram_det_eq_zero_iff_exists_blindPacket hf]
  constructor
  · rintro ⟨c, hpair, hc⟩
    change WithLp.toLp 2
      (reportY (finiteDerivativeReporterPacket c f),
        reportZ (finiteDerivativeReporterPacket c f)) = 0 at hpair
    have hzero := (WithLp.toLp_eq_zero 2).mp hpair
    exact ⟨c, (Prod.mk_eq_zero.mp hzero).1, (Prod.mk_eq_zero.mp hzero).2, hc⟩
  · rintro ⟨c, hY, hZ, hc⟩
    refine ⟨c, ?_, hc⟩
    change WithLp.toLp 2
      (reportY (finiteDerivativeReporterPacket c f),
        reportZ (finiteDerivativeReporterPacket c f)) = 0
    simp only [hY, hZ, Prod.mk_zero_zero, WithLp.toLp_zero]

end

end HTGeometry
