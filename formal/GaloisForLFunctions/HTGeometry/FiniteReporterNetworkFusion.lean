import GaloisForLFunctions.HTGeometry.FiniteReporterConditionalInformation
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

/-- Fuse a family of Hilbert-valued reporters into its `L2` product. -/
def finiteFamilyDerivativeReporter
    {ι : Type*}
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

/-- **Exact finite-network capacity balance.**  Visible coefficient capacity of the fused network
plus the dimension of the coefficient space invisible to every component is exactly the jet
resolution.  Thus fusion loses no directions except the common blind intersection. -/
theorem finiteDerivativeReporterMap_family_capacity_balance
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (n : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    finrank ℂ (LinearMap.range (finiteDerivativeReporterMap n f
        (finiteFamilyDerivativeReporter report))) +
      finrank ℂ ((⨅ a, LinearMap.ker (finiteDerivativeReporterMap n f (report a))) :
        Submodule ℂ (Fin n → ℂ)) = n := by
  rw [← ker_finiteDerivativeReporterMap_family]
  exact finiteDerivativeReporterMap_rank_nullity n f (finiteFamilyDerivativeReporter report)

/-! ## Sequential information fusion -/

/-- **Common-predictor classification for fused innovation.**  Conditional information of the
fused network vanishes exactly when one coefficient packet predicts the newest reading for every
panel simultaneously.  Individual panel redundancies with different prediction coefficients are
not enough; the dependence relation must align across the network. -/
theorem finiteDerivativeReporterConditionalInformation_family_eq_zero_iff_exists_commonPrediction
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (N : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    finiteDerivativeReporterConditionalInformation N f
        (finiteFamilyDerivativeReporter report) = 0 ↔
      ∃ c : Fin N → ℂ, ∀ a,
        ∑ i, c i • report a (iteratedDeriv (i : ℕ) f) =
          report a (iteratedDeriv N f) := by
  rw [finiteDerivativeReporterConditionalInformation_eq_zero_iff]
  constructor
  · intro hmem
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
    refine ⟨c, fun a => ?_⟩
    have hc' := congrArg WithLp.ofLp hc
    have hfun :
        (∑ i, c i • fun a => report a (iteratedDeriv (i : ℕ) f)) =
          fun a => report a (iteratedDeriv N f) := by
      simpa [finiteFamilyDerivativeReporter_apply] using hc'
    simpa [Finset.sum_apply] using congrFun hfun a
  · rintro ⟨c, hc⟩
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
    refine ⟨c, ?_⟩
    apply WithLp.ofLp_injective 2
    funext a
    simpa [finiteFamilyDerivativeReporter_apply, Finset.sum_apply] using hc a

/-- **Network rank-stagnation classification.**  The fused visible coefficient space fails to
grow at the next derivative order exactly when one coefficient packet predicts that newest
reading in every panel simultaneously. -/
theorem finiteDerivativeReporterMap_family_finrank_succ_eq_iff_exists_commonPrediction
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (N : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    finrank ℂ (LinearMap.range (finiteDerivativeReporterMap (N + 1) f
        (finiteFamilyDerivativeReporter report))) =
        finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f
          (finiteFamilyDerivativeReporter report))) ↔
      ∃ c : Fin N → ℂ, ∀ a,
        ∑ i, c i • report a (iteratedDeriv (i : ℕ) f) =
          report a (iteratedDeriv N f) := by
  rw [← finiteDerivativeReporterConditionalInformation_eq_zero_iff_finrank_range_eq,
    finiteDerivativeReporterConditionalInformation_family_eq_zero_iff_exists_commonPrediction]

/-- **Exact network innovation/rank law.**  The fused visible coefficient capacity grows by one
exactly when no common coefficient packet predicts the newest reading across all panels.  Panels
may each be individually redundant; only a shared prediction prevents a fused rank gain. -/
theorem finiteDerivativeReporterMap_family_finrank_succ_eq_add_one_iff_not_exists_commonPrediction
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (N : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    finrank ℂ (LinearMap.range (finiteDerivativeReporterMap (N + 1) f
        (finiteFamilyDerivativeReporter report))) =
        finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f
          (finiteFamilyDerivativeReporter report))) + 1 ↔
      ¬ ∃ c : Fin N → ℂ, ∀ a,
        ∑ i, c i • report a (iteratedDeriv (i : ℕ) f) =
          report a (iteratedDeriv N f) := by
  rw [← finiteDerivativeReporterConditionalInformation_pos_iff_finrank_range_succ_eq_add_one]
  have hzero :=
    finiteDerivativeReporterConditionalInformation_family_eq_zero_iff_exists_commonPrediction
      N f report
  have hnonneg := finiteDerivativeReporterConditionalInformation_nonneg
    N f (finiteFamilyDerivativeReporter report)
  constructor
  · intro hpos hexists
    exact (ne_of_gt hpos) (hzero.mpr hexists)
  · intro hnot
    apply lt_of_le_of_ne hnonneg
    intro hzero'
    exact hnot (hzero.mp hzero'.symm)

/-- Fused zero innovation forces zero innovation in every component, with a common dependence
relation supplied by the network theorem above. -/
theorem finiteDerivativeReporterConditionalInformation_component_eq_zero_of_family
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (N : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a)
    (hzero : finiteDerivativeReporterConditionalInformation N f
      (finiteFamilyDerivativeReporter report) = 0) (a : ι) :
    finiteDerivativeReporterConditionalInformation N f (report a) = 0 := by
  obtain ⟨c, hc⟩ :=
    (finiteDerivativeReporterConditionalInformation_family_eq_zero_iff_exists_commonPrediction
      N f report).mp hzero
  apply (finiteDerivativeReporterConditionalInformation_eq_zero_iff
    N f (report a)).mpr
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  exact ⟨c, hc a⟩

/-- Any component carrying a new derivative innovation forces the fused network to carry that
innovation as well. -/
theorem finiteDerivativeReporterConditionalInformation_family_pos_of_component
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (N : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) (a : ι)
    (hpos : 0 < finiteDerivativeReporterConditionalInformation N f (report a)) :
    0 < finiteDerivativeReporterConditionalInformation N f
      (finiteFamilyDerivativeReporter report) := by
  rw [finiteDerivativeReporterConditionalInformation_pos_iff] at hpos ⊢
  intro hfamily
  apply hpos
  obtain ⟨c, hc⟩ :=
    (finiteDerivativeReporterConditionalInformation_family_eq_zero_iff_exists_commonPrediction
      N f report).mp
      ((finiteDerivativeReporterConditionalInformation_eq_zero_iff
        N f (finiteFamilyDerivativeReporter report)).mpr hfamily)
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  exact ⟨c, hc a⟩

/-- A one-dimensional visible-rank gain in any component remains a one-dimensional gain after
finite-family fusion. -/
theorem finiteDerivativeReporterMap_family_finrank_succ_eq_add_one_of_component
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (N : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) (a : ι)
    (hcomponent :
      finrank ℂ (LinearMap.range (finiteDerivativeReporterMap (N + 1) f (report a))) =
        finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f (report a))) + 1) :
    finrank ℂ (LinearMap.range (finiteDerivativeReporterMap (N + 1) f
        (finiteFamilyDerivativeReporter report))) =
      finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f
        (finiteFamilyDerivativeReporter report))) + 1 := by
  apply (finiteDerivativeReporterConditionalInformation_pos_iff_finrank_range_succ_eq_add_one
    N f (finiteFamilyDerivativeReporter report)).mp
  apply finiteDerivativeReporterConditionalInformation_family_pos_of_component N f report a
  exact (finiteDerivativeReporterConditionalInformation_pos_iff_finrank_range_succ_eq_add_one
    N f (report a)).mpr hcomponent

/-- A reporter component that identifies the whole `N`-coefficient block makes the fused network
identify it as well. -/
theorem finiteDerivativeReporterGram_family_det_ne_zero_of_component
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (N : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) (a : ι)
    (hcomponent : (finiteDerivativeReporterGram N f (report a)).det ≠ 0) :
    (finiteDerivativeReporterGram N f
      (finiteFamilyDerivativeReporter report)).det ≠ 0 := by
  rw [finiteDerivativeReporterGram_det_ne_zero_iff_forall_conditionalInformation_pos]
    at hcomponent ⊢
  intro k hk
  exact finiteDerivativeReporterConditionalInformation_family_pos_of_component
    k f report a (hcomponent k hk)

/-- Consequently, singular fused information forces every component Gram block to be singular. -/
theorem finiteDerivativeReporterGram_component_det_eq_zero_of_family
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (N : ℕ) (f : ℂ → ℂ)
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a)
    (hfamily : (finiteDerivativeReporterGram N f
      (finiteFamilyDerivativeReporter report)).det = 0) (a : ι) :
    (finiteDerivativeReporterGram N f (report a)).det = 0 := by
  by_contra hcomponent
  exact finiteDerivativeReporterGram_family_det_ne_zero_of_component
    N f report a hcomponent hfamily

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
