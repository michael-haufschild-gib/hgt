import GaloisForLFunctions.HTGeometry.SourceGaugeObservabilitySpectrum
import GaloisForLFunctions.HTGeometry.WeakSequentialCompactness
import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow
import GaloisForLFunctions.HTGeometry.CompactAdjoint
import GaloisForLFunctions.HTGeometry.CommutingProjectionIntersectionEnergy
import GaloisForLFunctions.HTGeometry.UnboundedFredholm

noncomputable section

open Complex Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

omit [TopologicalSpace.SeparableSpace H] in
/-- The Gram operator and its original bounded operator have exactly the same kernel. -/
theorem ker_adjoint_comp_self
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : H →L[ℂ] F) :
    LinearMap.ker (((ContinuousLinearMap.adjoint T).comp T : H →L[ℂ] H) : H →ₗ[ℂ] H) =
      LinearMap.ker (T : H →ₗ[ℂ] F) := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    change (ContinuousLinearMap.adjoint T).comp T x = 0 at hx
    have hinner : inner ℂ ((ContinuousLinearMap.adjoint T).comp T x) x =
        inner ℂ (T x) (T x) :=
      ContinuousLinearMap.adjoint_inner_left T x (T x)
    have hzero : inner ℂ (T x) (T x) = 0 := by
      calc
        inner ℂ (T x) (T x) =
            inner ℂ ((ContinuousLinearMap.adjoint T).comp T x) x := hinner.symm
        _ = 0 := by rw [hx, inner_zero_left]
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp hzero
  · intro hx
    change T x = 0 at hx
    change ContinuousLinearMap.adjoint T (T x) = 0
    rw [hx, map_zero]

omit [TopologicalSpace.SeparableSpace H] in
/-- Closed range of the Gram operator forces closed range of the original bounded operator. -/
theorem isClosed_range_of_isClosed_range_adjoint_comp_self
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : H →L[ℂ] F)
    (hclosed : IsClosed (Set.range ((ContinuousLinearMap.adjoint T).comp T))) :
    IsClosed (Set.range T) := by
  let A : H →L[ℂ] H := (ContinuousLinearMap.adjoint T).comp T
  have hker : LinearMap.ker (A : H →ₗ[ℂ] H) =
      LinearMap.ker (T : H →ₗ[ℂ] F) := ker_adjoint_comp_self T
  obtain ⟨c, hc, hbound⟩ :=
    (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range A).mpr hclosed
  apply (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range T).mp
  let M : ℝ := max ‖ContinuousLinearMap.adjoint T‖ 1
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨c / M, div_pos hc hM, ?_⟩
  intro x hx
  have hxA : x ∈ (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ := by
    rwa [hker]
  have hlower : c * ‖x‖ ≤ ‖A x‖ := hbound x hxA
  have hupper : ‖A x‖ ≤ M * ‖T x‖ := by
    calc
      ‖A x‖ = ‖ContinuousLinearMap.adjoint T (T x)‖ := rfl
      _ ≤ ‖ContinuousLinearMap.adjoint T‖ * ‖T x‖ :=
        (ContinuousLinearMap.adjoint T).le_opNorm (T x)
      _ ≤ M * ‖T x‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hb : c * ‖x‖ ≤ M * ‖T x‖ := hlower.trans hupper
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  simpa only [mul_comm] using hb

/-- The range of identity plus a compact operator on a separable complex Hilbert space is closed.
This is the closed-range half of the Fredholm alternative, proved from weak sequential compactness. -/
theorem isClosed_range_one_add_of_isCompactOperator
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    IsClosed (Set.range (1 + K : H →L[ℂ] H)) := by
  let A : H →L[ℂ] H := 1 + K
  let T := ContinuousLinearMap.transverseRestriction A
  have hTinj : Function.Injective T :=
    ContinuousLinearMap.transverseRestriction_injective A
  by_contra hclosed
  have hTclosed : ¬ IsClosed (Set.range T) := by
    rw [ContinuousLinearMap.range_transverseRestriction]
    exact hclosed
  obtain ⟨u, huNorm, huZero⟩ :=
    (GaloisForLFunctions.hasApproximateUnitKernel_iff_not_isClosed_range
      T hTinj).mpr hTclosed
  obtain ⟨w, phi, hphi, _hwNorm, hweak⟩ :=
    exists_weaklyConvergent_subseq_of_bounded
      (fun n => ((u n : (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H)) 1
      (fun n => by simpa using (le_of_eq (huNorm n)))
  have hAuZero : Tendsto
      (fun n => A ((u (phi n) : (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H))
      atTop (nhds 0) := by
    change Tendsto ((fun n => T (u n)) ∘ phi) atTop (nhds 0)
    exact huZero.comp hphi.tendsto_atTop
  have hwKer : w ∈ LinearMap.ker (A : H →ₗ[ℂ] H) := by
    rw [LinearMap.mem_ker]
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    have hweakA := hweak (ContinuousLinearMap.adjoint A (A w))
    have hstrongA : Tendsto
        (fun n => inner ℂ
          (A ((u (phi n) : (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H)) (A w))
        atTop (nhds 0) := by
      simpa using hAuZero.inner (𝕜 := ℂ)
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (A w : H)) atTop (nhds (A w)))
    have hweakA' : Tendsto
        (fun n => inner ℂ
          (A ((u (phi n) : (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H)) (A w))
        atTop (nhds (inner ℂ (A w) (A w))) := by
      simpa only [ContinuousLinearMap.adjoint_inner_right] using hweakA
    exact tendsto_nhds_unique hweakA' hstrongA
  have hwPerp : w ∈ (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    have hseqZero : ∀ n,
        inner ℂ (((u (phi n) :
          (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H)) z = 0 := by
      intro n
      have hzorth := (Submodule.mem_orthogonal
        (LinearMap.ker (A : H →ₗ[ℂ] H))
        (((u (phi n) : (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H))).mp
          (u (phi n)).2 z hz
      rw [← inner_conj_symm, hzorth, map_zero]
    have hlim := hweak z
    have hzero : Tendsto
        (fun n => inner ℂ
          (((u (phi n) : (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H)) z)
        atTop (nhds 0) := by
      simpa only [hseqZero] using tendsto_const_nhds
    have hwz : inner ℂ w z = 0 := tendsto_nhds_unique hlim hzero
    rw [← inner_conj_symm, hwz, map_zero]
  have hwZero : w = 0 := by
    have hww := (Submodule.mem_orthogonal
      (LinearMap.ker (A : H →ₗ[ℂ] H)) w).mp hwPerp w hwKer
    exact inner_self_eq_zero.mp hww
  have hweakZero : ∀ y : H, Tendsto
      (fun n => inner ℂ
        (((u (phi n) : (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H)) y)
      atTop (nhds 0) := by
    intro y
    simpa [hwZero] using hweak y
  obtain ⟨C, hCcompact, hKC⟩ := hK.image_closedBall_subset_compact 1
  have hKmem : ∀ n,
      K (((u (phi n) : (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H)) ∈ C := by
    intro n
    apply hKC
    refine ⟨((u (phi n) : (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H), ?_, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using le_of_eq (huNorm (phi n))
  obtain ⟨y, _hyC, psi, hpsi, hKlim⟩ := hCcompact.tendsto_subseq hKmem
  have hyZero : y = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    have hweakK := (hweakZero (ContinuousLinearMap.adjoint K y)).comp
      hpsi.tendsto_atTop
    have hweakK' : Tendsto
        (fun n => inner ℂ
          (K (((u (phi (psi n)) :
            (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H))) y)
        atTop (nhds 0) := by
      change Tendsto
        ((fun n => inner ℂ
          (K (((u (phi n) :
            (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H))) y) ∘ psi)
        atTop (nhds 0)
      simpa only [ContinuousLinearMap.adjoint_inner_right] using hweakK
    have hstrongK' : Tendsto
        (fun n => inner ℂ
          (K (((u (phi (psi n)) :
            (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H))) y)
        atTop (nhds (inner ℂ y y)) := by
      simpa [Function.comp_def] using hKlim.inner (𝕜 := ℂ)
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (y : H)) atTop (nhds y))
    exact tendsto_nhds_unique hstrongK' hweakK'
  have hKZero : Tendsto
      (fun n => K (((u (phi (psi n)) :
        (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H)))
      atTop (nhds 0) := by
    simpa [hyZero, Function.comp_def] using hKlim
  have hAuZero' := hAuZero.comp hpsi.tendsto_atTop
  have huStrongZero : Tendsto
      (fun n => (((u (phi (psi n)) :
        (LinearMap.ker (A : H →ₗ[ℂ] H))ᗮ) : H)))
      atTop (nhds 0) := by
    have hsub := hAuZero'.sub hKZero
    convert hsub using 1
    · funext n
      simp [A]
    · simp
  have huNormZero := tendsto_zero_iff_norm_tendsto_zero.mp huStrongZero
  have huNormOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    simpa only [Submodule.norm_coe, huNorm] using huNormZero
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds huNormOne)

omit [TopologicalSpace.SeparableSpace H] in
/-- The kernel of identity plus a compact operator is finite dimensional. -/
theorem finiteDimensional_ker_one_add_of_isCompactOperator
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    FiniteDimensional ℂ
      (LinearMap.ker ((1 + K : H →L[ℂ] H) : H →ₗ[ℂ] H)) := by
  apply finiteDimensional_of_isCompactOperator_of_bounded_below hK
    (LinearMap.ker ((1 + K : H →L[ℂ] H) : H →ₗ[ℂ] H))
    (ContinuousLinearMap.isClosed_ker (1 + K)) (c := 1) one_pos
  intro x hx
  have hzero : (1 + K : H →L[ℂ] H) x = 0 := hx
  have hsum : x + K x = 0 := by
    simpa only [add_apply, one_apply_eq_self] using hzero
  have hKx : K x = -x := by
    calc
      K x = (x + K x) - x := by abel
      _ = 0 - x := congrArg (fun z => z - x) hsum
      _ = -x := zero_sub x
  rw [hKx, norm_neg, one_mul]

/-- Identity plus a compact operator has finite-dimensional cokernel. -/
theorem finiteDimensional_coker_one_add_of_isCompactOperator
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    FiniteDimensional ℂ
      (H ⧸ LinearMap.range ((1 + K : H →L[ℂ] H) : H →ₗ[ℂ] H)) := by
  let A : H →L[ℂ] H := 1 + K
  have hclosed : IsClosed (Set.range A) :=
    isClosed_range_one_add_of_isCompactOperator K hK
  letI : (LinearMap.range (A : H →ₗ[ℂ] H)).HasOrthogonalProjection :=
    hasOrthogonalProjection_of_isClosed hclosed
  have hKadj : IsCompactOperator (ContinuousLinearMap.adjoint K) :=
    isCompactOperator_adjoint_rectangular K hK
  have hfdAdj : FiniteDimensional ℂ
      (LinearMap.ker ((ContinuousLinearMap.adjoint A : H →L[ℂ] H) : H →ₗ[ℂ] H)) := by
    have hfd := finiteDimensional_ker_one_add_of_isCompactOperator
      (ContinuousLinearMap.adjoint K) hKadj
    have hAdjA : ContinuousLinearMap.adjoint A =
        1 + ContinuousLinearMap.adjoint K := by
      let adj : (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] (H →L[ℂ] H) :=
        ContinuousLinearMap.adjoint
      change adj (1 + K) = 1 + adj K
      rw [adj.map_add, ContinuousLinearMap.adjoint_one]
    rw [hAdjA]
    exact hfd
  haveI hfdOrth : FiniteDimensional ℂ
      (LinearMap.range (A : H →ₗ[ℂ] H))ᗮ := by
    rw [ContinuousLinearMap.orthogonal_range A]
    exact hfdAdj
  exact (Submodule.quotientEquivOrthogonal
    (LinearMap.range (A : H →ₗ[ℂ] H))).toLinearEquiv.symm.finiteDimensional

end GaloisForLFunctions.HTGeometry
