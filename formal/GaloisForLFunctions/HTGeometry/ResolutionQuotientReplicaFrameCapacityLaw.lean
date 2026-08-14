import GaloisForLFunctions.HTGeometry.StaticShortcutReplicaProjectorFrameLaw
import Mathlib.Topology.MetricSpace.CoveringNumbers

open scoped BigOperators ComplexConjugate NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite pseudometric space has a nonempty maximal separated set, and maximality makes it a
cover at the same resolution. -/
theorem exists_maximalSeparated_finset_cover
    {I : Type*} [Fintype I] [Nonempty I] [PseudoMetricSpace I]
    (δ : ℝ≥0) :
    ∃ S : Finset I,
      S.Nonempty ∧
      (∀ i : I, ∃ c ∈ S, dist i c ≤ (δ : ℝ)) ∧
      (∀ c ∈ S, ∀ d ∈ S, c ≠ d → (δ : ℝ) < dist c d) := by
  classical
  let A : Set I := Set.univ
  have hpack : Metric.packingNumber δ A ≠ ⊤ := by
    apply ne_of_lt
    refine lt_of_le_of_lt (Metric.packingNumber_le_encard_self A) ?_
    simp [A]
  let T : Set I := Metric.maximalSeparatedSet δ A
  have hTfinite : T.Finite := by
    rw [← Set.encard_ne_top_iff]
    rw [Metric.encard_maximalSeparatedSet hpack]
    exact hpack
  let S : Finset I := hTfinite.toFinset
  have hcover : Metric.IsCover δ A T :=
    Metric.isCover_maximalSeparatedSet hpack
  have hsep : Metric.IsSeparated δ T :=
    Metric.isSeparated_maximalSeparatedSet
  refine ⟨S, ?_, ?_, ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨c, hcT, hic⟩ := hcover (by simp [A] : i ∈ A)
    exact ⟨c, by simpa [S] using hcT⟩
  · intro i
    obtain ⟨c, hcT, hic⟩ := hcover (by simp [A] : i ∈ A)
    refine ⟨c, by simpa [S] using hcT, ?_⟩
    simpa [edist_dist] using hic
  · intro c hc d hd hcd
    have hcT : c ∈ T := by simpa [S] using hc
    have hdT : d ∈ T := by simpa [S] using hd
    have := hsep hcT hdT hcd
    simpa [edist_dist] using this

variable {α : Type*} [Fintype α]

/-- Pure-state normalization expressed by unit diagonal fidelity. -/
def FinitePureStateNormalized (ψ : α → ℂ) : Prop :=
  finitePureStateFidelity ψ ψ = 1

/-- A normalized pure-state projector has unit Hilbert--Schmidt norm. -/
theorem norm_finitePureProjectorEuclidean_sq
    {ψ : α → ℂ} (hψ : FinitePureStateNormalized ψ) :
    ‖finitePureProjectorEuclidean ψ‖ ^ 2 = 1 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [inner_finitePureProjectorEuclidean]
  simpa [FinitePureStateNormalized] using hψ

/-- Projector chordal distance is exactly complementary fidelity. -/
theorem norm_finitePureProjectorEuclidean_sub_sq
    {ψ φ : α → ℂ}
    (hψ : FinitePureStateNormalized ψ)
    (hφ : FinitePureStateNormalized φ) :
    ‖finitePureProjectorEuclidean ψ - finitePureProjectorEuclidean φ‖ ^ 2 =
      2 - 2 * finitePureStateFidelity ψ φ := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  rw [norm_finitePureProjectorEuclidean_sq hψ,
    norm_finitePureProjectorEuclidean_sq hφ,
    inner_finitePureProjectorEuclidean]
  simp
  ring

/-- Complete pair average is controlled by its diagonal and a uniform off-diagonal bound. -/
theorem finite_average_pow_le_diagonal_offDiagonal
    {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (f : C → C → ℝ) (r : ℕ) (κ : ℝ)
    (hf0 : ∀ c d, 0 ≤ f c d)
    (hdiag : ∀ c, f c c = 1)
    (hoff : ∀ c d, c ≠ d → f c d ≤ κ) :
    (∑ c, ∑ d,
        (Fintype.card C : ℝ)⁻¹ * (Fintype.card C : ℝ)⁻¹ * f c d ^ r) ≤
      (Fintype.card C : ℝ)⁻¹ +
        (1 - (Fintype.card C : ℝ)⁻¹) * κ ^ r := by
  classical
  let N : ℝ := Fintype.card C
  let g : C → C → ℝ := fun c d => if c = d then 1 else κ ^ r
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  calc
    (∑ c, ∑ d, N⁻¹ * N⁻¹ * f c d ^ r) ≤
        ∑ c, ∑ d, N⁻¹ * N⁻¹ * g c d := by
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro d hd
      have hinv : 0 ≤ N⁻¹ * N⁻¹ :=
        mul_nonneg (inv_nonneg.mpr hNpos.le) (inv_nonneg.mpr hNpos.le)
      apply mul_le_mul_of_nonneg_left _ hinv
      by_cases hcd : c = d
      · subst d
        simp [g, hdiag]
      · simp only [g, if_neg hcd]
        exact pow_le_pow_left₀ (hf0 c d) (hoff c d hcd) r
    _ = N⁻¹ + (1 - N⁻¹) * κ ^ r := by
      have hinner (c : C) :
          (∑ d, N⁻¹ * N⁻¹ * g c d) =
            N * (N⁻¹ * N⁻¹ * κ ^ r) +
              N⁻¹ * N⁻¹ * (1 - κ ^ r) := by
        calc
          (∑ d, N⁻¹ * N⁻¹ * g c d) =
              ∑ d, (N⁻¹ * N⁻¹ * κ ^ r +
                if c = d then N⁻¹ * N⁻¹ * (1 - κ ^ r) else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            by_cases hcd : c = d
            · simp [g, hcd]
              ring
            · simp [g, hcd]
          _ = N * (N⁻¹ * N⁻¹ * κ ^ r) +
                N⁻¹ * N⁻¹ * (1 - κ ^ r) := by
            rw [Finset.sum_add_distrib]
            simp [N]
      simp_rw [hinner]
      simp [N]
      field_simp
      ring

/-- Every finite pure-state target family admits a maximal resolution packing which also covers
the complete target image at the same Hilbert--Schmidt resolution. -/
theorem exists_resolutionPacking_projector_cover
    {I : Type*} [Fintype I] [Nonempty I]
    (target : I → α → ℂ) (δ : ℝ≥0) :
    ∃ S : Finset I,
      S.Nonempty ∧
      (∀ i : I, ∃ c ∈ S,
        ‖finitePureProjectorEuclidean (target i) -
          finitePureProjectorEuclidean (target c)‖ ≤ (δ : ℝ)) ∧
      (∀ c ∈ S, ∀ d ∈ S, c ≠ d →
        (δ : ℝ) <
          ‖finitePureProjectorEuclidean (target c) -
            finitePureProjectorEuclidean (target d)‖) := by
  let f : I → EuclideanSpace ℂ (α × α) :=
    fun i => finitePureProjectorEuclidean (target i)
  letI : PseudoMetricSpace I := PseudoMetricSpace.induced f inferInstance
  obtain ⟨S, hS, hcover, hsep⟩ :=
    exists_maximalSeparated_finset_cover (I := I) δ
  refine ⟨S, hS, ?_, ?_⟩
  · intro i
    obtain ⟨c, hc, hic⟩ := hcover i
    refine ⟨c, hc, ?_⟩
    change dist (f i) (f c) ≤ (δ : ℝ) at hic
    simpa [f, dist_eq_norm] using hic
  · intro c hc d hd hcd
    have h := hsep c hc d hd hcd
    change (δ : ℝ) < dist (f c) (f d) at h
    simpa [f, dist_eq_norm] using h

/-- A normalized `δ`-separated projector packing has replica frame energy bounded by its diagonal
mass plus exponentially suppressed off-diagonal mass. -/
theorem resolutionPacking_replicaFrameEnergy_le
    {I : Type*} [Fintype I]
    (target : I → α → ℂ) (S : Finset I) (hS : S.Nonempty)
    (hnorm : ∀ i, FinitePureStateNormalized (target i))
    (δ : ℝ≥0)
    (hsep : ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
      (δ : ℝ) <
        ‖finitePureProjectorEuclidean (target c) -
          finitePureProjectorEuclidean (target d)‖)
    (r : ℕ) :
    finitePreparationFrameEnergy
        (fun c : {i // i ∈ S} => finitePureProjectorEuclidean
          (finitePureTensorPower r (target c))) ≤
      (Fintype.card {i // i ∈ S} : ℝ)⁻¹ +
        (1 - (Fintype.card {i // i ∈ S} : ℝ)⁻¹) *
          (1 - (δ : ℝ) ^ 2 / 2) ^ r := by
  classical
  letI : Nonempty {i // i ∈ S} := Finset.nonempty_coe_sort.mpr hS
  rw [finitePreparationFrameEnergy_replicaProjector_eq_averageFidelity]
  apply finite_average_pow_le_diagonal_offDiagonal
  · intro c d
    exact sq_nonneg ‖finiteComplexInner (target c) (target d)‖
  · intro c
    exact hnorm c
  · intro c d hcd
    have hdist := hsep c c.property d d.property (Subtype.coe_ne_coe.mpr hcd)
    have hsquare := norm_finitePureProjectorEuclidean_sub_sq
      (hnorm c) (hnorm d)
    have hδ0 : 0 ≤ (δ : ℝ) := δ.coe_nonneg
    have hD0 : 0 ≤ ‖finitePureProjectorEuclidean (target c) -
        finitePureProjectorEuclidean (target d)‖ := norm_nonneg _
    nlinarith

/-- A maximal resolution packing simultaneously supplies target coverage and the replica-frame
capacity bound. -/
theorem exists_resolutionPacking_replicaFrameEnergy_le
    {I : Type*} [Fintype I] [Nonempty I]
    (target : I → α → ℂ)
    (hnorm : ∀ i, FinitePureStateNormalized (target i))
    (δ : ℝ≥0) (r : ℕ) :
    ∃ S : Finset I,
      S.Nonempty ∧
      (∀ i : I, ∃ c ∈ S,
        ‖finitePureProjectorEuclidean (target i) -
          finitePureProjectorEuclidean (target c)‖ ≤ (δ : ℝ)) ∧
      (∀ c ∈ S, ∀ d ∈ S, c ≠ d →
        (δ : ℝ) <
          ‖finitePureProjectorEuclidean (target c) -
            finitePureProjectorEuclidean (target d)‖) ∧
      finitePreparationFrameEnergy
          (fun c : {i // i ∈ S} => finitePureProjectorEuclidean
            (finitePureTensorPower r (target c))) ≤
        (Fintype.card {i // i ∈ S} : ℝ)⁻¹ +
          (1 - (Fintype.card {i // i ∈ S} : ℝ)⁻¹) *
            (1 - (δ : ℝ) ^ 2 / 2) ^ r := by
  obtain ⟨S, hS, hcover, hsep⟩ :=
    exists_resolutionPacking_projector_cover target δ
  refine ⟨S, hS, hcover, hsep, ?_⟩
  exact resolutionPacking_replicaFrameEnergy_le target S hS hnorm δ hsep r

/-- Once the off-diagonal replica overlap falls below reciprocal packing size, complete frame
energy is at most twice the diagonal mass. -/
theorem resolutionPacking_replicaFrameEnergy_le_two_inv
    {I : Type*} [Fintype I]
    (target : I → α → ℂ) (S : Finset I) (hS : S.Nonempty)
    (hnorm : ∀ i, FinitePureStateNormalized (target i))
    (δ : ℝ≥0)
    (hsep : ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
      (δ : ℝ) <
        ‖finitePureProjectorEuclidean (target c) -
          finitePureProjectorEuclidean (target d)‖)
    (r : ℕ)
    (hreplica : (1 - (δ : ℝ) ^ 2 / 2) ^ r ≤
      (Fintype.card {i // i ∈ S} : ℝ)⁻¹) :
    finitePreparationFrameEnergy
        (fun c : {i // i ∈ S} => finitePureProjectorEuclidean
          (finitePureTensorPower r (target c))) ≤
      2 * (Fintype.card {i // i ∈ S} : ℝ)⁻¹ := by
  letI : Nonempty {i // i ∈ S} := Finset.nonempty_coe_sort.mpr hS
  let N : ℝ := Fintype.card {i // i ∈ S}
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card {i // i ∈ S})
  have hNinv0 : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
  have hNinv1 : N⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hNpos]
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card {i // i ∈ S})
  have hmass0 : 0 ≤ 1 - N⁻¹ := sub_nonneg.mpr hNinv1
  calc
    finitePreparationFrameEnergy
        (fun c : {i // i ∈ S} => finitePureProjectorEuclidean
          (finitePureTensorPower r (target c))) ≤
        N⁻¹ + (1 - N⁻¹) * (1 - (δ : ℝ) ^ 2 / 2) ^ r :=
      resolutionPacking_replicaFrameEnergy_le target S hS hnorm δ hsep r
    _ ≤ N⁻¹ + (1 - N⁻¹) * N⁻¹ := by
      gcongr
    _ ≤ 2 * N⁻¹ := by nlinarith [mul_self_nonneg N⁻¹]

/-- Capturing any original endpoint transfers to a center of a resolution cover, at additive loss
in Hilbert--Schmidt radius. -/
theorem resolutionPacking_completeTarget_transfer
    {I : Type*} [Fintype I]
    (target : I → α → ℂ) (S : Finset I)
    (δ ε : ℝ)
    (hcover : ∀ i : I, ∃ c ∈ S,
      ‖finitePureProjectorEuclidean (target i) -
        finitePureProjectorEuclidean (target c)‖ ≤ δ)
    (x : α → ℂ) (i : I)
    (hcapture : ‖finitePureProjectorEuclidean x -
      finitePureProjectorEuclidean (target i)‖ ≤ ε) :
    ∃ c ∈ S,
      ‖finitePureProjectorEuclidean x -
        finitePureProjectorEuclidean (target c)‖ ≤ ε + δ := by
  obtain ⟨c, hc, hic⟩ := hcover i
  refine ⟨c, hc, ?_⟩
  calc
    ‖finitePureProjectorEuclidean x - finitePureProjectorEuclidean (target c)‖ =
        ‖(finitePureProjectorEuclidean x - finitePureProjectorEuclidean (target i)) +
          (finitePureProjectorEuclidean (target i) -
            finitePureProjectorEuclidean (target c))‖ := by
      apply congrArg norm
      abel
    _ ≤ ‖finitePureProjectorEuclidean x - finitePureProjectorEuclidean (target i)‖ +
        ‖finitePureProjectorEuclidean (target i) -
          finitePureProjectorEuclidean (target c)‖ := norm_add_le _ _
    _ ≤ ε + δ := add_le_add hcapture hic

/-- A projector-radius bound gives its exact fidelity threshold. -/
theorem finitePureStateFidelity_ge_of_projector_distance_le
    {ψ φ : α → ℂ}
    (hψ : FinitePureStateNormalized ψ)
    (hφ : FinitePureStateNormalized φ)
    {ρ : ℝ}
    (hdist : ‖finitePureProjectorEuclidean ψ -
      finitePureProjectorEuclidean φ‖ ≤ ρ) :
    1 - ρ ^ 2 / 2 ≤ finitePureStateFidelity ψ φ := by
  have hsquare := norm_finitePureProjectorEuclidean_sub_sq hψ hφ
  have hD0 : 0 ≤ ‖finitePureProjectorEuclidean ψ -
      finitePureProjectorEuclidean φ‖ := norm_nonneg _
  nlinarith

/-- Resolution-cover transfer also supplies a fidelity certificate for the selected center. -/
theorem resolutionPacking_fidelity_transfer
    {I : Type*} [Fintype I]
    (target : I → α → ℂ) (S : Finset I)
    (hnorm : ∀ i, FinitePureStateNormalized (target i))
    (δ ε : ℝ)
    (hcover : ∀ i : I, ∃ c ∈ S,
      ‖finitePureProjectorEuclidean (target i) -
        finitePureProjectorEuclidean (target c)‖ ≤ δ)
    (x : α → ℂ) (hx : FinitePureStateNormalized x) (i : I)
    (hcapture : ‖finitePureProjectorEuclidean x -
      finitePureProjectorEuclidean (target i)‖ ≤ ε) :
    ∃ c ∈ S,
      ‖finitePureProjectorEuclidean x -
        finitePureProjectorEuclidean (target c)‖ ≤ ε + δ ∧
      1 - (ε + δ) ^ 2 / 2 ≤ finitePureStateFidelity x (target c) := by
  obtain ⟨c, hc, hdist⟩ :=
    resolutionPacking_completeTarget_transfer target S δ ε hcover x i hcapture
  refine ⟨c, hc, hdist, ?_⟩
  exact finitePureStateFidelity_ge_of_projector_distance_le hx (hnorm c) hdist

/-- Under a nonnegative transferred threshold, the fidelity certificate tensorizes to every
replica order. -/
theorem resolutionPacking_replicaFidelity_transfer
    {I : Type*} [Fintype I]
    (target : I → α → ℂ) (S : Finset I)
    (hnorm : ∀ i, FinitePureStateNormalized (target i))
    (δ ε : ℝ)
    (hcover : ∀ i : I, ∃ c ∈ S,
      ‖finitePureProjectorEuclidean (target i) -
        finitePureProjectorEuclidean (target c)‖ ≤ δ)
    (x : α → ℂ) (hx : FinitePureStateNormalized x) (i : I)
    (hcapture : ‖finitePureProjectorEuclidean x -
      finitePureProjectorEuclidean (target i)‖ ≤ ε)
    (r : ℕ)
    (hthreshold : 0 ≤ 1 - (ε + δ) ^ 2 / 2) :
    ∃ c ∈ S,
      ‖finitePureProjectorEuclidean x -
        finitePureProjectorEuclidean (target c)‖ ≤ ε + δ ∧
      (1 - (ε + δ) ^ 2 / 2) ^ r ≤
        finitePureStateFidelity x (target c) ^ r := by
  obtain ⟨c, hc, hdist, hfid⟩ :=
    resolutionPacking_fidelity_transfer target S hnorm δ ε hcover x hx i hcapture
  refine ⟨c, hc, hdist, ?_⟩
  exact pow_le_pow_left₀ hthreshold hfid r

/-- Real Hilbert--Schmidt space occupied by vectorized `r`-replica pure-state projectors. -/
abbrev FinitePureReplicaProjectorSpace (r : ℕ) :=
  EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))

/-- Replica-projector dictionary selected by a finite resolution packing. -/
def resolutionPackingReplicaTarget
    {I : Type*} [Fintype I] (r : ℕ) (target : I → α → ℂ) (S : Finset I) :
    {i // i ∈ S} → FinitePureReplicaProjectorSpace (α := α) r :=
  fun c => finitePureProjectorEuclidean (finitePureTensorPower r (target c))

/-- **Resolution-quotient adaptive observer--spectral law.**  In the inverse-capacity replica
regime, every weighted adaptive shortcut history is bounded by `2/N` times the same
centralizer-centered recurrence energy. -/
theorem adaptive_resolutionPacking_shortcuts_force_recurrence_energy
    {I J : Type*} [Fintype I] [Fintype J]
    (target : I → α → ℂ) (S : Finset I) (hS : S.Nonempty)
    (hnorm : ∀ i, FinitePureStateNormalized (target i))
    (δ : ℝ≥0)
    (hsep : ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
      (δ : ℝ) <
        ‖finitePureProjectorEuclidean (target c) -
          finitePureProjectorEuclidean (target d)‖)
    (r : ℕ)
    (hreplica : (1 - (δ : ℝ) ^ 2 / 2) ^ r ≤
      (Fintype.card {i // i ∈ S} : ℝ)⁻¹)
    (PiOp P : FinitePureReplicaProjectorSpace (α := α) r →L[ℝ]
      FinitePureReplicaProjectorSpace (α := α) r)
    (U : UnitaryFlow ℝ (FinitePureReplicaProjectorSpace (α := α) r))
    (x : FinitePureReplicaProjectorSpace (α := α) r)
    (chosen : J → {i // i ∈ S}) (time : J → ℝ) (w : J → ℝ)
    (hPisa : IsSelfAdjoint PiOp)
    (hPiid : ∀ z, PiOp (PiOp z) = PiOp z)
    (hPiP : ∀ z, PiOp (P z) = PiOp z)
    (hPU : ∀ t z, P (U.op t z) = P z)
    (hUP : ∀ t z, U.op t (P z) = P z)
    (hPiMoment : PiOp
      (finitePreparationMoment (resolutionPackingReplicaTarget r target S)) = PiOp x)
    (hnonneg : ∀ j i, 0 ≤ inner ℝ (U.op (time j) x)
      (resolutionPackingReplicaTarget r target S i))
    {a : ℝ}
    (hcollision : ∀ j, a ≤ inner ℝ (U.op (time j) x)
      (resolutionPackingReplicaTarget r target S (chosen j)))
    (hw : ∀ j, 0 ≤ w j)
    (heta : 0 ≤ (Fintype.card {i // i ∈ S} : ℝ)⁻¹ * a -
      (inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
        inner ℝ (staticMemory PiOp P x)
          (preparationMemory PiOp x
            (finitePreparationMoment (resolutionPackingReplicaTarget r target S))))) :
    ((((Fintype.card {i // i ∈ S} : ℝ)⁻¹ * a -
        (inner ℝ (universalSector PiOp x) (universalSector PiOp x) +
          inner ℝ (staticMemory PiOp P x)
            (preparationMemory PiOp x
              (finitePreparationMoment (resolutionPackingReplicaTarget r target S))))) *
        ∑ j, w j) ^ 2) ≤
      (2 * (Fintype.card {i // i ∈ S} : ℝ)⁻¹) *
        ∑ i, ∑ j, w i * w j *
          inner ℝ (x - P x) (U.op (time j - time i) (x - P x)) := by
  have hmain := adaptive_shortcuts_force_recurrence_energy
    PiOp P U x (resolutionPackingReplicaTarget r target S) chosen time w
    hPisa hPiid hPiP hPU hUP hPiMoment hnonneg hcollision hw heta
  have hframe :
      finitePreparationFrameEnergy (resolutionPackingReplicaTarget r target S) ≤
        2 * (Fintype.card {i // i ∈ S} : ℝ)⁻¹ := by
    change finitePreparationFrameEnergy
        (fun c : {i // i ∈ S} => finitePureProjectorEuclidean
          (finitePureTensorPower r (target c))) ≤
      2 * (Fintype.card {i // i ∈ S} : ℝ)⁻¹
    exact resolutionPacking_replicaFrameEnergy_le_two_inv
      target S hS hnorm δ hsep r hreplica
  have hfactor :
      finitePreparationFrameEnergy (resolutionPackingReplicaTarget r target S) -
          ‖universalSector PiOp x‖ ^ 2 ≤
        2 * (Fintype.card {i // i ∈ S} : ℝ)⁻¹ := by
    exact le_trans (sub_le_self _ (sq_nonneg _)) hframe
  have henergy0 :
      0 ≤ ∑ i, ∑ j, w i * w j *
        inner ℝ (x - P x) (U.op (time j - time i) (x - P x)) := by
    rw [← weightedRecurrenceEnergy_flow_eq_kernel]
    rw [weightedRecurrenceEnergy_eq_norm_sq]
    exact sq_nonneg _
  exact le_trans hmain (mul_le_mul_of_nonneg_right hfactor henergy0)

end

end GaloisForLFunctions.HTGeometry
