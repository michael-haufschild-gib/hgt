import GaloisForLFunctions.HTGeometry.FiniteAndersonRecurrenceLocalitySeparationLaw
import GaloisForLFunctions.HTGeometry.FiniteSpectralClusterUniformLocalityLaw
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw

/-!
# Finite Anderson all-time recurrence--locality separation

Near a simple atomic Hamiltonian, spectral projections remain close to
coordinate projections.  Their mixing budget bounds every Schrödinger
transition amplitude uniformly over the entire real time axis.  Density of
maximally projective onsite packets then selects the same positive-hopping
Hamiltonian with both all-time locality and maximal global recurrence rank.
-/

open Set Filter Topology
open NormedSpace
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every off-diagonal transition amplitude is smaller than `ε` for every
real time. -/
def AllTimeOffDiagonalSmall
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (g : ℝ) (p : Fin n → ℝ) (ε : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ t : ℝ,
    ‖finiteAndersonEvolution T g p t i j‖ < ε

/-- Canonical real spectrum of a scaled finite Anderson Hamiltonian. -/
def scaledFiniteAndersonCanonicalEnergy
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) (g : ℝ) (p : Fin n → ℝ) :
    Fin n → ℝ :=
  (finiteAndersonHamiltonian_isHermitian
    ((g : ℂ) • T)
    (hT.smul (by rw [isSelfAdjoint_iff]; simp)) p).eigenvalues

/-- Maximal projective onsite packets explore the full torus of relative
phases in completed time. -/
theorem scaledFiniteAnderson_projectivePhase_tendsto_haar
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) (g : ℝ) (p : Fin n → ℝ)
    (hp : p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT g)
    (reference : Fin n) :
    Tendsto
      (finiteTorusPhaseProbabilityMeasure
        (projectiveFrequency
          (scaledFiniteAndersonCanonicalEnergy T hT g p)
          reference))
      atTop
      (𝓝
        (finiteTorusHaarProbabilityMeasure
          {i : Fin n // i ≠ reference})) := by
  apply projectivePhaseProbabilityMeasure_tendsto_haar
  simpa [scaledFiniteAndersonCanonicalEnergy,
    scaledFiniteAndersonProjectiveMaximalSet,
    finiteAndersonProjectiveMaximalSet] using hp

theorem continuous_scaledFiniteAndersonHamiltonian
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    Continuous
      (fun q : ℝ × (Fin n → ℝ) =>
        scaledFiniteAndersonHamiltonian T q.1 q.2) := by
  unfold scaledFiniteAndersonHamiltonian
  fun_prop

/-- Real hopping scale and real onsite potential preserve Hermiticity. -/
theorem scaledFiniteAndersonHamiltonian_isHermitian_allTime
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) (g : ℝ) (p : Fin n → ℝ) :
    (scaledFiniteAndersonHamiltonian T g p).IsHermitian := by
  rw [scaledFiniteAndersonHamiltonian_eq]
  exact finiteAndersonHamiltonian_isHermitian ((g : ℂ) • T)
    (hT.smul (by rw [isSelfAdjoint_iff]; simp)) p

/-- Finite Hermitian Schrödinger evolution is unitary. -/
theorem finiteAndersonEvolution_mem_unitaryGroup_allTime
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) (g : ℝ) (p : Fin n → ℝ)
    (t : ℝ) :
    finiteAndersonEvolution T g p t ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  let H := scaledFiniteAndersonHamiltonian T g p
  let A := (-(Complex.I * (t : ℂ))) • H
  have hH : H.IsHermitian :=
    scaledFiniteAndersonHamiltonian_isHermitian_allTime T hT g p
  have hskew : A.conjTranspose = -A := by
    dsimp only [A]
    rw [Matrix.conjTranspose_smul, hH.eq]
    ext i j
    simp
  have hstar :
      (exp A).conjTranspose = exp (-A) := by
    rw [← Matrix.exp_conjTranspose, hskew]
  rw [finiteAndersonEvolution]
  change exp A ∈ Matrix.unitaryGroup (Fin n) ℂ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    hstar, ← Matrix.exp_add_of_commute A (-A)
      (Commute.refl A).neg_right, add_neg_cancel, exp_zero]

/-- Every entry of finite Hermitian Schrödinger evolution has modulus at
most one. -/
theorem finiteAndersonEvolution_entry_norm_le_one
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) (g : ℝ) (p : Fin n → ℝ)
    (t : ℝ) (a b : Fin n) :
    ‖finiteAndersonEvolution T g p t a b‖ ≤ 1 :=
  entry_norm_bound_of_unitary
    (finiteAndersonEvolution_mem_unitaryGroup_allTime
      T hT g p t) a b

/-- A separated cluster certificate plus a small projection mixing budget
implies all-time transition suppression. -/
theorem allTimeOffDiagonalSmall_of_cluster_mixing
    {n : ℕ} [Nonempty (Fin n)]
    {energy : Fin n → ℝ} {δ ε : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → 4 * δ ≤ |energy i - energy j|)
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (g : ℝ) (p : Fin n → ℝ)
    (hcluster :
      SpectrallyClusteredAround energy δ
        (scaledFiniteAndersonHamiltonian T g p))
    (hmixing :
      ∀ i j, i ≠ j →
        spectralProjectionMixingBudget
          (fun k => spectralClusterProjection energy δ
            (scaledFiniteAndersonHamiltonian T g p) k)
          i j < ε) :
    AllTimeOffDiagonalSmall T g p ε := by
  intro i j hij t
  let H := scaledFiniteAndersonHamiltonian T g p
  let P : Fin n → Matrix (Fin n) (Fin n) ℂ :=
    fun k => spectralClusterProjection energy δ H k
  let U := finiteAndersonEvolution T g p t
  have hH : H.IsHermitian :=
    scaledFiniteAndersonHamiltonian_isHermitian_allTime T hT g p
  have hsum : ∑ k, P k = 1 :=
    spectralClusterProjection_sum_eq_one hH hδ hsep hcluster
  have hidempotent : ∀ k, P k * P k = P k :=
    fun k =>
      spectralClusterProjection_mul_self hδ hsep hcluster k
  have hcommute : ∀ k, Commute (P k) U := by
    intro k
    exact spectralClusterProjection_commute_exp hH k
  have hentry : ∀ a b, ‖U a b‖ ≤ 1 :=
    fun a b =>
      finiteAndersonEvolution_entry_norm_le_one T hT g p t a b
  apply norm_apply_lt_of_projection_mixingBudget_lt
    P U hsum hidempotent hcommute hentry
  exact hmixing i j hij

/-- All-time locality is a joint neighborhood property at every separated
atomic onsite packet. -/
theorem eventually_joint_allTimeOffDiagonalSmall
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (energy : Fin n → ℝ) {δ ε : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → 4 * δ ≤ |energy i - energy j|)
    (hε : 0 < ε) :
    ∀ᶠ q : ℝ × (Fin n → ℝ) in 𝓝 (0, energy),
      AllTimeOffDiagonalSmall T q.1 q.2 ε := by
  let A : (ℝ × (Fin n → ℝ)) →
      Matrix (Fin n) (Fin n) ℂ :=
    fun q => scaledFiniteAndersonHamiltonian T q.1 q.2
  have hAcont : ContinuousAt A (0, energy) :=
    (continuous_scaledFiniteAndersonHamiltonian T).continuousAt
  have hHermitian : ∀ q, (A q).IsHermitian :=
    fun q =>
      scaledFiniteAndersonHamiltonian_isHermitian_allTime
        T hT q.1 q.2
  have hA0 :
      A (0, energy) =
        Matrix.diagonal (fun i => (energy i : ℂ)) := by
    simp [A, scaledFiniteAndersonHamiltonian]
  have hnear :=
    eventually_all_spectralProjectionMixingBudget_lt
      hδ hsep hε hAcont hHermitian hA0
  filter_upwards [hnear] with q hq
  exact allTimeOffDiagonalSmall_of_cluster_mixing
    hδ hsep T hT q.1 q.2 hq.1 hq.2

/-- Every injective finite real packet admits a positive uniform separation
scale. -/
theorem exists_positive_four_mul_le_abs_sub
    {n : ℕ} (energy : Fin n → ℝ)
    (hinjective : Function.Injective energy) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ i j, i ≠ j → 4 * δ ≤ |energy i - energy j| := by
  by_cases hsub : Subsingleton (Fin n)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i j hij
    exact (hij (hsub.elim i j)).elim
  · letI : Nontrivial (Fin n) :=
      not_subsingleton_iff_nontrivial.mp hsub
    let pairs : Finset (Fin n × Fin n) :=
      (Finset.univ.product Finset.univ).filter fun q => q.1 ≠ q.2
    let gaps : Finset ℝ :=
      pairs.image fun q => |energy q.1 - energy q.2|
    obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin n)
    have hpairs : (i, j) ∈ pairs := by
      simp [pairs, hij]
    have hgaps : |energy i - energy j| ∈ gaps := by
      exact Finset.mem_image.2 ⟨(i, j), hpairs, rfl⟩
    have hgne : gaps.Nonempty := ⟨_, hgaps⟩
    let d : ℝ := gaps.min' hgne
    have hdmem : d ∈ gaps := Finset.min'_mem gaps hgne
    obtain ⟨q, hqpairs, hqd⟩ := Finset.mem_image.1 hdmem
    have hqne : q.1 ≠ q.2 := by
      simpa [pairs] using hqpairs
    have hdpos : 0 < d := by
      rw [← hqd]
      exact abs_pos.mpr (sub_ne_zero.mpr (hinjective.ne hqne))
    refine ⟨d / 4, by positivity, ?_⟩
    intro a b hab
    have habpairs : (a, b) ∈ pairs := by
      simp [pairs, hab]
    have habgaps : |energy a - energy b| ∈ gaps :=
      Finset.mem_image.2 ⟨(a, b), habpairs, rfl⟩
    have hmin : d ≤ |energy a - energy b| :=
      Finset.min'_le gaps _ habgaps
    convert hmin using 1
    ring

/-- **Finite Anderson all-time recurrence--locality separation law.**
For every Hermitian hopping matrix and separated atomic packet, one can
choose positive hopping and an onsite potential so that:

1. the canonical spectrum has maximal projective rational rank; and
2. every off-diagonal transition amplitude remains below `ε` for all
   real times.
-/
theorem exists_finiteAnderson_maximalProjective_allTimeLocalized
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (energy : Fin n → ℝ) {δ ε : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → 4 * δ ≤ |energy i - energy j|)
    (hε : 0 < ε) :
    ∃ g : ℝ, ∃ p : Fin n → ℝ,
      0 < g ∧
      p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT g ∧
      AllTimeOffDiagonalSmall T g p ε := by
  let s : Set (ℝ × (Fin n → ℝ)) :=
    {q | AllTimeOffDiagonalSmall T q.1 q.2 ε}
  have hs : s ∈ 𝓝 (0, energy) :=
    eventually_joint_allTimeOffDiagonalSmall
      T hT energy hδ hsep hε
  exact exists_positive_dense_fiber_of_mem_nhds_prod
    energy s hs
    (scaledFiniteAndersonProjectiveMaximalSet T hT)
    (fun g _hg => scaledFiniteAndersonProjectiveMaximalSet_dense T hT g)

/-- Injectivity of the chosen atomic onsite packet is the only spectral
separation assumption needed by the all-time law. -/
theorem exists_finiteAnderson_maximalProjective_allTimeLocalized_of_injective
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (energy : Fin n → ℝ) (hinjective : Function.Injective energy)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ, ∃ p : Fin n → ℝ,
      0 < g ∧
      p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT g ∧
      AllTimeOffDiagonalSmall T g p ε := by
  obtain ⟨δ, hδ, hsep⟩ :=
    exists_positive_four_mul_le_abs_sub energy hinjective
  exact exists_finiteAnderson_maximalProjective_allTimeLocalized
    T hT energy hδ hsep hε

/-- Every off-diagonal transition amplitude remains below its own prescribed
positive tolerance for all real times. -/
def AllTimeOffDiagonalBelow
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (g : ℝ) (p : Fin n → ℝ)
    (bound : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ t : ℝ,
    ‖finiteAndersonEvolution T g p t i j‖ < bound i j

/-- A finite family of strictly positive off-diagonal tolerances admits one
strictly positive uniform lower bound. -/
theorem exists_positive_uniform_offDiagonal_bound
    {n : ℕ} (bound : Fin n → Fin n → ℝ)
    (hbound : ∀ i j, i ≠ j → 0 < bound i j) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ i j, i ≠ j → ε ≤ bound i j := by
  by_cases hsub : Subsingleton (Fin n)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i j hij
    exact (hij (hsub.elim i j)).elim
  · letI : Nontrivial (Fin n) :=
      not_subsingleton_iff_nontrivial.mp hsub
    let pairs : Finset (Fin n × Fin n) :=
      (Finset.univ.product Finset.univ).filter fun q => q.1 ≠ q.2
    let values : Finset ℝ :=
      pairs.image fun q => bound q.1 q.2
    obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin n)
    have hpairs : (i, j) ∈ pairs := by
      simp [pairs, hij]
    have hvalues : bound i j ∈ values := by
      exact Finset.mem_image.2 ⟨(i, j), hpairs, rfl⟩
    have hvne : values.Nonempty := ⟨_, hvalues⟩
    let ε : ℝ := values.min' hvne
    have hεmem : ε ∈ values := Finset.min'_mem values hvne
    obtain ⟨q, hqpairs, hqε⟩ := Finset.mem_image.1 hεmem
    have hqne : q.1 ≠ q.2 := by
      simpa [pairs] using hqpairs
    have hεpos : 0 < ε := by
      rw [← hqε]
      exact hbound q.1 q.2 hqne
    refine ⟨ε, hεpos, ?_⟩
    intro a b hab
    have habpairs : (a, b) ∈ pairs := by
      simp [pairs, hab]
    have habvalues : bound a b ∈ values :=
      Finset.mem_image.2 ⟨(a, b), habpairs, rfl⟩
    exact Finset.min'_le values _ habvalues

/-- **Arbitrary finite Anderson locality-profile law.**
For any prescribed positive off-diagonal envelope, the same positive-hopping
Hamiltonian can have maximal projective recurrence rank while every
transition amplitude stays below that envelope for all real times. -/
theorem exists_finiteAnderson_maximalProjective_allTimeBelow_of_injective
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (energy : Fin n → ℝ) (hinjective : Function.Injective energy)
    (bound : Fin n → Fin n → ℝ)
    (hbound : ∀ i j, i ≠ j → 0 < bound i j) :
    ∃ g : ℝ, ∃ p : Fin n → ℝ,
      0 < g ∧
      p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT g ∧
      AllTimeOffDiagonalBelow T g p bound := by
  obtain ⟨ε, hε, hεbound⟩ :=
    exists_positive_uniform_offDiagonal_bound bound hbound
  obtain ⟨g, p, hg, hp, hsmall⟩ :=
    exists_finiteAnderson_maximalProjective_allTimeLocalized_of_injective
      T hT energy hinjective hε
  refine ⟨g, p, hg, hp, ?_⟩
  intro i j hij t
  exact (hsmall i j hij t).trans_le (hεbound i j hij)

/-- Every positive exponential spatial envelope is compatible, in finite
volume, with maximal projective recurrence rank and positive hopping. -/
theorem
    exists_finiteAnderson_maximalProjective_exponentialLocality_of_injective
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (energy : Fin n → ℝ) (hinjective : Function.Injective energy)
    (distance : Fin n → Fin n → ℝ)
    {C μ : ℝ} (hC : 0 < C) (_hμ : 0 < μ) :
    ∃ g : ℝ, ∃ p : Fin n → ℝ,
      0 < g ∧
      p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT g ∧
      ∀ i j, i ≠ j → ∀ t : ℝ,
        ‖finiteAndersonEvolution T g p t i j‖ <
          C * Real.exp (-μ * distance i j) := by
  apply exists_finiteAnderson_maximalProjective_allTimeBelow_of_injective
    T hT energy hinjective
  intro i j hij
  exact mul_pos hC (Real.exp_pos _)

/-- Dividing the full positive-hopping Hamiltonian by its hopping scale
fixes the hopping coefficient at one and divides every onsite energy by the
same scale. -/
theorem scaledFiniteAndersonHamiltonian_inv_smul
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    {g : ℝ} (hg : g ≠ 0) (p : Fin n → ℝ) :
    scaledFiniteAndersonHamiltonian T 1 (fun i => g⁻¹ * p i) =
      ((g⁻¹ : ℝ) : ℂ) • scaledFiniteAndersonHamiltonian T g p := by
  have hgC : (g : ℂ) ≠ 0 := by
    exact_mod_cast hg
  ext i j
  by_cases hij : i = j
  · subst j
    simp [scaledFiniteAndersonHamiltonian]
    field_simp [hgC]
  · simp [scaledFiniteAndersonHamiltonian, hij]
    field_simp [hgC]

/-- Fixing hopping strength at one only rescales the time variable. -/
theorem finiteAndersonEvolution_fixed_eq_rescaled
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    {g : ℝ} (hg : g ≠ 0) (p : Fin n → ℝ) (t : ℝ) :
    finiteAndersonEvolution T 1 (fun i => g⁻¹ * p i) t =
      finiteAndersonEvolution T g p (g⁻¹ * t) := by
  rw [finiteAndersonEvolution, finiteAndersonEvolution,
    scaledFiniteAndersonHamiltonian_inv_smul T hg p]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- Maximal projective spectral rank survives the same conversion from a
positive hopping scale to fixed hopping strength. -/
theorem scaledFiniteAndersonProjectiveMaximalSet_to_fixed
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) {g : ℝ} (hg : g ≠ 0)
    (p : Fin n → ℝ)
    (hp : p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT g) :
    (fun i => g⁻¹ * p i) ∈
      scaledFiniteAndersonProjectiveMaximalSet T hT 1 := by
  let H := scaledFiniteAndersonHamiltonian T g p
  let hH : H.IsHermitian :=
    scaledFiniteAndersonHamiltonian_isHermitian_allTime T hT g p
  let q : Fin n → ℝ := fun i => g⁻¹ * p i
  let Hfixed := scaledFiniteAndersonHamiltonian T 1 q
  let hHfixed : Hfixed.IsHermitian :=
    scaledFiniteAndersonHamiltonian_isHermitian_allTime T hT 1 q
  have hmatrix : Hfixed = ((g⁻¹ : ℝ) : ℂ) • H := by
    exact scaledFiniteAndersonHamiltonian_inv_smul T hg p
  have hscaledHermitian :
      (((g⁻¹ : ℝ) : ℂ) • H).IsHermitian :=
    hH.smul (by rw [isSelfAdjoint_iff]; simp)
  have hpH : MaximallyProjectiveEnergy hH.eigenvalues := by
    let hCanonical :=
      finiteAndersonHamiltonian_isHermitian
        ((g : ℂ) • T)
        (hT.smul (by rw [isSelfAdjoint_iff]; simp)) p
    have hpCanonical :
        MaximallyProjectiveEnergy hCanonical.eigenvalues := by
      exact hp
    have heigen :
        hH.eigenvalues = hCanonical.eigenvalues := by
      apply
        (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
          hH hCanonical).2
      rfl
    rw [heigen]
    exact hpCanonical
  have hmaxScaled :=
    maximallyProjectiveEnergy_eigenvalues_real_smul
      H hH (inv_ne_zero hg) hscaledHermitian hpH
  have heigen :
      hHfixed.eigenvalues = hscaledHermitian.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        hHfixed hscaledHermitian).2
    exact congrArg Matrix.charpoly hmatrix
  change MaximallyProjectiveEnergy hHfixed.eigenvalues
  rw [heigen]
  exact hmaxScaled

/-- **Fixed-hopping finite Anderson locality-profile law.**
For every fixed finite Hermitian hopping matrix and every positive spatial
envelope, some onsite potential gives both maximal projective recurrence
rank and all-time transition suppression below that envelope. No
small-hopping qualifier remains in the conclusion. -/
theorem exists_finiteAnderson_fixedHopping_maximalProjective_allTimeBelow
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (energy : Fin n → ℝ) (hinjective : Function.Injective energy)
    (bound : Fin n → Fin n → ℝ)
    (hbound : ∀ i j, i ≠ j → 0 < bound i j) :
    ∃ p : Fin n → ℝ,
      p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT 1 ∧
      AllTimeOffDiagonalBelow T 1 p bound := by
  obtain ⟨g, p, hg, hp, hsmall⟩ :=
    exists_finiteAnderson_maximalProjective_allTimeBelow_of_injective
      T hT energy hinjective bound hbound
  let q : Fin n → ℝ := fun i => g⁻¹ * p i
  refine ⟨q, ?_, ?_⟩
  · exact scaledFiniteAndersonProjectiveMaximalSet_to_fixed
      T hT (ne_of_gt hg) p hp
  · intro i j hij t
    rw [finiteAndersonEvolution_fixed_eq_rescaled
      T (ne_of_gt hg) p t]
    exact hsmall i j hij (g⁻¹ * t)

/-- Fixed hopping is compatible with every positive finite-volume
exponential spatial envelope and maximal projective recurrence rank. -/
theorem
    exists_finiteAnderson_fixedHopping_maximalProjective_exponentialLocality
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (energy : Fin n → ℝ) (hinjective : Function.Injective energy)
    (distance : Fin n → Fin n → ℝ)
    {C μ : ℝ} (hC : 0 < C) (_hμ : 0 < μ) :
    ∃ p : Fin n → ℝ,
      p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT 1 ∧
      ∀ i j, i ≠ j → ∀ t : ℝ,
        ‖finiteAndersonEvolution T 1 p t i j‖ <
          C * Real.exp (-μ * distance i j) := by
  apply exists_finiteAnderson_fixedHopping_maximalProjective_allTimeBelow
    T hT energy hinjective
  intro i j hij
  exact mul_pos hC (Real.exp_pos _)

/-- The auxiliary separated atomic packet can be chosen canonically; it is
not an assumption on the fixed-hopping Hamiltonian in the conclusion. -/
theorem exists_finiteAnderson_fixedHopping_maximalProjective_allTimeBelow_any
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (bound : Fin n → Fin n → ℝ)
    (hbound : ∀ i j, i ≠ j → 0 < bound i j) :
    ∃ p : Fin n → ℝ,
      p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT 1 ∧
      AllTimeOffDiagonalBelow T 1 p bound := by
  apply exists_finiteAnderson_fixedHopping_maximalProjective_allTimeBelow
    T hT (fun i : Fin n => (i : ℝ))
  · intro i j hij
    apply Fin.ext
    change (i.val : ℝ) = j.val at hij
    exact_mod_cast hij
  · exact hbound

/-- **Unconditional fixed-hopping exponential separation law.**
Every finite Hermitian hopping matrix admits an onsite potential with
maximal projective recurrence rank and any prescribed positive exponential
all-time transition envelope. -/
theorem
    exists_finiteAnderson_fixedHopping_maximalProjective_exponentialLocality_any
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (distance : Fin n → Fin n → ℝ)
    {C μ : ℝ} (hC : 0 < C) (_hμ : 0 < μ) :
    ∃ p : Fin n → ℝ,
      p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT 1 ∧
      ∀ i j, i ≠ j → ∀ t : ℝ,
        ‖finiteAndersonEvolution T 1 p t i j‖ <
          C * Real.exp (-μ * distance i j) := by
  apply exists_finiteAnderson_fixedHopping_maximalProjective_allTimeBelow_any
    T hT
  intro i j hij
  exact mul_pos hC (Real.exp_pos _)

/-- One fixed-hopping Hamiltonian simultaneously satisfies the exponential
all-time spatial envelope and full-projective-torus Haar completion. -/
theorem
    exists_finiteAnderson_fixedHopping_exponentialLocality_fullHaar
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian)
    (distance : Fin n → Fin n → ℝ)
    {C μ : ℝ} (hC : 0 < C) (hμ : 0 < μ) :
    ∃ p : Fin n → ℝ,
      p ∈ scaledFiniteAndersonProjectiveMaximalSet T hT 1 ∧
      (∀ i j, i ≠ j → ∀ t : ℝ,
        ‖finiteAndersonEvolution T 1 p t i j‖ <
          C * Real.exp (-μ * distance i j)) ∧
      ∀ reference : Fin n,
        Tendsto
          (finiteTorusPhaseProbabilityMeasure
            (projectiveFrequency
              (scaledFiniteAndersonCanonicalEnergy T hT 1 p)
              reference))
          atTop
          (𝓝
            (finiteTorusHaarProbabilityMeasure
              {i : Fin n // i ≠ reference})) := by
  obtain ⟨p, hp, hlocal⟩ :=
    exists_finiteAnderson_fixedHopping_maximalProjective_exponentialLocality_any
      T hT distance hC hμ
  exact ⟨p, hp, hlocal,
    fun reference =>
      scaledFiniteAnderson_projectivePhase_tendsto_haar
        T hT 1 p hp reference⟩

end

end GaloisForLFunctions.HTGeometry
