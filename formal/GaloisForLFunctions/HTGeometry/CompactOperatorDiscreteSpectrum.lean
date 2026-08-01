import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Discreteness of the nonzero spectrum of a compact symmetric operator

A compact symmetric operator on an inner product space has only finitely many eigenvalues outside
any ball around the origin, hence countably many eigenvalues in total, and by the Fredholm
alternative the same holds for its spectrum.

The mechanism is orthogonality rather than the Riesz lemma: eigenvectors of a symmetric operator
belonging to distinct eigenvalues are orthogonal, so unit eigenvectors `w m`, `w n` for distinct
eigenvalues satisfy

`‖T (w m) - T (w n)‖ ≥ |⟪T (w m) - T (w n), w m⟫| = ‖mu m‖ ≥ eps`,

by Cauchy--Schwarz.  Infinitely many such eigenvalues would produce a sequence in the compact
closure of the image of the unit ball with no Cauchy subsequence.
-/

namespace GaloisForLFunctions.HTGeometry

open Module.End Filter Topology
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Eigenvectors of a symmetric operator for distinct eigenvalues are orthogonal. -/
theorem inner_eq_zero_of_hasEigenvector_of_ne {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {mu nu : 𝕜} {v w : E} (hv : HasEigenvector T mu v) (hw : HasEigenvector T nu w)
    (hmn : mu ≠ nu) : ⟪v, w⟫_𝕜 = 0 :=
  hT.orthogonalFamily_eigenspaces hmn ⟨v, hv.1⟩ ⟨w, hw.1⟩

/-- **Discrete nonzero point spectrum.**  A compact symmetric operator has only finitely many
eigenvalues of norm at least any positive bound. -/
theorem finite_setOf_hasEigenvalue_norm_ge {T : E →ₗ[𝕜] E}
    (hT : IsCompactOperator T) (hsymm : T.IsSymmetric) {eps : ℝ} (heps : 0 < eps) :
    {mu : 𝕜 | HasEigenvalue T mu ∧ eps ≤ ‖mu‖}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set S : Set 𝕜 := {mu : 𝕜 | HasEigenvalue T mu ∧ eps ≤ ‖mu‖} with hS
  let g : ℕ ↪ S := Set.Infinite.natEmbedding S hinf
  have hev : ∀ n : ℕ, HasEigenvalue T ((g n : 𝕜)) := fun n => (g n).2.1
  choose v hv using fun n : ℕ => (hev n).exists_hasEigenvector
  have hvne : ∀ n, v n ≠ 0 := fun n => (hv n).2
  have hvnorm : ∀ n, ‖v n‖ ≠ 0 := fun n => norm_ne_zero_iff.mpr (hvne n)
  have hunit : ∀ n : ℕ, ∃ u : E, HasEigenvector T ((g n : 𝕜)) u ∧ ‖u‖ = 1 := by
    intro n
    refine ⟨((‖v n‖ : 𝕜))⁻¹ • v n, ⟨Submodule.smul_mem _ _ (hv n).1, ?_⟩, ?_⟩
    · exact smul_ne_zero (inv_ne_zero (by exact_mod_cast hvnorm n)) (hvne n)
    · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
      exact inv_mul_cancel₀ (hvnorm n)
  choose w hweig hnorm using hunit
  have hdist : ∀ m n : ℕ, m ≠ n → eps ≤ ‖T (w m) - T (w n)‖ := by
    intro m n hmn
    have hne : ((g m : 𝕜)) ≠ ((g n : 𝕜)) := by
      intro h
      exact hmn (g.injective (Subtype.ext h))
    have hTm : T (w m) = ((g m : 𝕜)) • w m := mem_eigenspace_iff.mp (hweig m).1
    have hTn : T (w n) = ((g n : 𝕜)) • w n := mem_eigenspace_iff.mp (hweig n).1
    have hnm : ⟪w n, w m⟫_𝕜 = 0 :=
      inner_eq_zero_of_hasEigenvector_of_ne hsymm (hweig n) (hweig m) hne.symm
    have hself : ⟪w m, w m⟫_𝕜 = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hnorm m]
      norm_num
    have hinner : ⟪T (w m) - T (w n), w m⟫_𝕜 = (starRingEnd 𝕜) ((g m : 𝕜)) := by
      rw [inner_sub_left, hTm, hTn, inner_smul_left, inner_smul_left, hself, hnm]
      ring
    have hcs := norm_inner_le_norm (𝕜 := 𝕜) (T (w m) - T (w n)) (w m)
    rw [hinner, hnorm m, mul_one, RCLike.norm_conj] at hcs
    exact le_trans (g m).2.2 hcs
  have hKcompact : IsCompact (closure (T '' Metric.closedBall (0 : E) 1)) :=
    hT.isCompact_closure_image_closedBall 1
  have hmem : ∀ n : ℕ, T (w n) ∈ closure (T '' Metric.closedBall (0 : E) 1) := by
    intro n
    refine subset_closure ⟨w n, ?_, rfl⟩
    simp [Metric.mem_closedBall, hnorm n]
  obtain ⟨a, -, phi, hphi, hlim⟩ := hKcompact.tendsto_subseq hmem
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (eps / 2) (by linarith)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (by omega)
  have hne : phi N ≠ phi (N + 1) := (hphi (by omega : N < N + 1)).ne
  have hbig := hdist (phi N) (phi (N + 1)) hne
  have htri : dist (T (w (phi N))) (T (w (phi (N + 1)))) ≤
      dist (T (w (phi N))) a + dist a (T (w (phi (N + 1)))) := dist_triangle _ _ _
  rw [dist_comm a] at htri
  rw [dist_eq_norm] at htri
  simp only [Function.comp_apply] at h1 h2
  linarith

/-- The eigenvalues of a compact symmetric operator form a countable set. -/
theorem countable_setOf_hasEigenvalue {T : E →ₗ[𝕜] E}
    (hT : IsCompactOperator T) (hsymm : T.IsSymmetric) :
    {mu : 𝕜 | HasEigenvalue T mu}.Countable := by
  have hsub : {mu : 𝕜 | HasEigenvalue T mu} ⊆
      {0} ∪ ⋃ n : ℕ, {mu : 𝕜 | HasEigenvalue T mu ∧ (1 / (n + 1 : ℝ)) ≤ ‖mu‖} := by
    intro mu hmu
    by_cases h0 : mu = 0
    · exact Or.inl h0
    · refine Or.inr (Set.mem_iUnion.mpr ?_)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr h0)
      exact ⟨n, hmu, hn.le⟩
  refine Set.Countable.mono hsub (Set.Countable.union (Set.countable_singleton 0) ?_)
  exact Set.countable_iUnion fun n =>
    (finite_setOf_hasEigenvalue_norm_ge hT hsymm (by positivity)).countable

section Spectrum

variable [CompleteSpace E]

/-- **Discrete nonzero spectrum.**  Through the Fredholm alternative, a compact symmetric
continuous operator has only finitely many spectral points of norm at least any positive bound. -/
theorem finite_setOf_mem_spectrum_norm_ge {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hsymm : (T : E →ₗ[𝕜] E).IsSymmetric)
    {eps : ℝ} (heps : 0 < eps) :
    {mu : 𝕜 | mu ∈ spectrum 𝕜 T ∧ eps ≤ ‖mu‖}.Finite := by
  refine Set.Finite.subset (finite_setOf_hasEigenvalue_norm_ge hT hsymm heps) ?_
  rintro mu ⟨hspec, hnorm⟩
  have h0 : mu ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    linarith
  exact ⟨(IsCompactOperator.hasEigenvalue_iff_mem_spectrum hT h0).mpr hspec, hnorm⟩

/-- The spectrum of a compact symmetric continuous operator is countable. -/
theorem countable_spectrum_of_isCompactOperator {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hsymm : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (spectrum 𝕜 T).Countable := by
  have hsub : spectrum 𝕜 T ⊆
      {0} ∪ ⋃ n : ℕ, {mu : 𝕜 | mu ∈ spectrum 𝕜 T ∧ (1 / (n + 1 : ℝ)) ≤ ‖mu‖} := by
    intro mu hmu
    by_cases h0 : mu = 0
    · exact Or.inl h0
    · refine Or.inr (Set.mem_iUnion.mpr ?_)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr h0)
      exact ⟨n, hmu, hn.le⟩
  refine Set.Countable.mono hsub (Set.Countable.union (Set.countable_singleton 0) ?_)
  exact Set.countable_iUnion fun n =>
    (finite_setOf_mem_spectrum_norm_ge hT hsymm (by positivity)).countable

end Spectrum

end GaloisForLFunctions.HTGeometry
