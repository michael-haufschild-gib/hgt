import GaloisForLFunctions.HTGeometry.MultivariateAnalyticZeroNull
import GaloisForLFunctions.HTGeometry.RealFiniteAnalyticEscape
import GaloisForLFunctions.HTGeometry.RealAnalyticZeroFiniteness
import GaloisForLFunctions.HTGeometry.DenseNullContinuationSeam
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Good
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Analytic matrix rank stratification

For a globally real-analytic finite square-matrix family, rank defect attains a minimum. Its
minimum-defect stratum is open and dense, while every larger-defect parameter lies in one
nontrivial analytic normal-form minor and is therefore Lebesgue-null. This is the determinantal
engine for resource-filtered relation typicality.
-/

open Set MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem analyticOnNhd_matrix_det
    {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype ι] [DecidableEq ι]
    {A : X → Matrix ι ι ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) univ) :
    AnalyticOnNhd ℝ (fun x => (A x).det) univ := by
  rw [show (fun x => (A x).det) = fun x => ∑ σ : Equiv.Perm ι,
      (Equiv.Perm.sign σ : ℝ) * ∏ i, A x (σ i) i by
    funext x
    exact Matrix.det_apply' (A x)]
  have hterm : ∀ σ : Equiv.Perm ι,
      AnalyticOnNhd ℝ
        (fun x => (Equiv.Perm.sign σ : ℝ) * ∏ i, A x (σ i) i) univ := by
    intro σ
    have hp : AnalyticOnNhd ℝ
        (∏ i, fun x => A x (σ i) i) univ :=
      Finset.analyticOnNhd_prod _ fun i _ => hA (σ i) i
    have hp' : AnalyticOnNhd ℝ (fun x => ∏ i, A x (σ i) i) univ := by
      convert hp using 1
      ext x
      simp
    exact analyticOnNhd_const.mul hp'
  have hsum : AnalyticOnNhd ℝ
      (∑ σ : Equiv.Perm ι,
        fun x => (Equiv.Perm.sign σ : ℝ) * ∏ i, A x (σ i) i) univ :=
    Finset.analyticOnNhd_sum _ fun σ _ => hterm σ
  convert hsum using 1
  ext x
  simp

theorem analyticOnNhd_const_mul_matrix_mul_const_entry
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : ℕ} {A : X → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) univ)
    (V U : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    AnalyticOnNhd ℝ (fun x => (V * A x * U) i j) univ := by
  have hinner : ∀ k : Fin n,
      AnalyticOnNhd ℝ (fun x => ∑ l, V i l * A x l k) univ := by
    intro k
    have hs : AnalyticOnNhd ℝ
        (∑ l : Fin n, fun x => V i l * A x l k) univ :=
      Finset.analyticOnNhd_sum _ fun l _ => analyticOnNhd_const.mul (hA l k)
    convert hs using 1
    ext x
    simp
  have houter : AnalyticOnNhd ℝ
      (fun x => ∑ k, (∑ l, V i l * A x l k) * U k j) univ := by
    have hs : AnalyticOnNhd ℝ
        (∑ k : Fin n, fun x => (∑ l, V i l * A x l k) * U k j) univ :=
      Finset.analyticOnNhd_sum _ fun k _ => (hinner k).mul analyticOnNhd_const
    convert hs using 1
    ext x
    simp
  simpa only [Matrix.mul_apply] using houter

def normalFormPrincipalMinor {X κ : Type*} {n ρ : ℕ}
    (V U : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin n ≃ Fin ρ ⊕ κ)
    (A : X → Matrix (Fin n) (Fin n) ℝ) (x : X) : Matrix (Fin ρ) (Fin ρ) ℝ :=
  (V * A x * U).submatrix
    (fun i => e.symm (Sum.inl i)) (fun i => e.symm (Sum.inl i))

theorem analyticOnNhd_normalFormPrincipalMinor_det
    {X κ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n ρ : ℕ} {A : X → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) univ)
    (V U : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin n ≃ Fin ρ ⊕ κ) :
    AnalyticOnNhd ℝ
      (fun x => (normalFormPrincipalMinor V U e A x).det) univ := by
  apply analyticOnNhd_matrix_det
  intro i j
  exact analyticOnNhd_const_mul_matrix_mul_const_entry hA V U
    (e.symm (Sum.inl i)) (e.symm (Sum.inl j))

theorem normalFormPrincipalMinor_det_eq_one
    {X κ : Type*} {n ρ : ℕ} (A : X → Matrix (Fin n) (Fin n) ℝ) (x : X)
    (V U : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin n ≃ Fin ρ ⊕ κ)
    (h : V * A x * U = (Matrix.fromBlocks 1 0 0 0).submatrix e e) :
    (normalFormPrincipalMinor V U e A x).det = 1 := by
  have hminor : normalFormPrincipalMinor V U e A x = 1 := by
    ext i j
    simp [normalFormPrincipalMinor, h, Matrix.fromBlocks]
  rw [hminor]
  simp

theorem normalFormPrincipalMinor_rank_le_of_det_ne_zero
    {X κ : Type*} {n ρ : ℕ}
    (A : X → Matrix (Fin n) (Fin n) ℝ) (x : X)
    (V U : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin n ≃ Fin ρ ⊕ κ)
    (hV : IsUnit V) (hU : IsUnit U)
    (hdet : (normalFormPrincipalMinor V U e A x).det ≠ 0) :
    ρ ≤ (A x).rank := by
  have hminorUnit : IsUnit (normalFormPrincipalMinor V U e A x) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr hdet)
  have hminorRank : (normalFormPrincipalMinor V U e A x).rank = ρ := by
    simpa using Matrix.rank_of_isUnit _ hminorUnit
  have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 hV
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).1 hU
  have htransRank : (V * A x * U).rank = (A x).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det U (V * A x) hUdet,
      Matrix.rank_mul_eq_right_of_isUnit_det V (A x) hVdet]
  rw [← htransRank, ← hminorRank]
  exact Matrix.rank_submatrix_le _ _ _

def matrixRankDefect {X : Type*} {n : ℕ}
    (A : X → Matrix (Fin n) (Fin n) ℝ) (x : X) : ℕ :=
  n - (A x).rank

def genericMatrixRankDefect {X : Type*} {n : ℕ}
    (A : X → Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  sInf (Set.range (matrixRankDefect A))

theorem exists_matrixRankDefect_eq_generic
    {X : Type*} [Nonempty X] {n : ℕ}
    (A : X → Matrix (Fin n) (Fin n) ℝ) :
    ∃ x, matrixRankDefect A x = genericMatrixRankDefect A := by
  simpa [genericMatrixRankDefect] using
    (Nat.sInf_mem (Set.range_nonempty (matrixRankDefect A)))

theorem genericMatrixRankDefect_le
    {X : Type*} {n : ℕ}
    (A : X → Matrix (Fin n) (Fin n) ℝ) (x : X) :
    genericMatrixRankDefect A ≤ matrixRankDefect A x := by
  exact Nat.sInf_le ⟨x, rfl⟩

/-- A maximal-rank normal-form minor contains every larger-defect parameter in its zero set. -/
theorem matrixRankDefect_exceptional_subset_normalForm_zeroSet
    {X κ : Type*} {n ρ : ℕ} (A : X → Matrix (Fin n) (Fin n) ℝ)
    (x₀ : X) (hx₀ : matrixRankDefect A x₀ = genericMatrixRankDefect A)
    (V U : Matrix (Fin n) (Fin n) ℝ) (e : Fin n ≃ Fin ρ ⊕ κ)
    (hρ : ρ = (A x₀).rank) (hV : IsUnit V) (hU : IsUnit U) :
    {x | genericMatrixRankDefect A < matrixRankDefect A x} ⊆
      {x | (normalFormPrincipalMinor V U e A x).det = 0} := by
  intro x hx
  by_contra hdet
  have hρle := normalFormPrincipalMinor_rank_le_of_det_ne_zero A x V U e hV hU hdet
  have hxrank : (A x).rank ≤ n := Matrix.rank_le_height _
  have hx₀rank : (A x₀).rank ≤ n := Matrix.rank_le_height _
  change genericMatrixRankDefect A < matrixRankDefect A x at hx
  rw [← hx₀] at hx
  simp only [matrixRankDefect] at hx
  omega

theorem analytic_matrixRankDefect_exceptional_volume_zero
    {m n : ℕ} {A : (Fin m → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) univ) :
    volume {x | genericMatrixRankDefect A < matrixRankDefect A x} = 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_matrixRankDefect_eq_generic A
  obtain ⟨V, U, e₀, hV, hU, hnormal₀⟩ := Matrix.exists_rank_normal_form (A x₀)
  let ρ := (A x₀).rank
  have hnormal : V * A x₀ * U = (Matrix.fromBlocks 1 0 0 0).submatrix e₀ e₀ :=
    hnormal₀
  let f : (Fin m → ℝ) → ℝ :=
    fun x => (normalFormPrincipalMinor V U e₀ A x).det
  have hf : AnalyticOnNhd ℝ f univ :=
    analyticOnNhd_normalFormPrincipalMinor_det hA V U e₀
  have hfx₀ : f x₀ ≠ 0 := by
    have hone : f x₀ = 1 := by
      simpa [f, ρ] using
        normalFormPrincipalMinor_det_eq_one A x₀ V U e₀ hnormal
    simp [hone]
  have hsubset : {x | genericMatrixRankDefect A < matrixRankDefect A x} ⊆
      {x | f x = 0} := by
    simpa [f] using matrixRankDefect_exceptional_subset_normalForm_zeroSet
      A x₀ hx₀ V U e₀ (by rfl) hV hU
  exact measure_mono_null hsubset
    (analytic_zero_set_volume_fin m f hf ⟨x₀, hfx₀⟩)

theorem analytic_matrixRankDefect_generic_dense
    {m n : ℕ} {A : (Fin m → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) univ) :
    Dense {x | matrixRankDefect A x = genericMatrixRankDefect A} := by
  have hzero := analytic_matrixRankDefect_exceptional_volume_zero hA
  have hopen : ∀ U : Set (Fin m → ℝ), IsOpen U → U.Nonempty → volume U ≠ 0 := by
    intro U hU hUne
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
    exact ne_of_gt ((KleinbockMargulis.volume_ball_pos x hε).trans_le (measure_mono hball))
  have hdense := GaloisForLFunctions.dense_compl_of_measure_zero_of_open_pos
    volume hzero hopen
  have hsets : {x | genericMatrixRankDefect A < matrixRankDefect A x}ᶜ =
      {x | matrixRankDefect A x = genericMatrixRankDefect A} := by
    ext x
    simp only [mem_compl_iff, mem_setOf_eq, not_lt]
    exact ⟨fun h => le_antisymm h (genericMatrixRankDefect_le A x), fun h => by simp [h]⟩
  rw [← hsets]
  exact hdense

theorem isOpen_analytic_matrixRankDefect_generic
    {m n : ℕ} {A : (Fin m → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) univ) :
    IsOpen {x | matrixRankDefect A x = genericMatrixRankDefect A} := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form (A x)
  let f : (Fin m → ℝ) → ℝ :=
    fun y => (normalFormPrincipalMinor V U e A y).det
  have hf : AnalyticOnNhd ℝ f univ :=
    analyticOnNhd_normalFormPrincipalMinor_det hA V U e
  have hfx : f x ≠ 0 := by
    have hone : f x = 1 := by
      simpa [f] using normalFormPrincipalMinor_det_eq_one A x V U e hnormal
    simp [hone]
  have hopen : IsOpen {y | f y ≠ 0} :=
    isOpen_ne.preimage hf.continuous
  have hsub : {y | f y ≠ 0} ⊆
      {y | matrixRankDefect A y = genericMatrixRankDefect A} := by
    intro y hy
    have hrank := normalFormPrincipalMinor_rank_le_of_det_ne_zero A y V U e hV hU hy
    have hrankx : (A x).rank ≤ n := Matrix.rank_le_height _
    have hranky : (A y).rank ≤ n := Matrix.rank_le_height _
    have hdefle : matrixRankDefect A y ≤ matrixRankDefect A x := by
      simp only [matrixRankDefect]
      omega
    apply le_antisymm
    · rw [hx] at hdefle
      exact hdefle
    · exact genericMatrixRankDefect_le A y
  exact Filter.mem_of_superset (hopen.mem_nhds hfx) hsub

theorem analytic_matrixRankDefect_generic_open_dense_fullMeasure
    {m n : ℕ} {A : (Fin m → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) univ) :
    IsOpen {x | matrixRankDefect A x = genericMatrixRankDefect A} ∧
      Dense {x | matrixRankDefect A x = genericMatrixRankDefect A} ∧
      volume {x | genericMatrixRankDefect A < matrixRankDefect A x} = 0 :=
  ⟨isOpen_analytic_matrixRankDefect_generic hA,
    analytic_matrixRankDefect_generic_dense hA,
    analytic_matrixRankDefect_exceptional_volume_zero hA⟩

/-- In one real analytic parameter, every compact set contains only finitely many exceptional
rank-defect points. This is the locally finite form of card Theorem 2.1(4). -/
theorem analytic_matrixRankDefect_exceptional_inter_compact_finite
    {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) univ)
    {K : Set ℝ} (hK : IsCompact K) :
    (K ∩ {x | genericMatrixRankDefect A < matrixRankDefect A x}).Finite := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_matrixRankDefect_eq_generic A
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form (A x₀)
  let f : ℝ → ℝ := fun x => (normalFormPrincipalMinor V U e A x).det
  have hf : AnalyticOnNhd ℝ f univ :=
    analyticOnNhd_normalFormPrincipalMinor_det hA V U e
  have hfx₀ : f x₀ ≠ 0 := by
    have hone : f x₀ = 1 := by
      simpa [f] using normalFormPrincipalMinor_det_eq_one A x₀ V U e hnormal
    simp [hone]
  have hsubset : {x | genericMatrixRankDefect A < matrixRankDefect A x} ⊆
      {x | f x = 0} := by
    simpa [f] using matrixRankDefect_exceptional_subset_normalForm_zeroSet
      A x₀ hx₀ V U e (by rfl) hV hU
  have hfinite := finite_zeros_of_analyticOnNhd isPreconnected_univ hf
    (Set.mem_univ x₀) hfx₀ hK (Set.subset_univ K)
  apply hfinite.subset
  rintro x ⟨hxK, hx⟩
  exact ⟨hxK, by simpa using hsubset hx⟩

/-- In one real analytic parameter, the exceptional rank-defect set carries the discrete subtype
topology. -/
theorem analytic_matrixRankDefect_exceptional_discreteTopology
    {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) univ) :
    DiscreteTopology {x | genericMatrixRankDefect A < matrixRankDefect A x} := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_matrixRankDefect_eq_generic A
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form (A x₀)
  let f : ℝ → ℝ := fun x => (normalFormPrincipalMinor V U e A x).det
  have hf : AnalyticOnNhd ℝ f univ :=
    analyticOnNhd_normalFormPrincipalMinor_det hA V U e
  have hfx₀ : f x₀ ≠ 0 := by
    have hone : f x₀ = 1 := by
      simpa [f] using normalFormPrincipalMinor_det_eq_one A x₀ V U e hnormal
    simp [hone]
  have hsubset : {x | genericMatrixRankDefect A < matrixRankDefect A x} ⊆
      {x | f x = 0} := by
    simpa [f] using matrixRankDefect_exceptional_subset_normalForm_zeroSet
      A x₀ hx₀ V U e (by rfl) hV hU
  rw [discreteTopology_subtype_iff]
  intro x hx
  have hne := eventually_ne_zero_of_analyticOnNhd isPreconnected_univ hf
    (Set.mem_univ x₀) hfx₀ (Set.mem_univ x)
  rw [← Filter.empty_mem_iff_bot]
  refine Filter.mem_of_superset
    (Filter.inter_mem_inf hne
      (Filter.mem_principal_self {x | genericMatrixRankDefect A < matrixRankDefect A x})) ?_
  rintro z ⟨hzf, hzexc⟩
  exact hzf (hsubset hzexc)

end

end GaloisForLFunctions.HTGeometry
