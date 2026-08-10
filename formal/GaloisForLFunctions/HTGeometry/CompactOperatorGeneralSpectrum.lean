import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Discreteness of the nonzero spectrum of a general compact operator

The existing compact-spectrum lane in this project treats symmetric operators.  The Hedenmalm
source inverse is compact but not symmetric, so its determinant multiplicities require the
general Banach-space statement: only finitely many eigenvalues can stay a positive distance from
zero.

The proof is the classical Riesz-lemma argument.  Distinct eigenvectors are linearly independent.
Their finite initial spans form a strictly increasing invariant flag.  Riesz vectors in successive
flag quotients have unit norm and remain uniformly separated after applying the compact operator,
contradicting sequential compactness.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Module.End Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Discrete nonzero point spectrum, without normality.**  A compact complex operator has only
finitely many eigenvalues whose norms exceed any fixed positive threshold. -/
theorem finite_setOf_hasEigenvalue_norm_ge_general {T : E →L[ℂ] E}
    (hT : IsCompactOperator T) {eps : ℝ} (heps : 0 < eps) :
    {mu : ℂ | HasEigenvalue (T : E →ₗ[ℂ] E) mu ∧ eps ≤ ‖mu‖}.Finite := by
  classical
  by_contra hinf
  rw [Set.not_finite] at hinf
  let S : Set ℂ := {mu : ℂ | HasEigenvalue (T : E →ₗ[ℂ] E) mu ∧ eps ≤ ‖mu‖}
  let g : ℕ ↪ S := Set.Infinite.natEmbedding S hinf
  let lam : ℕ → ℂ := fun n ↦ (g n : ℂ)
  have hlam_ge (n : ℕ) : eps ≤ ‖lam n‖ := (g n).2.2
  have hlam_ne (n : ℕ) : lam n ≠ 0 := by
    intro hn
    simpa [hn] using (lt_of_lt_of_le heps (hlam_ge n)).ne'
  have hev (n : ℕ) : HasEigenvalue (T : E →ₗ[ℂ] E) (lam n) := (g n).2.1
  choose v hv using fun n : ℕ ↦ (hev n).exists_hasEigenvector
  have hvne (n : ℕ) : v n ≠ 0 := (hv n).2
  let w : ℕ → E := fun n ↦ ((‖v n‖ : ℂ)⁻¹) • v n
  have hweig (n : ℕ) : HasEigenvector (T : E →ₗ[ℂ] E) (lam n) (w n) := by
    refine ⟨Submodule.smul_mem _ _ (hv n).1, ?_⟩
    exact smul_ne_zero (inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr (hvne n))) (hvne n)
  have hwnorm (n : ℕ) : ‖w n‖ = 1 := by
    simp only [w, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hvne n))
  have hlam_inj : Function.Injective lam := by
    intro m n hmn
    exact g.injective (Subtype.ext hmn)
  have hli : LinearIndependent ℂ w :=
    Module.End.eigenvectors_linearIndependent' (T : E →ₗ[ℂ] E) lam hlam_inj w hweig

  let V (n : ℕ) : Submodule ℂ E :=
    Submodule.span ℂ (Set.range fun i : Fin n ↦ w (i : ℕ))
  have hV_mono {m n : ℕ} (hmn : m ≤ n) : V m ≤ V n := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, lt_of_lt_of_le i.isLt hmn⟩, rfl⟩
  have hV_closed (n : ℕ) : IsClosed (V n : Set E) := by
    letI : FiniteDimensional ℂ (V n) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range fun i : Fin n ↦ w (i : ℕ))
    exact Submodule.closed_of_finiteDimensional (V n)
  have hw_mem_succ (n : ℕ) : w n ∈ V (n + 1) := by
    exact Submodule.subset_span ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
  have hw_not_mem (n : ℕ) : w n ∉ V n := by
    intro hn
    apply hli.notMem_span n
    apply Submodule.span_mono (R := ℂ) ?_ hn
    rintro _ ⟨i, rfl⟩
    refine ⟨(i : ℕ), ?_, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_lt i.isLt
  have hT_mem (n : ℕ) {x : E} (hx : x ∈ V n) : T x ∈ V n := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨i, rfl⟩
        have heq : T (w (i : ℕ)) = lam (i : ℕ) • w (i : ℕ) := by
          simpa using mem_eigenspace_iff.mp (hweig (i : ℕ)).1
        rw [heq]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y hx hy ihx ihy => simpa using Submodule.add_mem (V n) ihx ihy
    | smul c x hx ih => simpa [map_smul] using Submodule.smul_mem (V n) c ih
  have hdefect (n : ℕ) {x : E} (hx : x ∈ V (n + 1)) :
      T x - lam n • x ∈ V n := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨i, rfl⟩
        change T (w (i : ℕ)) - lam n • w (i : ℕ) ∈ V n
        have heq : T (w (i : ℕ)) = lam (i : ℕ) • w (i : ℕ) := by
          simpa using mem_eigenspace_iff.mp (hweig (i : ℕ)).1
        rw [heq]
        by_cases hi : (i : ℕ) = n
        · simp [hi]
        · have hil : (i : ℕ) < n := lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hi
          exact Submodule.sub_mem _
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hil⟩, rfl⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hil⟩, rfl⟩))
    | zero => simp
    | add x y hx hy ihx ihy =>
        simpa [map_add, smul_add, add_sub_add_comm] using Submodule.add_mem (V n) ihx ihy
    | smul c x hx ih =>
        simpa [map_smul, smul_sub, smul_smul, mul_comm] using
          Submodule.smul_mem (V n) c ih

  have hriesz (n : ℕ) :
      ∃ x ∈ V (n + 1), ‖x‖ = 1 ∧ ∀ y ∈ V n, (1 / 2 : ℝ) ≤ ‖x - y‖ := by
    have hclosed : IsClosed
        ((V n).comap (V (n + 1)).subtype : Set (V (n + 1))) := by
      simpa using! (hV_closed n).preimage_val
    have hproper : ∃ x : V (n + 1), x ∉ (V n).comap (V (n + 1)).subtype := by
      refine ⟨⟨w n, hw_mem_succ n⟩, ?_⟩
      simpa [Submodule.mem_comap] using hw_not_mem n
    obtain ⟨x, hxnot, hxnorm, hxfar⟩ :=
      riesz_lemma_of_lt_one hclosed hproper (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨x, x.2, hxnorm, ?_⟩
    intro y hy
    have hy' : (⟨y, hV_mono (Nat.le_succ n) hy⟩ : V (n + 1)) ∈
        (V n).comap (V (n + 1)).subtype := hy
    simpa using hxfar ⟨y, hV_mono (Nat.le_succ n) hy⟩ hy'
  choose x hxV hxnorm hxfar using hriesz

  have hsep_lt {m n : ℕ} (hmn : m < n) :
      eps / 2 ≤ ‖T (x n) - T (x m)‖ := by
    let q : E := T (x n) - lam n • x n
    have hq : q ∈ V n := hdefect n (hxV n)
    have hxm : x m ∈ V n := hV_mono (Nat.succ_le_of_lt hmn) (hxV m)
    have hTxm : T (x m) ∈ V n := hT_mem n hxm
    let y : E := T (x m) - q
    have hy : y ∈ V n := Submodule.sub_mem _ hTxm hq
    have hyinv : (lam n)⁻¹ • y ∈ V n := Submodule.smul_mem _ _ hy
    have hfar := hxfar n ((lam n)⁻¹ • y) hyinv
    have heq : T (x n) - T (x m) = lam n • (x n - (lam n)⁻¹ • y) := by
      dsimp [q, y]
      rw [smul_sub, smul_smul, mul_inv_cancel₀ (hlam_ne n), one_smul]
      abel
    rw [heq, norm_smul]
    calc
      eps / 2 ≤ ‖lam n‖ * (1 / 2 : ℝ) := by
        exact div_le_iff₀ (by norm_num : (0 : ℝ) < 2) |>.2 (by simpa using hlam_ge n)
      _ ≤ ‖lam n‖ * ‖x n - (lam n)⁻¹ • y‖ :=
        mul_le_mul_of_nonneg_left hfar (norm_nonneg _)
  have hsep (m n : ℕ) (hmn : m ≠ n) : eps / 2 ≤ ‖T (x m) - T (x n)‖ := by
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · simpa [norm_sub_rev] using hsep_lt hlt
    · exact hsep_lt hgt

  have hcompact : IsCompact (closure (T '' Metric.closedBall (0 : E) 1)) :=
    hT.isCompact_closure_image_closedBall 1
  have hmem (n : ℕ) : T (x n) ∈ closure (T '' Metric.closedBall (0 : E) 1) := by
    refine subset_closure ⟨x n, ?_, rfl⟩
    simp [Metric.mem_closedBall, hxnorm n]
  obtain ⟨a, -, phi, hphi, hlim⟩ := hcompact.tendsto_subseq hmem
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (eps / 4) (by positivity)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (by omega)
  have hne : phi N ≠ phi (N + 1) := (hphi (by omega : N < N + 1)).ne
  have hbig := hsep (phi N) (phi (N + 1)) hne
  have htri : dist (T (x (phi N))) (T (x (phi (N + 1)))) ≤
      dist (T (x (phi N))) a + dist a (T (x (phi (N + 1)))) := dist_triangle _ _ _
  rw [dist_comm a, dist_eq_norm] at htri
  simp only [Function.comp_apply] at h1 h2
  linarith

/-- A generalized eigenspace for a nonzero eigenvalue lies in the range of the operator.  This
algebraic fact is what removes the zero-padding directions from finite-section multiplicity
computations. -/
theorem maxGenEigenspace_le_range_of_ne_zero {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (f : Module.End K V) {mu : K} (hmu : mu ≠ 0) :
    f.maxGenEigenspace mu ≤ LinearMap.range f := by
  intro x hx
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f mu x).mp hx
  let g : Module.End K V := f - mu • 1
  have aux : ∀ (n : ℕ) (y : V), (g ^ n) y = 0 → y ∈ LinearMap.range f := by
    intro n
    induction n with
    | zero =>
        intro y hy
        simp only [pow_zero, Module.End.one_apply] at hy
        rw [hy]
        exact (LinearMap.range f).zero_mem
    | succ n ih =>
        intro y hy
        have hgy : (g ^ n) (g y) = 0 := by
          simpa [pow_succ] using hy
        obtain ⟨v, hv⟩ := ih (g y) hgy
        refine ⟨mu⁻¹ • (y - v), ?_⟩
        have hdiff : f y - f v = mu • y := by
          rw [hv]
          simp [g]
        rw [map_smul, map_sub, hdiff, smul_smul, inv_mul_cancel₀ hmu, one_smul]
  exact aux k x (by simpa [g] using hk)

section Spectrum

/-- **Discrete nonzero spectrum, without normality.**  For a compact complex operator, every
closed annulus avoiding zero meets the spectrum in a finite set. -/
theorem finite_setOf_mem_spectrum_norm_ge_general {T : E →L[ℂ] E}
    (hT : IsCompactOperator T) {eps : ℝ} (heps : 0 < eps) :
    {mu : ℂ | mu ∈ spectrum ℂ T ∧ eps ≤ ‖mu‖}.Finite := by
  apply (finite_setOf_hasEigenvalue_norm_ge_general hT heps).subset
  rintro mu ⟨hmu, hnorm⟩
  have hmu0 : mu ≠ 0 := by
    intro h
    simpa [h] using (lt_of_lt_of_le heps hnorm).ne'
  exact ⟨(hT.hasEigenvalue_iff_mem_spectrum hmu0).2 hmu, hnorm⟩

/-- **Every nonzero spectral point of a compact operator is isolated.**  The radius is chosen
strictly below the norm of the centre, so the whole contour also avoids zero. -/
theorem exists_isolating_closedBall_nonzero_spectrum_general {T : E →L[ℂ] E}
    (hT : IsCompactOperator T) {mu : ℂ} (hmu : mu ∈ spectrum ℂ T) (hmu0 : mu ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < ‖mu‖ ∧
      ∀ nu ∈ Metric.closedBall mu r, nu ≠ mu → nu ∈ resolventSet ℂ T := by
  let S : Set ℂ := {nu : ℂ | nu ∈ spectrum ℂ T ∧ ‖mu‖ / 2 ≤ ‖nu‖}
  have hmuNorm : 0 < ‖mu‖ := norm_pos_iff.mpr hmu0
  have hSfinite : S.Finite :=
    finite_setOf_mem_spectrum_norm_ge_general hT (half_pos hmuNorm)
  have hmuS : mu ∈ S := ⟨hmu, by linarith⟩
  obtain ⟨rho, hrho, hiso⟩ :=
    Metric.exists_closedBall_inter_eq_singleton_of_discrete hSfinite.isDiscrete hmuS
  let r : ℝ := min rho (‖mu‖ / 4)
  have hr : 0 < r := lt_min hrho (by positivity)
  have hrmu : r < ‖mu‖ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨r, hr, hrmu, fun nu hnu hnumeq => ?_⟩
  by_contra hnures
  have hnuspec : nu ∈ spectrum ℂ T := by simpa [spectrum] using hnures
  have hdist : ‖mu - nu‖ ≤ r := by
    have := Metric.mem_closedBall.mp hnu
    simpa [Complex.dist_eq, norm_sub_rev] using this
  have htri : ‖mu‖ ≤ ‖mu - nu‖ + ‖nu‖ := by
    calc
      ‖mu‖ = ‖(mu - nu) + nu‖ := by ring_nf
      _ ≤ ‖mu - nu‖ + ‖nu‖ := norm_add_le _ _
  have hnulower : ‖mu‖ / 2 ≤ ‖nu‖ := by
    have hrle : r ≤ ‖mu‖ / 4 := min_le_right _ _
    linarith
  have hnuS : nu ∈ S := ⟨hnuspec, hnulower⟩
  have hnuRho : nu ∈ Metric.closedBall mu rho :=
    Metric.closedBall_subset_closedBall (min_le_left _ _) hnu
  have hsingleton : nu ∈ ({mu} : Set ℂ) := by
    rw [← hiso]
    exact ⟨hnuRho, hnuS⟩
  exact hnumeq (by simpa using hsingleton)

end Spectrum

end GaloisForLFunctions.HTGeometry
